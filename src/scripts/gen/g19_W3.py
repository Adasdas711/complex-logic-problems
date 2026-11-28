#!/usr/bin/env python3
"""Раздел 19, § 22–31 («Логическая физика», гл. 3, с. 151–171): программная проверка ответов черновиков.

Карточки § 22–31 написаны вручную (drafts/19.22.md … drafts/19.31.md). Здесь пересчитано всё, что поддаётся
механической проверке: числа (скорость, минимальные длительности и интервалы, число посредников), выполнимость
и противоречивость пропозициональных комбинаций (предикаты тенденций, парадокс связей, условные предикаты,
причинные отношения $C^1$, $C^2$), значения $E(\\text{Мир})$ в неклассическом случае, конечность Мира в прошлом
на конечных и счётных порядках, опосредованность воздействия относительно класса.

Высказывания вида $x \\to (Rx)y$, $tP(a)$, $cQ(a)$ рассматриваются как отдельные пропозициональные
переменные (их внутреннее строение логикой высказываний не учитывается), связанные лишь условиями, которые
принимает книга: $\\vdash P(a) \\to tP(a)$ (с. 159), $\\vdash Q(a) \\to x$ (с. 162) и т. п.

  python3 src/scripts/gen/g19_W3.py      — все проверки; код выхода 1 при расхождении
"""
import itertools
import math
import sys
from fractions import Fraction as F

FAIL = []


def ok(cond, what):
    if not cond:
        FAIL.append(what)


# ---------- логика высказываний: перебор оценок ----------
def models(atoms, constraints):
    for vals in itertools.product([False, True], repeat=len(atoms)):
        v = dict(zip(atoms, vals))
        if all(c(v) for c in constraints):
            yield v


def sat(atoms, constraints, formula):
    return any(formula(v) for v in models(atoms, constraints))


def entails(atoms, constraints, prem, concl):
    return all(concl(v) for v in models(atoms, constraints) if prem(v))


imp = lambda a, b: (not a) or b  # noqa: E731


# ---------- § 22. Скорость (с. 151–153) ----------
def speed_bounds(m, n, kmin):
    """Скорость m/n; нижний предел 1/n (m = 1); верхний — при непрерывном ряде изменений минимальной
    длительности: m_max = n / kmin (с. 152)."""
    return F(m) / F(n), 1 / F(n), (F(n) / F(kmin)) / F(n), F(n) / F(kmin)


v, lo, hi, mmax = speed_bounds(6, 3, F(1, 4))
ok((v, lo, hi, mmax) == (2, F(1, 3), 4, 12), "22: m=6, n=3, kmin=1/4")
ok(lo <= v <= hi, "22: границы")
# перемещение: эталон 0,5 м, путь 20 м за 8 с
m = F(20) / F(1, 2)
ok(m == 40 and m / 8 == 5 and F(20, 8) == F(5, 2), "22: перемещения")
# отчёты: (m, n, kmin) -> возможно ли
reports = {"а": (10, 2, F(1, 4)), "б": (8, 2, F(1, 4)), "в": (0, 2, F(1, 4)), "г": (3, F(1, 2), F(1, 4))}
verdict = {}
for k, (mm, nn, kk) in reports.items():
    if mm < 1:
        verdict[k] = "процесса нет"
    elif F(nn) < F(kk):
        verdict[k] = "невозможно"
    elif F(mm) > F(nn) / F(kk):
        verdict[k] = "невозможно"
    else:
        verdict[k] = F(mm) / F(nn)
# г: m_max = (1/2)/(1/4) = 2 < 3 -> невозможно
ok(verdict == {"а": "невозможно", "б": 4, "в": "процесса нет", "г": "невозможно"}, f"22: отчёты {verdict}")

# ---------- § 24. Разность различных протяжённостей не меньше минимальной (с. 154) ----------
def diffs_ok(lengths, lmin):
    return all(a == b or abs(a - b) >= lmin for a, b in itertools.combinations(lengths, 2))


ok(not diffs_ok([F(3), F("3.2")], F(1, 2)), "24: 3 и 3,2 при min 0,5")
ok(diffs_ok([F(3), F("3.5"), F(5)], F(1, 2)), "24: 3; 3,5; 5")
ok(not diffs_ok([F(2), F("2.5"), F("2.75")], F(1, 2)), "24: 2; 2,5; 2,75")
ok(diffs_ok([F(4), F(4), F("5.5")], F(1, 2)), "24: 4; 4; 5,5")

# ---------- § 25. Мир в целом (с. 155–158) ----------
def E_world(vals):
    """vals — значения E для эмпирических индивидов: 'E', 'notE' (¬E), '?E'.
    ⊢ E(Мир) ≡ (∃x)E(x); ⊢ ¬E(Мир) ≡ (∀x)¬E(x) (с. 156); ?E ≡ Df ~E ∧ ~¬E (с. 66)."""
    if any(x == "E" for x in vals):
        return "E"
    if all(x == "notE" for x in vals):
        return "notE"
    return "?E"


ok(E_world(["E", "notE", "notE"]) == "E", "25: а")
ok(E_world(["notE", "notE"]) == "notE", "25: б")
ok(E_world(["notE", "?E", "notE"]) == "?E", "25: в")
ok(E_world(["?E", "E"]) == "E", "25: г")


def past_finite(order):
    """(∃x)(∀y)(x ≤ βy) на конечном порядке (числа — места во времени, больше — позже)."""
    return any(all(x <= y for y in order) for x in order)


def past_infinite(order):
    """(∀x)(∃y)(y < βx)."""
    return all(any(y < x for y in order) for x in order)


for o in ([0, 1, 2, 5], [3], list(range(-5, 6))):
    ok(past_finite(o) and not past_infinite(o), f"25: конечный порядок {o}")
# все конечные непустые порядки до 5 элементов: оба определения не выполняются одновременно
for k in range(1, 6):
    for o in itertools.combinations(range(8), k):
        ok(not (past_finite(o) and past_infinite(o)), "25: несовместимость")
# ℤ и ℕ (рассуждение): у ℕ есть наименьший — конечен в прошлом; у ℤ для каждого x есть x-1 — бесконечен.

# ---------- § 26. Опосредованная связь (с. 158) ----------
def between(c, a, b):
    """c между a и b относительно α (с. 82): (c > a ∧ b > c) ∨ (a > c ∧ c > b)."""
    return (c > a and b > c) or (a > c and c > b)


ok(between(2, 0, 4) and not between(5, 0, 4) and not between(0, 0, 4), "26: между")
# места в единицах минимального интервала: при интервале, равном минимальному, промежуточного места нет
ok(not any(between(c, 0, 1) for c in range(-3, 5)), "26: минимальный интервал")

# ---------- § 27. Предикаты тенденций (с. 159–160) ----------
A27 = ["P1", "P2", "P3", "tP1", "tP2", "tP3"]
C27 = [lambda v, i=i: imp(v[f"P{i}"], v[f"tP{i}"]) for i in (1, 2, 3)]
ok(sat(A27, C27, lambda v: not v["P1"] and not v["P2"] and v["P3"] and v["tP1"] and v["tP2"]), "27: с. 160")
ok(not sat(A27, C27, lambda v: v["P1"] and not v["tP1"]), "27: P ∧ ~tP")
ok(sat(A27, C27, lambda v: v["tP1"] and not v["P1"]), "27: tP ∧ ~P")
ok(entails(A27, C27, lambda v: not v["tP1"], lambda v: not v["P1"]), "27: ~tP → ~P")
ok(not entails(A27, C27, lambda v: not v["P1"], lambda v: not v["tP1"]), "27: ~P ⊬ ~tP")
C27x = C27 + [lambda v: imp(v["P1"], not v["P2"])]
ok(not sat(A27, C27x, lambda v: v["P1"] and v["P2"]), "27: P1 ∧ P2 при исключении")
ok(sat(A27, C27x, lambda v: v["tP1"] and v["tP2"]), "27: tP1 ∧ tP2 при исключении")
# условие реализации: x → (tP → Q); Q и P несовместимы — выполнимо вместе с x, tP, Q, ~P
A27b = ["x", "P", "tP", "Q"]
C27b = [lambda v: imp(v["P"], v["tP"]), lambda v: imp(v["x"], imp(v["tP"], v["Q"])), lambda v: not (v["P"] and v["Q"])]
ok(sat(A27b, C27b, lambda v: v["x"] and v["tP"] and v["Q"] and not v["P"]), "27: реализация")
ok(entails(A27b, C27b, lambda v: v["x"] and v["tP"], lambda v: v["Q"] and not v["P"]), "27: реализация ⇒ Q ∧ ~P")

# ---------- § 28. Парадокс связей (с. 160–162) ----------
ok(not sat(["x", "y"], [], lambda v: v["x"] and not v["y"] and not v["x"] and v["y"]), "28: x∧~y∧~x∧y")
# общий случай: условия w1 → ~y, w2 → ~x; совместное применение: x ∧ y ∧ w1 ∧ w2
A28 = ["x", "y", "w1", "w2"]
C28 = [lambda v: imp(v["w1"], not v["y"]), lambda v: imp(v["w2"], not v["x"])]
ok(not sat(A28, C28, lambda v: v["x"] and v["y"] and v["w1"] and v["w2"]), "28: общий случай")
ok(sat(A28, C28, lambda v: v["x"] and v["w1"]) and sat(A28, C28, lambda v: v["y"] and v["w2"]), "28: (1), (2) по отдельности")
# одинаковые условия (без ~y, ~x) не дают противоречия
ok(sat(["x", "y", "w"], [], lambda v: v["x"] and v["y"] and v["w"]), "28: без различия условий")
# n сил: w^i → ~x^j (j ≠ i)
for n in range(2, 6):
    A = [f"x{i}" for i in range(n)] + [f"w{i}" for i in range(n)]
    C = [lambda v, i=i, j=j: imp(v[f"w{i}"], not v[f"x{j}"]) for i in range(n) for j in range(n) if i != j]
    ok(not sat(A, C, lambda v: all(v[f"x{i}"] and v[f"w{i}"] for i in range(n))), f"28: n={n}")
    # любые две силы уже дают противоречие
    ok(not sat(A, C, lambda v: v["x0"] and v["w0"] and v["x1"] and v["w1"]), f"28: пара, n={n}")
# тенденции: z*, v* — не противоречие
ok(sat(["zs", "vs"], [], lambda v: v["zs"] and v["vs"]), "28: z* ∧ v*")

# ---------- § 29. Условные предикаты (с. 162–163) ----------
A29 = ["C", "x", "Q"]           # C — высказывание x → (Rx)Q(a), т. е. cQ(a) по определению (1)
C29 = [lambda v: imp(v["Q"], v["x"])]   # (2) ⊢ Q(a) → x
ok(sat(A29, C29, lambda v: v["C"] and not v["x"]), "29: (3) выполнимо")
ok(entails(A29, C29, lambda v: v["C"] and not v["x"], lambda v: v["C"] and not v["Q"]), "29: (3) ⇒ (6)")
ok(entails(A29, C29, lambda v: not v["x"], lambda v: not v["Q"]), "29: (5)")
ok(not entails(A29, C29, lambda v: v["C"], lambda v: v["Q"]), "29: cQ ⊬ Q")

# ---------- § 30. Воздействие (с. 163–167) ----------
def max_mediators(t, d, i):
    """Непрерывный ряд sα, sγ¹, …, sγⁿ, sβ: n событий длительностью не меньше d, n + 1 интервалов,
    каждый равен минимальному i (соседние соприкасаются, АФ⁷); n·d + (n + 1)·i ≤ t (с. 165)."""
    n = 0
    while (n + 1) * d + (n + 2) * i <= t:
        n += 1
    return n


ok(max_mediators(20, 2, 1) == 6 and 6 * 2 + 7 * 1 == 19, "30: t=20, d=2, i=1")
ok(max_mediators(F(9, 10), F(1, 10), F(1, 20)) == 5, "30: t=0,9, d=0,1, i=0,05")
ok(5 * F(1, 10) + 6 * F(1, 20) == F(8, 10) and 6 * F(1, 10) + 7 * F(1, 20) > F(9, 10), "30: проверка 5 и 6")
ok(max_mediators(10, 3, 1) == 2, "30: t=10, d=3, i=1")
# общая граница: n ≤ (t − i)/(d + i)
for t, d, i in [(20, 2, 1), (10, 3, 1), (F(9, 10), F(1, 10), F(1, 20)), (100, 7, 2)]:
    ok(max_mediators(t, d, i) == math.floor(F(t - i) / F(d + i)), f"30: граница {t, d, i}")
# «мимо цели»: длительности 3, 4, 2, 5 и 5 интервалов по 1 при t = 15
ok(sum([3, 4, 2, 5]) + 5 * 1 == 19 and 19 > 15, "30: мимо цели")
ok(sum([2, 2, 3]) + 4 * 1 == 11 and 11 <= 15, "30: ряд укладывается")
# перемещение тела c: 120 м при скорости c не больше 40 м/с — не меньше 3 с
ok(F(120, 40) == 3 and 2 < 3 and 5 >= 3, "30: перемещение c")


def mediated(chains, A):
    """chains — цепочки посредников [c¹, …, cⁿ] (для каждой даны α→(Rα)γ¹, …, γⁿ→(Rγⁿ)β).
    Опосредованное относительно A — есть цепочка, все посредники которой в A; непосредственное — нет
    ни одного c ∈ A с α→(Rα)γ и γ→(Rγ)β (цепочки длины 1) (с. 164)."""
    med = any(ch and all(c in A for c in ch) for ch in chains)
    direct = not any(len(ch) == 1 and ch[0] in A for ch in chains)
    return med, direct


chains = [["c1"], ["c2", "c3"]]
ok(mediated(chains, {"c1"}) == (True, False), "30: A1")
ok(mediated(chains, {"c2", "c3"}) == (True, True), "30: A2")
ok(mediated(chains, {"c3"}) == (False, True), "30: A3")
ok(mediated(chains, {"c2"}) == (False, True), "30: A4")

# ---------- § 31. Причина (с. 167–171) ----------
# C1: x → (Rx)y — переменная K; C2: x ∧ (Rx)y ∧ (~x → (R~x)~y) — x, Rxy, N
def C1(v):
    return v["K"]


def C2(v):
    return v["x"] and v["Rxy"] and v["N"]


A31 = ["x", "Rxy", "K", "N"]
ok(sat(A31, [], lambda v: C1(v) and not v["x"]), "31: C1 ∧ ~x выполнимо")
ok(not sat(A31, [], lambda v: C2(v) and not v["x"]), "31: C2 ∧ ~x невыполнимо")
ok(entails(A31, [], C2, lambda v: v["x"] and v["Rxy"]), "31: C2 ⊨ x ∧ (Rx)y")
ok(not entails(A31, [], C2, C1), "31: C2 ⊭ C1 (как переменные)")
# две причины одного sy по C2
A31b = ["x", "z", "Rxy", "Rzy", "Nx", "Nz"]
ok(sat(A31b, [], lambda v: all(v.values())), "31: sxC²sy ∧ szC²sy")
# сценарии задачи 31 (серия): (x, Rxy, K, N) -> (C1, C2)
scen = {"а": dict(x=True, Rxy=True, K=True, N=True), "б": dict(x=False, Rxy=False, K=True, N=True),
        "в": dict(x=True, Rxy=True, K=True, N=False), "г": dict(x=True, Rxy=True, K=False, N=True)}
res = {k: (C1(v), C2(v)) for k, v in scen.items()}
ok(res == {"а": (True, True), "б": (True, False), "в": (True, False), "г": (False, True)}, f"31: сценарии {res}")

if FAIL:
    print("Расхождения:", *FAIL, sep="\n  ")
    sys.exit(1)
print("g19_W3: все проверки § 22–31 пройдены")
