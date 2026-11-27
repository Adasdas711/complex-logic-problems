#!/usr/bin/env python3
"""Усложнённые задачи § 2 гл. 1 (теоремные схемы S¹) — образец переработки для занятия 10.

Заменяет в src/data/zadachi/01.md карточки с теми же номерами:
  01.02-002…006 — «получается ли формула из схемы»: составные подстановки и почти-примеры (ступени 4–5);
  01.02-011, 012, 018, 019 — длинный вывод с двумя неверными основаниями (ступень 6, диагностика);
  01.02-020…023 — выводы в 8–12 строк с R1 и R2 (ступени 6–7).
Каждый вывод проверяется s1.check2; почти-примеры — s1.axiom / s1.is_lemma.
Задачи 01.02-007…010 (существует ли формула — пример двух схем) написаны вручную в HAND.

Запуск: python3 src/scripts/gen/hard01_02.py
"""
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts"))
from s1 import C, D, N, V, axiom, check2, ftex, is_lemma, strong_tautology, tex  # noqa: E402
from open_form import test_like  # noqa: E402

rnd = random.Random(1970_1002)
x, y, z, u, w = (V(c) for c in "xyzuw")
CONV = "Буквы $x, y, z, u, w$ — элементарные высказывания; запись по соглашению книги (с. 15)."
REF = ("Схемы и правила $S^1$ (с. 15–18): A1 $x \\vdash \\sim\\sim x$; A2 $\\sim\\sim x \\vdash x$; A3 $xy \\vdash x$; "
       "A4 $xy \\vdash yx$; A7 $\\sim(xy) \\vdash \\sim xy : x\\sim y : \\sim x\\sim y$; A8 — обратная к A7; "
       "A9 $\\sim(x : y) \\vdash xy : \\sim x\\sim y$; A10 — обратная к A9; T1 $xy \\vdash y$; T2 $x \\vdash x$; "
       "T3 $x \\vdash xx$; T4 $xx \\vdash x$; T5 $yx \\vdash xy$; T6 $x : y \\vdash y : x$; T7 $y : x \\vdash x : y$; "
       "R1 — если $x \\vdash y$ и $y \\vdash z$, то $x \\vdash z$; R2 — если $x \\vdash y$ и $x \\vdash z$, то $x \\vdash yz$.")
L = "абвгдеж"


def why_text(wh):
    return wh if isinstance(wh, str) else f"{wh[0]}: {wh[1]}, {wh[2]}"


def show(lines, mark=()):
    return "\n".join(f"{n}. ${ftex(a, b)}$ [{why_text(wh)}]" for n, (a, b, wh) in enumerate(lines, 1))


def sub(a, b):
    """a — часть b (или совпадает с ней)."""
    return a == b or (b[0] == "neg" and sub(a, b[1])) or (b[0] in ("conj", "dis") and any(sub(a, c) for c in b[1]))


def size(f):
    return len(tex(f))


# ---------- шаги вывода от одной посылки ----------
ALLOW_T = True   # False — только аксиомные схемы (задачи § 1, до теоремных схем § 2)


def moves(q):
    """Схемы, применимые к формуле q как к посылке: [(имя, заключение)]."""
    out = []
    if q[0] == "neg" and q[1][0] == "neg":
        out.append(("A2", q[1][1]))
    if q[0] == "conj" and len(q[1]) == 2:
        a, b = q[1]
        out += [("A3", a), ("A4", C(b, a))] + ([("T1", b)] if ALLOW_T else [])
        if a == b and ALLOW_T:
            out.append(("T4", a))
    if q[0] == "neg" and q[1][0] == "conj" and len(q[1][1]) == 2:
        a, b = q[1][1]
        out.append(("A7", D(C(N(a), b), C(a, N(b)), C(N(a), N(b)))))
    if q[0] == "neg" and q[1][0] == "dis" and len(q[1][1]) == 2:
        a, b = q[1][1]
        out.append(("A9", D(C(a, b), C(N(a), N(b)))))
    if q[0] == "dis" and len(q[1]) == 2 and ALLOW_T:
        a, b = q[1]
        out.append(("T6", D(b, a)))
    if q[0] in ("v", "neg") and size(q) < 6:
        out.append(("A1", N(N(q))))
    return out


def build(P, want=9):
    """Случайный вывод от посылки P: R1 с примерами схем и R2. Возвращает строки вывода."""
    for _ in range(60):
        lines, facts = [], []
        first = moves(P)
        if not first:
            return None
        name, r = rnd.choice(first)
        lines.append((P, r, name))
        facts.append((r, 1))
        used_r2, tries = 0, 0
        while len(lines) < want and tries < 60:
            tries += 1
            if len(facts) >= 2 and rnd.random() < 0.3:
                (q1, i), (q2, j) = rnd.sample(facts, 2)
                if size(C(q1, q2)) > 34 or C(q1, q2) in [f for f, _ in facts] or sub(q1, q2) or sub(q2, q1):
                    continue
                lines.append((P, C(q1, q2), ("R2", i, j)))
                facts.append((C(q1, q2), len(lines)))
                used_r2 += 1
                continue
            q, i = rnd.choice(facts)
            opts = [(n, r) for n, r in moves(q) if size(r) <= 34 and r not in [f for f, _ in facts] and r != P]
            if not opts:
                continue
            name, r = rnd.choice(opts)
            lines.append((q, r, name))
            lines.append((P, r, ("R1", i, len(lines))))
            facts.append((r, len(lines)))
        a, b = lines[-1][0], lines[-1][1]
        if (lines[-1][0] == P and used_r2 and sum(1 for *_, wh in lines if isinstance(wh, tuple)) >= 3
                and not check2(lines) and strong_tautology(a, b) and 10 <= size(b) <= 30):
            return lines
    return None


def prune(lines):
    """Оставляет только строки, нужные для последней, и перенумеровывает ссылки."""
    need, stack = set(), [len(lines)]
    while stack:
        n = stack.pop()
        if n in need:
            continue
        need.add(n)
        wh = lines[n - 1][2]
        if isinstance(wh, tuple):
            stack += [wh[1], wh[2]]
    keep = sorted(need)
    new = {old: i for i, old in enumerate(keep, 1)}
    out = []
    for old in keep:
        a, b, wh = lines[old - 1]
        out.append((a, b, wh if isinstance(wh, str) else (wh[0], new[wh[1]], new[wh[2]])))
    return out


def build_ok(want, least=7):
    for _ in range(600):
        lines = build(premises(), want + 4)
        if lines:
            lines = prune(lines)
            if len(lines) >= least and not check2(lines):
                return lines
    raise RuntimeError("вывод не построен")


def premises():
    X, Y, Z = rnd.sample([x, y, z, N(x), N(y), u, w], 3)
    return rnd.choice([C(N(N(X)), Y), C(X, N(D(Y, Z))), C(N(C(X, Y)), Z), N(D(C(X, Y), Z)), C(D(X, Y), N(N(Z)))])


# ---------- почти-примеры ----------
def inst(name, X, Y):
    return {"A3": (C(X, Y), X), "T1": (C(X, Y), Y), "A4": (C(X, Y), C(Y, X)), "T5": (C(Y, X), C(X, Y)),
            "A7": (N(C(X, Y)), D(C(N(X), Y), C(X, N(Y)), C(N(X), N(Y)))),
            "A9": (N(D(X, Y)), D(C(X, Y), C(N(X), N(Y)))), "T6": (D(X, Y), D(Y, X))}[name]


def fits(a, b, name):
    return axiom(a, b) == name if name[0] == "A" else is_lemma(a, b, name)


SCHEME = {"A3": "xy \\vdash x", "T1": "xy \\vdash y", "A4": "xy \\vdash yx", "T5": "yx \\vdash xy",
          "A7": "\\sim(xy) \\vdash \\sim xy : x\\sim y : \\sim x\\sim y", "A9": "\\sim(x : y) \\vdash xy : \\sim x\\sim y",
          "T6": "x : y \\vdash y : x"}


def near_miss(name, X, Y):
    a, b = inst(name, X, Y)
    if name == "A7":
        return a, D(C(N(X), Y), C(X, N(Y)), C(N(X), Y))          # третий член повторяет первый
    if name == "A9":
        return a, D(C(X, Y), C(N(X), Y))                          # второй член без отрицания перед Y
    if name == "A4":
        return a, C(Y, N(X)) if X[0] != "neg" else C(Y, X[1])
    if name == "T5":
        return C(Y, X), C(Y, X)
    return a, N(b) if b[0] != "neg" else b[1]


def compound():
    return rnd.choice([C(x, N(y)), D(u, w), N(C(y, z)), C(N(x), z), D(x, N(z)), N(N(u))])


def sub_text(X, Y, name):
    return f"$x$ := ${tex(X)}$" + ("" if name in ("A1", "A2") else f", $y$ := ${tex(Y)}$")


def subst_card(num, name, yes):
    X, Y = compound(), compound()
    while Y == X:
        Y = compound()
    a, b = inst(name, X, Y) if yes else near_miss(name, X, Y)
    assert fits(a, b, name) == yes, (name, yes)
    cond = (f"{CONV} Схема {name}: ${SCHEME[name]}$. Установите, получается ли из неё формула ${ftex(a, b)}$ заменой "
            "метапеременных (одинаковые буквы — одинаковыми высказываниями). Если получается — укажите замену; "
            "если нет — назовите вхождение, которое мешает.")
    if yes:
        ans = f"Получается: {sub_text(X, Y, name)}."
        sol = (f"1. Сопоставляем посылку ${tex(a)}$ с посылкой схемы: {sub_text(X, Y, name)}.\n"
               f"2. Подставляем в заключение схемы ${SCHEME[name].split(' \\vdash ')[1]}$ и получаем ${tex(b)}$ — "
               "это заключение данной формулы.\n3. Значит, формула — пример схемы (схемы — с. 15–18).")
    else:
        ga, gb = inst(name, X, Y)
        ans = f"Не получается: по посылке {sub_text(X, Y, name)}, тогда заключение должно быть ${tex(gb)}$."
        sol = (f"1. Посылка ${tex(a)}$ однозначно задаёт замену: {sub_text(X, Y, name)}.\n"
               f"2. При этой замене схема даёт заключение ${tex(gb)}$, а в формуле — ${tex(b)}$: они различаются.\n"
               "3. Другой замены нет, поэтому формула — не пример схемы (схемы — с. 15–18).")
    return num, dict(level=5 if yes else 4, type="R" if yes else "E", step="vary", form="sym", answer="short",
                     source="с. 15–18, гл. 1, § 2", tags="S1, теоремные схемы, подстановка", cond=cond, ans=ans, sol=sol)


# ---------- выводы ----------
def deriv_card(num):
    lines = build_ok(rnd.choice([9, 10, 11]), least=8)
    a, b = lines[-1][0], lines[-1][1]
    cond = f"{CONV} Выведите в $S^1$ формулу ${ftex(a, b)}$, пользуясь аксиомными схемами, теоремными схемами § 2 и правилами $S^1$."
    ans = f"Например, вывод в {len(lines)} строк (см. решение); последняя строка — ${ftex(a, b)}$ [{why_text(lines[-1][2])}]."
    sol = show(lines) + "\n\nСхемы — с. 15–18; правила R1, R2 — с. 17."
    return num, dict(level=7 if len(lines) >= 10 else 6, type="D", step="open", form="sym", answer="proof",
                     source="с. 15–20, гл. 1, § 1–2", tags="S1, вывод", cond=cond, ans=ans, sol=sol)


WRONG = {"A3": "T1", "T1": "A3", "A2": "A1", "A1": "A2", "A7": "A9", "A9": "A7", "T6": "A4", "A4": "T6", "T4": "T3"}


def diag_card(num):
    for _ in range(200):
        lines = build_ok(rnd.choice([8, 9]), least=7)
        cand = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, str) and wh in WRONG]
        rs = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, tuple) and wh[0] == "R1"]
        if len(cand) < 1 or len(rs) < 1:
            continue
        i = rnd.choice(cand)
        j = rnd.choice(rs)
        bad = list(lines)
        a, b, wh = bad[i]
        bad[i] = (a, b, WRONG[wh])
        a2, b2, wh2 = bad[j]
        bad[j] = (a2, b2, ("R2", wh2[1], wh2[2]))
        errs = check2(bad)
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        if steps == sorted([i + 1, j + 1]):
            break
    else:
        raise RuntimeError("нет подходящего вывода")
    p, q = sorted([i, j])
    fix = {i: lines[i][2], j: lines[j][2]}
    cond = (f"{CONV} В выводе формулы ${ftex(lines[-1][0], lines[-1][1])}$ ровно два основания указаны неверно. "
            f"Найдите их, объясните, почему каждое неверно, и исправьте.\n\n{show(bad)}")
    ans = (f"Шаг {p + 1}: верно [{why_text(fix[p])}]; шаг {q + 1}: верно [{why_text(fix[q])}].")
    exp = []
    for k in (p, q):
        a, b, _ = lines[k]
        if k == i:
            exp.append(f"Шаг {k + 1}: ${ftex(a, b)}$ — пример схемы {fix[k]}, а не {WRONG[fix[k]]} "
                       f"(схемы — с. 15–18).")
        else:
            exp.append(f"Шаг {k + 1}: R2 даёт формулу с конъюнкцией двух заключений при одной посылке, а здесь "
                       f"заключение строки {fix[k][1]} служит посылкой строки {fix[k][2]} — это R1 (с. 17).")
    sol = "\n".join(exp) + "\n\nИсправленный вывод:\n\n" + show(lines)
    assert not check2(lines)
    return num, dict(level=6, type="E", step="vary", form="sym", answer="text", source="с. 15–18, гл. 1, § 2",
                     tags="S1, вывод, диагностика", cond=cond, ans=ans, sol=sol)


def show_hidden(lines, hide_why, hide_f):
    out = []
    for n, (a, b, wh) in enumerate(lines, 1):
        f = "…" if n in hide_f else f"${ftex(a, b)}$"
        out.append(f"{n}. {f} [{'…' if n in hide_why else why_text(wh)}]")
    return "\n".join(out)


def complete_card(num):
    """Длинный вывод: пропущены три-четыре основания и две строки-формулы."""
    lines = build_ok(rnd.choice([10, 11]), least=9)
    schema_lines = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, str)]
    rule_lines = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, tuple)]
    hide_f = set(rnd.sample(schema_lines[1:] or schema_lines, min(2, len(schema_lines) - 1 or 1)))
    hide_why = set(rnd.sample([n for n in schema_lines if n not in hide_f], min(2, len(schema_lines) - len(hide_f))))
    hide_why |= set(rnd.sample(rule_lines[:-1], min(2, len(rule_lines) - 1)))
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} В выводе формулы ${ftex(a, b)}$ пропущены основания некоторых шагов и формулы некоторых строк "
            f"(«…»). Восстановите их.\n\n{show_hidden(lines, hide_why, hide_f)}")
    parts = []
    for n in sorted(hide_why | hide_f):
        la, lb, wh = lines[n - 1]
        s = f"{n} — " + (f"${ftex(la, lb)}$" if n in hide_f else "")
        if n in hide_why:
            s += ("" if n not in hide_f else " ") + f"[{why_text(wh)}]"
        parts.append(s)
    ans = "; ".join(parts)
    sol = ("Строку-формулу восстанавливаем по соседним строкам: в R1 заключение одной строки — посылка другой, "
           "в R2 обе строки имеют общую посылку. Полный вывод:\n\n" + show(lines) + "\n\nСхемы — с. 15–18; правила — с. 17.")
    return dict(level=5, type="D", step="complete", form="sym", answer="build", source="с. 15–20, гл. 1, § 1–2",
                tags="S1, вывод, дополнение", cond=cond, ans=ans, sol=sol)


NAMES = ["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10", "T1", "T2", "T3", "T4", "T5", "T6", "T7"]


def all_schemes(a, b):
    out = []
    for n in NAMES:
        if n[0] == "A" and n not in ("A3", "A4") and axiom(a, b) == n:
            out.append(n)
        elif n in ("A3", "A4"):
            if a[0] == "conj" and len(a[1]) == 2 and b == (a[1][0] if n == "A3" else C(a[1][1], a[1][0])):
                out.append(n)
        elif n[0] == "T" and is_lemma(a, b, n):
            out.append(n)
    return out


def recognize_card():
    X, Y, Z = compound(), compound(), compound()
    while len({X, Y, Z}) < 3:
        Y, Z = compound(), compound()
    pool = [(*inst("A9", X, Y), "A9", f"$x$ := ${tex(X)}$, $y$ := ${tex(Y)}$"),
            (C(X, X), X, "A3", f"$x$ := ${tex(X)}$, $y$ := ${tex(X)}$"),
            (D(Y, X), D(X, Y), "T6", f"$x$ := ${tex(Y)}$, $y$ := ${tex(X)}$"),
            (N(N(C(Z, Z))), C(Z, Z), "A2", f"$x$ := ${tex(C(Z, Z))}$"),
            (C(Y, Z), C(Z, Y), "A4", f"$x$ := ${tex(Y)}$, $y$ := ${tex(Z)}$")]
    rnd.shuffle(pool)
    for a, b, n, _ in pool:
        assert n in all_schemes(a, b)
    items = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b, _, _) in enumerate(pool))
    ans = "; ".join(f"{L[k]}) " + ", ".join(all_schemes(a, b)) + f" ({n}: {s})" for k, (a, b, n, s) in enumerate(pool))
    cond = (f"{CONV} Для каждой формулы найдите все аксиомные (A1–A4, A7–A10) и теоремные (T1–T7) схемы, примером "
            f"которых она является, и для одной из них укажите замену метапеременных.\n\n{items}")
    sol = ("Формула — пример схемы, если получается из неё заменой метапеременных (одинаковые — одинаково). "
           "Совпадение членов даёт сразу несколько схем: $XX \\vdash X$ — пример A3, T1 и T4; "
           "$XY \\vdash YX$ — пример A4 и T5; $X : Y \\vdash Y : X$ — пример T6 и T7. Схемы — с. 15–18.\n\n"
           + "  \n".join(f"{L[k]}) " + ", ".join(all_schemes(a, b)) + f"; замена для {n}: {s}." for k, (a, b, n, s) in enumerate(pool)))
    return dict(level=4, type="R", step="iso", form="sym", answer="short", source="с. 15–18, гл. 1, § 1–2",
                tags="S1, теоремные схемы", cond=cond, ans=ans, sol=sol)


def series_card():
    """Тавтологичность и доказуемость в S¹ для длинных формул: доказуемая, с новой буквой, не тавтология."""
    from s1 import counterexample, new_atoms, tautology
    items = []
    tries = 0
    want = ["strong", "new", "non", rnd.choice(["strong", "new", "non"])]
    while len(items) < 4 and tries < 5000:
        tries += 1
        kind = want[len(items)]
        if kind in ("strong", "new"):
            lines = build_ok(6, least=4)
            a, b = lines[-1][0], lines[-1][1]
            if kind == "new":
                b = D(b, C(z, N(z))) if rnd.random() < .5 else C(b, D(w, N(w)))
                b = N(N(b)) if rnd.random() < .3 else b
                if not tautology(a, b) or not new_atoms(a, b):
                    continue
        else:
            lines = build_ok(6, least=4)
            a, b = lines[-1][0], lines[-1][1]
            b = C(b, N(lines[0][1])) if b[0] != "neg" else b[1]
            if tautology(a, b):
                continue
        if a != b and 12 <= len(tex(a)) + len(tex(b)) <= 46 and (a, b) not in items:
            items.append((a, b))
    rnd.shuffle(items)
    ans, sol = [], []
    for k, (a, b) in enumerate(items):
        if strong_tautology(a, b):
            ans.append(f"{L[k]}) тавтология, в $S^1$ доказуема")
            sol.append(f"{L[k]}) Тавтология, новых букв в заключении нет — сильная тавтология, по § 7, MT6 (с. 32) доказуема.")
        elif tautology(a, b):
            na = ", ".join(f"${t}$" for t in sorted(new_atoms(a, b)))
            ans.append(f"{L[k]}) тавтология, в $S^1$ недоказуема")
            sol.append(f"{L[k]}) Тавтология, но в заключение входит {na}, которого нет в посылке; по § 4, MT1 (с. 21) — недоказуема.")
        else:
            env = counterexample(a, b)
            ev = ", ".join(f"${p} = {v}$" for p, v in sorted(env.items()))
            ans.append(f"{L[k]}) не тавтология, в $S^1$ недоказуема")
            sol.append(f"{L[k]}) При {ev} посылка — 1, заключение — 0: не тавтология; по § 5, MT1 (с. 22) — недоказуема.")
    body = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b) in enumerate(items))
    cond = (f"{CONV} Для каждой формулы установите: (1) её тавтологичность — верна ли она как формула классической "
            "логики высказываний ($:$ — «одно и только одно из»); (2) её доказуемость в $S^1$. Для нетавтологии укажите "
            "значения, при которых посылка истинна, а заключение ложно. Пользуйтесь критерием: формула доказуема в $S^1$ "
            "тогда и только тогда, когда она — сильная тавтология, то есть тавтология, в заключение которой не входят "
            "элементарные высказывания, отсутствующие в посылке (§ 4, MT1, с. 21; § 5, MT1, с. 22; § 7, MT6, с. 32)."
            f"\n\n{body}")
    return dict(level=7, type="S", step="transfer", form="sym", answer="short", source="с. 15–32, гл. 1",
                tags="S1, классическая логика", cond=cond, ans="; ".join(ans), sol="\n".join(sol))


# ---------- вручную: существует ли формула — пример двух схем ----------
HAND = {
    7: dict(level=6, type="A", step="open", form="sym", answer="build", source="с. 15–18, гл. 1, § 1–2",
            tags="S1, схемы, построение",
            cond=f"{CONV} Постройте формулу следования, которая одновременно является примером аксиомной схемы A3 "
                 "($xy \\vdash x$) и теоремной схемы T1 ($xy \\vdash y$), или докажите, что такой формулы нет.",
            ans="Есть, например $zz \\vdash z$ (и вообще любая $XX \\vdash X$).",
            sol="1. Пример A3 имеет вид $XY \\vdash X$, пример T1 — $X'Y' \\vdash Y'$ (с. 15, 18).\n"
                "2. Посылки совпадают: $X = X'$, $Y = Y'$. Заключения совпадают: $X = Y'= Y$.\n"
                "3. Значит, годится любая формула $XX \\vdash X$, например $zz \\vdash z$; она же пример T4."),
    8: dict(level=6, type="A", step="open", form="sym", answer="build", source="с. 15, гл. 1, § 1",
            tags="S1, схемы, построение",
            cond=f"{CONV} Постройте формулу следования, которая одновременно является примером схем A1 "
                 "($x \\vdash \\sim\\sim x$) и A2 ($\\sim\\sim x \\vdash x$), или докажите, что такой формулы нет.",
            ans="Такой формулы нет.",
            sol="1. Пример A1: $X \\vdash \\sim\\sim X$; пример A2: $\\sim\\sim Y \\vdash Y$ (с. 15).\n"
                "2. Совпадение посылок даёт $X = \\sim\\sim Y$, совпадение заключений — $\\sim\\sim X = Y$.\n"
                "3. Тогда $Y = \\sim\\sim\\sim\\sim Y$: высказывание совпадает со своей собственной частью, что "
                "невозможно (в $\\sim\\sim\\sim\\sim Y$ знаков больше, чем в $Y$). Формулы нет."),
    9: dict(level=6, type="A", step="open", form="sym", answer="build", source="с. 18, гл. 1, § 2",
            tags="S1, схемы, построение",
            cond=f"{CONV} Постройте формулу следования, которая одновременно является примером теоремных схем T3 "
                 "($x \\vdash xx$) и T4 ($xx \\vdash x$), или докажите, что такой формулы нет.",
            ans="Такой формулы нет.",
            sol="1. Пример T3: $X \\vdash XX$; пример T4: $YY \\vdash Y$ (с. 18).\n"
                "2. Посылки: $X = YY$; заключения: $XX = Y$.\n"
                "3. Тогда $Y = (YY)(YY)$: высказывание длиннее самого себя — невозможно. Формулы нет."),
    10: dict(level=6, type="A", step="open", form="sym", answer="build", source="с. 15–16, гл. 1, § 1",
             tags="S1, схемы, построение",
             cond=f"{CONV} Постройте формулу следования, которая одновременно является примером аксиомных схем A3 "
                  "($xy \\vdash x$) и A4 ($xy \\vdash yx$), или докажите, что такой формулы нет.",
             ans="Такой формулы нет.",
             sol="1. Пример A3: $XY \\vdash X$; пример A4: $X'Y' \\vdash Y'X'$ (с. 15–16).\n"
                 "2. Посылки совпадают: $X = X'$, $Y = Y'$; заключения: $X = YX$.\n"
                 "3. Высказывание $X$ было бы собственной частью высказывания $YX$, равного ему, — невозможно. Формулы нет."),
}


def render(cid, c, sec=2):
    return (f'---\nid: "{cid}"\nchapter: 1\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\nstep: {c["step"]}\n'
            f'condition: def\nform: {c["form"]}\nanswer: {c["answer"]}\nsource: "{c["source"]}"\nsystem: "S^1"\n'
            f'generated: true\ntags: [{c["tags"]}]\n---\n\n## Условие\n\n{c["cond"]}\n\n## Ответ\n\n{c["ans"]}\n\n'
            f'## Решение\n\n{c["sol"]}\n')


def main():
    cards = {}
    for num, (name, yes) in zip(range(2, 7), [("A7", True), ("T5", True), ("A9", False), ("A4", True), ("A7", False)]):
        cards[num] = subst_card(num, name, yes)[1]
    for num in (11, 12, 18, 19):
        cards[num] = diag_card(num)[1]
    for num in range(20, 24):
        cards[num] = deriv_card(num)[1]
    cards.update(HAND)
    for num in range(13, 18):
        cards[num] = complete_card(num)
    cards[1] = recognize_card()
    extra = {f"01.01-{n}": series_card() for n in (110, 111, 112)}
    for c in list(cards.values()) + list(extra.values()):
        assert not test_like(c["cond"]), c["cond"][:80]
    path = ROOT / "data" / "zadachi" / "01.md"
    text = path.read_text(encoding="utf-8")
    parts = re.split(r"(\n=====\n)", text)
    done = 0
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(01\.0[12])-(\d{3})"', chunk, re.M)
        if not m:
            continue
        cid = f"{m.group(1)}-{m.group(2)}"
        c = cards.get(int(m.group(2))) if m.group(1) == "01.02" else extra.get(cid)
        if c:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            sec = int(m.group(1)[-1])
            parts[i] = lead + render(cid, c, sec).rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
            done += 1
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {done} из {len(cards) + len(extra)}")


if __name__ == "__main__":
    main()
