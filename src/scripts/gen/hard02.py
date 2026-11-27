#!/usr/bin/env python3
"""Усложнение гл. 2 (система S₁, занятия 16–20) по образцу занятия 10.

Заменяет в src/data/zadachi/02.md карточки ступеней 1–4 (и короткие задачи ступеней 5–6) трудными:
  § 1–2 — выводы в S₁ в 8–12 строк (A1–A11, R1, R2), дополнение длинных выводов (пропущены и основания, и формулы
          строк), выводы с двумя неверными основаниями (в том числе A1/A2 — нумерация S₁ обратна S¹), составные
          замены и почти-примеры схем A7–A11, опознание всех схем, серии длинных формул (полнота, MT5) с
          обоснованием значениями; построения «пример двух схем или докажите, что нельзя» — вручную;
  § 3 — длинные формулы в таблицах независимости (с. 43–44) с обоснованием значениями, таблицы с пропусками,
        диагностика с двумя ошибками;
  § 4 — перевод длинных формул S¹ ↔ S₁ (D2 § 3 гл. 1; D1 § 1 гл. 2) с проверкой доказуемости, диагностика;
  § 5 — сильное следование для длинных формул, диагностика с двумя ошибками, построения.
Выводы проверяются s1w.check, доказуемость — критерием сильной тавтологии, таблицы — indep_w.

Запуск: python3 src/scripts/gen/hard02.py
"""
import random
import re
import sys
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts"))
import indep_w as IW  # noqa: E402
import s1 as S  # noqa: E402
from s1 import C, N, V, atoms  # noqa: E402
from s1w import W, axiom, check, counterexample, ftex, new_atoms, strong, tautology, tex, value  # noqa: E402
from open_form import test_like  # noqa: E402

rnd = random.Random(1970_0200)
x, y, z, u, w = (V(c) for c in "xyzuw")
L = "абвгдежз"
CONV = ("Буквы $x, y, z, u, w$ — элементарные высказывания; $\\vee$ — соединительная дизъюнкция («по крайней мере одно "
        "из», гл. 2, § 1, с. 36); запись — по соглашению книги.")
CRIT = ("Критерий: формула доказуема в $S_1$ тогда и только тогда, когда она — сильная тавтология, то есть тавтология, "
        "в заключение которой не входят элементарные высказывания, отсутствующие в посылке (гл. 2, § 2, MT5, с. 43; "
        "обратное — непротиворечивость и непарадоксальность $S_1$, с. 37).")
SRC1 = "с. 36–37, гл. 2, § 1"


def why_text(wh):
    return wh if isinstance(wh, str) else f"{wh[0]}: {wh[1]}, {wh[2]}"


def show(lines):
    return "\n".join(f"{n}. ${ftex(a, b)}$ [{why_text(wh)}]" for n, (a, b, wh) in enumerate(lines, 1))


def size(f):
    return len(tex(f))


def sub(a, b):
    return a == b or (b[0] == "neg" and sub(a, b[1])) or (b[0] in ("conj", "wdis") and any(sub(a, c) for c in b[1]))


# ---------- шаги вывода в S₁ ----------
def moves(q):
    out = []
    if q[0] == "neg" and q[1][0] == "neg":
        out.append(("A1", q[1][1]))
    if q[0] == "conj" and len(q[1]) == 2:
        a, b = q[1]
        out += [("A3", a), ("A4", C(b, a))]
        if a[0] == "wdis" and len(a[1]) == 2:
            out.append(("A7", W(C(a[1][0], b), a[1][1])))
        if a[0] == "conj" and len(a[1]) == 2 and all(t[0] != "conj" for t in a[1]) and b[0] != "conj":
            out.append(("A6", C(a[1][0], a[1][1], b)))
        if b[0] == "conj" and len(b[1]) == 2 and all(t[0] != "conj" for t in b[1]) and a[0] != "conj":
            out.append(("A6", C(a, b[1][0], b[1][1])))
    if q[0] == "conj" and len(q[1]) == 3 and all(t[0] != "conj" for t in q[1]):
        a, b, c = q[1]
        out += [("A5", C(C(a, b), c)), ("A5", C(a, C(b, c)))]
    if q[0] == "neg" and q[1][0] == "conj":
        out.append(("A9", W(*(N(t) for t in q[1][1]))))
    if q[0] == "wdis" and all(t[0] == "neg" for t in q[1]):
        out.append(("A10", N(C(*(t[1] for t in q[1])))))
    if q[0] == "wdis" and len(q[1]) == 2:
        a, b = q[1]
        if a[0] == "conj" and b[0] == "conj" and len(a[1]) == 2 and len(b[1]) == 2 and a[1][1] == b[1][1]:
            out.append(("A8", C(W(a[1][0], b[1][0]), a[1][1])))
        if a[0] == "conj" and len(a[1]) == 2 and size(q) < 16:
            out.append(("A11", C(q, W(a[1][1], N(a[1][1])))))
    if q[0] in ("v", "neg") and size(q) < 6:
        out.append(("A2", N(N(q))))
    for n, r in out:
        assert axiom(q, r) == n, (n, tex(q), tex(r), axiom(q, r))
    return out


def build(P, want):
    for _ in range(60):
        lines, facts = [], []
        first = moves(P)
        if not first:
            return None
        name, r = rnd.choice(first)
        lines.append((P, r, name))
        facts.append((r, 1))
        used_r2, tries = 0, 0
        while len(lines) < want and tries < 80:
            tries += 1
            if len(facts) >= 2 and rnd.random() < 0.28:
                (q1, i), (q2, j) = rnd.sample(facts, 2)
                if size(C(q1, q2)) > 34 or C(q1, q2) in [f for f, _ in facts] or sub(q1, q2) or sub(q2, q1):
                    continue
                lines.append((P, C(q1, q2), ("R2", i, j)))
                facts.append((C(q1, q2), len(lines)))
                used_r2 += 1
                continue
            q, i = rnd.choice(facts)
            opts = [(n, r) for n, r in moves(q) if size(r) <= 36 and r not in [f for f, _ in facts] and r != P]
            if not opts:
                continue
            name, r = rnd.choice(opts)
            lines.append((q, r, name))
            lines.append((P, r, ("R1", i, len(lines))))
            facts.append((r, len(lines)))
        a, b = lines[-1][0], lines[-1][1]
        if (a == P and used_r2 and sum(1 for *_, wh in lines if isinstance(wh, tuple)) >= 3 and not check(lines)
                and strong(a, b) and 10 <= size(b) <= 34):
            return lines
    return None


def prune(lines):
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
    return [(a, b, wh if isinstance(wh, str) else (wh[0], new[wh[1]], new[wh[2]])) for a, b, wh in
            (lines[o - 1] for o in keep)]


def premises():
    X, Y, Z = rnd.sample([x, y, z, N(x), N(y), u, w], 3)
    return rnd.choice([C(W(X, Y), Z), N(C(X, Y)), W(N(X), N(Y)), C(N(N(X)), Y), W(C(X, Y), Z), C(X, Y, Z),
                       W(C(X, Z), C(Y, Z)), C(X, W(Y, Z)), N(C(X, Y, Z))])


SEEN = set()


def build_ok(want, least):
    for _ in range(3000):
        lines = build(premises(), want + 4)
        if lines:
            lines = prune(lines)
            key = ftex(lines[-1][0], lines[-1][1])
            if len(lines) >= least and not check(lines) and key not in SEEN:
                SEEN.add(key)
                return lines
    raise RuntimeError("вывод не построен")


def card(level, typ, step, ans_kind, src, tags, cond, ans, sol, form="sym", system="S_1"):
    return dict(level=level, type=typ, step=step, form=form, answer=ans_kind, source=src, tags=tags, cond=cond,
                ans=ans, sol=sol, system=system)


SCH = ("Схемы и правила $S_1$ (с. 36–37): A1 $\\sim\\sim x \\vdash x$; A2 $x \\vdash \\sim\\sim x$; A3 $xy \\vdash x$; "
       "A4 $xy \\vdash yx$; A5, A6 — расстановка скобок в конъюнкции; A7 $(x \\vee y)z \\vdash xz \\vee y$; "
       "A8 $xz \\vee yz \\vdash (x \\vee y)z$; A9 $\\sim(x^1 \\ldots x^n) \\vdash \\sim x^1 \\vee \\ldots \\vee \\sim x^n$; "
       "A10 — обратная к A9; A11 $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$; R1–R3 — как в $S^1$ (с. 17).")


def c_deriv(src="с. 36–37, гл. 2, § 1"):
    lines = build_ok(rnd.choice([9, 10, 11]), least=8)
    a, b = lines[-1][0], lines[-1][1]
    cond = f"{CONV} Выведите в $S_1$ формулу ${ftex(a, b)}$, пользуясь аксиомными схемами A1–A11 и правилами R1, R2."
    ans = f"Например, вывод в {len(lines)} строк (см. решение); последняя строка — ${ftex(a, b)}$ [{why_text(lines[-1][2])}]."
    sol = show(lines) + "\n\n" + SCH
    return card(7 if len(lines) >= 10 else 6, "D", "open", "proof", src, "S1w, вывод", cond, ans, sol)


def show_hidden(lines, hide_why, hide_f):
    return "\n".join(f"{n}. {'…' if n in hide_f else '$' + ftex(a, b) + '$'} [{'…' if n in hide_why else why_text(wh)}]"
                     for n, (a, b, wh) in enumerate(lines, 1))


def c_complete(src=SRC1):
    lines = build_ok(rnd.choice([10, 11]), least=9)
    sl = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, str)]
    rl = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, tuple)]
    hide_f = set(rnd.sample(sl[1:] or sl, min(2, max(1, len(sl) - 1))))
    hide_why = set(rnd.sample([n for n in sl if n not in hide_f], min(2, len(sl) - len(hide_f))))
    hide_why |= set(rnd.sample(rl[:-1], min(2, len(rl) - 1)))
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} В выводе в $S_1$ формулы ${ftex(a, b)}$ пропущены основания некоторых шагов и формулы некоторых "
            f"строк («…»). Восстановите их.\n\n{show_hidden(lines, hide_why, hide_f)}")
    parts = []
    for n in sorted(hide_why | hide_f):
        la, lb, wh = lines[n - 1]
        parts.append(f"{n} — " + (f"${ftex(la, lb)}$ " if n in hide_f else "") + (f"[{why_text(wh)}]" if n in hide_why else "").strip())
    sol = ("Формулу строки восстанавливаем по соседним: в R1 заключение одной строки — посылка другой, в R2 обе строки "
           "имеют общую посылку; основание — по виду формулы.\n\n" + show(lines) + "\n\n" + SCH)
    return card(5, "D", "complete", "build", src, "S1w, вывод, дополнение", cond, "; ".join(p.strip() for p in parts), sol)


WRONG = {"A1": "A2", "A2": "A1", "A3": "A4", "A4": "A3", "A9": "A10", "A10": "A9", "A7": "A8", "A8": "A7",
         "A5": "A6", "A6": "A5", "A11": "A7"}
WHY = {"A1": "по нумерации $S_1$ A1 — это $\\sim\\sim x \\vdash x$ (снятие двойного отрицания), а A2 — $x \\vdash \\sim\\sim x$; "
             "в $S^1$ наоборот",
       "A2": "в $S_1$ A2 — $x \\vdash \\sim\\sim x$ (введение двойного отрицания), а A1 — $\\sim\\sim x \\vdash x$; "
             "в $S^1$ наоборот",
       "A3": "A3 оставляет первый член конъюнкции, A4 переставляет члены",
       "A4": "A4 переставляет члены конъюнкции, A3 оставляет первый член",
       "A9": "A9 раскрывает отрицание конъюнкции в дизъюнкцию отрицаний, A10 — обратный переход",
       "A10": "A10 собирает дизъюнкцию отрицаний в отрицание конъюнкции, A9 — обратный переход",
       "A7": "A7 — $(x \\vee y)z \\vdash xz \\vee y$, A8 — обратная по направлению $xz \\vee yz \\vdash (x \\vee y)z$",
       "A8": "A8 — $xz \\vee yz \\vdash (x \\vee y)z$, A7 — $(x \\vee y)z \\vdash xz \\vee y$",
       "A5": "A5 расставляет скобки в конъюнкции без скобок, A6 снимает их",
       "A6": "A6 снимает скобки в конъюнкции, A5 расставляет их",
       "A11": "A11 — $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$, а A7 — $(x \\vee y)z \\vdash xz \\vee y$"}


def c_diag(src=SRC1):
    for _ in range(300):
        lines = build_ok(rnd.choice([8, 9]), least=7)
        cand = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, str) and wh in WRONG]
        rs = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, tuple) and wh[0] == "R1"]
        if not cand or not rs:
            continue
        pri = [i for i in cand if lines[i][2] in ("A1", "A2")] or cand
        i, j = rnd.choice(pri), rnd.choice(rs)
        bad = list(lines)
        a, b, wh = bad[i]
        bad[i] = (a, b, WRONG[wh])
        a2, b2, wh2 = bad[j]
        bad[j] = (a2, b2, ("R2", wh2[1], wh2[2]))
        errs = check(bad)
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        if steps == sorted([i + 1, j + 1]):
            break
    else:
        raise RuntimeError("нет вывода для диагностики")
    p, q = sorted([i, j])
    fix = {i: lines[i][2], j: lines[j][2]}
    cond = (f"{CONV} В выводе в $S_1$ формулы ${ftex(lines[-1][0], lines[-1][1])}$ ровно два основания указаны неверно. "
            f"Найдите их, объясните, почему каждое неверно, и исправьте.\n\n{show(bad)}")
    ans = f"Шаг {p + 1}: [{why_text(fix[p])}]; шаг {q + 1}: [{why_text(fix[q])}]."
    exp = []
    for k in (p, q):
        a, b, _ = lines[k]
        if k == i:
            exp.append(f"Шаг {k + 1}: ${ftex(a, b)}$ — пример {fix[k]}, а не {WRONG[fix[k]]}: {WHY[fix[k]]} (с. 36).")
        else:
            exp.append(f"Шаг {k + 1}: R2 соединяет в конъюнкцию заключения двух строк с общей посылкой, а здесь "
                       f"заключение строки {fix[k][1]} — посылка строки {fix[k][2]}: это R1 (с. 17, 36).")
    sol = "\n".join(exp) + "\n\nИсправленный вывод:\n\n" + show(lines)
    return card(6, "E", "vary", "text", src, "S1w, вывод, диагностика", cond, ans, sol)


# ---------- составные замены и почти-примеры ----------
SCHEME = {"A7": "(x \\vee y)z \\vdash xz \\vee y", "A8": "xz \\vee yz \\vdash (x \\vee y)z",
          "A9": "\\sim(xy) \\vdash \\sim x \\vee \\sim y", "A10": "\\sim x \\vee \\sim y \\vdash \\sim(xy)",
          "A11": "xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)", "A1": "\\sim\\sim x \\vdash x"}


def inst(name, X, Y, Z):
    return {"A7": (C(W(X, Y), Z), W(C(X, Z), Y)), "A8": (W(C(X, Z), C(Y, Z)), C(W(X, Y), Z)),
            "A9": (N(C(X, Y)), W(N(X), N(Y))), "A10": (W(N(X), N(Y)), N(C(X, Y))),
            "A11": (W(C(X, Y), Z), C(W(C(X, Y), Z), W(Y, N(Y)))), "A1": (N(N(X)), X)}[name]


def near(name, X, Y, Z):
    a, b = inst(name, X, Y, Z)
    return {"A7": (a, W(C(X, Z), C(Y, Z))),                 # «раскрыл» оба члена
            "A8": (W(C(X, Z), C(Y, X)), C(W(X, Y), Z)),      # вторые множители разные
            "A9": (a, W(N(X), Y)),                           # потерян второй знак ∼
            "A10": (a, N(C(Y, X))),                          # переставлены члены
            "A11": (a, C(W(C(X, Y), Z), W(X, N(X)))),        # взят не тот член
            "A1": (N(N(X)), N(X))}[name]


NEAR_WHY = {"A7": "по A7 второй член дизъюнкции остаётся без множителя: должно быть ${}$",
            "A8": "в посылке A8 оба члена дизъюнкции имеют один и тот же второй множитель",
            "A9": "по A9 отрицание ставится перед каждым членом: должно быть ${}$",
            "A10": "A10 сохраняет порядок членов: должно быть ${}$",
            "A11": "в A11 добавляется $y \\vee \\sim y$ для второго члена конъюнкции $xy$: должно быть ${}$",
            "A1": "A1 снимает оба знака $\\sim$: должно быть ${}$"}


def compound():
    return rnd.choice([C(x, N(y)), W(u, w), N(C(y, z)), C(N(x), z), W(x, N(z)), N(N(u)), N(W(x, y))])


def c_subst(name, yes):
    for _ in range(100):
        X, Y, Z = compound(), compound(), compound()
        if len({X, Y, Z}) == 3:
            break
    a, b = inst(name, X, Y, Z) if yes else near(name, X, Y, Z)
    assert (axiom(a, b) == name) == yes, (name, yes, ftex(a, b), axiom(a, b))
    cond = (f"{CONV} Схема {name} системы $S_1$: ${SCHEME[name]}$. Установите, получается ли из неё формула "
            f"${ftex(a, b)}$ заменой букв высказываниями (одинаковые буквы — одинаковыми). Если получается — укажите "
            "замену; если нет — назовите место, которое мешает.")
    sub_t = {"A7": f"$x$ := ${tex(X)}$, $y$ := ${tex(Y)}$, $z$ := ${tex(Z)}$",
             "A8": f"$x$ := ${tex(X)}$, $y$ := ${tex(Y)}$, $z$ := ${tex(Z)}$",
             "A9": f"$x$ := ${tex(X)}$, $y$ := ${tex(Y)}$", "A10": f"$x$ := ${tex(X)}$, $y$ := ${tex(Y)}$",
             "A11": f"$x$ := ${tex(X)}$, $y$ := ${tex(Y)}$, $z$ := ${tex(Z)}$", "A1": f"$x$ := ${tex(X)}$"}[name]
    if yes:
        ans = f"Получается: {sub_t}."
        sol = (f"1. Посылка ${tex(a)}$ задаёт замену: {sub_t}.\n2. При этой замене заключение схемы даёт ${tex(b)}$ — "
               f"заключение данной формулы.\n3. Формула — пример {name} (с. 36).")
        return card(5, "A", "vary", "short", SRC1, "S1w, схемы, подстановка", cond, ans, sol)
    good = inst(name, X, Y, Z)[1]
    msg = NEAR_WHY[name].replace("${}$", f"${tex(good)}$")
    if name == "A8":
        ans = f"Не получается: {msg} (здесь ${tex(Z)}$ и ${tex(X)}$)."
        sol = (f"1. По первому члену посылки $x$ := ${tex(X)}$, $z$ := ${tex(Z)}$; во втором члене второй множитель "
               f"${tex(X)}$, а должен быть тот же $z$ = ${tex(Z)}$.\n2. Значит, посылка не имеет вида $xz \\vee yz$, "
               "и формула — не пример A8 (с. 36).")
    else:
        ans = f"Не получается: {msg}."
        sol = (f"1. Посылка ${tex(a)}$ однозначно задаёт замену: {sub_t}.\n2. При ней схема даёт заключение "
               f"${tex(good)}$, а в формуле — ${tex(b)}$.\n3. Другой замены нет, формула — не пример {name} (с. 36).")
    return card(4, "E", "vary", "short", SRC1, "S1w, схемы, почти-пример", cond, ans, sol)


NAMES = ["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10", "A11"]


def all_schemes(a, b):
    out = []
    if a == N(N(b)):
        out.append("A1")
    if b == N(N(a)):
        out.append("A2")
    if a[0] == "conj" and len(a[1]) == 2:
        if b == a[1][0]:
            out.append("A3")
        if b == C(a[1][1], a[1][0]):
            out.append("A4")
    for n in ("A7", "A8", "A9", "A10", "A11"):
        if axiom(a, b) == n:
            out.append(n)
    return out


def c_recognize():
    X, Y, Z = compound(), compound(), compound()
    while len({X, Y, Z}) < 3:
        Y, Z = compound(), compound()
    pool = [(*inst("A7", X, Y, Z), "A7"), (C(X, X), C(X, X), "A4"), (*inst("A11", Y, Z, X), "A11"),
            (*inst("A10", Z, Y, X), "A10"), (*near(rnd.choice(["A7", "A9", "A11"]), X, Z, Y), None)]
    rnd.shuffle(pool)
    for a, b, n in pool:
        assert (n in all_schemes(a, b)) if n else not all_schemes(a, b), (n, ftex(a, b))
    items = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b, _) in enumerate(pool))
    ans = "; ".join(f"{L[k]}) " + (", ".join(all_schemes(a, b)) or "ни одной") for k, (a, b, _) in enumerate(pool))
    sol = ("Формула — пример схемы, если получается из неё заменой букв (одинаковые — одинаково). При совпадении членов "
           "формула может быть примером нескольких схем: $XX \\vdash XX$ — пример A4 (замена $x$ := $X$, $y$ := $X$). "
           "Схемы — с. 36.\n\n" + "\n".join(
               f"{L[k]}) " + (", ".join(all_schemes(a, b)) if all_schemes(a, b) else
                              "ни одной: посылка задаёт замену, а заключение с ней не согласуется") + "."
               for k, (a, b, _) in enumerate(pool)))
    cond = (f"{CONV} Для каждой формулы найдите все аксиомные схемы $S_1$ из A1–A4, A7–A11, примером которых она является; "
            f"если ни одной — объясните, что мешает.\n\n{items}")
    return card(4, "R", "iso", "short", SRC1, "S1w, схемы", cond, ans, sol)


# ---------- серии длинных формул: доказуемость (MT5) ----------
def rnd_w(names, depth):
    if depth == 0 or rnd.random() < 0.2:
        v = V(rnd.choice(names))
        return N(v) if rnd.random() < 0.3 else v
    k = rnd.random()
    if k < 0.2:
        s_ = rnd_w(names, depth - 1)
        return N(s_)
    op = C if k < 0.6 else W
    a, b = rnd_w(names, depth - 1), rnd_w(names, depth - 1)
    return op(a, b) if a != b else a


def env_t(e):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(e.items()))


def c_series(src="с. 36–45, гл. 2, § 1–2", level=6):
    need = ["strong", "new", "non", rnd.choice(["strong", "non"])]
    items = []
    while len(items) < 4:
        k = need[len(items)]
        if k == "strong":
            lines = build_ok(6, least=4)
            a, b = lines[-1][0], lines[-1][1]
        else:
            lt = rnd.sample("xyz", 2)
            a = rnd_w(lt, 2)
            b = rnd_w(lt + (["u"] if k == "new" else []), 2)
        st = "strong" if strong(a, b) else "new" if tautology(a, b) else "non"
        if st == k and a != b and 14 <= len(tex(a)) + len(tex(b)) <= 44 and (a, b) not in items:
            items.append((a, b))
    rnd.shuffle(items)
    ans, sol = [], []
    for k, (a, b) in enumerate(items):
        if strong(a, b):
            ans.append(f"{L[k]}) доказуема")
            sol.append(f"{L[k]}) Тавтология (нет набора значений, где посылка — 1, а заключение — 0), новых элементарных "
                       f"высказываний в заключении нет: сильная тавтология, по MT5 (с. 43) — теорема $S_1$.")
        elif tautology(a, b):
            na = ", ".join(f"${t}$" for t in sorted(new_atoms(a, b)))
            ans.append(f"{L[k]}) недоказуема (новая буква {na})")
            sol.append(f"{L[k]}) Тавтология, но в заключение входит {na}, которого нет в посылке; по непарадоксальности "
                       "$S_1$ (с. 37) недоказуема.")
        else:
            e = counterexample(a, b)
            ans.append(f"{L[k]}) недоказуема ({env_t(e)})")
            sol.append(f"{L[k]}) При {env_t(e)} посылка — 1, заключение — 0: не тавтология; теоремы $S_1$ — тавтологии "
                       "(непротиворечивость, с. 37).")
    cond = (f"{CONV} Исследуйте доказуемость в $S_1$ каждой формулы и обоснуйте значениями: для недоказуемой — набор "
            f"значений, где посылка 1, а заключение 0, или элементарное высказывание, которого нет в посылке. {CRIT}\n\n"
            + "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b) in enumerate(items)))
    return card(level, "C", "open", "short", src, "S1w, доказуемость", cond, "; ".join(ans), "\n".join(sol))


# ---------- § 3: таблицы независимости ----------
TT = {"A1": ("значения 1 и 0, отмечено 1; $x \\vdash y$ имеет значение 0 только при $x = 1$, $y = 0$; $\\sim x = 1$, "
             "конъюнкция и дизъюнкция — как обычно"),
      "A3": ("значения 1 и 0, отмечено 1; $x \\vdash y$ имеет значение 0 только при $x = 1$, $y = 0$; $xy = 1$, "
             "$x \\vee y = 1$, $\\sim x = x$"),
      "A4": ("значения 1 и 0, отмечено 1; $x \\vdash y$ имеет значение 0 только при $x = 1$, $y = 0$; $xy = x$, "
             "$x \\vee y = x$, $\\sim x = x$"),
      "A9": ("значения 1 и 0, отмечено 1; $x \\vdash y$ имеет значение 0 только при $x = 1$, $y = 0$; $x \\vee y = y$, "
             "отрицание и конъюнкция — как обычно"),
      "A11": ("значения 1, 2, 3, отмечено 1; $xy = \\max(x, y)$, $x \\vee y = \\min(x, y)$, $\\sim x = 4 - x$; "
              "$x \\vdash y$ имеет значение 1 тогда и только тогда, когда значение $x$ не меньше значения $y$"),
      "R1": ("значения 1, 2, 3, отмечено 1; $xy = \\max(x, y)$, $x \\vee y = \\min(x, y)$, $\\sim x = 4 - x$; "
             "$x \\vdash y$ имеет неотмеченное значение только при $x \\in \\{1, 2\\}$, $y = 3$")}
TPAGE = {"A1": "с. 43", "A3": "с. 43", "A4": "с. 44", "A9": "с. 44", "A11": "с. 44", "R1": "с. 44"}


def tval(f, env, t):
    k = f[0]
    if k == "v":
        return env[f[1]]
    if k == "neg":
        return t["neg"](tval(f[1], env, t))
    vs = [tval(a, env, t) for a in f[1]]
    return t["conj"](vs) if k == "conj" else t["wdis"](vs)


def c_table(level=5):
    tn = rnd.choice(["A1", "A3", "A4", "A9", "A11"])
    t = IW.TABLES[tn]
    items = []
    tries = 0
    while len(items) < 4 and tries < 5000:
        tries += 1
        if rnd.random() < 0.5:
            lines = build_ok(5, least=3)
            a, b = lines[-1][0], lines[-1][1]
        else:
            nm = rnd.choice(["A3", "A4", "A7", "A9", "A10", "A11", "A1", "A2"])
            X, Y, Z = compound(), compound(), compound()
            a, b = {"A1": (N(N(X)), X), "A2": (X, N(N(X))), "A3": (C(X, Y), X), "A4": (C(X, Y), C(Y, X))}.get(
                nm, None) or inst(nm, X, Y, Z)
        ok, env = IW.valid(a, b, t)
        want_bad = len(items) in (0, 2)
        if ok == (not want_bad) and len(tex(a)) + len(tex(b)) <= 46 and (a, b) not in items:
            items.append((a, b))
    rnd.shuffle(items)
    ans, sol = [], []
    for k, (a, b) in enumerate(items):
        ok, env = IW.valid(a, b, t)
        if ok:
            ans.append(f"{L[k]}) тавтологична")
            sol.append(f"{L[k]}) При всех значениях формула получает отмеченное значение.")
        else:
            va, vb = tval(a, env, t), tval(b, env, t)
            ans.append(f"{L[k]}) не тавтологична: {env_t(env)}")
            sol.append(f"{L[k]}) При {env_t(env)} посылка имеет значение {va}, заключение — {vb}; формула получает "
                       "неотмеченное значение.")
    cond = (f"{CONV} Таблица для {tn} (гл. 2, § 3, {TPAGE[tn]}): {TT[tn]}. Для каждой формулы (все они — теоремы $S_1$ или "
            "примеры её схем) установите, тавтологична ли она в этой таблице; для нетавтологичной укажите значения, при "
            "которых формула получает неотмеченное значение, и вычислите при них посылку и заключение.\n\n"
            + "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b) in enumerate(items)))
    for a, b in items:
        assert strong(a, b)
    return card(level, "V", "iso", "short", "с. 43–45, гл. 2, § 3", "S1w, независимость", cond, "; ".join(ans),
                f"Таблица для {tn}, {TPAGE[tn]}.\n\n" + "\n".join(sol))


def c_table_diag(level=6):
    tn = rnd.choice(["A1", "A3", "A4", "A9", "A11"])
    t = IW.TABLES[tn]
    rows = []
    while len(rows) < 4:
        nm = rnd.choice(["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10", "A11"])
        X, Y, Z = rnd.sample([x, y, z, N(x), u], 3)
        a, b = IW.instance(nm, X, Y, Z)
        if (nm, ) not in [(r[0],) for r in rows]:
            rows.append((nm, a, b, IW.valid(a, b, t)[0]))
    flip = rnd.sample(range(4), 2)
    claim = [(not ok) if i in flip else ok for i, (_, _, _, ok) in enumerate(rows)]
    body = "\n".join(f"{n + 1}. ${ftex(a, b)}$ (пример {nm}) — {'тавтологична' if c else 'не тавтологична'}"
                     for n, ((nm, a, b, _), c) in enumerate(zip(rows, claim)))
    cond = (f"{CONV} Таблица для {tn} (гл. 2, § 3, {TPAGE[tn]}): {TT[tn]}. Студент проверил в этой таблице четыре формулы. "
            f"Ровно в двух выводах он ошибся. Найдите их и обоснуйте значениями.\n\n{body}")
    ans, sol = [], []
    for n, (nm, a, b, ok) in enumerate(rows):
        if n in flip:
            if ok:
                ans.append(f"строка {n + 1}: тавтологична")
                sol.append(f"Строка {n + 1}: при всех значениях формула получает отмеченное значение — тавтологична.")
            else:
                env = IW.valid(a, b, t)[1]
                ans.append(f"строка {n + 1}: не тавтологична ({env_t(env)})")
                sol.append(f"Строка {n + 1}: при {env_t(env)} посылка — {tval(a, env, t)}, заключение — "
                           f"{tval(b, env, t)}; значение неотмеченное.")
    return card(level, "E", "vary", "text", "с. 43–45, гл. 2, § 3", "S1w, независимость, диагностика", cond,
                "; ".join(ans), "\n".join(sol) + f"\n\nОстальные строки верны (таблица для {tn}, {TPAGE[tn]}).")


def c_table_fill(level=5):
    tn = rnd.choice(["A10" if False else "A11", "R1", "A1", "A4"])
    t = IW.TABLES[tn]
    want_bad = rnd.random() < 0.6
    for _ in range(2000):
        nm = rnd.choice(["A7", "A9", "A10", "A11", "A3", "A4"])
        X, Y, Z = rnd.sample([x, y, N(x), N(y)], 3)
        a, b = IW.instance(nm, X, Y, Z)
        names = sorted(atoms(a) | atoms(b))
        if len(names) == 2 and IW.valid(a, b, t)[0] != want_bad:
            vals = {tval(a, dict(zip(names, vs)), t) for vs in product(t["vals"], repeat=2)}
            if len(vals) > 1:
                break
    envs = [dict(zip(names, vs)) for vs in product(t["vals"], repeat=2)]
    hide = set(rnd.sample(range(len(envs)), min(4, len(envs))))
    rows = []
    for i, e in enumerate(envs):
        va, vb = tval(a, e, t), tval(b, e, t)
        f = t["ent"](va, vb)
        rows.append((e, va, vb, f))
    head = f"| ${names[0]}$ | ${names[1]}$ | посылка | заключение | формула |\n|---|---|---|---|---|\n"
    body = "".join(f"| {e[names[0]]} | {e[names[1]]} | {'?' if i in hide else va} | {'?' if i in hide else vb} | "
                   f"{'?' if i in hide else f} |\n" for i, (e, va, vb, f) in enumerate(rows))
    bad = [i for i, (_, _, _, f) in enumerate(rows) if f != 1]
    cond = (f"{CONV} Таблица для {tn} (гл. 2, § 3, {TPAGE[tn]}): {TT[tn]}. Заполните пропуски «?» в таблице значений "
            f"формулы ${ftex(a, b)}$ (пример {nm}) и установите, тавтологична ли она в этой таблице. «Формула» — "
            f"1, если значение отмеченное, и 0 иначе.\n\n{head}{body}")
    ans = ("; ".join(f"строка {i + 1}: {rows[i][1]}, {rows[i][2]}, {rows[i][3]}" for i in sorted(hide)) +
           ("; тавтологична" if not bad else f"; не тавтологична (строк{'а' if len(bad) == 1 else 'и'} " +
            ", ".join(str(i + 1) for i in bad) + ")"))
    sol = f"Вычисляем по таблице для {tn} ({TPAGE[tn]}):\n\n" + head + "".join(
        f"| {e[names[0]]} | {e[names[1]]} | {va} | {vb} | {f} |\n" for e, va, vb, f in rows)
    return card(level, "V", "complete", "build", "с. 43–45, гл. 2, § 3", "S1w, независимость", cond, ans, sol)


# ---------- § 4: перевод S¹ ↔ S₁ ----------
def to_s1(f):
    """∨ → ∼(∼x∼y) (D2 § 3 гл. 1), только двучленные дизъюнкции."""
    k = f[0]
    if k == "v":
        return f
    if k == "neg":
        return N(to_s1(f[1]))
    if k == "conj":
        return C(*(to_s1(a) for a in f[1]))
    a, b = f[1]
    return N(C(N(to_s1(a)), N(to_s1(b))))


def s1tex(f):
    return S.tex(f)


def c_translate(level=6):
    for _ in range(5000):
        lt = rnd.sample("xyz", 2)
        a, b = rnd_w(lt, 2), rnd_w(lt, 2)
        if (repr(a).count("wdis") + repr(b).count("wdis") >= 2 and 12 <= len(tex(a)) + len(tex(b)) <= 32
                and a != b and rnd.random() < (0.8 if strong(a, b) else 0.4)):
            break
    A, B = to_s1(a), to_s1(b)
    st = strong(a, b)
    assert st == S.strong_tautology(A, B)
    verdict = "доказуема" if st else "недоказуема"
    cond = (f"{CONV} Переведите формулу $S_1$ ${ftex(a, b)}$ на язык $S^1$, раскрыв каждое $x \\vee y$ по D2 § 3 гл. 1 "
            "($x \\vee y$ есть сокращение для $\\sim(\\sim x\\sim y)$, с. 20), проверьте значениями, что перевод не меняет "
            "значений посылки и заключения, и исследуйте доказуемость формулы в $S^1$ и в $S_1$ (§ 4, MT1, с. 45). " + CRIT)
    why = ("сильная тавтология" if st else ("в заключение входит новая буква" if new_atoms(a, b) else
                                             f"не тавтология: {env_t(counterexample(a, b))}"))
    ans = f"${s1tex(A)} \\vdash {s1tex(B)}$; в обеих системах {verdict} ({why})."
    sol = (f"1. Раскрываем $\\vee$ изнутри: ${tex(a)}$ → ${s1tex(A)}$; ${tex(b)}$ → ${s1tex(B)}$.\n"
           "2. «Не оба члена ложны» — то же, что «по крайней мере один истинен» (с. 20, 36), поэтому значения посылки и "
           "заключения при переводе не меняются (проверяется перебором наборов).\n"
           f"3. Формула — {why}; по MT5 § 2 и MT1 § 4 (множества теорем $S^1$ и $S_1$ совпадают, с. 45) она {verdict} "
           "в обеих системах.")
    return card(level, "T", "transfer", "short", "с. 20, 37, 43, 45, гл. 1, § 3; гл. 2, § 1–4", "S1, S1w, эквивалентность",
                cond, ans, sol, system="S_1")


def c_translate_diag(level=6):
    a = C(W(x, N(y)), N(W(z, x)))
    b = W(N(y), z)
    A_wrong_1 = N(C(N(x), y))           # потерян ∼ перед ∼y
    good_a = to_s1(a)
    good_b = to_s1(b)
    stud_a = C(A_wrong_1, N(N(C(N(z), N(x)))))
    stud_b = S.D(N(y), z)
    cond = (f"{CONV} Студент переводит формулу $S_1$ ${ftex(a, b)}$ на язык $S^1$ по D2 § 3 гл. 1 ($x \\vee y$ — "
            "сокращение для $\\sim(\\sim x\\sim y)$, с. 20) и получает:\n\n"
            f"$${s1tex(stud_a)} \\vdash {s1tex(stud_b)}$$\n\n"
            "Найдите все ошибки перевода, объясните их и дайте верный перевод. Затем исследуйте доказуемость исходной "
            "формулы в $S_1$. " + CRIT)
    st = strong(a, b)
    ans = (f"Ошибки: в $x \\vee \\sim y$ потерян знак $\\sim$ перед $\\sim y$; заключение переведено через $:$ "
           f"(сильная дизъюнкция) вместо $\\sim(\\sim\\sim y\\sim z)$. Верно: ${s1tex(good_a)} \\vdash {s1tex(good_b)}$; "
           f"формула {'доказуема' if st else 'недоказуема'}.")
    ce = counterexample(a, b)
    sol = (f"1. $x \\vee \\sim y$ есть $\\sim(\\sim x\\sim\\sim y)$: под общим отрицанием стоят отрицания обоих членов, "
           f"а студент написал $\\sim(\\sim x y)$.\n"
           f"2. $\\sim(z \\vee x)$ — это $\\sim\\sim(\\sim z\\sim x)$: здесь студент прав.\n"
           f"3. $\\sim y \\vee z$ студент записал как $\\sim y : z$, но $:$ — сильная дизъюнкция («одно и только одно из»), "
           f"а $\\vee$ — «по крайней мере одно из» (с. 36); верно $\\sim(\\sim\\sim y\\sim z)$.\n\n"
           f"Верный перевод: ${s1tex(good_a)} \\vdash {s1tex(good_b)}$.\n\n"
           + (f"Формула — сильная тавтология, по MT5 (с. 43) доказуема в $S_1$." if st else
              f"При {env_t(ce)} посылка — 1, заключение — 0: формула недоказуема." if ce else
              "В заключение входит новая буква: формула недоказуема."))
    return card(level, "E", "vary", "text", "с. 20, 36–37, 45, гл. 1, § 3; гл. 2, § 1, 4", "S1, S1w, эквивалентность, диагностика",
                cond, ans, sol)


# ---------- § 5: сильное следование ----------
CRIT_S = ("$S^s$ — $S^1$, $S_1$ и любая эквивалентная им система (§ 5, с. 45); формула доказуема в $S^s$ тогда и только "
          "тогда, когда она — сильная тавтология (гл. 1, § 4–5, 7; гл. 2, § 2, MT5; § 4, MT1).")


def c_ss_series(level=6):
    c = c_series(src="с. 45, гл. 2, § 5", level=level)
    c["cond"] = c["cond"].replace(CRIT, CRIT_S).replace("в $S_1$", "в $S^s$")
    c["sol"] = c["sol"].replace("теорема $S_1$", "теорема $S_1$, а значит, и $S^s$").replace(
        "теоремы $S_1$ — тавтологии", "теоремы $S^s$ — тавтологии")
    c["system"] = "S^s"
    c["tags"] = "сильное следование, доказуемость"
    return c


def c_ss_diag(level=6):
    items = []
    need = ["strong", "new", "non", "strong"]
    while len(items) < 4:
        k = need[len(items)]
        if k == "strong":
            lines = build_ok(6, least=4)
            a, b = lines[-1][0], lines[-1][1]
        else:
            lt = rnd.sample("xyz", 2)
            a = rnd_w(lt, 2)
            b = rnd_w(lt + (["u"] if k == "new" else []), 2)
        st = "strong" if strong(a, b) else "new" if tautology(a, b) else "non"
        if st == k and a != b and len(tex(a)) + len(tex(b)) <= 40 and (a, b) not in items:
            items.append((a, b))
    rnd.shuffle(items)
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for k, (a, b) in enumerate(items):
        st = strong(a, b)
        if k in wrong:
            if st:
                claim = rnd.choice(["недоказуема: из противоречия или в тавтологию следование не принимается",
                                    "недоказуема: заключение длиннее посылки"])
                ans.append(f"{k + 1}: доказуема")
                sol.append(f"{k + 1}. Неверно: формула — сильная тавтология, значит, доказуема (MT5, с. 43). Длина и "
                           "вид частей значения не имеют — важны тавтологичность и условие на элементарные высказывания.")
            elif tautology(a, b):
                claim = "доказуема: это тавтология"
                na = ", ".join(f"${t}$" for t in sorted(new_atoms(a, b)))
                ans.append(f"{k + 1}: недоказуема (новая буква {na})")
                sol.append(f"{k + 1}. Неверно: тавтологии мало — в заключение входит {na}, которого нет в посылке; такие "
                           "формулы в $S^s$ недоказуемы (непарадоксальность, с. 37).")
            else:
                claim = "доказуема: в заключении нет новых букв"
                e = counterexample(a, b)
                ans.append(f"{k + 1}: недоказуема ({env_t(e)})")
                sol.append(f"{k + 1}. Неверно: условия на буквы мало — при {env_t(e)} посылка 1, заключение 0, формула не "
                           "тавтология.")
        else:
            claim = ("доказуема: сильная тавтология" if st else
                     "недоказуема: новая буква в заключении" if tautology(a, b) else
                     f"недоказуема: при {env_t(counterexample(a, b))} посылка 1, заключение 0")
        lines.append(f"{k + 1}. ${ftex(a, b)}$ — {claim}.")
    cond = (f"{CONV} Студент исследовал доказуемость четырёх формул в $S^s$:\n\n" + "\n".join(lines) +
            f"\n\nРовно два вывода неверны. Найдите их, объясните ошибку и дайте верный ответ с обоснованием. {CRIT_S}")
    return card(level, "E", "vary", "text", "с. 45, гл. 2, § 5", "сильное следование, диагностика", cond,
                "; ".join(ans), "\n".join(sol) + "\n\nОстальные выводы верны.", system="S^s")


# ---------- вручную ----------
HAND = {
    "02.01-020": card(6, "A", "open", "build", SRC1, "S1w, схемы, построение",
                      f"{CONV} Постройте формулу следования, которая одновременно является примером схем A7 "
                      "($(x \\vee y)z \\vdash xz \\vee y$) и A3 ($xy \\vdash x$) системы $S_1$, или докажите, что такой "
                      "формулы нет.",
                      "Такой формулы нет.",
                      "1. Пример A7: $(X \\vee Y)Z \\vdash XZ \\vee Y$; пример A3: $X'Y' \\vdash X'$ (с. 36).\n"
                      "2. Посылки совпадают: $X' = X \\vee Y$, $Y' = Z$. Тогда заключение A3 — $X \\vee Y$, и должно "
                      "быть $X \\vee Y = XZ \\vee Y$.\n"
                      "3. Двучленные дизъюнкции совпадают, только если совпадают члены: $X = XZ$. Но $XZ$ длиннее $X$ — "
                      "высказывание не может совпадать со своей собственной частью. Формулы нет."),
    "02.01-021": card(6, "A", "open", "build", SRC1, "S1w, схемы, построение",
                      f"{CONV} Постройте формулу следования, которая одновременно является примером схем A9 "
                      "($\\sim(xy) \\vdash \\sim x \\vee \\sim y$) и A2 ($x \\vdash \\sim\\sim x$) системы $S_1$, или "
                      "докажите, что такой формулы нет. Затем ответьте на тот же вопрос для A4 и A9.",
                      "Для A9 и A2 — нет; для A4 и A9 — тоже нет.",
                      "1. A9 и A2: заключение A9 — дизъюнкция $\\sim X \\vee \\sim Y$, заключение A2 — $\\sim\\sim X'$ "
                      "(с главным знаком $\\sim$). Высказывание не может быть сразу дизъюнкцией и отрицанием: формулы нет.\n"
                      "2. A4 и A9: посылка A4 — конъюнкция $XY$, посылка A9 — отрицание $\\sim(X'Y')$; они не совпадают — "
                      "формулы нет.\n"
                      "Общий приём: сравнить главные операторы посылок и заключений схем (с. 36)."),
    "02.05-008": card(6, "A", "open", "build", "с. 45, гл. 2, § 5", "сильное следование, построение",
                      f"{CONV} Постройте формулу $x \\vdash y$, доказуемую в $S^s$, у которой посылка — противоречие "
                      "(ложна при всех значениях), а заключение — не противоречие. Затем докажите, что формула "
                      "$x \\vdash y \\vee \\sim y$, где в $y$ есть элементарное высказывание, отсутствующее в $x$, в $S^s$ "
                      "недоказуема, хотя она тавтология. " + CRIT_S,
                      "Например, $x\\sim x \\vdash x$; вторая часть — по условию на элементарные высказывания.",
                      "1. $x\\sim x \\vdash x$: посылка ложна при всех значениях — тавтология; элементарных высказываний, "
                      "отсутствующих в посылке, в заключении нет. Сильная тавтология — доказуема в $S^s$ (MT5, с. 43). "
                      "Заключение $x$ — не противоречие.\n"
                      "2. $x \\vdash y \\vee \\sim y$: заключение истинно при всех значениях — тавтология. Но в $y$ есть "
                      "буква, которой нет в $x$, — формула не сильная тавтология и по непарадоксальности (с. 37) "
                      "недоказуема. Это и отличает сильное следование: «парадоксы» с новыми буквами не принимаются."),
    "02.05-009": card(6, "M", "open", "proof", "с. 45, гл. 2, § 5", "сильное следование, построение",
                      f"{CONV} Постройте две формулы $x \\vdash y$ и $y \\vdash z$, доказуемые в $S^s$, такие что "
                      "$x \\vdash z$ тоже доказуема, и объясните, почему так будет всегда (правило R1). Затем выясните, "
                      "можно ли построить доказуемые в $S^s$ формулы $x \\vdash y$ и $z \\vdash v$, для которых "
                      "$xz \\vdash yv$ недоказуема. " + CRIT_S,
                      "Например, $xy \\vdash x$, $x \\vdash \\sim\\sim x$, $xy \\vdash \\sim\\sim x$. Вторых формул нет: "
                      "$xz \\vdash yv$ всегда сильная тавтология.",
                      "1. $xy \\vdash x$ (A3), $x \\vdash \\sim\\sim x$ (A2), по R1 — $xy \\vdash \\sim\\sim x$ (с. 17, 36). "
                      "Всегда: R1 — правило $S_1$, а $S^s$ эквивалентна $S_1$ (§ 5, с. 45).\n"
                      "2. Пусть $x \\vdash y$ и $z \\vdash v$ — сильные тавтологии. Если $xz = 1$, то $x = 1$ и $z = 1$, "
                      "значит, $y = 1$ и $v = 1$, и $yv = 1$: $xz \\vdash yv$ — тавтология. Буквы $y$ входят в $x$, буквы "
                      "$v$ — в $z$, значит, буквы $yv$ входят в $xz$. Формула — сильная тавтология и доказуема (MT5). "
                      "Требуемых формул нет."),
}


def plan():
    out = {}
    s1 = ["02.01-%03d" % n for n in range(1, 26) if n not in (20, 21)]
    k1 = ([lambda n=n: c_subst(n, True) for n in ("A7", "A11", "A9", "A8")] + [lambda n=n: c_subst(n, False) for n in
                                                                               ("A7", "A1")] +
          [c_recognize] * 2 + [c_deriv] * 5 + [c_complete] * 5 + [c_diag] * 3 + [c_series] * 2)
    assert len(s1) == len(k1), (len(s1), len(k1))
    rnd.shuffle(k1)
    out.update(zip(s1, k1))
    s2 = ["02.02-%03d" % n for n in range(1, 18)]
    src2 = "с. 36–43, гл. 2, § 1–2"
    k2 = ([lambda: c_series(src="с. 37–43, гл. 2, § 2", level=6)] * 4 + [lambda: c_deriv(src2)] * 3 +
          [lambda: c_complete(src2)] * 3 + [lambda: c_diag(src2)] * 4 + [lambda: c_subst("A10", True),
                                                                          lambda: c_subst("A9", False),
                                                                          lambda: c_subst("A10", False)])
    assert len(s2) == len(k2), (len(s2), len(k2))
    rnd.shuffle(k2)
    out.update(zip(s2, k2))
    s3 = ["02.03-%03d" % n for n in range(1, 9)]
    k3 = [c_table] * 3 + [c_table_fill] * 2 + [c_table_diag] * 3
    rnd.shuffle(k3)
    out.update(zip(s3, k3))
    out.update({"02.04-001": c_translate, "02.04-002": c_translate, "02.04-003": c_translate,
                "02.04-004": c_translate_diag})
    s5 = ["02.05-%03d" % n for n in range(1, 11) if n not in (8, 9)]
    k5 = [c_ss_series] * 4 + [c_ss_diag] * 4
    rnd.shuffle(k5)
    out.update(zip(s5, k5))
    return out


def render(cid, c):
    sec = int(cid.split(".")[1].split("-")[0])
    sysl = f'system: "{c["system"]}"\n' if c.get("system") else ""
    return (f'---\nid: "{cid}"\nchapter: 2\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\n'
            f'step: {c["step"]}\ncondition: def\nform: {c["form"]}\nanswer: {c["answer"]}\nsource: "{c["source"]}"\n'
            f'{sysl}generated: true\ntags: [{c["tags"]}]\n---\n\n## Условие\n\n{c["cond"]}\n\n## Ответ\n\n{c["ans"]}\n\n'
            f'## Решение\n\n{c["sol"]}\n')


def main():
    cards = {cid: fn() for cid, fn in plan().items()}
    cards.update(HAND)
    for cid, c in cards.items():
        assert not test_like(c["cond"]), (cid, c["cond"][:120])
    path = ROOT / "data" / "zadachi" / "02.md"
    parts = re.split(r"(\n=====\n)", path.read_text(encoding="utf-8"))
    done = set()
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(02\.\d\d-\d{3})"', chunk, re.M)
        if m and m.group(1) in cards:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            parts[i] = lead + render(m.group(1), cards[m.group(1)]).rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
            done.add(m.group(1))
    assert done == set(cards), sorted(set(cards) - done)
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {len(done)}")


if __name__ == "__main__":
    main()
