#!/usr/bin/env python3
"""Серии для занятий 16–18: гл. 2 (система S₁, полнота, независимость, эквивалентность S¹ и S₁) и смешанный набор
после гл. 1. Выводы проверяются s1w.check, доказуемость — критерием сильной тавтологии (гл. 2, § 2, MT5; § 4, MT1;
гл. 1, § 4–5), таблицы независимости — indep_w.py (только таблицы, подтверждённые проверкой).
Пишет drafts/02-gen.md и drafts/17.02-gen.md.
"""
import importlib.util
import random
import sys
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import indep_w as IW  # noqa: E402
import s1 as S  # noqa: E402
from s1 import C, D, N, V, atoms  # noqa: E402
from s1w import (AXIOM_TEXT, W, axiom, check, counterexample, ftex, instance, new_atoms, show, strong,  # noqa: E402
                 tautology, tex, value, why_text)

rnd = random.Random(1970_36)
x, y, z, u, w = (V(n) for n in "xyzuw")
L = "абвгдежз"
CONV = ("Буквы $x, y, z, u, w$ — элементарные высказывания; $\\vee$ — соединительная дизъюнкция («по крайней мере одно "
        "из», гл. 2, § 1, с. 36); запись — по соглашению книги.")
CRIT = ("Пользуйтесь критерием: формула доказуема в $S_1$ тогда и только тогда, когда она — сильная тавтология (гл. 2, "
        "§ 2, MT5, с. 43; обратное — из совпадения теорем $S^1$ и $S_1$, § 4, с. 45, и гл. 1, § 4–5).")
SEEN = set()


def card(sec, level, typ, step, form, ans, tags, body, series, src, ch=2, system="S_1"):
    sysl = f'system: "{system}"\n' if system else ""
    ser = f"series: {series}\n" if series else ""
    return (f"---\nchapter: {ch}\nsection: {sec}\nlevel: {level}\ntype: {typ}\nstep: {step}\ncondition: def\n"
            f"form: {form}\nanswer: {ans}\nsource: \"{src}\"\n{sysl}{ser}generated: true\ntags: [{tags}]\n---\n\n{body}\n")


def env_text(env):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(env.items()))


def rnd_w(names, depth):
    if depth == 0 or rnd.random() < 0.25:
        v = V(rnd.choice(names))
        return N(v) if rnd.random() < 0.35 else v
    k = rnd.choice(["neg", "conj", "conj", "wdis", "wdis"])
    if k == "neg":
        s = rnd_w(names, depth - 1)
        return N(s) if s[0] != "neg" else s
    a, b = rnd_w(names, depth - 1), rnd_w(names, depth - 1)
    if a == b:
        return rnd_w(names, depth)
    return (k, (a, b))


def fresh(gen, ok=lambda f: True):
    for _ in range(1000):
        f = gen()
        if repr(f) not in SEEN and ok(f):
            SEEN.add(repr(f))
            return f
    raise RuntimeError


def verdict(a, b):
    if strong(a, b):
        return "доказуема", "сильная тавтология — по MT5 § 2 (с. 43) теорема $S_1$."
    if new_atoms(a, b):
        return "недоказуема", ("в заключение входит " + ", ".join(f"${t}$" for t in sorted(new_atoms(a, b))) +
                               ", которого нет в посылке (непарадоксальность $S_1$, с. 37).")
    return "недоказуема", (f"при {env_text(counterexample(a, b))} посылка — 1, заключение — 0: не тавтология, а теоремы "
                           "$S_1$ — тавтологии.")


# ---------- выводы в S₁ ----------
def templates(X, Y, Z):
    return [
        ((C(X, Y), N(N(X))), [(C(X, Y), X, "A3"), (X, N(N(X)), "A2"), (C(X, Y), N(N(X)), ("R1", 1, 2))]),
        ((N(N(C(X, Y))), Y), [(N(N(C(X, Y))), C(X, Y), "A1"), (C(X, Y), C(Y, X), "A4"), (C(Y, X), Y, "A3"),
                              (N(N(C(X, Y))), C(Y, X), ("R1", 1, 2)), (N(N(C(X, Y))), Y, ("R1", 4, 3))]),
        ((N(C(X, Y)), N(C(Y, X))), [(C(X, Y), C(Y, X), "A4"), (C(Y, X), C(X, Y), "A4"),
                                    (N(C(X, Y)), N(C(Y, X)), ("R3", 1, 2))]),
        ((N(C(X, Y)), W(N(Y), N(X))), [(C(X, Y), C(Y, X), "A4"), (C(Y, X), C(X, Y), "A4"),
                                       (N(C(X, Y)), N(C(Y, X)), ("R3", 1, 2)), (N(C(Y, X)), W(N(Y), N(X)), "A9"),
                                       (N(C(X, Y)), W(N(Y), N(X)), ("R1", 3, 4))]),
        ((W(N(X), N(Y)), N(C(Y, X))), [(W(N(X), N(Y)), N(C(X, Y)), "A10"), (C(X, Y), C(Y, X), "A4"),
                                       (C(Y, X), C(X, Y), "A4"), (N(C(X, Y)), N(C(Y, X)), ("R3", 2, 3)),
                                       (W(N(X), N(Y)), N(C(Y, X)), ("R1", 1, 4))]),
        ((W(C(X, Z), C(Y, Z)), C(Z, W(X, Y))), [(W(C(X, Z), C(Y, Z)), C(W(X, Y), Z), "A8"),
                                                (C(W(X, Y), Z), C(Z, W(X, Y)), "A4"),
                                                (W(C(X, Z), C(Y, Z)), C(Z, W(X, Y)), ("R1", 1, 2))]),
        ((W(C(X, Y), Z), W(Y, N(Y))), [(W(C(X, Y), Z), C(W(C(X, Y), Z), W(Y, N(Y))), "A11"),
                                       (C(W(C(X, Y), Z), W(Y, N(Y))), C(W(Y, N(Y)), W(C(X, Y), Z)), "A4"),
                                       (C(W(Y, N(Y)), W(C(X, Y), Z)), W(Y, N(Y)), "A3"),
                                       (W(C(X, Y), Z), C(W(Y, N(Y)), W(C(X, Y), Z)), ("R1", 1, 2)),
                                       (W(C(X, Y), Z), W(Y, N(Y)), ("R1", 4, 3))]),
        ((W(N(N(X)), Y), W(X, Y)), [(N(N(X)), X, "A1"), (X, N(N(X)), "A2"), (W(N(N(X)), Y), W(X, Y), ("R3", 1, 2))]),
        ((C(W(X, Y), Z), N(N(W(C(X, Z), Y)))), [(C(W(X, Y), Z), W(C(X, Z), Y), "A7"),
                                                (W(C(X, Z), Y), N(N(W(C(X, Z), Y))), "A2"),
                                                (C(W(X, Y), Z), N(N(W(C(X, Z), Y))), ("R1", 1, 2))]),
        ((C(Z, W(X, Y)), W(C(X, Z), Y)), [(C(Z, W(X, Y)), C(W(X, Y), Z), "A4"), (C(W(X, Y), Z), W(C(X, Z), Y), "A7"),
                                          (C(Z, W(X, Y)), W(C(X, Z), Y), ("R1", 1, 2))]),
    ]


def pick():
    return rnd.sample([x, y, z, N(u), C(u, w), W(u, w)], 3)


def derivation(k=None):
    while True:
        X, Y, Z = pick()
        ts = templates(X, Y, Z)
        goal, lines = ts[k if k is not None else rnd.randrange(len(ts))]
        if repr(goal) in SEEN:
            if k is not None:
                continue
            continue
        assert not check(lines), (check(lines), goal)
        SEEN.add(repr(goal))
        return goal, lines


ALT = {"A1": "A2", "A2": "A1", "A3": "A4", "A4": "A3", "A7": "A8", "A8": "A7", "A9": "A10", "A10": "A9", "A11": "A3",
       "R1": "R2", "R2": "R1", "R3": "R1"}


def sec1():
    out, SRC = [], "с. 36–37, гл. 2, § 1"
    names = ["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10", "A11"]
    its = [(n, instance(n, *rnd.sample([x, y, N(z), C(u, w)], 3))) for n in rnd.sample(names, 5)]
    out.append(card(1, 1, "R", "iso", "sym", "short", "S1w, аксиомы",
                    f"## Условие\n\n{CONV} Каким аксиомным схемам $S_1$ (с. 36) соответствуют формулы?\n\n" +
                    "\n".join(f"{L[k]}) ${ftex(*f)}$" for k, (_, f) in enumerate(its)) + "\n\n## Ответ\n\n" +
                    "; ".join(f"{L[k]}) {n}" for k, (n, _) in enumerate(its)) + "\n\n## Решение\n\nСхемы $S_1$ — с. 36: " +
                    "; ".join(f"{n}: ${AXIOM_TEXT[n]}$" for n in names) + ".", "какая-схема", SRC))
    for nm in ("A7", "A11"):
        X, Y, Z = rnd.sample([x, N(y), C(u, w), W(u, z)], 3)
        a, b = instance(nm, X, Y, Z)
        sub = f"$x$ — ${tex(X)}$, $y$ — ${tex(Y)}$" + (f", $z$ — ${tex(Z)}$" if nm in ("A7", "A8", "A11") else "")
        out.append(card(1, 2, "D", "iso", "sym", "short", "S1w, аксиомы",
                        f"## Условие\n\n{CONV} Подставьте в схему {nm} ($ {AXIOM_TEXT[nm]} $) вместо {sub}.\n\n## Ответ\n\n"
                        f"${ftex(a, b)}$\n\n## Решение\n\nС. 36. Буквы в схемах — метапеременные (Введение, § 10, с. 14).",
                        "подстановка", SRC).replace("$ " + AXIOM_TEXT[nm] + " $", "$" + AXIOM_TEXT[nm] + "$"))
    out.append(card(1, 2, "E", "iso", "sym", "short", "S1w, аксиомы, диагностика",
                    f"## Условие\n\n{CONV} Студент: «В $S_1$, как и в $S^1$, A1 — это $x \\vdash \\sim\\sim x$». Найдите "
                    "ошибку.\n\n## Ответ\n\nВ $S_1$ A1 — $\\sim\\sim x \\vdash x$, а $x \\vdash \\sim\\sim x$ — A2: нумерация "
                    "обратная по сравнению с $S^1$.\n\n## Решение\n\nС. 36 ($S_1$) и с. 15 ($S^1$). Схемы $S_1$ "
                    "отличаются и списком, и нумерацией.", None, SRC))
    # ступень 3
    for _ in range(2):
        env = {n: rnd.randint(0, 1) for n in "xyz"}
        fs = [fresh(lambda: rnd_w("xyz", 3), lambda f: f[0] != "v") for _ in range(5)]
        out.append(card(1, 3, "C", "iso", "sym", "short", "S1w, интерпретация",
                        f"## Условие\n\n{CONV} Вычислите значения при {env_text(env)} ($x^1 \\vee \\ldots \\vee x^n$ имеет "
                        "значение 0, только если все $x^i$ имеют значение 0, с. 36).\n\n" +
                        "\n".join(f"{L[k]}) ${tex(f)}$" for k, f in enumerate(fs)) + "\n\n## Ответ\n\n" +
                        "; ".join(f"{L[k]}) {value(f, env)}" for k, f in enumerate(fs)) +
                        "\n\n## Решение\n\nОтрицание и конъюнкция — как в гл. 1 (с. 22); $\\vee$ — по с. 36.", "значения", SRC))
    out.append(card(1, 3, "E", "iso", "sym", "short", "S1w, интерпретация, диагностика",
                    f"## Условие\n\n{CONV} Студент: «$x \\vee y$ при $x = y = 1$ имеет значение 0, ведь дизъюнкция — "
                    "“одно и только одно из”». Найдите ошибку.\n\n## Ответ\n\nЭто сильная дизъюнкция $x : y$. "
                    "$x \\vee y$ при $x = y = 1$ имеет значение 1.\n\n## Решение\n\nС. 36: $\\vee$ читается «по крайней "
                    "мере одно из» и имеет значение 0, только если все члены — 0.", None, SRC))
    X, Y = rnd.sample([x, N(y), C(u, w)], 2)
    exp = W(C(X, N(Y)), C(N(X), Y))
    out.append(card(1, 3, "D", "iso", "sym", "short", "S1w, сокращения",
                    f"## Условие\n\n{CONV} По D1 § 1 гл. 2 (с. 37) раскройте сильную дизъюнкцию ${tex(X)} : {tex(Y)}$ и "
                    f"$x : y : z$ через $\\vee$.\n\n## Ответ\n\n${tex(exp)}$; $x\\sim y\\sim z \\vee y\\sim x\\sim z \\vee "
                    "z\\sim x\\sim y$\n\n## Решение\n\nD1 (с. 37): $x : y$ — сокращение для $x\\sim y \\vee \\sim xy$; "
                    "$x^1 : \\ldots : x^n$ — для $y^1 \\vee \\ldots \\vee y^n$, где $y^i$ — конъюнкция $x^i$ и отрицаний "
                    "остальных.", "раскрыть-D1", SRC))
    # ступень 4
    for _ in range(3):
        goal, lines = derivation()
        hide = sorted(rnd.sample(range(1, len(lines) + 1), min(2, len(lines))))
        shown = "\n".join(f"{n}. ${ftex(a, b)}$ [{'…' if n in hide else why_text(wh)}]"
                          for n, (a, b, wh) in enumerate(lines, 1))
        out.append(card(1, 4, "D", "complete", "sym", "short", "S1w, вывод",
                        f"## Условие\n\n{CONV} Восстановите пропущенные основания вывода в $S_1$.\n\n{shown}\n\n"
                        "## Ответ\n\n" + "; ".join(f"{n} — {why_text(lines[n - 1][2])}" for n in hide) +
                        f"\n\n## Решение\n\n{show(lines)}\n\nПравила R1–R3 — как в $S^1$ (с. 17, 36).", "дополнить", SRC))
    made = 0
    while made < 2:
        goal, lines = derivation()
        ks = [k for k, l in enumerate(lines) if isinstance(l[2], str)]
        k = rnd.choice(ks)
        bad = list(lines)
        bad[k] = (lines[k][0], lines[k][1], ALT[lines[k][2]])
        if not check(bad):
            continue
        out.append(card(1, 4, "E", "complete", "sym", "short", "S1w, вывод, диагностика",
                        f"## Условие\n\n{CONV} В выводе $S_1$ одно основание указано неверно. Найдите и исправьте.\n\n"
                        f"{show(bad)}\n\n## Ответ\n\nШаг {k + 1}: верно — {lines[k][2]}.\n\n## Решение\n\n{show(lines)}",
                        None, SRC))
        made += 1
    # ступень 5
    for k in (1, 3, 4, 5, 6, 8):
        goal, lines = derivation(k)
        out.append(card(1, 5, "D", "iso", "sym", "proof", "S1w, вывод",
                        f"## Условие\n\n{CONV} Выведите в $S_1$ формулу ${ftex(*goal)}$.\n\n## Ответ\n\nВывод из "
                        f"{len(lines)} шагов (см. решение).\n\n## Решение\n\n{show(lines)}", "вывод", SRC))
    for a, b, claim, why in [(W(x, y), C(x, y), "A3", "это не A3 ($xy \\vdash x$): в посылке дизъюнкция, а не "
                              "конъюнкция; формула и не тавтология — при $x = 1$, $y = 0$ посылка 1, заключение 0"),
                             (N(W(x, y)), C(N(x), N(y)), "A9", "A9 в $S_1$ — $\\sim(xy) \\vdash \\sim x \\vee \\sim y$; "
                              "формула студента — другая (она верна, но аксиомой не является)")]:
        out.append(card(1, 5, "E", "vary", "sym", "short", "S1w, аксиомы, диагностика",
                        f"## Условие\n\n{CONV} Студент: «${ftex(a, b)}$ — аксиома $S_1$ по схеме {claim}». Проверьте."
                        f"\n\n## Ответ\n\nНеверно: {why}.\n\n## Решение\n\nСхемы $S_1$ — с. 36.", None, SRC))
    # ступень 6
    for _ in range(4):
        if rnd.random() < 0.4:
            (a, b), lines = derivation()
            sol = "Доказуема. Вывод:\n\n" + show(lines)
            v = "доказуема"
        else:
            a, b = fresh(lambda: (rnd_w("xy", 2), rnd_w("xyz", 2)), lambda f: not strong(*f))
            v, why = verdict(a, b)
            sol = "Недоказуема: " + why
        out.append(card(1, 6, "C", "open", "sym", "proof", "S1w, доказуемость",
                        f"## Условие\n\n{CONV} Доказуема ли в $S_1$ формула ${ftex(a, b)}$? {CRIT}\n\n## Ответ\n\n{v}\n\n"
                        f"## Решение\n\n{sol}", "доказуемость", "с. 36–45, гл. 2, § 1–4"))
    for a, b, txt in [(x, W(x, y), "«по крайней мере одно из»: если есть $x$, есть и «$x$ или $y$»"),
                      (W(x, y), D(x, y), "обе дизъюнкции означают «или»")]:
        v, why = verdict(a, b)
        out.append(card(1, 6, "E", "open", "sym", "short", "S1w, доказуемость, диагностика",
                        f"## Условие\n\n{CONV} Студент: «${ftex(a, b)}$ доказуема в $S_1$: {txt}». Проверьте. {CRIT}\n\n"
                        f"## Ответ\n\n{v.capitalize()}: {why}\n\n## Решение\n\nКритерий — MT5 § 2 (с. 43). "
                        + ("Сравните с T2, п. 10 (с. 39): $x \\vdash x \\vee y$ — только если в $y$ нет новых элементарных "
                           "высказываний." if b == W(x, y) else "При $x = y = 1$ $x \\vee y$ истинно, а $x : y$ — нет."),
                        None, "с. 36–43, гл. 2, § 1–2"))
    # ступень 7: сильная или соединительная
    for _ in range(3):
        while True:
            p = rnd_w("xy", 2)
            q = rnd_w("xy", 2)
            ps, qs = swap(p), swap(q)
            if "wdis" in repr(p) + repr(q) and tautology(p, q) != S.tautology(ps, qs) and repr((p, q)) not in SEEN:
                SEEN.add(repr((p, q)))
                break
        out.append(card(1, 7, "S", "transfer", "sym", "short", "S1w, S1, дизъюнкции",
                        f"## Условие\n\n{CONV} Тавтология ли ${ftex(p, q)}$? Тавтология ли формула, в которой каждый "
                        f"$\\vee$ заменён на $:$ — ${S.ftex(ps, qs)}$?\n\n## Ответ\n\n"
                        f"с $\\vee$ — {'да' if tautology(p, q) else 'нет'}; с $:$ — {'да' if S.tautology(ps, qs) else 'нет'}"
                        "\n\n## Решение\n\n" +
                        (f"С $\\vee$: при {env_text(counterexample(p, q))} формула имеет значение 0. " if not tautology(p, q)
                         else "С $\\vee$: значения 0 нет. ") +
                        (f"С $:$: при {env_text(S.counterexample(ps, qs))} формула имеет значение 0."
                         if not S.tautology(ps, qs) else "С $:$: значения 0 нет.") +
                        " Дизъюнкции расходятся, когда истинны оба члена (с. 22, 36).", "две-дизъюнкции",
                        "с. 22, 36, гл. 1, § 5; гл. 2, § 1"))
    return out


def swap(f):
    if f[0] == "v":
        return f
    if f[0] == "neg":
        return N(swap(f[1]))
    return ("dis" if f[0] == "wdis" else f[0], tuple(swap(a) for a in f[1]))


# ---------- § 2: полнота ----------
def sec2():
    out, SRC = [], "с. 37–43, гл. 2, § 2"
    p, q = V("p"), V("q")
    X = rnd.choice([C(p, N(q)), W(p, q), N(C(p, q))])
    out.append(card(2, 2, "D", "iso", "sym", "short", "S1w, полнота",
                    f"## Условие\n\nБуквы $p, q$ — элементарные высказывания. Запишите для высказывания ${tex(X)}$ и "
                    "элементарного $p$ взаимную выводимость по п. 7 T1 § 2 (с. 38).\n\n## Ответ\n\n"
                    f"${tex(X)} \\dashv\\vdash {tex(C(X, W(p, N(p))))}$\n\n## Решение\n\nT1, п. 7: $x \\dashv\\vdash x(p \\vee "
                    "\\sim p)$, где $p$ входит в $x$; $\\dashv\\vdash$ — сокращение для пары $x \\vdash y$, $y \\vdash x$ "
                    "(с. 37).", "T1-7", SRC))
    # ступень 4: MT6, MT7 (4) + E (2)
    for _ in range(2):
        X, Y, Z, V_ = rnd.sample([x, N(y), C(u, w), z, W(u, N(z))], 4)
        out.append(card(2, 4, "D", "iso", "sym", "short", "S1w, производные правила",
                        f"## Условие\n\n{CONV} Доказуемы ${tex(X)} \\vdash {tex(W(Y, Z))}$ и ${tex(Z)} \\vdash {tex(V_)}$. "
                        "Какую формулу даёт MT6 § 2?\n\n## Ответ\n\n" + f"${tex(X)} \\vdash {tex(W(Y, V_))}$" +
                        "\n\n## Решение\n\nMT6 (с. 43): если $x \\vdash y \\vee z$ и $z \\vdash v$ доказуемы, то доказуема "
                        "$x \\vdash y \\vee v$.", "MT6", SRC))
        X, Y, Z, V_ = rnd.sample([x, N(y), C(u, w), z, W(u, N(z))], 4)
        out.append(card(2, 4, "D", "iso", "sym", "short", "S1w, производные правила",
                        f"## Условие\n\n{CONV} Доказуемы ${tex(X)} \\vdash {tex(Y)}$ и ${tex(Z)} \\vdash {tex(V_)}$. "
                        "Какую формулу даёт MT7 § 2?\n\n## Ответ\n\n" + f"${tex(W(X, Z))} \\vdash {tex(W(Y, V_))}$" +
                        "\n\n## Решение\n\nMT7 (с. 43): из $x \\vdash y$ и $z \\vdash v$ — $x \\vee z \\vdash y \\vee v$.",
                        "MT7", SRC))
    out.append(card(2, 4, "E", "iso", "sym", "short", "S1w, производные правила, диагностика",
                    f"## Условие\n\n{CONV} Студент: «Из $x \\vdash y \\vee z$ и $z \\vdash v$ по MT6 получаю $x \\vdash yv$». "
                    "Найдите ошибку.\n\n## Ответ\n\nMT6 даёт $x \\vdash y \\vee v$, а не конъюнкцию. $x \\vdash yv$ "
                    "может быть неверна: при $x = y = 1$, $z = v = 0$.\n\n## Решение\n\nMT6 (с. 43). Пример: $x \\vdash x "
                    "\\vee z$ невыводима, если… — проще: из $x \\vdash x \\vee x$ и $x \\vdash x$ ничего не следует о "
                    "$x \\vdash x \\cdot x$; но в общем случае конъюнкция требует обеих частей (R2).", None, SRC)
               .replace("MT6 (с. 43). Пример: $x \\vdash x \\vee z$ невыводима, если… — проще: из $x \\vdash x \\vee x$ и "
                        "$x \\vdash x$ ничего не следует о $x \\vdash x \\cdot x$; но в общем случае конъюнкция требует "
                        "обеих частей (R2).",
                        "MT6 (с. 43). Конъюнкцию в заключении даёт только R2 из $x \\vdash y$ и $x \\vdash v$; "
                        "здесь $x \\vdash y$ не дана."))
    out.append(card(2, 4, "E", "iso", "sym", "short", "S1w, производные правила, диагностика",
                    f"## Условие\n\n{CONV} Студент: «Из $x \\vdash y$ и $z \\vdash v$ по MT7 получаю $xz \\vdash y \\vee v$ — "
                    "это и есть MT7». Найдите ошибку.\n\n## Ответ\n\nMT7 говорит о посылке $x \\vee z$, а не $xz$.\n\n"
                    "## Решение\n\nMT7 (с. 43): $x \\vee z \\vdash y \\vee v$. Формула студента тоже тавтологична, но это "
                    "не MT7.", None, SRC))
    # ступень 5: пункты T1 (2) + E T2 (1)
    items = [(C(x, x), x, "4"), (W(x, x), x, "5"), (C(W(x, y), z), W(C(x, z), C(y, z)), "6"),
             (x, C(x, W(x, N(x))), "7")]
    for a, b, n in rnd.sample(items, 2):
        out.append(card(2, 5, "C", "iso", "sym", "short", "S1w, полнота",
                        f"## Условие\n\n{CONV} Проверьте, что обе формулы ${ftex(a, b)}$ и ${ftex(b, a)}$ — сильные "
                        "тавтологии, и найдите этот пункт среди пунктов T1 § 2.\n\n## Ответ\n\nОбе — сильные тавтологии; "
                        f"п. {n} T1 (с. 38).\n\n## Решение\n\nЗначения обеих частей совпадают при всех значениях, элементарные "
                        "высказывания одни и те же.", "T1-пункт", SRC))
    out.append(card(2, 5, "E", "vary", "sym", "short", "S1w, полнота, диагностика",
                    f"## Условие\n\n{CONV} Студент: «По T2 § 2 $x \\vee \\sim xxy \\dashv\\vdash x$ при любом $y$». Найдите "
                    "ошибку.\n\n## Ответ\n\nT2 требует, чтобы в $y$ не входили элементарные высказывания, отсутствующие "
                    "в $x$. Иначе $x \\vdash x \\vee \\sim xxy$ вводит новые элементарные высказывания и недоказуема.\n\n"
                    "## Решение\n\nT2 (с. 39). Направление $x \\vee \\sim xxy \\vdash x$ верно всегда.", None, SRC))
    # ступень 6: доказуемость (4)
    for _ in range(4):
        a, b = fresh(lambda: (rnd_w("xy", 2), rnd_w("xy", 2)))
        v, why = verdict(a, b)
        out.append(card(2, 6, "C", "open", "sym", "short", "S1w, доказуемость",
                        f"## Условие\n\n{CONV} Доказуема ли в $S_1$ формула ${ftex(a, b)}$? {CRIT}\n\n## Ответ\n\n{v}\n\n"
                        f"## Решение\n\n{why[0].upper() + why[1:]}", "доказуемость", "с. 37–45, гл. 2, § 2–4"))
    return out


# ---------- § 3: независимость ----------
TT = {"A1": "$\\sim x = 1$; остальное — как обычно",
      "A3": "$xy = 1$, $x \\vee y = 1$, $\\sim x = x$",
      "A4": "$xy = x$, $x \\vee y = x$, $\\sim x = x$"}


def sec3():
    out, SRC = [], "с. 43–45, гл. 2, § 3"
    intro = lambda k: (f"Таблица для {k} (с. 43–44): значения 1 и 0, отмечено 1; $x \\vdash y$ имеет значение 0 только при "
                       f"$x = 1$, $y = 0$; {TT[k]}.")
    k = "A4"
    env = {n: rnd.randint(0, 1) for n in "xyz"}
    fs = [fresh(lambda: rnd_w("xyz", 2), lambda f: f[0] != "v") for _ in range(5)]
    t = IW.TABLES[k]
    out.append(card(3, 2, "D", "iso", "sym", "short", "S1w, независимость",
                    f"## Условие\n\n{CONV} {intro(k)} Вычислите в этой таблице значения при {env_text(env)}.\n\n" +
                    "\n".join(f"{L[i]}) ${tex(f)}$" for i, f in enumerate(fs)) + "\n\n## Ответ\n\n" +
                    "; ".join(f"{L[i]}) {IW.val(f, env, t)}" for i, f in enumerate(fs)) +
                    "\n\n## Решение\n\nПо таблице значение конъюнкции и дизъюнкции — значение первого члена, отрицание "
                    "значения не меняет.", "таблица", SRC))
    a, b = IW.SAMPLES["A3"][0]
    ok, e = IW.valid(a, b, IW.TABLES["A3"])
    out.append(card(3, 3, "D", "iso", "sym", "short", "S1w, независимость",
                    f"## Условие\n\n{CONV} {intro('A3')} Найдите значения, при которых ${ftex(a, b)}$ (A3) имеет значение 0."
                    f"\n\n## Ответ\n\n{env_text(e)}: посылка 1, заключение 0.\n\n## Решение\n\nС. 43, п. 3.", "опровергнуть", SRC))
    out.append(card(3, 3, "E", "iso", "sym", "short", "S1w, независимость, диагностика",
                    f"## Условие\n\n{CONV} {intro('A1')} Студент: «Раз $\\sim x = 1$, то A2 ($x \\vdash \\sim\\sim x$) тоже "
                    "не тавтологична». Проверьте.\n\n## Ответ\n\nНеверно: $\\sim\\sim x = 1$, заключение A2 всегда 1, "
                    "формула тавтологична. Не тавтологична A1 ($\\sim\\sim x \\vdash x$) при $x = 0$.\n\n## Решение\n\n"
                    "С. 43, п. 1; схемы $S_1$ — с. 36.", None, SRC))
    # ступень 4: дополнение (3) + E (2)
    for k in ("A1", "A3", "A4"):
        t = IW.TABLES[k]
        a, b = IW.SAMPLES[k][0]
        names = sorted(atoms(a) | atoms(b))
        rws = [dict(zip(names, v)) for v in product((1, 0), repeat=len(names))]
        hide = sorted(rnd.sample(range(len(rws)), 2))
        tab = "\n".join("| " + " | ".join(str(r[n]) for n in names) + f" | {IW.val(a, r, t)} | " +
                        ("?" if i in hide else str(IW.val(b, r, t))) + " |" for i, r in enumerate(rws))
        out.append(card(3, 4, "D", "complete", "sym", "short", "S1w, независимость",
                        f"## Условие\n\n{CONV} {intro(k)} Заполните пропуски (значения заключения) в таблице для "
                        f"${ftex(a, b)}$ и найдите строку, где формула имеет значение 0.\n\n| " +
                        " | ".join(f"${n}$" for n in names) + " | посылка | заключение |\n|" + "---|" * (len(names) + 2) +
                        f"\n{tab}\n\n## Ответ\n\n" + "; ".join(f"строка {i + 1}: {IW.val(b, rws[i], t)}" for i in hide) +
                        f"; значение 0 — при {env_text(IW.valid(a, b, t)[1])}.\n\n## Решение\n\nС. 43–44.", "таблица-дополнить",
                        SRC))
    out.append(card(3, 4, "E", "complete", "sym", "short", "S1w, независимость, диагностика",
                    f"## Условие\n\n{CONV} {intro('A4')} Студент: «A7 $(x \\vee y)z \\vdash xz \\vee y$ здесь не тавтологична: "
                    "при $x = 0$, $y = 1$, $z = 1$ посылка 1, заключение 0». Проверьте.\n\n## Ответ\n\nНеверно: посылка "
                    "$(x \\vee y)z = x \\vee y = x = 0$, формула имеет значение 1. A7 в этой таблице тавтологична: обе части "
                    "равны $x$.\n\n## Решение\n\nС. 44, п. 4: значение конъюнкции и дизъюнкции — значение первого члена.",
                    None, SRC))
    out.append(card(3, 4, "E", "complete", "sym", "short", "S1w, независимость, диагностика",
                    f"## Условие\n\n{CONV} {intro('A3')} Студент: «Здесь и A4 не тавтологична, ведь $xy = 1$ при любых "
                    "значениях». Проверьте.\n\n## Ответ\n\nНеверно: $xy = yx = 1$, формула $1 \\vdash 1$ имеет значение 1.\n\n"
                    "## Решение\n\nС. 43, п. 3. Не тавтологична только A3.", None, SRC))
    # ступень 5: трёхзначные (2) + E (1)
    t = IW.TABLES["A11"]
    a, b = IW.SAMPLES["A11"][0]
    e = IW.valid(a, b, t)[1]
    out.append(card(3, 5, "D", "vary", "sym", "short", "S1w, независимость",
                    f"## Условие\n\n{CONV} Таблица для A11 (с. 44): значения 1, 2, 3, отмечено 1; $xy = \\max(x, y)$, "
                    "$x \\vee y = \\min(x, y)$, $\\sim x = 4 - x$; $x \\vdash y$ имеет значение 1 тогда и только тогда, когда "
                    f"значение $x$ не меньше значения $y$. Найдите значения, при которых ${ftex(a, b)}$ (A11) не тавтологична."
                    f"\n\n## Ответ\n\nНапример, {env_text(e)}: посылка {IW.val(a, e, t)}, заключение {IW.val(b, e, t)}.\n\n"
                    "## Решение\n\nС. 44, п. 11. Вычисляем по таблице; формула имеет значение 1, только если посылка "
                    "не меньше заключения.", "трёхзначная", SRC))
    t = IW.TABLES["R1"]
    p, q = V("p"), V("q")
    out.append(card(3, 5, "D", "vary", "sym", "short", "S1w, независимость",
                    f"## Условие\n\nБуквы $p, q$ — элементарные высказывания. Таблица для R1 (с. 44): значения 1, 2, 3, "
                    "отмечено 1; $xy = \\max(x, y)$, $x \\vee y = \\min(x, y)$, $\\sim x = 4 - x$; $x \\vdash y$ имеет "
                    "неотмеченное значение только при $x$ = 1 или 2 и $y = 3$. Вычислите значения обеих частей "
                    "$p \\vee \\sim qq \\vdash p(q \\vee \\sim q)$ при $p = 3$, $q = 2$.\n\n## Ответ\n\nПосылка 2, "
                    "заключение 3 — значение неотмеченное.\n\n## Решение\n\n$\\sim q = 2$, $\\sim qq = \\max(2, 2) = 2$, "
                    "$p \\vee \\sim qq = \\min(3, 2) = 2$; $q \\vee \\sim q = 2$, $p(q \\vee \\sim q) = \\max(3, 2) = 3$. "
                    "Так книга (с. 44) обосновывает независимость R1.", None, SRC))
    out.append(card(3, 5, "E", "vary", "sym", "short", "S1w, независимость, диагностика",
                    f"## Условие\n\n{CONV} Таблица для A11 (с. 44): $xy = \\max(x, y)$, $x \\vee y = \\min(x, y)$, "
                    "$\\sim x = 4 - x$; $x \\vdash y$ имеет значение 1, когда значение $x$ не меньше значения $y$. Студент: "
                    "«При $x = 2$ $\\sim x = 2$, значит, $x \\sim x = 2$ — это “ложь”, и A3 здесь не тавтологична». "
                    "Найдите ошибку.\n\n## Ответ\n\nЗначение 2 не означает «ложь»: отмечено только 1, а формула следования "
                    "получает значение по правилу «$x \\geq y$». A3: $\\max(x, y) \\geq x$ всегда — тавтологична.\n\n"
                    "## Решение\n\nС. 44, п. 11.", None, SRC))
    # ступень 6: чужие таблицы (3)
    for k in ("A1", "A3", "A4"):
        t = IW.TABLES[k]
        nms = rnd.sample([n for n in IW.SAMPLES if n not in (k, "A5", "A6")], 3) + [k]
        rnd.shuffle(nms)
        res = {n: IW.valid(*IW.SAMPLES[n][0], t) for n in nms}
        out.append(card(3, 6, "C", "open", "sym", "short", "S1w, независимость",
                        f"## Условие\n\n{CONV} {intro(k)} Какие формулы тавтологичны в этой таблице?\n\n" +
                        "\n".join(f"{L[i]}) ${ftex(*IW.SAMPLES[n][0])}$" for i, n in enumerate(nms)) + "\n\n## Ответ\n\n" +
                        "; ".join(f"{L[i]}) " + ("да" if res[n][0] else "нет") for i, n in enumerate(nms)) +
                        "\n\n## Решение\n\n" + "\n".join(f"{L[i]}) пример {n}: " + ("тавтологична." if res[n][0] else
                                                                                  f"при {env_text(res[n][1])} — 0.")
                                                        for i, n in enumerate(nms)), "чужая-таблица", SRC))
    # ступень 9: что нельзя вывести без …
    for nm, (a, b) in [("$x \\vee y \\vdash y \\vee x$", (W(x, y), W(y, x))),
                       ("$\\sim(xy) \\vdash \\sim y \\vee \\sim x$", (N(C(x, y)), W(N(y), N(x))))]:
        keys = ["A1", "A3", "A4", "A11"]
        fail = [k for k in keys if not IW.valid(a, b, IW.TABLES[k])[0]]
        out.append(card(3, 9, "M", "transfer", "meta", "proof", "S1w, независимость",
                        f"## Условие\n\n{CONV} Формула {nm} доказуема в $S_1$. Пользуясь таблицами § 3 для A1, A3, A4, A11 "
                        "(в них правила R1–R3 сохраняют тавтологичность), выясните, без каких схем или правил её нельзя вывести.\n\n## Ответ\n\n" +
                        (", ".join(fail) if fail else "эти таблицы ничего не показывают") +
                        "\n\n## Решение\n\nЕсли в таблице для схемы (правила) остальные аксиомы тавтологичны и правила "
                        "сохраняют тавтологичность, а формула — нет, её нельзя вывести без этой схемы (правила). Проверка: " +
                        "; ".join(f"{k} — " + ("не тавтологична" if k in fail else "тавтологична") for k in keys) + ".",
                        "нужна-схема", SRC))
    return out


# ---------- § 4: эквивалентность ----------
def sec4():
    out, SRC = [], "с. 20, 37, 45, гл. 1, § 3; гл. 2, § 1, 4"
    X, Y = rnd.sample([x, N(y), C(u, w)], 2)
    out.append(card(4, 3, "D", "iso", "sym", "short", "S1, S1w, эквивалентность",
                    f"## Условие\n\n{CONV} Переведите формулу $S^1$ ${S.ftex(D(X, Y), C(D(X, Y), z))}$ на язык $S_1$, "
                    "раскрыв $:$ по D1 § 1 гл. 2 (с. 37).\n\n## Ответ\n\n" +
                    f"${ftex(W(C(X, N(Y)), C(N(X), Y)), C(W(C(X, N(Y)), C(N(X), Y)), z))}$\n\n## Решение\n\n"
                    "D1 (с. 37): $x : y$ — сокращение для $x\\sim y \\vee \\sim xy$.", "перевод", SRC))
    for f in (W(x, N(y)), C(W(x, y), z)):
        g = S.N(S.C(*(N(a) for a in f[1]))) if f[0] == "wdis" else C(N(C(N(x), N(y))), z)
        out.append(card(4, 4, "D", "iso", "sym", "short", "S1, S1w, эквивалентность",
                        f"## Условие\n\n{CONV} Переведите высказывание $S_1$ ${tex(f)}$ на язык $S^1$, раскрыв $\\vee$ по D2 "
                        "§ 3 гл. 1 (с. 20), и проверьте, что значения совпадают.\n\n## Ответ\n\n" + f"${S.tex(g)}$" +
                        "\n\n## Решение\n\nD2 § 3 гл. 1: $x \\vee y$ — сокращение для $\\sim(\\sim x\\sim y)$; «не оба ложны» — "
                        "это и есть «по крайней мере одно из».", "перевод", SRC))
    out.append(card(4, 5, "E", "vary", "sym", "short", "S1, S1w, эквивалентность, диагностика",
                    f"## Условие\n\n{CONV} Студент переводит $x \\vee y$ на язык $S^1$ как $x : y$ и делает вывод: "
                    "«Раз множества теорем $S^1$ и $S_1$ совпадают (§ 4), $x \\vee y \\vdash x : y$ — теорема». Найдите "
                    "ошибку.\n\n## Ответ\n\nПеревод неверен: $x \\vee y$ — это $\\sim(\\sim x\\sim y)$ (D2 § 3 гл. 1). "
                    "$x \\vee y \\vdash x : y$ не тавтология ($x = y = 1$).\n\n## Решение\n\nС. 20, 45. MT1 § 4 говорит о "
                    "совпадении теорем при принятых определениях D2 § 3 гл. 1 и D1 § 1 гл. 2.", None, SRC))
    a, b = W(C(x, N(y)), C(N(x), y)), W(x, y)
    out.append(card(4, 6, "C", "open", "sym", "short", "S1, S1w, эквивалентность",
                    f"## Условие\n\n{CONV} Доказуема ли в $S_1$ формула ${ftex(a, b)}$ (то есть $x : y \\vdash x \\vee y$ "
                    f"после раскрытия $:$)? А обратная? {CRIT}\n\n## Ответ\n\nПервая — да, обратная — нет.\n\n## Решение\n\n"
                    f"Первая — сильная тавтология. Обратная: {verdict(b, a)[1]}", None, "с. 37, 43, гл. 2, § 1–2"))
    return out


# ---------- смешанный набор после гл. 1 ----------
def mixed():
    spec = importlib.util.spec_from_file_location("g", ROOT / "scripts" / "gen" / "g01_04_09.py")
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    g.rnd.seed(17_200)
    cards = [g.value_card(2) for _ in range(3)] + [g.tval_card(2)]
    w = None
    while not w:
        w = g.wrong_value_card(2)
    cards.append(w)
    cards += [g.taut_card(3), g.taut_card(3), g.classify_card(3), g.classify_card(3), g.canon_check_card(3),
              g.kind_card(3, 5, g.SRC5)]
    goal, lines = g.G2.G1.derivation()
    c = g.G2.G1.corrupt(lines)
    while not c:
        goal, lines = g.G2.G1.derivation()
        c = g.G2.G1.corrupt(lines)
    new, n, right = c
    cards.append(g.card(1, 3, "E", "iso", "sym", "short", "S1, вывод, диагностика",
                        f"## Условие\n\n{g.CONV} Проверьте вывод в $S^1$; если есть ошибка — укажите шаг и исправьте.\n\n"
                        f"{g.G2.G1.show(new)}\n\n## Ответ\n\nОшибка в шаге {n}: верно — {right}.\n\n## Решение\n\n"
                        f"{g.G2.G1.show(lines)}", None, "с. 15–17, гл. 1, § 1"))
    import re
    out = []
    for c in cards:
        c = re.sub(r"chapter: 1\nsection: \d+\n", "chapter: 17\nsection: 2\n", c, count=1)
        c = re.sub(r"step: \w+\n", "step: mixed\n", c, count=1)
        c = re.sub(r"series: .*\n", "", c, count=1)
        out.append(c)
    return out


def main():
    a = sec1() + sec2() + sec3() + sec4()
    (ROOT / "drafts" / "02-gen.md").write_text("\n=====\n".join(a), encoding="utf-8")
    m = mixed()
    (ROOT / "drafts" / "17.02-gen.md").write_text("\n=====\n".join(m), encoding="utf-8")
    print(len(a), len(m))


if __name__ == "__main__":
    main()
