#!/usr/bin/env python3
"""Серии для занятий 9–11: гл. 1, § 1 (ступени 5–7), § 2 (теоремные схемы), смешанный набор после Введения
(ступени 5–6). Все выводы проверяются s1.check/check2, доказуемость — критерием сильной тавтологии.
Пишет drafts/01.01b-gen.md, drafts/01.02-gen.md, drafts/17.01b-gen.md.
"""
import importlib.util
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
from s1 import (AXIOM_TEXT, LEMMA_TEXT, C, D, N, V, axiom, check, check2, counterexample, ftex, instance,  # noqa
                lemma, new_atoms, strong_tautology, tautology, tex)


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / "gen" / f"{name}.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


G1 = load("g01_01")
rnd = random.Random(1970_18)
G1.rnd.seed(1970_19)
x, y, z, u, w = (V(c) for c in "xyzuw")
CONV = G1.CONV
L = "абвгдежз"
CRIT = ("Пользуйтесь критерием: формула доказуема в $S^1$ тогда и только тогда, когда она — сильная тавтология, то есть тавтология, в заключение которой не входят элементарные высказывания, отсутствующие в посылке (§ 4, MT1, с. 21; § 5, MT1, с. 22; § 7, MT6, с. 32).")


def card(sec, level, typ, step, form, ans, tags, body, series, src, cond="def"):
    meta = (f"chapter: 1\nsection: {sec}\nlevel: {level}\ntype: {typ}\nstep: {step}\ncondition: {cond}\n"
            f"form: {form}\nanswer: {ans}\nsource: \"{src}\"\nsystem: \"S^1\"\nseries: {series}\n"
            f"generated: true\ntags: [{tags}]")
    return f"---\n{meta}\n---\n\n{body}\n"


def env_text(env):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(env.items()))


def verdict_text(a, b):
    """Обоснование доказуемости/недоказуемости по § 4, 5, 7."""
    if strong_tautology(a, b):
        return "доказуема", ""
    if new_atoms(a, b):
        na = ", ".join(f"${t}$" for t in sorted(new_atoms(a, b)))
        return "недоказуема", (f"в заключение входит {na}, которого нет в посылке; по § 4, MT1 (с. 21) такая формула "
                               "не может быть теоремой $S^1$")
    env = counterexample(a, b)
    return "недоказуема", (f"при {env_text(env)} посылка имеет значение 1, а заключение — 0, то есть формула не "
                           "тавтология; по § 5, MT1 (с. 22) она не теорема $S^1$")


UNPROV_PARADOX = [lambda X, Y: (C(X, N(X)), Y), lambda X, Y: (X, D(Y, N(Y))), lambda X, Y: (X, N(C(Y, N(Y)))),
                  lambda X, Y: (C(N(X), X), N(Y))]
UNPROV_NONTAUT = [lambda X, Y: (C(X, Y), N(X)), lambda X, Y: (D(X, Y), C(X, Y)), lambda X, Y: (X, C(X, Y)),
                  lambda X, Y: (N(C(X, Y)), N(X)), lambda X, Y: (D(X, Y), X), lambda X, Y: (C(X, N(Y)), C(X, Y))]
SMALL = [x, y, z, N(x), N(z), D(u, w)]


def provable_item():
    goal, lines = G1.derivation()
    return goal, lines


def unprovable_item(kind=None):
    X, Y = rnd.sample(SMALL, 2)
    while atoms_overlap(X, Y):
        X, Y = rnd.sample(SMALL, 2)
    pool = {"p": UNPROV_PARADOX, "n": UNPROV_NONTAUT}[kind or rnd.choice("pn")]
    a, b = rnd.choice(pool)(X, Y)
    assert not strong_tautology(a, b)
    return a, b


def atoms_overlap(X, Y):
    from s1 import atoms
    return bool(atoms(X) & atoms(Y))


def show(lines):
    return G1.show(lines)


def open_card(sec, src, series):
    if rnd.random() < 0.45:
        (a, b), lines = provable_item()
        sol = f"Доказуема. Вывод:\n\n{show(lines)}"
        ans = "доказуема"
    else:
        a, b = unprovable_item()
        v, why = verdict_text(a, b)
        sol, ans = f"Недоказуема: {why}.", "недоказуема"
    body = (f"## Условие\n\n{CONV} Доказуема ли в $S^1$ формула ${ftex(a, b)}$? Если да — выведите её, если нет — "
            f"обоснуйте. {CRIT}\n\n## Ответ\n\n{ans}\n\n## Решение\n\n{sol}")
    return card(sec, 6, "C", "open", "sym", "proof", "S1, доказуемость", body, series, src)


def fake_card(sec, src, level=6):
    a, b = unprovable_item()
    claim = rnd.choice(["A3", "A4", "A7", "A9", "A1"])
    _, why = verdict_text(a, b)
    body = (f"## Условие\n\n{CONV} Студент утверждает, что формула ${ftex(a, b)}$ доказуема в $S^1$, и приводит "
            f"«вывод»:\n\n1. ${ftex(a, b)}$ [{claim}]\n\nПроверьте. {CRIT}\n\n## Ответ\n\nВывод ошибочен: формула — не "
            f"аксиома {claim}; более того, она недоказуема.\n\n## Решение\n\nСхема {claim} — с. 15–17: "
            f"${AXIOM_TEXT.get(claim, claim)}$; данная формула не получается из неё подстановкой. Недоказуемость: {why}.")
    return card(sec, level, "E", "open", "sym", "short", "S1, доказуемость, диагностика", body, "ложный-вывод", src)


def transfer_card(sec, src):
    items = []
    for _ in range(4):
        r = rnd.random()
        if r < 0.3:
            (a, b), _ = provable_item()
        elif r < 0.65:
            a, b = unprovable_item("p")
        else:
            a, b = unprovable_item("n")
        items.append((a, b))
    cond_ = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b) in enumerate(items))
    ans = "; ".join(f"{L[k]}) {'тавтология' if tautology(a, b) else 'не тавтология'}, в $S^1$ "
                    f"{'доказуема' if strong_tautology(a, b) else 'недоказуема'}" for k, (a, b) in enumerate(items))
    sol = "\n".join(f"{L[k]}) " + ("сильная тавтология — доказуема (§ 7, MT6)." if strong_tautology(a, b) else
                                   ("тавтология, но " + verdict_text(a, b)[1] + "." if tautology(a, b) else
                                    verdict_text(a, b)[1] + ".")) for k, (a, b) in enumerate(items))
    body = (f"## Условие\n\n{CONV} Для каждой формулы ответьте: (1) тавтология ли она, то есть верна ли как "
            f"формула классической логики высказываний ($:$ — «одно и только одно из»); (2) доказуема ли она в "
            f"$S^1$. {CRIT}\n\n{cond_}\n\n## Ответ\n\n{ans}\n\n## Решение\n\n{sol}\n\nРазница возникает на формулах "
            "вроде $x\\sim x \\vdash y$: в классической логике они верны, а в $S^1$ исключены как «парадоксы».")
    return card(sec, 7, "S", "transfer", "sym", "short", "S1, классическая логика", body, "S1-и-классика", src)


# ---------- § 1, ступени 5–7 ----------
def sec1():
    out = []
    SRC = "с. 15–17, 21–22, 32, гл. 1, § 1"
    for tpl in (G1.T11, G1.T12):
        goal, lines = G1.derivation(tpl)
        body = (f"## Условие\n\n{CONV} Выведите в $S^1$ формулу ${ftex(*goal)}$.\n\n## Ответ\n\nВывод из {len(lines)} "
                f"шагов (см. решение).\n\n## Решение\n\n{show(lines)}")
        out.append(card(1, 5, "D", "iso", "sym", "proof", "S1, вывод", body, "вывод", "с. 15–17, гл. 1, § 1"))
    for _ in range(16):
        out.append(open_card(1, SRC, "доказуемость"))
    for _ in range(8):
        out.append(fake_card(1, SRC))
    for _ in range(10):
        out.append(transfer_card(1, SRC))
    return out


# ---------- § 2: теоремные схемы ----------
def show2(lines):
    return "\n".join(f"{n}. ${ftex(a, b)}$ [{G1.why_text(wh)}]" for n, (a, b, wh) in enumerate(lines, 1))


def lemma_instance(name, X, Y):
    return {"T1": (C(X, Y), Y), "T2": (X, X), "T3": (X, C(X, X)), "T4": (C(X, X), X), "T5": (C(Y, X), C(X, Y)),
            "T6": (D(X, Y), D(Y, X)), "T7": (D(Y, X), D(X, Y))}[name]


def lemma_derivations(X, Y, Z):
    """Выводы с использованием T1–T7 как лемм."""
    return [
        ((C(D(X, Y), Z), D(Y, X)), [(C(D(X, Y), Z), D(X, Y), "A3"), (D(X, Y), D(Y, X), "T6"),
                                   (C(D(X, Y), Z), D(Y, X), ("R1", 1, 2))]),
        ((C(X, Y), C(Y, Y)), [(C(X, Y), Y, "T1"), (Y, C(Y, Y), "T3"), (C(X, Y), C(Y, Y), ("R1", 1, 2))]),
        ((C(X, X), N(N(X))), [(C(X, X), X, "T4"), (X, N(N(X)), "A1"), (C(X, X), N(N(X)), ("R1", 1, 2))]),
        ((C(Z, D(X, Y)), D(Y, X)), [(C(Z, D(X, Y)), D(X, Y), "T1"), (D(X, Y), D(Y, X), "T6"),
                                   (C(Z, D(X, Y)), D(Y, X), ("R1", 1, 2))]),
        ((C(X, Y), C(Y, X)), [(C(X, Y), Y, "T1"), (C(X, Y), X, "A3"), (C(X, Y), C(Y, X), ("R2", 1, 2))]),
        ((X, C(X, N(N(X)))), [(X, X, "T2"), (X, N(N(X)), "A1"), (X, C(X, N(N(X))), ("R2", 1, 2))]),
        ((N(N(D(X, Y))), D(Y, X)), [(N(N(D(X, Y))), D(X, Y), "A2"), (D(X, Y), D(Y, X), "T6"),
                                   (N(N(D(X, Y))), D(Y, X), ("R1", 1, 2))]),
        ((C(Y, X), N(N(Y))), [(C(Y, X), C(X, Y), "T5"), (C(X, Y), Y, "T1"), (C(Y, X), Y, ("R1", 1, 2)),
                              (Y, N(N(Y)), "A1"), (C(Y, X), N(N(Y)), ("R1", 3, 4))]),
    ]


def pick3():
    return rnd.sample([x, y, z, N(x), N(y), D(u, w), N(z)], 3)


def sec2():
    out, SRC = [], "с. 17–20, гл. 1, § 2"
    names = ["T1", "T2", "T3", "T4", "T5", "T6", "T7"]
    # ступень 1
    items = [(n, lemma_instance(n, *rnd.sample([x, y, N(z), D(u, w)], 2))) for n in rnd.sample(names, 5)]
    body = (f"## Условие\n\n{CONV} Каким теоремным схемам § 2 (T1–T7) соответствует каждая формула? Укажите все.\n\n" +
            "\n".join(f"{L[k]}) ${ftex(*f)}$" for k, (_, f) in enumerate(items)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[k]}) " + ", ".join(m for m in names if __import__("s1").is_lemma(*f, m))
                                             for k, (n, f) in enumerate(items)) +
            "\n\n## Решение\n\nСхемы T1–T7 — с. 18: " + "; ".join(f"{n}: ${LEMMA_TEXT[n]}$" for n in names) + ".")
    out.append(card(2, 1, "R", "iso", "sym", "short", "S1, теоремные схемы", body, "какая-T", SRC))
    # ступень 2: подстановка
    for k in range(5):
        n = names[k % 7] if k % 7 != 1 else "T6"
        X, Y = rnd.sample([x, y, N(z), D(u, w), C(u, w)], 2)
        a, b = lemma_instance(n, X, Y)
        sub = f"$x$ — ${tex(X)}$" + ("" if n in ("T2", "T3", "T4") else f", $y$ — ${tex(Y)}$")
        body = (f"## Условие\n\n{CONV} Подставьте в теоремную схему {n} (${LEMMA_TEXT[n]}$) вместо {sub}.\n\n## Ответ\n\n"
                f"${ftex(a, b)}$\n\n## Решение\n\nСхема {n} — с. 18; теоремные схемы, как и аксиомные, означают: формула "
                "доказуема для любых высказываний такого строения (Введение, § 10, с. 14).")
        out.append(card(2, 2, "D", "iso", "sym", "short", "S1, теоремные схемы", body, "подстановка-в-T", SRC))
    # ступень 3: аксиома или теоремная схема (4) + диагностика (2)
    for _ in range(4):
        its = []
        for _ in range(5):
            X, Y = rnd.sample([x, y, N(z), D(u, w)], 2)
            if rnd.random() < 0.5:
                f = lemma_instance(rnd.choice(names), X, Y)
            else:
                f = instance(rnd.choice(["A1", "A2", "A3", "A4", "A9"]), X, Y)
            from s1 import is_lemma
            labs = ([axiom(*f)] if axiom(*f) else []) + [n for n in names if is_lemma(*f, n)]
            lab = ", ".join(labs)
            its.append((f, lab))
        body = (f"## Условие\n\n{CONV} Для каждой формулы укажите все аксиомные (A1–A11) и теоремные (T1–T7) схемы, "
                f"которым она соответствует.\n\n" + "\n".join(f"{L[k]}) ${ftex(*f)}$" for k, (f, _) in enumerate(its)) +
                "\n\n## Ответ\n\n" + "; ".join(f"{L[k]}) {lab}" for k, (_, lab) in enumerate(its)) +
                "\n\n## Решение\n\nАксиомные схемы — с. 15–17, теоремные — с. 18. Одна формула может подходить под несколько "
                "схем: например, $xx \\vdash x$ — это и A3, и T1, и T4; T5 повторяет A4, а T7 — T6 с переименованными "
                "буквами.")
        out.append(card(2, 3, "C", "iso", "sym", "short", "S1, схемы", body, "A-или-T", SRC))
    for _ in range(2):
        X, Y = rnd.sample([x, y, N(z)], 2)
        wrong = rnd.choice([("T1", (C(X, Y), X), "A3"), ("T4", (C(X, Y), X), "A3"), ("T3", (X, C(X, Y)), None)])
        n, f, right = wrong
        tail = (f"Это {right}." if right else "Это не пример ни одной схемы; формула вообще недоказуема: в заключение "
                f"входит ${tex(Y)}$, которого нет в посылке (§ 4, MT1).")
        body = (f"## Условие\n\n{CONV} Студент: «${ftex(*f)}$ — пример теоремной схемы {n}». Найдите ошибку.\n\n## Ответ\n\n"
                f"Неверно: {n} — ${LEMMA_TEXT[n]}$. {tail}\n\n## Решение\n\nСхемы — с. 15, 18.")
        out.append(card(2, 3, "E", "iso", "sym", "short", "S1, схемы, диагностика", body, None, SRC))
    # ступень 4: дополнение (5) + диагностика (2)
    for k in range(5):
        X, Y, Z = pick3()
        goal, lines = rnd.choice(lemma_derivations(X, Y, Z))
        assert not check2(lines), check2(lines)
        hide = sorted(rnd.sample(range(1, len(lines) + 1), 2))
        shown = "\n".join(f"{n}. ${ftex(a, b)}$ [{'…' if n in hide else G1.why_text(wh)}]"
                          for n, (a, b, wh) in enumerate(lines, 1))
        body = (f"## Условие\n\n{CONV} В выводе ${ftex(*goal)}$ (с использованием теоремных схем § 2) не указаны "
                f"основания некоторых шагов. Восстановите их.\n\n{shown}\n\n## Ответ\n\n" +
                "; ".join(f"{n} — {G1.why_text(lines[n - 1][2])}" for n in hide) +
                f"\n\n## Решение\n\n{show2(lines)}")
        out.append(card(2, 4, "D", "complete", "sym", "short", "S1, вывод", body, "дополнение-вывода-T", SRC))
    for _ in range(2):
        X, Y, Z = pick3()
        goal, lines = rnd.choice(lemma_derivations(X, Y, Z))
        k = rnd.choice([n for n, l in enumerate(lines) if isinstance(l[2], str)])
        a, b, wh = lines[k]
        alt = {"T1": "A3", "A3": "T1", "T6": "T7", "T3": "T4", "T4": "T3", "A1": "A2", "A2": "A1", "T5": "A3",
               "T2": "A1"}[wh]
        bad = list(lines)
        bad[k] = (a, b, alt)
        if not check2(bad):
            continue
        shown = "\n".join(f"{n}. ${ftex(a, b)}$ [{G1.why_text(wh)}]" for n, (a, b, wh) in enumerate(bad, 1))
        body = (f"## Условие\n\n{CONV} В выводе ${ftex(*goal)}$ одно основание указано неверно. Найдите и исправьте."
                f"\n\n{shown}\n\n## Ответ\n\nШаг {k + 1}: верно — {wh}.\n\n## Решение\n\n{show2(lines)}")
        out.append(card(2, 4, "E", "complete", "sym", "short", "S1, вывод, диагностика", body, None, SRC))
    while sum('level: 4' in c for c in out) < 7:
        X, Y, Z = pick3()
        goal, lines = lemma_derivations(X, Y, Z)[7]
        body = (f"## Условие\n\n{CONV} Восстановите основания всех шагов вывода ${ftex(*goal)}$.\n\n" +
                "\n".join(f"{n}. ${ftex(a, b)}$ […]" for n, (a, b, _) in enumerate(lines, 1)) +
                "\n\n## Ответ\n\n" + "; ".join(f"{n} — {G1.why_text(l[2])}" for n, l in enumerate(lines, 1)) +
                f"\n\n## Решение\n\n{show2(lines)}")
        out.append(card(2, 4, "D", "complete", "sym", "short", "S1, вывод", body, "дополнение-вывода-T", SRC))
    # ступень 5: вывод с леммами (8) + диагностика (2)
    for k in range(8):
        X, Y, Z = pick3()
        goal, lines = lemma_derivations(X, Y, Z)[k]
        assert not check2(lines)
        body = (f"## Условие\n\n{CONV} Выведите в $S^1$ формулу ${ftex(*goal)}$, пользуясь аксиомными схемами и "
                f"теоремными схемами T1–T7 (с. 18).\n\n## Ответ\n\nВывод из {len(lines)} шагов (см. решение).\n\n"
                f"## Решение\n\n{show2(lines)}")
        out.append(card(2, 5, "D", "iso", "sym", "proof", "S1, вывод", body, "вывод-с-T", SRC))
    made = 0
    while made < 2:
        goal, lines = G1.derivation(rnd.choice([G1.T5, G1.T10, G1.T12]))
        c = G1.corrupt(lines)
        if not c:
            continue
        new, n, right = c
        body = (f"## Условие\n\n{CONV} Проверьте вывод ${ftex(*goal)}$; если есть ошибка — укажите шаг и исправьте."
                f"\n\n{G1.show(new)}\n\n## Ответ\n\nОшибка в шаге {n}: верно — {right}.\n\n## Решение\n\n{G1.show(lines)}")
        out.append(card(2, 5, "E", "open", "sym", "short", "S1, вывод, диагностика", body, None, SRC))
        made += 1
    # ступень 6: открытый исход (6) + ложные выводы (3)
    for _ in range(6):
        c = open_card(2, "с. 17–22, 32, гл. 1, § 2", "доказуемость")
        out.append(c.replace("level: 6\n", "level: 6\n", 1))
    for _ in range(3):
        out.append(fake_card(2, "с. 17–22, 32, гл. 1, § 2"))
    return out


# ---------- смешанный набор после Введения: ступени 5–6 ----------
def mixed():
    import statements as St
    import terms as T
    g58 = load("g00_05_08")
    g58.rnd.seed(17_02)
    out = []
    SRC = "Введение, с. 5–11"
    for _ in range(7):   # ступень 5: две ошибки в разборе
        e = g58.uniq(1, lambda: g58.stmt(3), St.is_stmt)[0]
        lines = St.chain(e)
        cand = [k for k, l in enumerate(lines) if "(дано)" not in l]
        if len(cand) < 3:
            continue
        ks = sorted(rnd.sample(cand, 2))
        shown = list(lines)
        for k in ks:
            shown[k] = shown[k].replace("— высказывание (", "— не высказывание (")
        body = (f"## Условие\n\n{g58.CONV} В разборе высказывания ${St.latex(e)}$ есть ошибки. Найдите все и исправьте.\n\n" +
                "\n".join(f"{i + 1}. {l}" for i, l in enumerate(shown)) +
                "\n\n## Ответ\n\nОшибки в строках " + " и ".join(str(k + 1) for k in ks) + ": там «высказывание» "
                "(по пунктам, указанным в скобках).\n\n## Решение\n\nВерный разбор (§ 5, D1–D2, с. 7):\n" +
                "\n".join(f"- {l}" for l in lines))
        meta = ("---\nchapter: 17\nsection: 1\nlevel: 5\ntype: E\nstep: mixed\ncondition: def\nform: sym\n"
                f"answer: short\nsource: \"{SRC}\"\ngenerated: true\ntags: [смешанный, диагностика]\n---\n\n")
        out.append(meta + body + "\n")
    while len(out) < 7:
        out.append(out[0])
    g4 = load("g00_04")
    g4.rnd.seed(17_03)
    for _ in range(9):   # ступень 6: что это — термин, высказывание, формула следования?
        pool = []
        t1 = g4.term_of(rnd.choice("SP"), 2)
        pool.append((T.latex(t1), T.verdict(t1)))
        s1_ = g58.stmt(2)
        pool.append((St.latex(s1_), "высказывание" if St.is_stmt(s1_) else "ничего из перечисленного"))
        a, b = g58.uniq(2, lambda: g58.stmt(1), St.is_stmt)
        pool.append((f"{St.latex(a)} \\vdash {St.latex(b)}", "формула следования"))
        pool.append((f"\\vdash {St.latex(a)}", "формула вырожденного следования"))
        bad = g58.bad_basic()
        pool.append((St.latex(bad), "ничего из перечисленного"))
        rnd.shuffle(pool)
        body = (f"## Условие\n\n{g58.CONV} Для каждого выражения определите, что это: субъект, предикат, "
                "высказывание, формула следования (или вырожденного следования) — или ничего из перечисленного.\n\n" +
                "\n".join(f"{L[k]}) ${e}$" for k, (e, _) in enumerate(pool)) +
                "\n\n## Ответ\n\n" + "; ".join(f"{L[k]}) {v}" for k, (_, v) in enumerate(pool)) +
                "\n\n## Решение\n\nТермины — § 4 (D1, D2, с. 5–6); высказывания — § 5 (D1, D2, с. 7); формулы следования — "
                "§ 8 (D1, D5, с. 10–11).")
        meta = ("---\nchapter: 17\nsection: 1\nlevel: 6\ntype: R\nstep: mixed\ncondition: def\nform: sym\n"
                f"answer: short\nsource: \"{SRC}\"\ngenerated: true\ntags: [смешанный]\n---\n\n")
        out.append(meta + body + "\n")
    return out


def main():
    (ROOT / "drafts").mkdir(exist_ok=True)
    a, b, c = sec1(), sec2(), mixed()
    for name, cards in (("01.01b-gen", a), ("01.02-gen", b), ("17.01b-gen", c)):
        (ROOT / "drafts" / f"{name}.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(a), len(b), len(c))


if __name__ == "__main__":
    main()
