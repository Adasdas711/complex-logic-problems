#!/usr/bin/env python3
"""Серии задач к Введению, § 4 «Термины» (с. 5–6): ступени 1–3.

Пишет черновик drafts/00.04-gen.md; затем: python3 scripts/split_cards.py drafts/00.04-gen.md --remove
Повторный запуск с тем же зерном даёт те же задачи.
"""
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
from terms import (P, S, X, conj, disj, each, fact, kinds, latex, name, neg, opp, parse_chain,  # noqa: E402
                   point, reading, some, such, asuch, tup, verdict, why_not)

rnd = random.Random(1970)
SUBJ = [S("s"), S("t"), S("u")]
PRED = [P("p"), P("q"), P("r")]
STAT = [X("x"), X("y")]
CONV = ("Обозначения: $s, t, u$ — простые субъекты; $p, q, r$ — простые предикаты; "
        "$x, y$ — высказывания.")
SRC = "с. 5–6, § 4, D1–D3"

UNARY = [neg, opp]
NARY = [conj, disj, each, some]


def atom(kind=None):
    pool = {"S": SUBJ, "P": PRED, "X": STAT}[kind] if kind else SUBJ + PRED + STAT
    return rnd.choice(pool)


def one_level():
    """Один оператор над простыми членами; примерно половина — не термины."""
    op = rnd.choice(["neg", "opp", "nary", "nary", "tuple", "fact", "such", "asuch", "name"])
    good = rnd.random() < 0.6
    k = rnd.choice("SP")
    if op in ("neg", "opp"):
        return rnd.choice(UNARY)(atom(k) if good else atom("X"))
    if op == "nary":
        f = rnd.choice(NARY)
        pool = SUBJ if k == "S" else PRED
        a = rnd.sample(pool, 2)
        if not good:
            a[1] = atom("P" if k == "S" else "S")
        return f(*a)
    if op == "tuple":
        a = rnd.sample(SUBJ, rnd.choice([2, 3]))
        if not good:
            a[-1] = atom("P")
        return tup(*a)
    if op == "fact":
        return fact(atom("X") if good else atom(k))
    if op == "such":
        return such(atom("X") if good else atom(k))
    if op == "asuch":
        return asuch(atom(k), atom("X")) if good else asuch(atom(k), atom(rnd.choice("SP")))
    return name(atom())


def closed(e):
    """Выражение с явными границами: простой член, скобочная форма, тильда над таким выражением."""
    from terms import Atom
    return isinstance(e, Atom) or e.op in ("conj", "disj", "each", "some", "tuple", "name") or (
        e.op == "opp" and closed(e.args[0]))


def closed_term(kind, depth):
    for _ in range(200):
        e = term_of(kind, depth)
        if closed(e):
            return e
    return atom(kind)


def term_of(kind, depth):
    """Случайный правильный термин вида kind ('S' или 'P') заданной глубины."""
    if depth == 0:
        return atom(kind)
    choices = ["neg", "opp", "nary", "asuch"] + (["tuple", "fact", "name"] if kind == "S" else ["such"])
    op = rnd.choice(choices)
    if op in ("neg", "opp"):
        return rnd.choice(UNARY)(closed_term(kind, depth - 1))
    if op == "nary":
        a = term_of(kind, depth - 1)
        b = term_of(kind, rnd.randint(0, depth - 1))
        while latex(b) == latex(a):
            b = term_of(kind, rnd.randint(0, depth - 1))
        return rnd.choice(NARY)(a, b)
    if op == "tuple":
        a, b = term_of("S", depth - 1), term_of("S", 0)
        while latex(b) == latex(a):
            b = term_of("S", 0)
        return tup(a, b)
    if op == "fact":
        return fact(atom("X"))
    if op == "such":
        return such(atom("X"))
    if op == "asuch":
        return asuch(closed_term(kind, depth - 1), atom("X"))
    return name(term_of(rnd.choice("SP"), depth - 1))


def spoil(e):
    """Портит термин в одном месте: подставляет член не того вида."""
    from terms import Op
    if not isinstance(e, Op):
        return atom("X") if e.kind != "X" else atom("S")
    args = list(e.args)
    i = rnd.randrange(len(args))
    args[i] = spoil(args[i])
    return Op(e.op, tuple(args))


def card(level, typ, step, cond, form, ans, body, series):
    meta = (f"chapter: 0\nsection: 4\nlevel: {level}\ntype: {typ}\nstep: {step}\ncondition: {cond}\n"
            f"form: {form}\nanswer: {ans}\nsource: \"{SRC}\"\nseries: {series}\ngenerated: true\n"
            f"tags: [термины]")
    return f"---\n{meta}\n---\n\n{body}\n"


def items(n, gen):
    out, seen = [], set()
    while len(out) < n:
        e = gen()
        if latex(e) not in seen:
            seen.add(latex(e))
            out.append(e)
    return out


def classify_card(level, exprs, series, step="iso"):
    letters = "абвгдежз"
    cond = "\n".join(f"{letters[i]}) ${latex(e)}$" for i, e in enumerate(exprs))
    ans = "; ".join(f"{letters[i]}) {verdict(e)}" for i, e in enumerate(exprs))
    sol = []
    for i, e in enumerate(exprs):
        if level == 1:
            ref = point(e) if kinds(e) else why_not(e)
            sol.append(f"{letters[i]}) ${latex(e)}$ — {verdict(e)}: {ref}.")
        else:
            sol.append(f"{letters[i]}) Разбор снизу вверх:\n" + "\n".join(f"   - {l}" for l in parse_chain(e)))
    task = ("Для каждого выражения определите, является ли оно термином, и если да — субъект это или "
            "предикат. Укажите пункт определения D1 (предикат) или D2 (субъект)." if level == 1 else
            "Для каждого выражения определите, термин ли это, и если да — субъект или предикат. "
            "Обоснуйте ответ разбором снизу вверх: для каждой части укажите пункт D1 или D2.")
    body = f"## Условие\n\n{CONV} {task}\n\n{cond}\n\n## Ответ\n\n{ans}\n\n## Решение\n\n" + "\n".join(sol)
    return card(level, "R" if level == 1 else "A", step, "def", "sym", "short" if level < 3 else "proof", body, series)


READABLE = ["neg", "conj", "disj", "each", "some", "opp", "fact", "such", "asuch", "name"]


def readable_one():
    op = rnd.choice(READABLE)
    k = rnd.choice("SP")
    if op in ("neg", "opp"):
        return {"neg": neg, "opp": opp}[op](atom(k))
    if op in ("conj", "disj", "each", "some"):
        pool = SUBJ if k == "S" else PRED
        return {"conj": conj, "disj": disj, "each": each, "some": some}[op](*rnd.sample(pool, 2))
    if op == "fact":
        return fact(atom("X"))
    if op == "such":
        return such(atom("X"))
    if op == "asuch":
        return asuch(atom(k), atom("X"))
    return name(atom())


def read_card(exprs, reverse=False):
    letters = "абвгдежз"
    if not reverse:
        cond = "\n".join(f"{letters[i]}) ${latex(e)}$" for i, e in enumerate(exprs))
        ans = "; ".join(f"{letters[i]}) «{reading(e)}»" for i, e in enumerate(exprs))
        task = "Прочитайте термины по правилам чтения из § 4."
        lvl, step = 1, "iso"
    else:
        cond = "\n".join(f"{letters[i]}) «{reading(e)}»" for i, e in enumerate(exprs))
        ans = "; ".join(f"{letters[i]}) ${latex(e)}$" for i, e in enumerate(exprs))
        task = "Запишите символами книги."
        lvl, step = 2, "vary"
    sol = ("Правила чтения терминов — § 4, с. 6, пп. 1–10. Обратите внимание: $(a \\cdot b)$ — "
           "«предмет, обозначаемый каждым из терминов», а $\\cdot\\,(a, b)$ — «каждый из предметов»; "
           "так же различаются $(a \\vee b)$ и $\\vee(a, b)$.")
    body = (f"## Условие\n\n{CONV} {task}\n\n{cond}\n\n## Ответ\n\n{ans}\n\n## Решение\n\n{sol}")
    return card(lvl, "T", step, "def", "sym", "short", body, "чтение-терминов" if not reverse else "запись-терминов")


def main():
    out = []
    # Ступень 1: 8 карточек на опознание, 3 на чтение.
    for _ in range(8):
        out.append(classify_card(1, items(5, one_level), "опознание-терминов"))
    for _ in range(3):
        out.append(read_card(items(5, readable_one)))
    # Ступень 2: 6 карточек на термины глубины 2 (часть испорчена), 4 на запись символами.
    def depth2():
        e = term_of(rnd.choice("SP"), 2)
        return spoil(e) if rnd.random() < 0.4 else e
    for _ in range(6):
        out.append(classify_card(2, items(4, depth2), "разбор-терминов"))
    for _ in range(4):
        out.append(read_card(items(5, readable_one), reverse=True))
    # Ступень 3: 8 карточек на термины глубины 3 с полным обоснованием.
    def depth3():
        e = term_of(rnd.choice("SP"), 3)
        return spoil(e) if rnd.random() < 0.4 else e
    for _ in range(8):
        out.append(classify_card(3, items(3, depth3), "разбор-терминов-3"))
    path = ROOT / "drafts" / "00.04-gen.md"
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n=====\n".join(out), encoding="utf-8")
    print(f"{len(out)} карточек → {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
