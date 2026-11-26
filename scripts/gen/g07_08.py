#!/usr/bin/env python3
"""Серии для занятий 51–60: гл. 7, § 5–21 (теория кванторов), гл. 8, § 1–5 (теория предикации),
смешанные 17.08 (окончание) и 17.09 (начало). Пишет drafts/51-60-gen.md.
Задачи ступеней 8–10 (с пометкой hand) пишутся здесь же по шаблонам доказательств книги.
"""
import importlib.util
import itertools
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import ifq as Q  # noqa: E402
from ifq import ALL, EL, EX, C, N, W, V  # noqa: E402

spec = importlib.util.spec_from_file_location("g06_07", ROOT / "scripts" / "gen" / "g06_07.py")
G6 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G6)
G6.rnd.seed(5160)
G6.G.rnd.seed(5161)
G6.G16.rnd.seed(5162)

rnd = random.Random(5163)
L = "абвгдежз"
USED = set()
for f in (ROOT / "data" / "zadachi").glob("*.md"):
    for c in f.read_text(encoding="utf-8").split("\n=====\n"):
        if "## Условие" in c and "## Ответ" in c:
            USED.add(c[c.index("## Условие"):c.index("## Ответ")])
G6.USED = USED

TT = "Буквы $a, b, c, d$ — термины; $x, y, z, v$ — высказывания."
TQ = "Буквы $a, b$ — термины; $x, y, z, v$ — высказывания."


# ---------------------------------------------------------------- оформление
def T(f, ctx="top"):
    """TeX в обозначениях книги (кванторы с внутренним отрицанием и неопределённостью, предикация)."""
    k = f[0]
    if k == "v":
        return f[1]
    if k == "el":
        return f"({f[1]} \\leftarrow {f[2]})"
    if k == "pn":
        return f"({f[1]} \\urcorner\\!\\leftarrow {f[2]})"
    if k == "pq":
        return f"({f[1]}? \\leftarrow {f[2]})"
    if k == "neg":
        g = f[1]
        return f"\\sim {T(g)}" if g[0] not in ("conj", "wdis", "dis") else f"\\sim({T(g, 'neg')})"
    if k == "conj":
        return "".join(f"({T(a)})" if a[0] in ("conj", "wdis", "dis") else T(a, "conj") for a in f[1])
    if k in ("wdis", "dis"):
        sep = " \\vee " if k == "wdis" else " : "
        out = sep.join(f"({T(a)})" if a[0] in ("wdis", "dis") else T(a) for a in f[1])
        return f"({out})" if ctx in ("conj", "neg", "q") else out
    if k in QK:
        g = f[2]
        inner = T(g) if g[0] not in ("conj", "wdis", "dis") else f"({T(g)})"
        return f"({QK[k]} {f[1]}){inner}"
    if k == "imp":
        return f"({T(f[1])} \\supset {T(f[2])})"
    raise ValueError(k)


QK = {"all": "\\forall", "ex": "\\exists", "nall": "\\urcorner\\forall", "nex": "\\urcorner\\exists",
      "qall": "?\\forall", "qex": "?\\exists"}


def FT(a, b=None):
    return f"\\vdash {T(a)}" if b is None else f"{T(a)} \\vdash {T(b)}"


def Qn(kind, a, f):
    return (kind, a, f)


def card(ch, sec, lvl, typ, step, cond, ans, sol, src, tags, form="sym", answ="short", system=None, gen=True):
    sysl = f'system: "{system}"\n' if system else ""
    genl = "generated: true\n" if gen else ""
    return (f"---\nchapter: {ch}\nsection: {sec}\nlevel: {lvl}\ntype: {typ}\nstep: {step}\ncondition: def\nform: {form}\n"
            f"answer: {answ}\nsource: \"{src}\"\n{sysl}{genl}tags: [{tags}]\n---\n\n## Условие\n\n{cond}\n\n## Ответ\n\n{ans}\n\n"
            f"## Решение\n\n{sol}\n")


def cond_of(c):
    return c[c.index("## Условие"):c.index("## Ответ")]


def fresh(fn, tries=80):
    c = None
    for _ in range(tries):
        c = fn()
        if c is not None and cond_of(c) not in USED:
            break
    USED.add(cond_of(c))
    return c


def items(lst):
    return "\n".join(f"{L[i]}) {s}" for i, s in enumerate(lst))


def answers(lst):
    return "; ".join(f"{L[i]}) {s}" for i, s in enumerate(lst))


def perm_letters(s, letters="xyzv"):
    p = dict(zip(letters, rnd.sample(letters, len(letters))))

    def rm(m):
        return re.sub(r"(?<![\\A-Za-z])([" + letters + r"])(?![A-Za-z])", lambda q: p[q.group(1)], m.group(0))
    return re.sub(r"\$[^$]+\$", rm, s)


# ---------------------------------------------------------------- формулы гл. 7
x, y, z, v = V("x"), V("y"), V("z"), V("v")
a_ = "a"

# § 6: теоремные схемы S^s_cq (с. 102–105) — tex и основания из книги
T6 = {
    1: ("\\sim(\\forall a)x \\vdash (\\exists a)\\sim x", "A6, A7"), 2: ("(\\exists a)x \\vdash \\sim(\\forall a)\\sim x", "A6, A7"),
    3: ("\\sim x \\vdash \\sim(\\forall a)x", "A2, T2"), 4: ("\\sim(\\exists a)x \\vdash \\sim x", "A6, A7, A1"),
    5: ("\\sim(\\exists a)(xy) \\vdash \\sim((\\forall a)x(\\exists a)y)", "A4, A6, A7, T1, T2"),
    6: ("\\sim((\\forall a)x \\vee (\\exists a)y) \\vdash \\sim(\\forall a)(x \\vee y)", "A3, A6, A7, T1, T2"),
    8: ("\\sim\\sim(\\exists a)\\sim x \\vdash \\sim(\\forall a)x", "A6, A7"), 9: ("\\sim(\\forall a)x \\vdash \\sim\\sim(\\exists a)\\sim x", "A6, A7"),
    10: ("(\\forall a)x(\\forall b)x \\vdash (\\forall a)(\\exists b)x", "A1, A2, R1, T17"),
    11: ("(\\forall a)x(\\exists b)x \\vdash (\\forall a)(\\exists b)x", "A1, R1, T17"),
    14: ("(\\forall a)(\\forall b)x \\vdash (\\forall b)(\\forall a)x", "A1, R1, T17"),
    15: ("(\\exists a)(\\forall b)x \\vdash (\\forall b)(\\exists a)x", "A1, A2, R1, T17, R2, T18"),
    16: ("(\\exists a)(\\exists b)x \\vdash (\\exists b)(\\exists a)x", "A2, R2, T18"),
    17: ("x \\vdash (\\forall a)x, где $a$ не входит свободно в $x$", None),
    18: ("(\\exists a)x \\vdash x, где $a$ не входит свободно в $x$", None),
    19: ("(\\forall a)x(\\forall a)y \\vdash (\\forall a)(xy)", "A1, R1, T17"), 20: ("(\\forall a)(xy) \\vdash (\\forall a)x(\\forall a)y", "A1, R1, T17"),
    21: ("(\\exists a)(xy) \\vdash (\\exists a)x(\\exists a)y", "R2"),
    22: ("(\\exists a)(x \\vee y) \\vdash (\\exists a)x \\vee (\\exists a)y", "T19, T20, A6, A7"),
    23: ("(\\exists a)x \\vee (\\exists a)y \\vdash (\\exists a)(x \\vee y)", "T19, T20, A6, A7"),
    24: ("(\\forall a)x \\vee (\\forall a)y \\vdash (\\forall a)(x \\vee y)", "T21, MT2, A6, A7"),
    25: ("(\\forall a)x \\vee (\\exists a)y \\vdash (\\exists a)(x \\vee y)", "T23, A1, A2, MT4"),
    26: ("(\\exists a)x \\vee (\\forall a)y \\vdash (\\exists a)(x \\vee y)", "T23, A1, A2, MT4"),
    27: ("(\\forall a)x \\vdash (\\exists a)x", "A1, A2"), 28: ("\\sim(\\exists a)x \\vdash \\sim(\\forall a)x", "T27, MT2"),
    29: ("(\\forall a)(xy) \\vdash (\\forall a)x(\\exists a)y", "T20, T27"), 30: ("(\\forall a)(xy) \\vdash (\\exists a)x(\\forall a)y", "T20, T27"),
    33: ("(\\exists a)(\\forall b)x \\vdash (\\exists b)(\\exists a)x", "T15, T27"),
    35: ("(\\forall a)x \\vee (\\forall a)y \\vdash (\\exists a)(x \\vee y)", "T24, T27"),
    36: ("(\\forall a)x(\\forall a)y \\vdash (\\exists a)(xy)", "T19, T27"),
    37: ("\\sim(\\forall a)\\sim x \\vdash (\\exists a)x", "A6, A7"), 38: ("(\\forall a)(\\forall b)x \\vdash (\\forall b)(\\exists a)x", "A1, A2, R1, T17"),
    39: ("(\\forall a)(\\forall b)x \\vdash (\\exists b)(\\forall a)x", "A1, R1, R2, T18"),
    40: ("(\\forall a)(\\forall b)x \\vdash (\\exists b)(\\exists a)x", "A1, A2"), 41: ("(\\forall a)(\\exists b)x \\vdash (\\exists b)(\\exists a)x", "A1, T16"),
}
T6REC = {k: v for k, v in T6.items() if k not in (17, 18)}
T6BASE = {k: v for k, v in T6.items() if v[1] and k not in (17, 18)}

# Формулы случаев 3–8 MT1 § 8 (с. 109–110): z = (a ← b), v = (a ← c); в случае 8 z = (a ← b)
zz, vv = EL("a", "b"), EL("a", "c")
K = {"A": ALL, "E": EX}
CASES = {}
CASES[3] = [(K[p]("a", zz if s else N(zz)), K[q]("a", zz)) for (p, s, q) in
            [("A", 1, "A"), ("E", 1, "A"), ("A", 1, "E"), ("E", 1, "E"), ("A", 0, "A"), ("A", 0, "E"), ("E", 0, "A"), ("E", 0, "E")]]
CASES[4] = [(K[p]("a", C(zz, vv)), C(K[q]("a", zz), K[r]("a", vv))) for p in "AE" for q, r in ["AA", "AE", "EA", "EE"]]
CASES[5] = [(K[p]("a", W(zz, vv)), W(K[q]("a", zz), K[r]("a", vv))) for p in "AE" for q, r in ["AA", "AE", "EA", "EE"]]
CASES[6] = [(C(K[q]("a", zz), K[r]("a", vv)), K[p]("a", C(zz, vv))) for q, r in ["AA", "AE", "EA", "EE"] for p in "AE"]
CASES[7] = [(W(K[q]("a", zz), K[r]("a", vv)), K[p]("a", W(zz, vv))) for p in "AE" for q, r in ["AA", "AE", "EA", "EE"]]
CASES[8] = [(K[p]("a", K[q]("b", zz)), K[r]("b", K[s]("a", zz))) for p in "AE" for q in "AE" for r in "AE" for s in "AE"]
# доказательства тавтологий (с. 109–110)
PROOF = {3: {0: "$a \\vdash a$ системы $S^s$", 2: "T27 § 6", 3: "$a \\vdash a$ системы $S^s$"},
         4: {0: "T20", 1: "T29", 2: "T30", 3: "T31 § 6", 7: "T21"},
         5: {1: "A4", 2: "T32", 3: "T34", 7: "T22"},
         6: {0: "T19", 1: "T36", 3: "A3", 5: "T42"},
         7: {0: "T24", 4: "T35", 5: "T25", 6: "T26", 7: "T23"},
         8: {0: "T14", 1: "T38", 2: "T39", 3: "T40", 7: "T41", 9: "T15", 11: "T33", 15: "T16"}}
for k, lst in CASES.items():
    for i, (p, q) in enumerate(lst):
        assert Q.qtaut(p, q) == (i in PROOF[k]), (k, i)
CASEP = {3: "с. 109", 4: "с. 109", 5: "с. 109", 6: "с. 109–110", 7: "с. 110", 8: "с. 110"}
ALLC = [(k, i, p, q) for k, lst in CASES.items() for i, (p, q) in enumerate(lst)]


# ---------------------------------------------------------------- 07.05 независимость
def free_terms(f):
    return {t for t in Q.terms(f) if Q.free_occ(t, f)}


def val_rule(rule, p, q):
    """Значение формулы p ⊢ q по исключающему правилу для A1 или A2, затем по общему."""
    fp, fq = free_terms(p), free_terms(q)
    if rule == "A1" and fq - fp:
        return 0, f"термин ${sorted(fq - fp)[0]}$ входит в заключение свободно, а в посылку — нет (исключающее правило)"
    if rule == "A2" and fp - fq:
        return 0, f"термин ${sorted(fp - fq)[0]}$ входит в посылку свободно, а в заключение — нет (исключающее правило)"
    s = Q.strong(Q.qfree(p), Q.qfree(q))
    return int(s), f"по общему правилу — значение бескванторной формы ${FT(Q.qfree(p), Q.qfree(q))}$: {int(s)}"


def ax_inst(n, X, Y, a="a"):
    return G6.aq_inst(n, X, Y, a)


def c705_val(lvl):
    rule = rnd.choice(["A1", "A2"])
    its = []
    for n in rnd.sample(["A1", "A2", "A3", "A4", "A6", "A7"], 4):
        X, Y = EL("a", rnd.choice("bc")), EL("a", "d")
        its.append(ax_inst(n, X, Y))
    res = [val_rule(rule, p, q) for p, q in its]
    cond = (f"{TT} Найдите значения формул по семантическим правилам, принятым для доказательства независимости {rule} "
            f"(§ 5 гл. 7, с. 101): сначала исключающее правило для {rule}, затем общее.\n\n" + items([f"${FT(p, q)}$" for p, q in its]))
    return card(7, 5, lvl, "C", "iso", cond, answers([str(r[0]) for r in res]),
                "\n".join(f"{L[i]}) {r[1]}." for i, r in enumerate(res)) + "\n\nС. 101–102.", "с. 101–102, гл. 7, § 5",
                "кванторы, независимость", system="S^s_cq")


R_EX = [("R1", "(\\forall b)((b \\leftarrow c)(b \\leftarrow d)) \\vdash (\\forall b)(b \\leftarrow c)",
         "$(\\forall b)zv$ имеет значение 1, а в $z = (b \\leftarrow c)$ входит термин $c$, отсутствующий в $v$; значит, $(\\forall b)z$ имеет значение 0, и формула — 0"),
        ("R2", "(\\exists b)((b \\leftarrow c)(b \\leftarrow d)) \\vdash (\\exists b)(b \\leftarrow c)",
         "$(\\exists b)(zv)$ имеет значение 1, $z$ содержит термин $c$, отсутствующий в $v$; значит, $(\\exists b)z$ имеет значение 0")]


def c705_rule(lvl):
    r, f, why = rnd.choice(R_EX)
    cond = (f"{TT} По исключающему семантическому правилу для {r} (§ 5 гл. 7, с. 102) найдите значение формулы ${f}$, "
            f"доказуемой с помощью {r}.")
    return card(7, 5, lvl, "C", "iso", cond, "0.", why[0].upper() + why[1:] + ". Значит, правило " + r +
                " выводит из формул со значением 1 формулу со значением 0 — оно независимо (с. 102).", "с. 102, гл. 7, § 5",
                "кванторы, независимость", system="S^s_cq")


E705 = [("«Чтобы доказать независимость A1, достаточно заметить, что $(\\forall a)(a \\leftarrow b) \\vdash (a \\leftarrow b)$ "
         "имеет значение 1 по общему правилу»", "сначала применяется исключающее правило (с. 101): термин $a$ в заключение входит "
         "свободно, а в посылку нет — формула имеет значение 0; только так показывается независимость"),
        ("«Для A2 исключающее правило: если $a$ входит свободно в заключение, а в посылку нет, формула имеет значение 0»",
         "это правило для A1; для A2 — термин входит свободно в посылку, а в заключение нет (с. 101)"),
        ("«Для A5 исключающее правило добавляет ограничение на вхождение $a$ в $x$»", "для A5 ограничение на вхождение $a$ "
         "в $x$, наоборот, отбрасывается (с. 101)"),
        ("«Для A6 правило: если $(\\exists b)\\sim z$ имеет значение 0, то $(\\forall b)z$ имеет значение 0»", "это правило для A7; "
         "для A6 — если $(\\exists b)\\sim z$ имеет значение 1, то $(\\forall b)z$ имеет значение 1 (с. 101)"),
        ("«Общее правило применяется первым, исключающее — только если общее не дало результата»", "в каждом случае сначала "
         "применяется исключающее правило, затем общее (с. 101)"),
        ("«Для R1 правило: если $(\\forall b)zv$ имеет значение 1, то $(\\forall b)z$ имеет значение 0»", "добавлено условие: в "
         "$z$ входит термин, отсутствующий в $v$ (с. 102)")]


def e705(lvl):
    s, w = rnd.choice(E705)
    return card(7, 5, lvl, "E", "open", f"{TT} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 5 (с. 101–102).",
                "с. 101–102, гл. 7, § 5", "кванторы, независимость, диагностика", system="S^s_cq")


def m705(lvl, d, i):
    if d:
        return e705(lvl)
    return c705_val(lvl) if i % 2 == 0 or lvl == 6 else c705_rule(lvl)


# ---------------------------------------------------------------- 07.06 следствия
def sub_vars(s):
    return perm_letters(s, "xy")


def t_rec(lvl, typ="R"):
    ks = rnd.sample(sorted(T6REC), 4)
    cond = (f"{TQ} Какие теоремные схемы $S^s_{{cq}}$ § 6 гл. 7 (с. 102–105) записаны ниже? Укажите номера.\n\n" +
            items([f"${T6REC[k][0]}$" for k in ks]))
    return card(7, 6, lvl, typ, "iso", cond, answers([f"T{k}" for k in ks]), "С. 102–105.", "с. 102–105, гл. 7, § 6",
                "кванторы, теоремы", system="S^s_cq")


def t_base(lvl, typ="D"):
    ks = rnd.sample(sorted(T6BASE), 3)
    cond = (f"{TQ} Восстановите основания (по списку книги, с. 102–105), на которых доказываются теоремные схемы "
            "$S^s_{cq}$:\n\n" + items([f"T{k}. ${T6BASE[k][0]}$" for k in ks]))
    return card(7, 6, lvl, typ, "complete", cond, answers([f"[{T6BASE[k][1]}]" for k in ks]),
                "С. 102–105: в квадратных скобках книга указывает схемы, позволяющие доказать теорему.", "с. 102–105, гл. 7, § 6",
                "кванторы, теоремы", system="S^s_cq")


DER = {
    "T27": ("(\\forall a)x \\vdash (\\exists a)x", ["$(\\forall a)x \\vdash x$ [A1]", "$x \\vdash (\\exists a)x$ [A2]",
                                                     "$(\\forall a)x \\vdash (\\exists a)x$ [$S^s$: 1, 2]"]),
    "T29": ("(\\forall a)(xy) \\vdash (\\forall a)x(\\exists a)y", ["$(\\forall a)(xy) \\vdash (\\forall a)x(\\forall a)y$ [T20]",
            "$(\\forall a)y \\vdash (\\exists a)y$ [T27]", "$(\\forall a)x(\\forall a)y \\vdash (\\forall a)x(\\exists a)y$ [$S^s$: 2]",
            "$(\\forall a)(xy) \\vdash (\\forall a)x(\\exists a)y$ [$S^s$: 1, 3]"]),
    "T36": ("(\\forall a)x(\\forall a)y \\vdash (\\exists a)(xy)", ["$(\\forall a)x(\\forall a)y \\vdash (\\forall a)(xy)$ [T19]",
            "$(\\forall a)(xy) \\vdash (\\exists a)(xy)$ [T27]", "$(\\forall a)x(\\forall a)y \\vdash (\\exists a)(xy)$ [$S^s$: 1, 2]"]),
    "T35": ("(\\forall a)x \\vee (\\forall a)y \\vdash (\\exists a)(x \\vee y)", ["$(\\forall a)x \\vee (\\forall a)y \\vdash (\\forall a)(x \\vee y)$ [T24]",
            "$(\\forall a)(x \\vee y) \\vdash (\\exists a)(x \\vee y)$ [T27]", "$(\\forall a)x \\vee (\\forall a)y \\vdash (\\exists a)(x \\vee y)$ [$S^s$: 1, 2]"]),
    "T40": ("(\\forall a)(\\forall b)x \\vdash (\\exists b)(\\exists a)x", ["$(\\forall a)(\\forall b)x \\vdash (\\forall b)x$ [A1]",
            "$(\\forall b)x \\vdash x$ [A1]", "$x \\vdash (\\exists a)x$ [A2]", "$(\\exists a)x \\vdash (\\exists b)(\\exists a)x$ [A2]",
            "$(\\forall a)(\\forall b)x \\vdash (\\exists b)(\\exists a)x$ [$S^s$: 1–4]"]),
    "T28": ("\\sim(\\exists a)x \\vdash \\sim(\\forall a)x", ["$(\\forall a)x \\vdash (\\exists a)x$ [T27]",
            "множества элементарных высказываний посылки и заключения совпадают [бескванторная форма $x \\vdash x$]",
            "$\\sim(\\exists a)x \\vdash \\sim(\\forall a)x$ [MT2: 1, 2]"]),
    "T3": ("\\sim x \\vdash \\sim(\\forall a)x", ["$\\sim x \\vdash (\\exists a)\\sim x$ [A2]", "$(\\exists a)\\sim x \\vdash \\sim(\\forall a)\\sim\\sim x$ [T2]",
           "$\\sim(\\forall a)\\sim\\sim x \\vdash \\sim(\\forall a)x$ [$S^s$: замена $\\sim\\sim x$ на $x$]", "$\\sim x \\vdash \\sim(\\forall a)x$ [$S^s$: 1–3]"]),
    "T21": ("(\\exists a)(xy) \\vdash (\\exists a)x(\\exists a)y", ["$xy \\vdash x$ [$S^s$]", "$(\\exists a)(xy) \\vdash (\\exists a)x$ [R2: 1]",
            "$xy \\vdash y$ [$S^s$]", "$(\\exists a)(xy) \\vdash (\\exists a)y$ [R2: 3]", "$(\\exists a)(xy) \\vdash (\\exists a)x(\\exists a)y$ [$S^s$: 2, 4]"]),
    "T19": ("(\\forall a)x(\\forall a)y \\vdash (\\forall a)(xy)", ["$(\\forall a)x(\\forall a)y \\vdash xy$ [A1, $S^s$]",
            "$(\\forall a)((\\forall a)x(\\forall a)y) \\vdash (\\forall a)(xy)$ [R1: 1]",
            "$(\\forall a)x(\\forall a)y \\vdash (\\forall a)((\\forall a)x(\\forall a)y)$ [T17: $a$ не входит свободно]",
            "$(\\forall a)x(\\forall a)y \\vdash (\\forall a)(xy)$ [$S^s$: 3, 2]"]),
}


def derive(lvl, hide=False):
    k = rnd.choice(sorted(DER))
    goal, st = DER[k]
    if hide:
        j = rnd.randrange(len(st))
        sh = [re.sub(r"\[[^\[\]]*\]$", "[…]", s) if i == j else s for i, s in enumerate(st)]
        return card(7, 6, lvl, "D", "complete", f"{TQ} Восстановите пропущенное основание в доказательстве {k} § 6: ${goal}$ "
                    "($S^s$ — шаг общей теории дедукции).\n\n" + "\n".join(f"{i + 1}. {s}" for i, s in enumerate(sh)),
                    f"Шаг {j + 1}: {re.search(r'\[([^\[\]]*)\]$', st[j]).group(1)}.", "\n".join(f"{i + 1}. {s}" for i, s in enumerate(st)),
                    "с. 102–105, гл. 7, § 6", "кванторы, вывод", system="S^s_cq")
    return card(7, 6, lvl, "D", "iso", f"{TQ} Докажите в $S^s_{{cq}}$ теоремную схему {k} § 6: ${goal}$. Можно ссылаться на "
                "предшествующие теоремные схемы § 6.", f"Доказательство из {len(st)} шагов (см. решение).",
                "\n".join(f"{i + 1}. {s}" for i, s in enumerate(st)) + "\n\nС. 102–105.", "с. 102–105, гл. 7, § 6", "кванторы, вывод",
                answ="proof", system="S^s_cq")


def mt_apply(lvl, typ="D"):
    v_ = rnd.choice([
        ("MT1", "доказуемы $x \\vdash yz$ и $z \\vdash v$", "$x \\vdash yv$"),
        ("MT1", "доказуемы $xy \\vdash z$ и $v \\vdash x$", "$vy \\vdash z$"),
        ("MT2", "доказуема $(\\forall a)x \\vdash (\\exists a)x$, множества элементарных высказываний посылки и заключения совпадают",
         "$\\sim(\\exists a)x \\vdash \\sim(\\forall a)x$"),
        ("MT3", "доказуемы $x \\vdash y \\vee z$ и $z \\vdash v$, множества элементарных высказываний совпадают", "$x \\vdash y \\vee v$"),
        ("MT4", "доказуемы $x \\vee y \\vdash z$ и $v \\vdash x$ (при условии MT3)", "$v \\vee y \\vdash z$"),
        ("MT5", "доказуемы $\\sim x \\vdash y$ и $x \\vdash v$ (при условии MT3)", "$\\sim v \\vdash y$"),
        ("MT5", "доказуемы $x \\vdash \\sim y$ и $v \\vdash y$ (при условии MT3)", "$x \\vdash \\sim v$"),
        ("MT*1", "доказуема $x \\vdash y$, множества элементарных высказываний $x$ и $y$ совпадают", "$\\sim(\\forall a)y \\vdash \\sim(\\forall a)x$"),
        ("MT*2", "доказуема $x \\vdash y$, множества элементарных высказываний $x$ и $y$ совпадают", "$\\sim(\\exists a)y \\vdash \\sim(\\exists a)x$")])
    cond = f"{TQ} В $S^s_{{cq}}$ {v_[1]}. Какую формулу позволяет получить {v_[0]} § 6 гл. 7 (с. 102–104)?"
    return card(7, 6, lvl, typ, "iso", cond, v_[2],
                f"{v_[0]} (с. 102–104).", "с. 102–104, гл. 7, § 6", "кванторы, метатеоремы", system="S^s_cq")


E706 = [
    ("Из доказуемой $(\\forall a)((a \\leftarrow b)(a \\leftarrow c)) \\vdash (\\forall a)(a \\leftarrow b)$ по MT2 получаем $\\sim(\\forall a)(a \\leftarrow b) \\vdash "
     "\\sim(\\forall a)((a \\leftarrow b)(a \\leftarrow c))$", "MT2 требует совпадения множеств элементарных высказываний посылки и заключения; здесь "
     "$(a \\leftarrow c)$ есть только в посылке. Полученная формула вводит в заключение $(a \\leftarrow c)$ и по MT1 § 3 недоказуема"),
    ("$(\\forall b)(\\exists a)(a \\leftarrow b) \\vdash (\\exists a)(\\forall b)(a \\leftarrow b)$ — это T15", "T15 — $(\\exists a)(\\forall b)x \\vdash "
     "(\\forall b)(\\exists a)x$; обратная формула не тавтология (случай 8 MT1 § 8, с. 110) и недоказуема"),
    ("$(a \\leftarrow b) \\vdash (\\forall a)(a \\leftarrow b)$ — пример T17", "T17 требует, чтобы $a$ не входил свободно в $x$; здесь $a$ входит "
     "свободно (с. 104)"),
    ("$(\\exists a)(a \\leftarrow b) \\vdash (a \\leftarrow b)$ — пример T18", "T18 требует, чтобы $a$ не входил свободно в $x$ (с. 104)"),
    ("$(\\forall a)(x \\vee y) \\vdash (\\forall a)x \\vee (\\forall a)y$ — это T24", "T24 — $(\\forall a)x \\vee (\\forall a)y \\vdash (\\forall a)(x \\vee y)$; "
     "обратная формула не тавтология (случай 5, с. 109)"),
    ("$(\\exists a)x(\\exists a)y \\vdash (\\exists a)(xy)$ — это T21", "T21 — $(\\exists a)(xy) \\vdash (\\exists a)x(\\exists a)y$; обратная формула "
     "не тавтология (случай 6, с. 109–110)"),
    ("$(\\exists a)x \\vdash (\\forall a)x$ — это T27", "T27 — $(\\forall a)x \\vdash (\\exists a)x$ (с. 104); формула студента — A5 и только "
     "при условии, что $a$ не входит свободно в $x$"),
    ("По MT1 из $x \\vdash yz$ и $z \\vdash v$ получаем $x \\vdash v$", "MT1 даёт $x \\vdash yv$ (с. 102); $x \\vdash v$ тоже доказуема, но "
     "не по MT1, а по $S^s$ (отбрасывание $y$ и транзитивность)"),
    ("MT*1 позволяет из любой доказуемой $x \\vdash y$ получить $\\sim(\\forall a)y \\vdash \\sim(\\forall a)x$", "MT*1 требует совпадения "
     "множеств элементарных высказываний $x$ и $y$ (с. 103)"),
]


def e706(lvl):
    s, w = rnd.choice(E706)
    return card(7, 6, lvl, "E", "open", f"{TT} Студент: «{s}». Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 6 (с. 102–105).",
                "с. 102–105, гл. 7, § 6", "кванторы, теоремы, диагностика", system="S^s_cq")


def prov706(lvl, typ="C"):
    its = rnd.sample(ALLC, 4)
    cond = (f"{TT} Доказуемы ли в $S^s_{{cq}}$ формулы? Если да, назовите теоремную или аксиомную схему.\n\n" +
            items([f"${FT(p, q)}$" for _, _, p, q in its]))
    ans = [("да, " + PROOF[k][i]) if i in PROOF[k] else "нет" for k, i, _, _ in its]
    sol = "\n".join(f"{L[j]}) " + (f"тавтология, доказуема ({PROOF[k][i]})." if i in PROOF[k] else
                                     f"не тавтология (случай {k} MT1 § 8, {CASEP[k]}); по процедуре § 9 (с. 120) контрольная форма совпадает с формулой (п. 1 D1) и не тавтология — недоказуема.")
                    for j, (k, i, _, _) in enumerate(its))
    return card(7, 6, lvl, typ, "open", cond, answers(ans), sol + "\n\nЗдесь $z$, $v$ — элементарные высказывания.",
                "с. 102–110, гл. 7, § 6, 8", "кванторы, доказуемость", system="S^s_cq")


def m706(lvl, d, i):
    if d:
        return e706(lvl)
    if lvl == 1:
        return t_rec(1)
    if lvl == 2:
        return t_rec(2, "C") if i % 2 else mt_apply(2)
    if lvl == 3:
        return [t_base, mt_apply, t_rec][i % 3](3) if i % 3 != 2 else t_rec(3, "C")
    if lvl == 4:
        return derive(4, hide=True) if i % 2 == 0 else t_base(4)
    if lvl == 5:
        return derive(5)
    if lvl == 6:
        return prov706(6)
    return prov706(7, "S")


# ---------------------------------------------------------------- 07.07 главная интерпретация
def qf_small(depth=2, bound="a"):
    if depth == 0 or rnd.random() < 0.25:
        return EL("a", rnd.choice("bc"))
    k = rnd.choice(["neg", "conj", "wdis", "q", "q"])
    if k == "neg":
        return N(qf_small(depth - 1))
    if k == "q":
        return rnd.choice([ALL, EX])("a", qf_small(depth - 1))
    return (k, (qf_small(depth - 1), qf_small(depth - 1)))


def has_dup(f):
    k = f[0]
    if k in ("conj", "wdis"):
        if len(set(map(repr, f[1]))) < len(f[1]):
            return True
        return any(has_dup(g) for g in f[1])
    if k == "neg":
        return has_dup(f[1])
    if k in ("all", "ex"):
        return has_dup(f[2])
    return False


def any_degenerate(f):
    k = f[0]
    if k in ("all", "ex"):
        return Q.degenerate(f) or any_degenerate(f[2])
    if k == "neg":
        return any_degenerate(f[1])
    if k in ("conj", "wdis"):
        return any(any_degenerate(g) for g in f[1])
    return False


def interp_card(lvl, typ="D"):
    for _ in range(500):
        f = qf_small(2)
        if Q.groups(f) and not Q.free_occ("a", f) and not has_dup(f) and not any_degenerate(f):
            break
    n = rnd.choice([2, 3])
    g = Q.interp(f, {"a": n})
    cond = (f"{TT} Постройте интерпретационную форму высказывания ${T(f)}$ (D2 § 7 гл. 7, с. 105) при ${n}$ отмеченных терминах "
            f"для $a$: $1a, \\ldots, {n}a$ (термины $b$, $c$ здесь не связаны кванторами; отмечать их не нужно).")
    return card(7, 7, lvl, typ, "iso", cond, f"${Q.itex(g)}$", "D2, п. 3 (с. 105): $(\\forall a)z$ заменяется конъюнкцией "
                "$z(1a) \\cdot \\ldots \\cdot z(na)$, $(\\exists a)z$ — дизъюнкцией $z(1a) \\vee \\ldots \\vee z(na)$; вложенные кванторы — "
                "изнутри наружу.", "с. 105, гл. 7, § 7", "кванторы, интерпретация")


def mark_card(lvl, typ="D"):
    f = None
    while f is None or not Q.free_occ("a", f):
        f = qf_small(2)
    i = rnd.choice([1, 2, 3])
    g = mark(f, "a", f"{i}a")
    cond = f"{TT} Запишите высказывание $x({i}a)$ (§ 7 гл. 7, с. 105), если $x$ есть ${T(f)}$."
    return card(7, 7, lvl, typ, "iso", cond, f"${T(g)}$", f"По § 7 $x(ia)$ образуется из $x$ заменой $a$ на $ia$ везде, где $a$ "
                "входит свободно; связанные вхождения не меняются.", "с. 105, гл. 7, § 7", "кванторы, отмеченные термины")


def mark(f, a, ia):
    k = f[0]
    if k == "el":
        return EL(ia if f[1] == a else f[1], ia if f[2] == a else f[2])
    if k == "neg":
        return N(mark(f[1], a, ia))
    if k in ("all", "ex"):
        return f if f[1] == a else (k, f[1], mark(f[2], a, ia))
    return (k, tuple(mark(g, a, ia) for g in f[1]))


DIRECT = [("$(\\forall a)x$ приписали значение 1", "$x$ должно иметь значение 1", "1"),
          ("$x$ имеет значение 1", "значение $(\\forall a)x$ не зависит от $x$", "1"),
          ("$(\\forall a)x$ приписали значение 0", "значение $x$ не зависит от значения $(\\forall a)x$", "2"),
          ("$x$ имеет значение 0", "$(\\forall a)x$ имеет значение 0", "2"),
          ("при установлении значения формулы мы вынуждены приписать $x$ значение 1", "$(\\forall a)x$ должно получить значение 1", "3"),
          ("остаётся возможность приписать $x$ значение 0", "$(\\forall a)x$ приписывается значение 0", "3"),
          ("нужно значение $(\\exists a)x$", "оно равно значению $\\sim(\\forall a)\\sim x$", "4"),
          ("$a$ не входит свободно в $x$", "$x$ равнозначно $(\\forall a)x$ и $(\\exists a)x$", "5")]


def direct_card(lvl, typ="C"):
    its = rnd.sample(DIRECT, 4)
    cond = (f"{TT} Что следует по правилам прямой интерпретации кванторов (§ 7 гл. 7, с. 106)? Укажите номер правила.\n\n" +
            items([s for s, _, _ in its]))
    return card(7, 7, lvl, typ, "iso", cond, answers([f"{a} (п. {n})" for _, a, n in its]), "С. 106, пп. 1–5.",
                "с. 106, гл. 7, § 7", "кванторы, интерпретация")


def taut_n(lvl, typ="C"):
    k, i, p, q = rnd.choice(ALLC)
    n = rnd.choice([1, 2])
    ts = sorted(Q.bound_terms(p) | Q.bound_terms(q))
    nm = {t: n for t in ts}
    ip, iq = Q.interp(p, nm), Q.interp(q, nm)
    t = Q.is_taut(Q.IMP(ip, iq))
    cond = (f"{TT} Постройте интерпретационную форму формулы ${FT(p, q)}$ при {n} отмеченн{'ом термине' if n == 1 else 'ых терминах'} "
            "для каждого связанного термина и установите, тавтология ли она.")
    ans = f"${Q.itex(ip)} \\vdash {Q.itex(iq)}$; " + ("тавтология" if t else "не тавтология")
    sol = "D2 § 7 (с. 105). "
    if not t:
        e = Q.counter(Q.IMP(ip, iq))
        sol += "Контрпример: " + ", ".join(f"$({kk.replace('←', ' \\leftarrow ')}) = {vv}$" for kk, vv in sorted(e.items())) + "."
    else:
        sol += "Импликация посылки и заключения принимает значение 1 при всех наборах значений."
    return card(7, 7, lvl, typ, "iso", cond, ans, sol + " По D3 формула — тавтология, если такова каждая её интерпретационная форма "
                "при любом числе отмеченных терминов.", "с. 105, гл. 7, § 7", "кванторы, интерпретация")


def separate(lvl):
    cands = []
    for k, i, p, q in ALLC:
        ts = sorted(Q.bound_terms(p) | Q.bound_terms(q))
        t1 = Q.is_taut(Q.IMP(Q.interp(p, {t: 1 for t in ts}), Q.interp(q, {t: 1 for t in ts})))
        if t1 and not Q.qtaut(p, q):
            cands.append((p, q))
    p, q = rnd.choice(cands)
    ts = sorted(Q.bound_terms(p) | Q.bound_terms(q))
    ip, iq = Q.interp(p, {t: 2 for t in ts}), Q.interp(q, {t: 2 for t in ts})
    e = Q.counter(Q.IMP(ip, iq))
    cond = (f"{TT} Покажите, что при одном отмеченном термине интерпретационная форма формулы ${FT(p, q)}$ — тавтология, а "
            "формула всё же не тавтология (D3 § 7).")
    sol = ("При $n = 1$ кванторы просто снимаются, и получается формула $S^s$ вида $u \\vdash u$ или $uw \\vdash u$ и т. п. При "
           f"$n = 2$: ${Q.itex(ip)} \\vdash {Q.itex(iq)}$; контрпример: " +
           ", ".join(f"$({kk.replace('←', ' \\leftarrow ')}) = {vv}$" for kk, vv in sorted(e.items())) + ".")
    return card(7, 7, lvl, "S", "transfer", cond, "При $n = 2$ интерпретационная форма не тавтология (контрпример в решении); по D3 "
                "этого достаточно.", sol, "с. 105, гл. 7, § 7", "кванторы, интерпретация")


E707 = [("«При построении интерпретационной формы $(\\forall a)z$ заменяется дизъюнкцией $z(1a) \\vee \\ldots \\vee z(na)$»",
         "$(\\forall a)z$ заменяется конъюнкцией, $(\\exists a)z$ — дизъюнкцией (D2, п. 3, с. 105)"),
        ("«$x(2a)$ получается заменой $a$ на $2a$ во всех вхождениях $a$, включая связанные»", "замена делается только там, где "
         "$a$ входит свободно (с. 105)"),
        ("«Если $n = 0$, то $(\\forall a)z$ заменяется на 1, а $(\\exists a)z$ — на 0»", "по D2 при $n = 0$ $(\\forall a)z$ и "
         "$(\\exists a)z$ заменяются на $z$ (с. 105)"),
        ("«Формула — тавтология, если её интерпретационная форма — тавтология при двух отмеченных терминах»", "по D3 требуется "
         "тавтологичность при любом числе отмеченных терминов (с. 105)"),
        ("«По прямой интерпретации, если $x$ имеет значение 1, то и $(\\forall a)x$ имеет значение 1»", "по п. 1 (с. 106) при $x = 1$ "
         "значение $(\\forall a)x$ не зависит от $x$"),
        ("«Прямая и косвенная интерпретации дают для некоторых формул разные значения»", "по с. 106 они равноценны: значение, "
         "приписанное формуле одной интерпретацией, приписывается и другой")]


def e707(lvl):
    s, w = rnd.choice(E707)
    return card(7, 7, lvl, "E", "open", f"{TT} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 7.",
                "с. 105–106, гл. 7, § 7", "кванторы, интерпретация, диагностика")


def m707(lvl, d, i):
    if d:
        return e707(lvl)
    if lvl == 1:
        return card(7, 7, 1, "R", "iso", f"{TT} Как в § 7 гл. 7 (с. 105) называется выражение $3a$ и что обозначает $x(3a)$?",
                    "$3a$ — отмеченный термин (D1); $x(3a)$ — высказывание, полученное из $x$ заменой $a$ на $3a$ везде, где $a$ входит свободно.",
                    "С. 105, D1.", "с. 105, гл. 7, § 7", "кванторы, отмеченные термины")
    if lvl == 2:
        return mark_card(2) if i % 2 == 0 else direct_card(2)
    if lvl == 3:
        return interp_card(3) if i % 2 == 0 else (mark_card(3) if i % 4 == 1 else direct_card(3))
    if lvl in (4, 5):
        return taut_n(lvl)
    if lvl == 6:
        return taut_n(6, "C")
    return separate(7)


# ---------------------------------------------------------------- 07.08 полнота
def kq(k):
    return {"A": "\\forall", "E": "\\exists"}[k]


def basis_inst():
    kind = rnd.randint(1, 8)
    neg = lambda f: N(f) if rnd.random() < 0.35 else f
    Kq = lambda: rnd.choice([ALL, EX])
    z_, v_ = EL("a", "b"), EL("a", "c")
    if kind == 1:
        return kind, (neg(Kq()("a", neg(z_))), neg(z_))
    if kind == 2:
        return kind, (neg(z_), neg(Kq()("a", neg(z_))))
    if kind == 3:
        return kind, (neg(Kq()("a", neg(z_))), neg(Kq()("a", neg(z_))))
    if kind == 4:
        return kind, (neg(Kq()("a", C(z_, v_))), C(neg(Kq()("a", z_)), neg(Kq()("a", v_))))
    if kind == 5:
        return kind, (neg(Kq()("a", W(z_, v_))), W(neg(Kq()("a", z_)), neg(Kq()("a", v_))))
    if kind == 6:
        return kind, (C(neg(Kq()("a", z_)), neg(Kq()("a", v_))), neg(Kq()("a", C(z_, v_))))
    if kind == 7:
        return kind, (W(neg(Kq()("a", z_)), neg(Kq()("a", v_))), neg(Kq()("a", W(z_, v_))))
    zz2 = EL("a", "b")
    return kind, (neg(Kq()("a", neg(Kq()("b", zz2)))), neg(Kq()("b", neg(Kq()("a", zz2)))))


def basis_card(lvl, typ="C"):
    its = []
    while len(its) < 4:
        k, f = basis_inst()
        if all(k != kk for kk, _ in its):
            its.append((k, f))
    cond = (f"{TT} Укажите вид базисной формулы (D1 § 8 гл. 7, с. 107), к которому относится каждая формула.\n\n" +
            items([f"${FT(*f)}$" for _, f in its]))
    return card(7, 8, lvl, typ, "iso", cond, answers([f"вид {k}" for k, _ in its]),
                "D1 (с. 107): K, K¹, K², K³ — $\\forall$ или $\\exists$ в любых комбинациях; α, β, γ, δ — наличие или отсутствие отрицания.",
                "с. 107, гл. 7, § 8", "кванторы, полнота", system="S^s_cq")


def case_card(lvl, typ="C"):
    k = rnd.choice([3, 4, 5, 6, 7])
    lst = CASES[k]
    idx = sorted(rnd.sample(range(len(lst)), 4))
    cond = (f"{TT} Подслучаи случая {k} в доказательстве MT1 § 8 гл. 7 ($z$, $v$ — высказывания). Какие из формул — тавтологии "
            "и какими схемами § 6 они доказываются?\n\n" + items([f"${FT(*lst[i])}$" for i in idx]))
    ans = [PROOF[k][i] if i in PROOF[k] else "не тавтология" for i in idx]
    return card(7, 8, lvl, typ, "iso", cond, answers(ans), f"{CASEP[k]}; проверено также по интерпретационной форме (D2 § 7) при "
                "$z = (a \\leftarrow b)$, $v = (a \\leftarrow c)$.", f"{CASEP[k]}, гл. 7, § 8", "кванторы, полнота", system="S^s_cq")


def ccls(f):
    k = f[0]
    return {"el": 1, "all": 2, "ex": 3, "wdis": 4, "conj": 5, "neg": 6}[k]


def ik_card(lvl, sec=8, typ="C"):
    its = []
    pool = [EL("a", "b"), ALL("a", EL("a", "b")), EX("b", EL("a", "b")), W(EL("a", "b"), EL("a", "c")),
            C(EL("a", "b"), ALL("a", EL("a", "c"))), W(ALL("a", EL("a", "b")), EX("a", EL("a", "c"))), C(EX("a", EL("a", "b")), EL("c", "d")),
            ALL("a", W(EL("a", "b"), EL("a", "c"))), EX("a", C(EL("a", "b"), EL("a", "c")))]
    for _ in range(4):
        p, q = rnd.sample(pool, 2)
        its.append((p, q))
    cond = (f"{TT} К какому случаю $i \\vdash k$ доказательства MT7 § 8 гл. 7 (с. 114–115) относится каждая формула? "
            "(1 — элементарное высказывание, 2 — $(\\forall a)z$, 3 — $(\\exists a)z$, 4 — дизъюнкция, 5 — конъюнкция.)\n\n" +
            items([f"${FT(p, q)}$" for p, q in its]))
    return card(7, sec, lvl, typ, "iso", cond, answers([f"${ccls(p)} \\vdash {ccls(q)}$" for p, q in its]),
                "С. 114–115: определяется главный оператор посылки и заключения.", "с. 114–115, гл. 7, § 8", "кванторы, полнота",
                system="S^s_cq")


def mtn_card(lvl, typ="C"):
    """MT2–MT5 при n = 3: тавтология ли формула; проверено по интерпретационной форме."""
    zs = [EL("a", t) for t in "bcd"]
    kind = rnd.choice(["MT2", "MT3", "MT4", "MT5"])
    Kq = [rnd.choice("AE") for _ in range(4)]
    Q0 = K[Kq[0]]
    if kind == "MT2":
        p, q = Q0("a", C(*zs)), C(*[K[k]("a", s) for k, s in zip(Kq[1:], zs)])
    elif kind == "MT3":
        p, q = C(*[K[k]("a", s) for k, s in zip(Kq[1:], zs)]), Q0("a", C(*zs))
    elif kind == "MT4":
        p, q = Q0("a", W(*zs)), W(*[K[k]("a", s) for k, s in zip(Kq[1:], zs)])
    else:
        p, q = W(*[K[k]("a", s) for k, s in zip(Kq[1:], zs)]), Q0("a", W(*zs))
    t = Q.qtaut(p, q, nmax=2)
    cond = (f"{TT} Формула ${FT(p, q)}$ имеет вид, рассматриваемый в {kind} § 8 гл. 7 (с. 110–113). Тавтология ли она и, если да, "
            "доказуема ли в $S^s_{cq}$?")
    ans = "Тавтология; доказуема по " + kind if t else "Не тавтология; недоказуема"
    sol = {"MT2": "С. 110–111: при K $= \\forall$ тавтологиями будут формулы при любых K$^i$; при K $= \\exists$ — только если все K$^i$ суть $\\exists$.",
           "MT3": "С. 111–112: если K есть $\\forall$, все K$^i$ должны быть $\\forall$; если K есть $\\exists$ — формула тавтологична, если среди K$^i$ не более одного $\\exists$.",
           "MT4": "С. 112: если K есть $\\forall$, тавтология лишь при условии, что ни один из K$^i$ не есть $\\forall$ или только один есть $\\forall$; если K есть $\\exists$, все K$^i$ должны быть $\\exists$.",
           "MT5": "С. 113: если K есть $\\forall$, все K$^i$ должны быть $\\forall$; если K есть $\\exists$ — тавтология при любом наборе K$^i$."}[kind]
    sol += (" Проверка по интерпретационной форме при двух отмеченных терминах" + (" не находит контрпримера." if t else
            " даёт контрпример.") + ("" if t else " По процедуре § 9 (с. 120): контрольная форма совпадает с формулой (п. 1 D1 § 9) и не тавтология — формула недоказуема."))
    if kind == "MT3":
        sol = sol.replace("формула тавтологична, если среди K$^i$ не более одного $\\exists$", "тавтологичность проверяется так же, как "
                          "в доказательстве (с. 112: «доказательство аналогично»)")
    if kind == "MT2" and Kq[0] == "E":
        pass
    return card(7, 8, lvl, typ, "open", cond, ans, sol, "с. 110–113, гл. 7, § 8", "кванторы, полнота", system="S^s_cq")


def mt6_card(lvl, typ="D"):
    qs = [("\\forall", "a"), ("\\forall", "b"), ("\\forall", "c")]
    qs = [(rnd.choice(["\\forall", "\\exists"]), t) for _, t in qs]
    perm = [1, 0, 2] if rnd.random() < 0.5 else [0, 2, 1]
    pre = "".join(f"({q} {t})" for q, t in qs)
    post = "".join(f"({qs[j][0]} {qs[j][1]})" for j in perm)
    case = "1" if perm == [1, 0, 2] else "2"
    cond = (f"{TT} Пусть формула ${pre}z \\vdash {post}z$ — тавтология (с ограничением). Какой случай доказательства MT6 § 8 "
            "гл. 7 (с. 114) к ней относится и как она доказывается?")
    return card(7, 8, lvl, typ, "iso", cond, f"Случай {case}: заключение отличается от посылки только порядком двух "
                f"{'первых' if case == '1' else 'последних'} кванторов; формула — базисная тавтология и по MT1 доказуема.",
                "С. 114.", "с. 114, гл. 7, § 8", "кванторы, полнота", system="S^s_cq")


def e708(lvl):
    k, i, p, q = rnd.choice(ALLC)
    t = i in PROOF[k]
    claim = ("не тавтология" if t else "тавтология")
    cond = (f"{TT} Студент: «Формула ${FT(p, q)}$ — {claim}, это видно по аналогии с соседними подслучаями случая {k} MT1 § 8». "
            "Найдите ошибку.")
    ans = (f"Неверно: формула — тавтология и доказуема в $S^s_{{cq}}$ ({PROOF[k][i]}; {CASEP[k]})." if t else
           f"Неверно: формула не тавтология ({CASEP[k]}: она не входит в число тавтологий случая {k}).")
    ts = sorted(Q.bound_terms(p) | Q.bound_terms(q))
    sol = "Аналогия не доказательство: каждый подслучай проверяется отдельно."
    if not t:
        ip, iq = Q.interp(p, {tt: 2 for tt in ts}), Q.interp(q, {tt: 2 for tt in ts})
        if not Q.is_taut(Q.IMP(ip, iq)):
            e = Q.counter(Q.IMP(ip, iq))
            sol += (f" Интерпретационная форма при двух отмеченных терминах: ${Q.itex(ip)} \\vdash {Q.itex(iq)}$; контрпример: " +
                    ", ".join(f"$({kk.replace('←', ' \\leftarrow ')}) = {vv}$" for kk, vv in sorted(e.items())) + ".")
    return card(7, 8, lvl, "E", "open", cond, ans, sol, f"{CASEP[k]}, гл. 7, § 8", "кванторы, полнота, диагностика", system="S^s_cq")


E708X = [("«В случае 4 $\\vdash$ 1 формула всегда доказуема»", "в доказательстве MT7 § 8 (с. 116) случаи $4 \\vdash 1$, $4 \\vdash 5$, $5 \\vdash 1$, "
          "$5 \\vdash 4$ исключаются; а в § 9 (с. 119) $4 \\vdash 1$ — тавтология лишь при условии, что каждая $z^i \\vdash y$ — тавтология"),
         ("«MT7 утверждает доказуемость любой тавтологии теории кванторов»", "MT7 требует, чтобы бескванторные формы посылки и "
          "заключения были тождественны или отличались лишь заменой $\\sim\\sim z$ на $z$ (с. 114)"),
         ("«Шестой случай (отрицание) рассматривается отдельно, как и остальные пять»", "по с. 115 он в силу $S^s$ и схем A6, A7, "
          "T1, T2, T7, T28, T37 § 6 сводится к остальным"),
         ("«В MT4 при K $= \\forall$ формула тавтологична, только если все K$^i$ суть $\\forall$»", "по с. 112 — лишь при условии, что ни "
          "один K$^i$ не есть $\\forall$ или только один из них есть $\\forall$"),
         ("«Базисная формула вида 3 — это $\\alpha(Ka)\\beta z \\vdash \\gamma z$»", "это вид 1; вид 3 — $\\alpha(K^1a)\\beta z \\vdash \\gamma(K^2a)\\delta z$ (с. 107)")]


def e708x(lvl):
    s, w = rnd.choice(E708X)
    return card(7, 8, lvl, "E", "open", f"{TT} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 8.",
                "с. 107–116, гл. 7, § 8", "кванторы, полнота, диагностика", system="S^s_cq")


def m708(lvl, d, i):
    if d:
        return e708(lvl) if i % 6 else e708x(lvl)
    if lvl == 2:
        return basis_card(2)
    if lvl == 3:
        return basis_card(3) if i % 2 else ik_card(3)
    if lvl == 4:
        return case_card(4) if i % 2 == 0 else mt6_card(4)
    if lvl in (5, 6):
        return mtn_card(lvl) if i % 2 == 0 else prov706(lvl).replace("chapter: 7\nsection: 6", "chapter: 7\nsection: 8")
    return mtn_card(7, "S")


# ---------------------------------------------------------------- 07.09 разрешимость
def rand_qf(depth=2):
    if depth == 0 or rnd.random() < 0.3:
        return EL(rnd.choice("ab"), rnd.choice("cd"))
    k = rnd.choice(["neg", "conj", "wdis", "q", "q"])
    if k == "neg":
        return N(rand_qf(depth - 1))
    if k == "q":
        return rnd.choice([ALL, EX])(rnd.choice("ab"), rand_qf(depth - 1))
    a1, a2 = rand_qf(depth - 1), rand_qf(depth - 1)
    while a1 == a2:
        a2 = rand_qf(depth - 1)
    return (k, (a1, a2))


def step1_card(lvl, typ="C"):
    its = []
    for want in rnd.sample([True, False, False, True], 4):
        for _ in range(400):
            p, q = rand_qf(2), rand_qf(2)
            if (Q.groups(p) or Q.groups(q)) and Q.strong(Q.qfree(p), Q.qfree(q)) == want:
                its.append((p, q))
                break
    cond = (f"{TT} Выполните первый шаг процедуры § 9 гл. 7 (с. 120) для каждой формулы: образуйте бескванторную форму и "
            "установите, доказуема ли она в $S^s$. Что отсюда следует?\n\n" + items([f"${FT(p, q)}$" for p, q in its]))
    ans = [("доказуема в $S^s$ — нужен второй шаг" if Q.strong(Q.qfree(p), Q.qfree(q)) else "недоказуема в $S^s$ — формула недоказуема в $S^s_{cq}$")
           for p, q in its]
    sol = "\n".join(f"{L[i]}) ${FT(Q.qfree(p), Q.qfree(q))}$." for i, (p, q) in enumerate(its))
    return card(7, 9, lvl, typ, "iso", cond, answers(ans), sol + "\n\nС. 120, шаг 1; критерий доказуемости в $S^s$ — гл. 5, § 2.",
                "с. 120, гл. 7, § 9", "кванторы, разрешимость", system="S^s_cq")


def ctrl1_card(lvl, typ="C"):
    its = []
    for _ in range(4):
        p, q = rand_qf(2), rand_qf(2)
        its.append((p, q))
    def stat(p, q):
        yt = Q.is_taut(Q.qfree(q))
        xc = Q.is_taut(N(Q.qfree(p)))
        return yt, xc
    cond = (f"{TT} Применяется ли к формуле пункт 1 определения контрольной формы (D1 § 9 гл. 7, с. 116): формула оставляется без "
            "изменения, если бескванторные формы $\\vdash y$ и $\\vdash \\sim x$ недоказуемы в $S^5$?\n\n" + items([f"${FT(p, q)}$" for p, q in its]))
    ans, sol = [], []
    for p, q in its:
        yt, xc = stat(p, q)
        ans.append("да" if not (yt or xc) else "нет")
        sol.append(f"$y^* = {T(Q.qfree(q))}$ — " + ("тавтология" if yt else "не тавтология") + f"; $x^* = {T(Q.qfree(p))}$ — " +
                   ("противоречие" if xc else "не противоречие"))
    return card(7, 9, lvl, typ, "iso", cond, answers(ans), "\n".join(f"{L[i]}) {s}." for i, s in enumerate(sol)) +
                "\n\nПо MT4 § 3 гл. 4 $\\vdash x$ доказуема в $S^5$ тогда и только тогда, когда $x$ — тавтология.",
                "с. 116, гл. 7, § 9", "кванторы, контрольная форма", system="S^s_cq")


def decide_card(lvl, typ="C"):
    """Полная процедура для формул, к которым применим п. 1 D1 (контрольная форма совпадает с формулой)."""
    its = []
    pool = list(ALLC)
    rnd.shuffle(pool)
    for k, i, p, q in pool:
        if Q.is_taut(Q.qfree(q)) or Q.is_taut(N(Q.qfree(p))):
            continue
        its.append((k, i, p, q))
        if len(its) == 3:
            break
    rows = []
    for k, i, p, q in its:
        s1 = Q.strong(Q.qfree(p), Q.qfree(q))
        t = i in PROOF[k]
        rows.append((s1, t))
    cond = (f"{TT} Установите по процедуре § 9 гл. 7 (с. 120), доказуемы ли формулы в $S^s_{{cq}}$ ($z$, $v$ — элементарные).\n\n" +
            items([f"${FT(p, q)}$" for _, _, p, q in its]))
    ans = answers(["да" if s1 and t else "нет" for s1, t in rows])
    sol = "\n".join(f"{L[j]}) шаг 1: ${FT(Q.qfree(p), Q.qfree(q))}$ " + ("доказуема в $S^s$" if s1 else "недоказуема в $S^s$ — стоп") +
                    ("" if not s1 else "; шаг 2: по п. 1 D1 контрольная форма совпадает с формулой; она " +
                     ("тавтология" if t else "не тавтология") + f" ({CASEP[k]})") + "."
                    for j, ((k, i, p, q), (s1, t)) in enumerate(zip(its, rows)))
    return card(7, 9, lvl, typ, "open", cond, ans, sol, "с. 109–110, 116, 120, гл. 7, § 8–9", "кванторы, разрешимость", system="S^s_cq")


E709 = [("«Если бескванторная форма формулы доказуема в $S^s$, то формула доказуема в $S^s_{cq}$»", "это лишь первый шаг процедуры "
         "(с. 120); нужно ещё построить контрольную форму и проверить, тавтология ли она (например, $(\\exists a)z \\vdash (\\forall a)z$ "
         "при $z = (a \\leftarrow b)$ имеет бескванторную форму $z \\vdash z$, но не тавтология)"),
        ("«По MT1 § 9: если формула — тавтология, то её контрольная форма — тавтология»", "MT1 утверждает обратное: если контрольная "
         "форма — тавтология, то и формула — тавтология, но не всегда наоборот (с. 117)"),
        ("«Контрольная форма строится всегда заменой бескванторных частей на ДНФ»", "по п. 1 D1 (с. 116), если бескванторные формы "
         "$\\vdash y$ и $\\vdash \\sim x$ недоказуемы в $S^5$, формула оставляется без изменения"),
        ("«Чтобы установить недоказуемость, достаточно, чтобы контрольная форма была недоказуема в $S^s$»", "по процедуре (с. 120) "
         "решает, является ли контрольная форма тавтологией; доказуемость в $S^s$ проверяется для бескванторной формы"),
        ("«MT4 § 9: если доказуема формула, то доказуема и её контрольная форма»", "это MT3; MT4 — если доказуема контрольная форма, "
         "то доказуема и сама формула (с. 117)"),
        ("«В MT5 § 9 случай, когда $x^* \\vdash y^*$ доказуема, а $y^* \\vdash x^*$ — нет, рассматривается отдельно от первого»",
         "по с. 118 второй случай сводится к первому через $x \\vdash yx$")]


def e709(lvl):
    s, w = rnd.choice(E709)
    return card(7, 9, lvl, "E", "open", f"{TT} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 9 (с. 116–120).",
                "с. 116–120, гл. 7, § 9", "кванторы, разрешимость, диагностика", system="S^s_cq")


def m709(lvl, d, i):
    if d:
        return e709(lvl) if i % 2 else e708(lvl).replace("chapter: 7\nsection: 8", "chapter: 7\nsection: 9")
    if lvl == 2:
        return ctrl1_card(2)
    if lvl == 3:
        return step1_card(3) if i % 2 == 0 else ctrl1_card(3)
    if lvl == 4:
        return [step1_card, ik_card, ctrl1_card][i % 3](4) if i % 3 != 1 else ik_card(4, 9)
    if lvl in (5, 6):
        return decide_card(lvl)
    return decide_card(7, "S")


# ---------------------------------------------------------------- 07.10–07.11
def closure(f):
    for t in sorted(free_terms(f)):
        f = ALL(t, f)
    return f


def taut1(f, nmax=2):
    g = closure(f)
    ts = sorted(Q.bound_terms(g))
    for combo in itertools.product(range(1, nmax + 1), repeat=len(ts)):
        if not Q.is_taut(Q.interp(g, dict(zip(ts, combo)))):
            return False
    return True


POOL1 = [Q.IMP(ALL("a", EL("a", "b")), EL("c", "b")), Q.IMP(EL("c", "b"), EX("a", EL("a", "b"))),
         Q.IMP(ALL("a", EL("a", "b")), EX("a", EL("a", "b"))), Q.IMP(ALL("a", EL("a", "b")), EL("a", "b")),
         Q.IMP(EL("a", "b"), EX("a", EL("a", "b"))), Q.IMP(EX("a", EL("a", "b")), ALL("a", EL("a", "b"))),
         W(ALL("a", EL("a", "b")), EX("a", N(EL("a", "b")))), W(EX("a", EL("a", "b")), ALL("a", N(EL("a", "b")))),
         W(ALL("a", EL("a", "b")), ALL("a", N(EL("a", "b"))))]


def s5cq_card(lvl, typ="C"):
    its = rnd.sample(POOL1, 3)
    cond = (f"{TT} Постройте интерпретационную форму (D1 § 10 гл. 7) и установите, тавтологии ли формулы $S^5_{{cq}}$ (D2, с. 121).\n\n" +
            items([f"${FT(f)}$" for f in its]))
    ans = [f"$\\vdash {T(closure(f))}$; " + ("тавтология" if taut1(f, 3) else "не тавтология") for f in its]
    return card(7, 10, lvl, typ, "iso", cond, answers(ans), "D1 (с. 120): если термин входит свободно в $x$, $\\vdash x$ заменяется на "
                "$\\vdash (\\forall a)x$; далее пп. 2, 3 D2 § 7. По MT1 (с. 121) доказуемые формулы — тавтологии; MT2 (с. 121) приводит "
                "две недоказуемые формулы.", "с. 120–121, гл. 7, § 10", "кванторы, S5cq", system="S^5_cq")


def m710(lvl, d, i):
    if d:
        s, w = rnd.choice([("«$\\vdash (\\forall a)(a \\leftarrow b) \\supset (c \\leftarrow b)$ доказуема в $S^5_{cq}$ — из общего следует частное»",
                            "по MT2 § 10 (с. 121) формула недоказуема: она не тавтология — $c$ не связан с $a$"),
                           ("«В $S^5_{cq}$ правило R1: если $x \\vdash y$, то $\\vdash (\\forall a)x$»", "R1 § 10: если $\\vdash x$, то $\\vdash (\\forall a)x$ (с. 120)"),
                           ("«Другие системы для классического случая получаются из $S^s_{cq}$ отбрасыванием аксиом»", "они получаются присоединением к "
                            "$S^w$, $S^m$, $S^c$, $S^5$, $S^6$ таких же дополнений, какие сделаны к $S^s$ (с. 120)")])
        return card(7, 10, lvl, "E", "open", f"{TT} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 10.",
                    "с. 120–121, гл. 7, § 10", "кванторы, S5cq, диагностика", system="S^5_cq")
    if lvl == 1:
        return card(7, 10, 1, "R", "iso", f"{TT} Какое правило вывода дополнительно принимается в $S^5_{{cq}}$ (§ 10 гл. 7)?",
                    "R1. Если $\\vdash x$, то $\\vdash (\\forall a)x$.", "С. 120.", "с. 120, гл. 7, § 10", "кванторы, S5cq", system="S^5_cq")
    if lvl == 2:
        f = rnd.choice(POOL1)
        return card(7, 10, 2, "D", "iso", f"{TT} Запишите интерпретационную форму формулы ${FT(f)}$ по п. 1 D1 § 10 гл. 7 (только "
                    "присоединение кванторов).", f"$\\vdash {T(closure(f))}$", "D1 (с. 120): для каждого термина, имеющего свободные "
                    "вхождения в $x$, $\\vdash x$ заменяется на $\\vdash (\\forall a)x$.", "с. 120, гл. 7, § 10", "кванторы, S5cq", system="S^5_cq")
    return s5cq_card(lvl, "S" if lvl == 7 else "C")


def a5star(lvl, typ="C"):
    its = []
    for _ in range(4):
        X = rnd.choice([EL("a", "b"), EL("c", "b"), W(EL("a", "b"), N(EL("a", "b"))), C(EL("a", "b"), N(EL("a", "b"))),
                        W(EL("c", "b"), N(EL("c", "b"))), ALL("a", EL("a", "b"))])
        its.append(X)
    ok = lambda X: (not Q.free_occ("a", X)) or Q.is_taut(Q.qfree(X)) and Q.is_taut(X if X[0] != "all" else X[2])
    def why(X):
        if not Q.free_occ("a", X):
            return "да: $a$ не входит свободно в $x$"
        if Q.is_taut(X):
            return "да: $\\vdash x$ доказуема в $S^5$ ($x$ — тавтология)"
        return "нет: $a$ входит свободно и $x$ не тавтология"
    cond = (f"{TT} Является ли формула $(\\exists a)x \\vdash (\\forall a)x$ примером схемы A*5 системы $S^{{s*}}_{{cq}}$ (§ 11 гл. 7, с. 121), "
            "если $x$ есть:\n\n" + items([f"${T(X)}$" for X in its]))
    return card(7, 11, lvl, typ, "iso", cond, answers([why(X).split(":")[0] for X in its]), "\n".join(f"{L[i]}) {why(X)}." for i, X in enumerate(its)) +
                "\n\nA*5: $a$ не входит свободно в $x$ или $\\vdash x$ доказуема в $S^5$ (с. 121).", "с. 121, гл. 7, § 11", "кванторы, расширение",
                system="S^s*_cq")


def m711(lvl, d, i):
    if d:
        s, w = rnd.choice([("«$x \\vdash (\\forall a)(x \\vee \\sim x)$ доказуема в $S^s_{cq}$, раз она — пример T5 § 11»",
                            "T5 имеет силу в $S^{s*}_{cq}$; в $S^s_{cq}$ формулы типа T5 и T6 недоказуемы (с. 121)"),
                           ("«T3 § 11 $(\\exists a)\\sim x \\vdash \\sim x$ верна для любого $x$»", "T1–T4 § 11 имеют силу для $x$, при которых "
                            "доказуема $\\vdash x$; в T3, T4 $\\sim x$ — противоречие (с. 121)"),
                           ("«A8 § 11 нужна при $n = 0$»", "A8 принимается при $n \\geq 1$ (с. 122)")])
        return card(7, 11, lvl, "E", "open", f"{TT} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 11.", "с. 121–122, гл. 7, § 11",
                    "кванторы, расширение, диагностика", system="S^s*_cq")
    if lvl == 1:
        return card(7, 11, 1, "R", "iso", f"{TT} Какой схемой заменяется A5 при расширении $S^s_{{cq}}$ до $S^{{s*}}_{{cq}}$ (§ 11 гл. 7)?",
                    "A*5. $(\\exists a)x \\vdash (\\forall a)x$, где $a$ не входит свободно в $x$ или $\\vdash x$ доказуема в $S^5$.", "С. 121.",
                    "с. 121, гл. 7, § 11", "кванторы, расширение", system="S^s*_cq")
    if lvl == 2:
        its = rnd.sample([("x \\vdash (\\forall a)x", "T1"), ("(\\exists a)x \\vdash x", "T2"), ("(\\exists a)\\sim x \\vdash \\sim x", "T3"),
                          ("\\sim x \\vdash (\\forall a)\\sim x", "T4"), ("x \\vdash (\\forall a)(x \\vee \\sim x)", "T5"), ("(\\exists a)(\\sim xx) \\vdash x", "T6")], 3)
        return card(7, 11, 2, "C", "iso", f"{TT} Укажите номера теоремных схем $S^{{s*}}_{{cq}}$ (с. 121):\n\n" + items([f"${s}$" for s, _ in its]),
                    answers([n for _, n in its]), "С. 121; в T1–T4 $\\vdash x$ доказуема.", "с. 121, гл. 7, § 11", "кванторы, расширение",
                    system="S^s*_cq")
    if lvl in (3, 4, 5):
        return a5star(lvl) if i % 2 == 0 or lvl == 3 else card(7, 11, lvl, "D", "iso",
            f"{TT} Как в $S^{{s*}}_{{cq}}$ получается T1 $x \\vdash (\\forall a)x$ при $x = (a \\leftarrow b) \\vee \\sim(a \\leftarrow b)$ "
            "(здесь $a$ входит свободно)?", "$x \\vdash (\\exists a)x$ [A2]; $(\\exists a)x \\vdash (\\forall a)x$ [A*5: $\\vdash x$ доказуема в $S^5$]; транзитивность.",
            "С. 121: T1–T4 имеют силу, если $\\vdash x$ доказуема.", "с. 121, гл. 7, § 11", "кванторы, расширение", answ="proof", system="S^s*_cq")
    pairs = [("(\\exists a)(\\sim(a \\leftarrow b)(a \\leftarrow b)) \\vdash (a \\leftarrow b)", "T6"),
             ("(a \\leftarrow b) \\vdash (\\forall a)((a \\leftarrow b) \\vee \\sim(a \\leftarrow b))", "T5"),
             ("(\\exists a)(\\sim(a \\leftarrow c)(a \\leftarrow c)) \\vdash (a \\leftarrow c)", "T6"),
             ("(a \\leftarrow c) \\vdash (\\forall a)((a \\leftarrow c) \\vee \\sim(a \\leftarrow c))", "T5"),
             ("(\\exists a)(\\sim(a \\leftarrow d)(a \\leftarrow d)) \\vdash (a \\leftarrow d)", "T6"),
             ("(a \\leftarrow d) \\vdash (\\forall a)((a \\leftarrow d) \\vee \\sim(a \\leftarrow d))", "T5")]
    k = 2 if lvl == 7 else 1
    its = rnd.sample(pairs, k)
    return card(7, 11, lvl, "S" if lvl == 7 else "C", "transfer",
                f"{TT} Сравните $S^s_{{cq}}$ и $S^{{s*}}_{{cq}}$: доказуемы ли в них формулы?\n\n" + items([f"${f}$" for f, _ in its]),
                answers([f"в $S^{{s*}}_{{cq}}$ — да (тип {n} § 11), в $S^s_{{cq}}$ — нет" for _, n in its]),
                "С. 121: «Формулы типа T5 и T6 недоказуемы в $S^s_{cq}$».", "с. 121, гл. 7, § 11", "кванторы, расширение", system="S^s*_cq")


# ---------------------------------------------------------------- 07.12–07.18 неклассический случай
xX = V("x")
NQ = {"A16": (ALL("a", xX), ("nex", "a", N(xX))), "A26": (("nall", "a", xX), EX("a", N(xX))),
      "A36": (("qall", "a", xX), ("qex", "a", N(xX))), "A17": (("nex", "a", N(xX)), ALL("a", xX)),
      "A27": (EX("a", N(xX)), ("nall", "a", xX)), "A37": (("qex", "a", N(xX)), ("qall", "a", xX)),
      "A18": (ALL("a", xX), C(N(("nall", "a", xX)), N(("qall", "a", xX)))),
      "A28": (("nall", "a", xX), C(N(ALL("a", xX)), N(("qall", "a", xX)))),
      "A38": (("qall", "a", xX), C(N(ALL("a", xX)), N(("nall", "a", xX)))),
      "A19": (C(N(("nall", "a", xX)), N(("qall", "a", xX))), ALL("a", xX)),
      "A29": (C(N(ALL("a", xX)), N(("qall", "a", xX))), ("nall", "a", xX)),
      "A39": (C(N(ALL("a", xX)), N(("nall", "a", xX))), ("qall", "a", xX)),
      "A10": (("nall", "a", C(xX, y)), W(("nall", "a", xX), ("nall", "a", y))),
      "A11": (W(("nall", "a", xX), ("nall", "a", y)), ("nall", "a", C(xX, y))),
      "A12": (W(("nex", "a", xX), ("nex", "a", y)), ("nex", "a", C(xX, y)))}
NQNAME = {k: (f"A^{k[1]}{k[2]}" if len(k) == 3 and k[1] in "123" and k[2] in "6789" else k) for k in NQ}


def qf13(f):
    """Бескванторная форма D1 § 13."""
    k = f[0]
    if k == "qall":
        return qf13(C(N(ALL(f[1], f[2])), N(("nall", f[1], f[2]))))
    if k == "qex":
        return qf13(C(N(EX(f[1], f[2])), N(("nex", f[1], f[2]))))
    if k == "nall":
        return qf13(N(ALL(f[1], f[2])))
    if k == "nex":
        return qf13(N(EX(f[1], f[2])))
    if k in ("all", "ex"):
        return qf13(f[2])
    if k == "neg":
        return N(qf13(f[1]))
    if k in ("v", "el"):
        return f
    return (k, tuple(qf13(g) for g in f[1]))


BOOK13 = {"A16": "x \\vdash \\sim\\sim x", "A26": "\\sim x \\vdash \\sim x", "A36": "\\sim x\\sim\\sim x \\vdash \\sim\\sim x\\sim\\sim\\sim x",
          "A17": "\\sim\\sim x \\vdash x", "A27": "\\sim x \\vdash \\sim x", "A37": "\\sim\\sim x\\sim\\sim\\sim x \\vdash \\sim x\\sim\\sim x",
          "A18": "x \\vdash \\sim\\sim x\\sim(\\sim x\\sim\\sim x)", "A28": "\\sim x \\vdash \\sim x\\sim(\\sim x\\sim\\sim x)",
          "A38": "\\sim x\\sim\\sim x \\vdash \\sim x\\sim\\sim x", "A19": "\\sim\\sim x\\sim(\\sim x\\sim\\sim x) \\vdash x",
          "A29": "\\sim x\\sim(\\sim x\\sim\\sim x) \\vdash \\sim x", "A39": "\\sim x\\sim\\sim x \\vdash \\sim x\\sim\\sim x",
          "A10": "\\sim(xy) \\vdash \\sim x \\vee \\sim y", "A11": "\\sim x \\vee \\sim y \\vdash \\sim(xy)", "A12": "\\sim x \\vee \\sim y \\vdash \\sim(xy)"}
for kk, (p, q) in NQ.items():
    got = FT(qf13(p), qf13(q)).replace(" ", "")
    assert got == BOOK13[kk].replace(" ", ""), (kk, got)
    assert Q.strong(qf13(p), qf13(q)), kk


def nqtex(k):
    return NQNAME[k]


def nq_rec(lvl, typ="R", sec=12):
    ks = rnd.sample(sorted(NQ), 4)
    cond = (f"{TQ} Каким аксиомным схемам $S^s_{{nq}}$ (§ 12 гл. 7, с. 123) соответствуют формулы?\n\n" +
            items([f"${FT(*NQ[k])}$" for k in ks]))
    return card(7, sec, lvl, typ, "iso", cond, answers([f"${nqtex(k)}$" for k in ks]), "С. 123.", "с. 123, гл. 7, § 12", "кванторы, неклассический случай",
                system="S^s_nq")


def nq_wf(lvl, typ="C"):
    its = [("(\\urcorner\\forall a)(a \\leftarrow b)", "высказывание"), ("(?\\exists a)\\sim(a \\leftarrow b)", "высказывание"),
           ("(\\urcorner\\exists a)", "кванторная группа, не высказывание"), ("(?\\forall x)(a \\leftarrow b)", "не высказывание: $x$ — не термин"),
           ("(\\urcorner\\forall a)(?\\exists b)(a \\leftarrow b)", "высказывание"), ("\\urcorner(\\forall a)(a \\leftarrow b)",
            "не высказывание: $\\urcorner$ входит в кванторную группу $(\\urcorner\\forall a)$, а не ставится перед ней")]
    pick = rnd.sample(its, 4)
    return card(7, 12, lvl, typ, "iso", f"{TQ} Что представляет собой каждое выражение по § 12 гл. 7 (с. 122)?\n\n" +
                items([f"${e}$" for e, _ in pick]), answers([d for _, d in pick]),
                "Дополнения к определениям высказывания и кванторной группы (с. 122).", "с. 122, гл. 7, § 12", "кванторы, неклассический случай")


def nq_sub(lvl):
    k = rnd.choice(sorted(NQ))
    X = rnd.choice([EL("a", "b"), N(EL("a", "c")), C(EL("a", "b"), EL("a", "c"))])
    Y = EL("a", "d")
    def s(f):
        if f == xX:
            return X
        if f == y:
            return Y
        if f[0] in ("v", "el"):
            return f
        if f[0] == "neg":
            return N(s(f[1]))
        if f[0] in QK:
            return (f[0], f[1], s(f[2]))
        return (f[0], tuple(s(g) for g in f[1]))
    p, q = NQ[k]
    return card(7, 12, lvl, "D", "iso", f"{TQ} Подставьте в схему ${nqtex(k)}$ (${FT(p, q)}$) вместо $x$ — ${T(X)}$" +
                (f", вместо $y$ — ${T(Y)}$" if k in ("A10", "A11", "A12") else "") + ".", f"${FT(s(p), s(q))}$",
                "С. 123.", "с. 123, гл. 7, § 12", "кванторы, неклассический случай", system="S^s_nq")


def m712(lvl, d, i):
    if d:
        s, w = rnd.choice([("«В $S^s_{nq}$ сохраняются аксиомные схемы A6 и A7 системы $S^s_{cq}$»", "вместо A6 и A7 принимаются $A^16$–$A^36$ и $A^17$–$A^37$ (с. 123)"),
                           ("«$(\\urcorner\\forall a)x \\vdash \\sim(\\forall a)x$ — это $A^28$»", "$A^28$ — $(\\urcorner\\forall a)x \\vdash \\sim(\\forall a)x\\sim(?\\forall a)x$ (с. 123)"),
                           ("«A12 — $(\\urcorner\\exists a)(xy) \\vdash (\\urcorner\\exists a)x \\vee (\\urcorner\\exists a)y$»", "A12 идёт в обратную сторону: "
                            "$(\\urcorner\\exists a)x \\vee (\\urcorner\\exists a)y \\vdash (\\urcorner\\exists a)(xy)$ (с. 123)")])
        return card(7, 12, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 12.", "с. 122–123, гл. 7, § 12",
                    "кванторы, неклассический случай, диагностика", system="S^s_nq")
    if lvl == 2:
        return nq_wf(2, "R")
    if lvl == 3:
        return nq_rec(3, "C") if i % 2 == 0 else nq_wf(3)
    if lvl in (4, 5):
        return nq_sub(lvl) if i % 2 == 0 else nq_rec(lvl, "C")
    return nq_sub(lvl).replace("type: D", "type: S" if lvl == 7 else "type: C")


def qf13_card(lvl, typ="D"):
    k = rnd.choice(sorted(NQ))
    p, q = NQ[k]
    return card(7, 13, lvl, typ, "iso", f"{TQ} Запишите бескванторную форму (D1 § 13 гл. 7, с. 123) схемы ${nqtex(k)}$: ${FT(p, q)}$.",
                f"${FT(qf13(p), qf13(q))}$", "D1 § 13: (1) $(?\\forall b)z$, $(?\\exists b)z$ → $\\sim(\\forall b)z\\sim(\\urcorner\\forall b)z$, "
                "$\\sim(\\exists b)z\\sim(\\urcorner\\exists b)z$; (2) $(\\urcorner\\forall b)z$, $(\\urcorner\\exists b)z$ → $\\sim(\\forall b)z$, "
                "$\\sim(\\exists b)z$; (3) кванторные группы исключаются. Ср. таблицу с. 124.", "с. 123–124, гл. 7, § 13", "кванторы, непротиворечивость",
                system="S^s_nq")


def rnd_nq(depth=2):
    if depth == 0 or rnd.random() < 0.25:
        return EL("a", rnd.choice("bc"))
    k = rnd.choice(["neg", "conj", "q", "q", "q"])
    if k == "neg":
        return N(rnd_nq(depth - 1))
    if k == "q":
        inner = rnd.choice([EL("a", rnd.choice("bc")), N(EL("a", rnd.choice("bc")))])
        return (rnd.choice(list(QK)), "a", inner)
    a1, a2 = rnd_nq(depth - 1), rnd_nq(depth - 1)
    while a1 == a2:
        a2 = rnd_nq(depth - 1)
    return ("conj", (a1, a2))


def qf13_rand(lvl, typ="C"):
    p, q = rnd_nq(2), rnd_nq(2)
    while not any(c in repr((p, q)) for c in ("nall", "qall", "nex", "qex")):
        p, q = rnd_nq(2), rnd_nq(2)
    s = Q.strong(qf13(p), qf13(q))
    return card(7, 13, lvl, typ, "open", f"{TQ} Образуйте бескванторную форму формулы ${FT(p, q)}$ (D1 § 13 гл. 7). Доказуема ли она в $S^s$? "
                "Что отсюда можно заключить о доказуемости формулы в $S^s_{nq}$?", f"${FT(qf13(p), qf13(q))}$; " +
                ("доказуема в $S^s$; вопрос о доказуемости в $S^s_{nq}$ этим не решается" if s else
                 "недоказуема в $S^s$; значит, формула недоказуема в $S^s_{nq}$"),
                "С. 124: бескванторные формы аксиом доказуемы в $S^s$, правила вывода это свойство сохраняют; значит, бескванторная форма "
                "любой доказуемой формулы доказуема в $S^s$. Критерий $S^s$ — гл. 5, § 2.", "с. 123–124, гл. 7, § 13", "кванторы, непротиворечивость",
                system="S^s_nq")


def m713(lvl, d, i):
    if d:
        s, w = rnd.choice([("«Бескванторная форма $(?\\forall a)x$ — это $?x$»", "по D1 § 13 $(?\\forall a)x$ заменяется на $\\sim(\\forall a)x\\sim(\\urcorner\\forall a)x$, "
                            "затем на $\\sim x\\sim\\sim x$ (с. 123)"),
                           ("«Бескванторная форма $(\\urcorner\\forall a)x$ — это $\\urcorner x$»", "$(\\urcorner\\forall a)x$ заменяется на $\\sim(\\forall a)x$, а "
                            "после исключения кванторной группы — $\\sim x$ (с. 123)"),
                           ("«Для непротиворечивости $S^s_{nq}$ достаточно, что бескванторные формы аксиом — тавтологии»", "нужно ещё, чтобы правила "
                            "вывода сохраняли свойство доказуемости бескванторных форм в $S^s$ (с. 124)"),
                           ("«Пункты 1 и 2 D1 § 13 можно выполнять в любом порядке»", "после п. 2 в формуле не остаётся $(\\urcorner\\forall b)$, но п. 1 "
                            "порождает $(\\urcorner\\forall b)z$, которые потом заменяются по п. 2; порядок книги: 1, 2, 3 (с. 123)")])
        return card(7, 13, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 13.", "с. 123–124, гл. 7, § 13",
                    "кванторы, непротиворечивость, диагностика", system="S^s_nq")
    if lvl <= 3:
        return qf13_card(lvl)
    return qf13_rand(lvl, "S" if lvl == 7 else "C")


T14 = [("(\\exists a)x \\dashv\\vdash (\\urcorner\\forall a)\\sim x", "T1"), ("(\\urcorner\\exists a)x \\dashv\\vdash (\\forall a)\\sim x", "T2"),
       ("(?\\exists a)x \\dashv\\vdash (?\\forall a)\\sim x", "T3"), ("\\sim(\\forall a)x \\dashv\\vdash (\\urcorner\\forall a)x \\vee (?\\forall a)x", "T4"),
       ("\\sim(\\urcorner\\forall a)x \\dashv\\vdash (\\forall a)x \\vee (?\\forall a)x", "T5"), ("\\sim(?\\forall a)x \\dashv\\vdash (\\forall a)x \\vee (\\urcorner\\forall a)x", "T6"),
       ("(\\exists a)(x \\vee y) \\dashv\\vdash (\\exists a)x \\vee (\\exists a)y", "T7"), ("(\\forall a)x \\vee (\\forall a)y \\vdash (\\forall a)(x \\vee y)", "T8")]


def m714(lvl, d, i):
    if d:
        s, w = rnd.choice([("«$\\sim(\\forall a)x \\dashv\\vdash (\\urcorner\\forall a)x$ — теорема $S^s_{nq}$»", "по T4 § 14 $\\sim(\\forall a)x \\dashv\\vdash "
                            "(\\urcorner\\forall a)x \\vee (?\\forall a)x$ (с. 124); отождествление внешнего и внутреннего отрицания — классический случай"),
                           ("«По MT1 § 14 в заключение доказуемой формулы $S^s_{nq}$ не входят термины, отсутствующие в посылке, — это следует из "
                            "непротиворечивости»", "MT1 говорит об элементарных высказываниях и очевидна из вида аксиомных схем и правил (с. 124)")])
        return card(7, 14, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 14.", "с. 124, гл. 7, § 14",
                    "кванторы, неклассический случай, диагностика", system="S^s_nq")
    if lvl in (2, 3):
        its = rnd.sample(T14, 3)
        return card(7, 14, lvl, "R" if lvl == 2 else "C", "iso", f"{TQ} Укажите номера теоремных схем $S^s_{{nq}}$ (§ 14 гл. 7, с. 124):\n\n" +
                    items([f"${s}$" for s, _ in its]), answers([n for _, n in its]), "С. 124.", "с. 124, гл. 7, § 14", "кванторы, неклассический случай",
                    system="S^s_nq")
    if not ((lvl == 4 and i == 1) or lvl == 7):
        its = rnd.sample(T14F, 2)
        return card(7, 14, lvl, "C", "iso", f"{TQ} Найдите бескванторные формы (D1 § 13) теоремных схем $S^s_{{nq}}$ и проверьте, что они доказуемы в $S^s$:\n\n" +
                    items([f"{n}. ${T(p)} {'\\dashv\\vdash' if two else '\\vdash'} {T(q)}$" for p, q, n, two in its]),
                    answers([f"${T(qf13(p))} {'\\dashv\\vdash' if two else '\\vdash'} {T(qf13(q))}$ — доказуема" for p, q, n, two in its]),
                    "D1 § 13 (с. 123); T1–T8 (с. 124). Обе части имеют одни и те же элементарные высказывания и равнозначны (или посылка влечёт "
                    "заключение) в $S^s$ — по § 13 так и должно быть для теорем $S^s_{nq}$.", "с. 123–124, гл. 7, § 13–14", "кванторы, неклассический случай",
                    system="S^s_nq")
    k = "T1" if lvl != 7 else "T4"
    der = {"T1": ("(\\exists a)x \\vdash (\\urcorner\\forall a)\\sim x", "$x \\vdash \\sim\\sim x$ [$S^s$]; R2: $(\\exists a)x \\vdash (\\exists a)\\sim\\sim x$; "
                  "$A^27$ при подстановке $\\sim x$ вместо $x$: $(\\exists a)\\sim\\sim x \\vdash (\\urcorner\\forall a)\\sim x$; транзитивность."),
           "T4": ("\\sim(\\forall a)x \\vdash (\\urcorner\\forall a)x \\vee (?\\forall a)x", "$A^19$: $\\sim(\\urcorner\\forall a)x\\sim(?\\forall a)x \\vdash (\\forall a)x$; "
                  "множества элементарных высказываний совпадают, контрапозиция по $S^s$: $\\sim(\\forall a)x \\vdash \\sim(\\sim(\\urcorner\\forall a)x\\sim(?\\forall a)x)$; "
                  "по $S^s$ (закон де Моргана) — $(\\urcorner\\forall a)x \\vee (?\\forall a)x$.")}[k]
    return card(7, 14, lvl, "S" if lvl == 7 else "D", "iso", f"{TQ} Покажите, как в $S^s_{{nq}}$ получается ${der[0]}$ ({k} § 14).",
                "См. решение.", der[1] + " С. 123–124.", "с. 123–124, гл. 7, § 12, 14", "кванторы, неклассический случай", answ="proof", system="S^s_nq")


T14F = [(EX("a", xX), ("nall", "a", N(xX)), "T1", True), (("nex", "a", xX), ALL("a", N(xX)), "T2", True),
        (("qex", "a", xX), ("qall", "a", N(xX)), "T3", True), (N(ALL("a", xX)), W(("nall", "a", xX), ("qall", "a", xX)), "T4", True),
        (N(("nall", "a", xX)), W(ALL("a", xX), ("qall", "a", xX)), "T5", True), (N(("qall", "a", xX)), W(ALL("a", xX), ("nall", "a", xX)), "T6", True),
        (EX("a", W(xX, y)), W(EX("a", xX), EX("a", y)), "T7", True), (W(ALL("a", xX), ALL("a", y)), ALL("a", W(xX, y)), "T8", False)]
for p_, q_, n_, two_ in T14F:
    assert Q.strong(qf13(p_), qf13(q_)) and (not two_ or Q.strong(qf13(q_), qf13(p_))), n_


def m715(lvl, d, i):
    if d:
        s, w = rnd.choice([("«По косвенной интерпретации $S^s_{nq}$ $(\\urcorner\\forall b)z$ заменяется на $\\sim(\\forall b)z$»", "по п. 3b (с. 125) "
                            "$(\\urcorner\\forall b)z$ заменяется на $(\\exists b)\\sim z$"),
                           ("«Если $\\{x\\}$ имеет значение 0, то $\\{\\sim x\\}$ имеет значение 1»", "по п. 2 (с. 125) значение другого в этом случае "
                            "не зависит от первого"),
                           ("«$\\sim(\\forall a)\\sim x \\vdash (\\exists a)x$ доказуема в $S^s_{nq}$, как в $S^s_{cq}$ (T37)»", "по MT3 § 15 (с. 126) "
                            "она недоказуема в $S^s_{nq}$ — не тавтология")])
        return card(7, 15, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 15.", "с. 125–126, гл. 7, § 15",
                    "кванторы, интерпретация, диагностика", system="S^s_nq")
    ITS = [("(?\\forall b)z", "\\sim(\\forall b)z\\sim(\\urcorner\\forall b)z", "a"), ("(?\\exists b)z", "\\sim(\\exists b)z\\sim(\\urcorner\\exists b)z", "a"),
           ("(\\urcorner\\forall b)z", "(\\exists b)\\sim z", "b"), ("(\\urcorner\\exists b)z", "(\\forall b)\\sim z", "b"),
           ("(\\forall b)z", "\\{z(1b)\\} \\cdot \\ldots \\cdot \\{z(nb)\\}", "c"), ("(\\exists b)z", "\\{z(1b)\\} \\vee \\ldots \\vee \\{z(nb)\\}", "c")]
    if lvl in (1, 2, 3):
        its = rnd.sample(ITS, 3)
        return card(7, 15, lvl, "R" if lvl == 1 else "C", "iso", f"{TQ} На что заменяются вхождения при построении интерпретационной формы "
                    "в $S^s_{nq}$ (косвенная интерпретация, § 15 гл. 7, с. 125)?\n\n" + items([f"${s}$" for s, _, _ in its]),
                    answers([f"${r}$ (п. 3{c})" for _, r, c in its]), "С. 125, п. 3a–c.", "с. 125, гл. 7, § 15", "кванторы, интерпретация")
    if lvl == 4:
        return card(7, 15, 4, "C", "iso", f"{TQ} По прямой интерпретации $S^s_{{nq}}$ (с. 125) $(\\forall a)x$ имеет значение 1. Какие значения "
                    "имеют $(\\urcorner\\forall a)x$ и $(?\\forall a)x$?", "$(\\urcorner\\forall a)x$ — 0 (п. 2); $(?\\forall a)x$ равнозначно "
                    "$\\sim(\\forall a)x\\sim(\\urcorner\\forall a)x$ (п. 1) — 0.", "С. 125.", "с. 125, гл. 7, § 15", "кванторы, интерпретация")
    if lvl == 5:
        return card(7, 15, 5, "C", "open", f"{TQ} По прямой интерпретации $S^s_{{nq}}$ $(\\forall a)x$ имеет значение 0. Что можно сказать о "
                    "$(\\urcorner\\forall a)x$ и $(?\\forall a)x$?", "Значение $(\\urcorner\\forall a)x$ не зависит от первого (п. 2); если "
                    "$(\\urcorner\\forall a)x = 1$, то $(?\\forall a)x = 0$, если $0$ — то $(?\\forall a)x = 1$ (п. 1).", "С. 125.", "с. 125, гл. 7, § 15",
                    "кванторы, интерпретация")
    if lvl == 6:
        return card(7, 15, 6, "C", "open", f"{TQ} Покажите, что $\\sim(\\urcorner\\forall a)x \\vdash (\\forall a)x$ не тавтология при прямой "
                    "интерпретации $S^s_{nq}$ (MT2 § 15).", "Пусть $(\\forall a)x = 0$, $(\\urcorner\\forall a)x = 0$ (допустимо по п. 2); тогда "
                    "$(?\\forall a)x = 1$, посылка $\\sim(\\urcorner\\forall a)x$ имеет значение 1, заключение — 0.", "С. 125.",
                    "с. 125, гл. 7, § 15", "кванторы, интерпретация")
    return card(7, 15, 7, "S", "transfer", f"{TQ} Сравните классический ($S^s_{{cq}}$) и неклассический ($S^s_{{nq}}$) случаи на формуле "
                "$\\sim(\\exists a)\\sim x \\vdash (\\forall a)x$.", "В $S^s_{cq}$ доказуема (A7); в $S^s_{nq}$ недоказуема (MT3 § 15: не тавтология).",
                "С. 99, 126.", "с. 99, 126, гл. 7, § 2, 15", "кванторы, интерпретация")


T16 = [("\\vdash \\sim((Ka)x(\\urcorner Ka)x)", "T1"), ("\\vdash \\sim((Ka)x(?Ka)x)", "T2"), ("\\vdash \\sim((\\urcorner Ka)x(?Ka)x)", "T3"),
       ("\\vdash (Ka)x \\vee (\\urcorner Ka)x \\vee (?Ka)x", "T4"), ("\\vdash (Ka)x : (\\urcorner Ka)x : (?Ka)x", "T5")]


def m716(lvl, d, i):
    if d:
        s, w = rnd.choice([("«В $S^5_{nq}$ доказуема $\\vdash (Ka)x \\vee (\\urcorner Ka)x$»", "по MT3 § 16 (с. 126–127) она недоказуема — не тавтология: "
                            "возможно $(?Ka)x$"),
                           ("«$(Ka)x$ и $(\\urcorner Ka)x$ находятся в классическом отношении»", "по MT1 § 16 (с. 126) формулы вида "
                            "$(\\alpha Ka)x : (\\beta Ka)x : \\sim(\\alpha Ka)x\\sim(\\beta Ka)x \\vdash (\\alpha Ka)x : (\\beta Ka)x$ недоказуемы — отношение неклассическое")])
        return card(7, 16, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 16.", "с. 126–127, гл. 7, § 16",
                    "кванторы, неклассический случай, диагностика", system="S^5_nq")
    if lvl <= 3:
        its = rnd.sample(T16, 3)
        return card(7, 16, lvl, "C" if lvl > 2 else "R", "iso", f"{TQ} K есть $\\forall$ или $\\exists$. Укажите номера теоремных схем $S^5_{{nq}}$ "
                    "(§ 16 гл. 7, с. 126):\n\n" + items([f"${s}$" for s, _ in its]), answers([n for _, n in its]), "С. 126.",
                    "с. 126, гл. 7, § 16", "кванторы, неклассический случай", system="S^5_nq")
    fs = [("\\vdash (\\forall a)x \\vee (\\urcorner\\forall a)x", False), ("\\vdash (\\forall a)x \\vee (\\urcorner\\forall a)x \\vee (?\\forall a)x", True),
          ("\\vdash \\sim((\\exists a)x(?\\exists a)x)", True), ("\\vdash (\\exists a)x \\vee (?\\exists a)x", False),
          ("\\vdash \\sim(\\urcorner\\exists a)x \\supset (\\exists a)x", False), ("\\vdash (\\urcorner\\forall a)x \\vee (?\\forall a)x", False)]
    its = rnd.sample(fs, 3)
    return card(7, 16, lvl, "S" if lvl == 7 else "C", "open", f"{TQ} Доказуемы ли в $S^5_{{nq}}$ формулы?\n\n" + items([f"${s}$" for s, _ in its]),
                answers(["да" if t else "нет" for _, t in its]), "T1–T5, MT2, MT3 § 16 (с. 126–127): из $(Ka)x$, $(\\urcorner Ka)x$, $(?Ka)x$ истинно "
                "ровно одно; дизъюнкция двух из них не тавтология.", "с. 126–127, гл. 7, § 16", "кванторы, неклассический случай", system="S^5_nq")


def m717(lvl, d, i):
    if d:
        s, w = rnd.choice([("«Классический вариант получается добавлением $(\\urcorner\\forall a)x \\vdash \\sim(\\forall a)x$»", "добавляется A*13 "
                            "$\\sim(\\forall a)x \\vdash (\\urcorner\\forall a)x$ (с. 127)"),
                           ("«В классическом варианте по-прежнему возможно $(?Ka)x$»", "имеет силу T1 § 17: $\\vdash \\sim(?Ka)x$ (с. 127)")])
        return card(7, 17, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 17.", "с. 127, гл. 7, § 17",
                    "кванторы, классический случай, диагностика")
    if lvl == 2:
        return card(7, 17, 2, "R", "iso", f"{TQ} Какую аксиомную схему нужно добавить к системам для неклассического случая, чтобы получить "
                    "классический (§ 17 гл. 7)?", "A*13. $\\sim(\\forall a)x \\vdash (\\urcorner\\forall a)x$.", "С. 127.", "с. 127, гл. 7, § 17", "кванторы, классический случай")
    if lvl == 3:
        return card(7, 17, 3, "C", "iso", f"{TQ} Какие теоремные схемы имеют силу после добавления A*13 (§ 17 гл. 7)?",
                    "T1. $\\vdash \\sim(?Ka)x$; T2. $(\\forall a)x \\dashv\\vdash \\sim(\\exists a)\\sim x$; T3. $\\vdash (Ka)x \\vee (\\urcorner Ka)x$.", "С. 127.",
                    "с. 127, гл. 7, § 17", "кванторы, классический случай")
    if lvl in (4, 5):
        sch = rnd.choice([("A*13", lambda X, k: f"\\sim(\\forall a){X} \\vdash (\\urcorner\\forall a){X}"),
                          ("T1", lambda X, k: f"\\vdash \\sim(?{k} a){X}"), ("T3", lambda X, k: f"\\vdash ({k} a){X} \\vee (\\urcorner{k} a){X}")])
        X = rnd.choice(["(a \\leftarrow b)", "\\sim(a \\leftarrow c)", "((a \\leftarrow b)(a \\leftarrow c))", "(\\exists b)(a \\leftarrow b)"])
        k = rnd.choice(["\\forall", "\\exists"])
        gen_ = {"A*13": "\\sim(\\forall a)x \\vdash (\\urcorner\\forall a)x", "T1": "\\vdash \\sim(?Ka)x", "T3": "\\vdash (Ka)x \\vee (\\urcorner Ka)x"}[sch[0]]
        kk = "" if sch[0] == "A*13" else f", K — ${k}$"
        return card(7, 17, lvl, "D", "iso", f"{TQ} Подставьте в схему {sch[0]} § 17 гл. 7 (${gen_}$) вместо $x$ — ${X}${kk}.",
                    f"${sch[1](X, k)}$", "С. 127.", "с. 127, гл. 7, § 17", "кванторы, классический случай")
    pool = [(f"\\vdash ({k} a)x \\vee (\\urcorner{k} a)x", False, True, "MT3 § 16 / T3 § 17") for k in ("\\forall", "\\exists")] + \
           [(f"\\vdash \\sim(?{k} a)x", False, True, "не тавтология в $S^5_{nq}$ (MT2 § 16) / T1 § 17") for k in ("\\forall", "\\exists")] + \
           [(f"\\vdash \\sim(({k} a)x(\\urcorner{k} a)x)", True, True, "T1 § 16") for k in ("\\forall", "\\exists")] + \
           [(f"\\vdash ({k} a)x \\vee (\\urcorner{k} a)x \\vee (?{k} a)x", True, True, "T4 § 16") for k in ("\\forall", "\\exists")]
    its = rnd.sample(pool, 3)
    yn = lambda b: "да" if b else "нет"
    return card(7, 17, lvl, "S" if lvl == 7 else "C", "transfer", f"{TQ} Доказуемы ли формулы в $S^5_{{nq}}$ и в системе, полученной из неё "
                "добавлением A*13 (§ 17 гл. 7)?\n\n" + items([f"${f}$" for f, _, _, _ in its]),
                answers([f"{yn(a)} / {yn(b)}" for _, a, b, _ in its]), "\n".join(f"{L[n]}) {w}." for n, (_, _, _, w) in enumerate(its)) +
                " С. 126–127.", "с. 126–127, гл. 7, § 16–17", "кванторы, классический случай")


REPL = [("(\\urcorner\\forall b)z", "(\\exists b)\\sim z"), ("(?\\forall b)z", "\\sim(\\forall b)z\\sim(\\exists b)\\sim z"),
        ("(\\urcorner\\exists b)z", "(\\forall b)\\sim z"), ("(?\\exists b)z", "\\sim(\\exists b)z\\sim(\\forall b)\\sim z")]
S18 = {1: "(\\forall a)x \\vdash (\\forall a)\\sim\\sim x", 2: "(\\exists a)\\sim x \\vdash (\\exists a)\\sim x",
       3: "\\sim(\\forall a)x\\sim(\\exists a)\\sim x \\vdash \\sim(\\exists a)x\\sim(\\forall a)\\sim x", 4: "(\\forall a)\\sim\\sim x \\vdash (\\forall a)x",
       5: "(\\exists a)\\sim x \\vdash (\\exists a)\\sim x", 6: "\\sim(\\exists a)x\\sim(\\forall a)\\sim x \\vdash \\sim(\\forall a)x\\sim(\\exists a)\\sim x",
       7: "(\\forall a)x \\vdash \\sim(\\exists a)\\sim x\\sim(\\sim(\\forall a)x\\sim(\\exists a)\\sim x)",
       8: "(\\exists a)\\sim x \\vdash \\sim(\\forall a)x\\sim(\\sim(\\forall a)x\\sim(\\exists a)\\sim x)",
       9: "\\sim(\\forall a)x\\sim(\\exists a)\\sim x \\vdash \\sim(\\forall a)x\\sim(\\exists a)\\sim x",
       10: "\\sim(\\exists a)\\sim x\\sim(\\sim(\\forall a)x\\sim(\\exists a)\\sim x) \\vdash (\\forall a)x",
       11: "\\sim(\\forall a)x\\sim(\\sim(\\forall a)x\\sim(\\exists a)\\sim x) \\vdash (\\exists a)\\sim x",
       12: "\\sim(\\forall a)x\\sim(\\exists a)\\sim x \\vdash \\sim(\\forall a)x\\sim(\\exists a)\\sim x",
       13: "(\\exists a)\\sim(xy) \\vdash (\\exists a)\\sim x \\vee (\\exists a)\\sim y", 14: "(\\exists a)\\sim x \\vee (\\exists a)\\sim y \\vdash (\\exists a)\\sim(xy)",
       15: "(\\forall a)\\sim x \\vee (\\forall a)\\sim y \\vdash (\\forall a)\\sim(xy)"}
S18SRC = {1: "A^16", 2: "A^26", 3: "A^36", 4: "A^17", 5: "A^27", 6: "A^37", 7: "A^18", 8: "A^28", 9: "A^38", 10: "A^19", 11: "A^29",
          12: "A^39", 13: "A10", 14: "A11", 15: "A12"}
DEP = {1, 2, 3, 4, 5, 6, 9, 12}


def repl18(f):
    k = f[0]
    if k == "nall":
        return EX(f[1], N(repl18(f[2])))
    if k == "qall":
        return C(N(ALL(f[1], repl18(f[2]))), N(EX(f[1], N(repl18(f[2])))))
    if k == "nex":
        return ALL(f[1], N(repl18(f[2])))
    if k == "qex":
        return C(N(EX(f[1], repl18(f[2]))), N(ALL(f[1], N(repl18(f[2])))))
    if k in ("all", "ex"):
        return (k, f[1], repl18(f[2]))
    if k == "neg":
        return N(repl18(f[1]))
    if k in ("v", "el"):
        return f
    return (k, tuple(repl18(g) for g in f[1]))


S18OK = set()
for n_, src in S18SRC.items():
    key = "A" + src[2:] if src.startswith("A^") else src
    p, q = NQ[key]
    if FT(repl18(p), repl18(q)).replace(" ", "") == S18[n_].replace(" ", ""):
        S18OK.add(n_)
print("§ 18: замена совпадает со списком с. 128 для схем", sorted(S18OK))


def m718(lvl, d, i):
    if d:
        s, w = rnd.choice([("«При замене (с. 127) $(?\\forall b)z$ переходит в $\\sim(\\forall b)z\\sim(\\urcorner\\forall b)z$»", "по с. 127 — в "
                            "$\\sim(\\forall b)z\\sim(\\exists b)\\sim z$: оператор $\\urcorner$ после замены не остаётся"),
                           ("«После замены все 15 схем присоединяются к схемам $S^s_{cq}$»", "схемы 1–4, 5, 6, 9, 12 отпадают как зависимые; "
                            "присоединяются остальные, без A6 и A7 (с. 128)"),
                           ("«Проблема полноты $S^s_{nq}$ решена в книге»", "книга её не рассматривает и ограничивается замечаниями (с. 127)")])
        return card(7, 18, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 18.", "с. 127–128, гл. 7, § 18",
                    "кванторы, полнота, диагностика", system="S^s_nq")
    if lvl in (3, 4):
        k = rnd.choice(sorted(S18OK))
        src = S18SRC[k]
        key = "A" + src[2:] if src.startswith("A^") else src
        p, q = NQ[key]
        return card(7, 18, lvl, "D", "iso", f"{TQ} Выполните замену § 18 гл. 7 (с. 127) в схеме ${src}$: ${FT(p, q)}$.",
                    f"${S18[k]}$ (схема {k} на с. 128)", "Замены: " + "; ".join(f"${a}$ → ${b}$" for a, b in REPL) + ".",
                    "с. 127–128, гл. 7, § 18", "кванторы, полнота", system="S^s_nq")
    ks = rnd.sample(sorted(S18), 4)
    return card(7, 18, lvl, "S" if lvl == 7 else "C", "iso", f"{TQ} Какие из схем, полученных заменой § 18 (с. 128), отпадают как зависимые?\n\n" +
                items([f"{k}. ${S18[k]}$" for k in ks]), answers(["отпадает" if k in DEP else "присоединяется" for k in ks]),
                "С. 128: схемы 1–4, 5, 6, 9, 12 отпадают как зависимые; остальные присоединяются к $S^s_{cq}$ без A6 и A7.",
                "с. 128, гл. 7, § 18", "кванторы, полнота", system="S^s_nq")


# ---------------------------------------------------------------- 07.19–07.21
T19 = {1: "(\\forall c)(a \\leftarrow b) \\vdash (a \\leftarrow b)", 2: "(a \\leftarrow b) \\vdash (\\exists c)(a \\leftarrow b)",
       3: "(\\forall c)(a \\leftarrow b) \\vdash \\sim(\\exists c)\\sim(a \\leftarrow b)", 4: "\\sim(\\exists c)\\sim(a \\leftarrow b) \\vdash (\\forall c)(a \\leftarrow b)",
       9: "(\\forall c)(a \\leftarrow b) \\vdash (\\forall c)(\\forall c)(a \\leftarrow b)", 10: "(\\exists c)(a \\leftarrow b) \\vdash (\\forall c)(\\exists c)(a \\leftarrow b)",
       11: "(\\exists c)(\\exists c)(a \\leftarrow b) \\vdash (\\exists c)(a \\leftarrow b)", 12: "(\\exists c)(\\forall c)(a \\leftarrow b) \\vdash (\\forall c)(a \\leftarrow b)",
       13: "(a \\leftarrow b) \\vdash (\\forall a^1)(a \\leftarrow b)", 14: "(\\exists a^1)(a \\leftarrow b) \\vdash (a \\leftarrow b)"}


def m719(lvl, d, i):
    if d:
        s, w = rnd.choice([("«По MT4 § 19 из T13 подстановкой $(a^1 \\leftarrow b)$ вместо $(a \\leftarrow b)$ получаем $(a^1 \\leftarrow b) \\vdash (\\forall a^1)(a^1 \\leftarrow b)$»",
                            "MT4 требует, чтобы в подставляемое высказывание не входил $a^1$ (с. 130)"),
                           ("«По MT5 § 19 в T14 можно подставить предикат $a^1$ на место $b$»", "MT5 требует, чтобы подставляемый предикат (субъект) не был "
                            "$a^1$ и не содержал $a^1$ (с. 130)"),
                           ("«MT1 § 19 позволяет подставлять высказывание лишь в одно из вхождений элементарного высказывания»", "подстановка делается "
                            "везде, где $a$ входит в $x \\vdash y$ (с. 129)")])
        return card(7, 19, lvl, "E", "open", f"Буквы $a, b, a^1$ — простые термины. Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 19.",
                    "с. 129–130, гл. 7, § 19", "кванторы, подстановка, диагностика", system="S^s_cq")
    if lvl == 3:
        ks = rnd.sample(sorted(T19), 3)
        return card(7, 19, 3, "R", "iso", "Буквы $a, b, a^1$ — простые термины; $c$ есть $a$, $b$, $a^1$, $a^2$, $b^1$ или $b^2$. Укажите номера "
                    "теорем $S^s_{cq}$ из § 19 гл. 7 (с. 129):\n\n" + items([f"${T19[k]}$" for k in ks]), answers([f"{k}" for k in ks]), "С. 129.",
                    "с. 129, гл. 7, § 19", "кванторы, подстановка", system="S^s_cq")
    if lvl in (4, 5):
        k = rnd.choice([1, 2, 3, 4, 9, 10, 11, 12])
        c, sub = rnd.choice(["a", "b"]), rnd.choice(["(d \\leftarrow e)", "\\sim(d \\leftarrow e)", "(d \\leftarrow e)(d \\leftarrow f)"])
        f = T19[k].replace("\\forall c", f"\\forall {c}").replace("\\exists c", f"\\exists {c}")
        g = f.replace("(a \\leftarrow b)", "@").replace("@", sub if sub.startswith("(d") and "(d \\leftarrow f)" not in sub else f"({sub})" if "(d \\leftarrow f)" in sub else sub)
        return card(7, 19, lvl, "D", "iso", f"Буквы $a, b, d, e, f$ — простые термины. По MT2 § 19 (с. 129) подставьте ${sub}$ на место элементарного "
                    f"высказывания $(a \\leftarrow b)$ в теорему {k}: ${f}$.", f"${g}$ — доказуема в $S^s_{{cq}}$ (MT2).",
                    "MT2 § 19: подстановка любого высказывания на место элементарного везде, где оно входит.", "с. 129, гл. 7, § 19", "кванторы, подстановка",
                    system="S^s_cq")
    its = [("$(a \\leftarrow b) \\vdash (\\forall a^1)(a \\leftarrow b)$, подстановка $(d \\leftarrow b)$ (MT4)", "да"),
           ("$(a \\leftarrow b) \\vdash (\\forall a^1)(a \\leftarrow b)$, подстановка $(a^1 \\leftarrow b)$ (MT4)", "нет: входит $a^1$"),
           ("$(\\exists a^1)(a \\leftarrow b) \\vdash (a \\leftarrow b)$, субъект $d$ вместо $a$ (MT5)", "да"),
           ("$(\\exists a^1)(a \\leftarrow b) \\vdash (a \\leftarrow b)$, субъект $a^1$ вместо $a$ (MT5)", "нет: подставляемый субъект есть $a^1$")]
    pick = rnd.sample(its, 3)
    return card(7, 19, lvl, "S" if lvl == 7 else "C", "open", "Буквы $a, b, d, a^1$ — простые термины. Допустима ли подстановка (§ 19 гл. 7, с. 130)?\n\n" +
                items([s for s, _ in pick]), answers([a for _, a in pick]), "MT4, MT5 (с. 130).", "с. 130, гл. 7, § 19", "кванторы, подстановка",
                system="S^s_cq")


def m720(lvl, d, i):
    if d:
        s, w = rnd.choice([("«По A*II $\\sim((\\forall a) \\cdot (\\exists b))x \\dashv\\vdash \\sim(\\forall a)x \\cdot \\sim(\\exists b)x$»", "по A*II "
                            "отрицание конъюнкции кванторных групп даёт дизъюнкцию: $\\sim(\\forall a)x \\vee \\sim(\\exists b)x$ (с. 131)"),
                           ("«Системы теории кванторов исчерпывают все свойства кванторов»", "по § 20 (с. 130) они определяют свойства кванторов лишь "
                            "в сочетании друг с другом и с операторами общей теории дедукции")])
        return card(7, 20, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 20.", "с. 130–131, гл. 7, § 20",
                    "кванторы, расширения, диагностика")
    if lvl == 2:
        return card(7, 20, 2, "D", "iso", f"{TQ} Запишите по схеме A*I (§ 20 гл. 7) формулу для $(\\exists a)(\\exists b)x$.",
                    "$(\\exists a)(\\exists b)x \\dashv\\vdash (\\exists(a, b))x$", "С. 130.", "с. 130, гл. 7, § 20", "кванторы, расширения")
    if lvl in (3, 4):
        k = rnd.choice(["\\forall", "\\exists"])
        n = rnd.choice([3, 4])
        lhs = "".join(f"({k} a^{j})" for j in range(1, n + 1))
        return card(7, 20, lvl, "D", "iso", f"{TQ} Запишите по схеме A*I (с. 131) формулу для ${lhs}x$.",
                    f"${lhs}x \\dashv\\vdash ({k}(" + ", ".join(f"a^{j}" for j in range(1, n + 1)) + "))x$", "С. 131.", "с. 131, гл. 7, § 20", "кванторы, расширения")
    v_ = [("((\\forall a) \\vee (\\exists b))x", "(\\forall a)x \\vee (\\exists b)x"), ("((\\forall a) \\cdot (\\exists b))x", "(\\forall a)x(\\exists b)x"),
          ("\\sim((\\forall a) \\cdot (\\forall b))x", "\\sim(\\forall a)x \\vee \\sim(\\forall b)x"), ("\\sim((\\exists a) \\vee (\\forall b))x", "\\sim(\\exists a)x\\sim(\\forall b)x"),
          ("(\\sim(\\forall a) \\cdot (\\exists b))x", "\\sim(\\forall a)x(\\exists b)x")]
    its = rnd.sample(v_, 2)
    return card(7, 20, lvl, "S" if lvl == 7 else "C", "iso", f"{TQ} Преобразуйте по схемам A*II (§ 20 гл. 7, с. 131):\n\n" + items([f"${s}$" for s, _ in its]),
                answers([f"${t}$" for _, t in its]), "A*II (с. 131); α, β — наличие $n$ отрицаний ($n \\geq 0$).", "с. 131, гл. 7, § 20", "кванторы, расширения")


S21 = [("(\\exists a)(x?\\rightarrow y) \\vdash \\sim(x \\rightarrow y)", "3"), ("(x \\rightarrow y) \\dashv\\vdash (x \\rightarrow (\\forall a)y)", "4"),
       ("(\\exists a)\\sim(x \\rightarrow y) \\vdash \\sim(x \\rightarrow y)", "классический случай")]


def m721(lvl, d, i):
    if d:
        s, w = rnd.choice([("«Схема $(\\exists a)\\sim(x \\rightarrow y) \\vdash \\sim(x \\rightarrow y)$ принимается и в неклассическом случае»", "по § 21 "
                            "(с. 131) она принимается или доказывается в классическом случае"),
                           ("«Для соединения теорий достаточно принять аксиомные схемы, не меняя определения высказывания»", "надо добавить "
                            "определение высказывания теории условных высказываний к определению высказывания теории кванторов (с. 131)")])
        return card(7, 21, lvl, "E", "open", f"{TQ} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 7, § 21.", "с. 131, гл. 7, § 21",
                    "кванторы и условные высказывания, диагностика")
    if lvl == 2:
        return card(7, 21, 2, "R", "iso", f"{TQ} Что надо сделать при соединении теории кванторов и теории условных высказываний (§ 21 гл. 7)?",
                    "Добавить определение высказывания теории условных высказываний к определению высказывания теории кванторов и принять "
                    "аксиомные схемы 1–5 § 21.", "С. 131.", "с. 131, гл. 7, § 21", "кванторы и условные высказывания")
    if lvl in (3, 4, 5):
        s, n = rnd.choice(S21)
        X = rnd.choice(["(a \\leftarrow b)", "\\sim(a \\leftarrow c)"])
        Y = rnd.choice(["(b \\leftarrow c)", "(a \\leftarrow d)"])
        g = s.replace("x", "@X").replace("y", "@Y").replace("@X", X).replace("@Y", Y)
        return card(7, 21, lvl, "D", "iso", f"Буквы $a, b, c, d$ — термины. Подставьте в схему {n if n.isdigit() else '(' + n + ')'} § 21 гл. 7 "
                    f"(${s}$) вместо $x$ — ${X}$, вместо $y$ — ${Y}$.", f"${g}$", "С. 131.", "с. 131, гл. 7, § 21", "кванторы и условные высказывания")
    ys = rnd.sample(["(a \\leftarrow b)", "\\sim(a \\leftarrow b)", "(a \\leftarrow b)(a \\leftarrow c)", "(b \\leftarrow c)", "(a \\leftarrow c) \\vee (a \\leftarrow d)"], 2 if lvl == 7 else 1)
    wrap = lambda Y: Y if Y.startswith("(") and " \\vee " not in Y and ")(" not in Y else f"({Y})"
    return card(7, 21, lvl, "S" if lvl == 7 else "C", "transfer", f"{TQ} По схеме 4 § 21 $(x \\rightarrow y) \\dashv\\vdash (x \\rightarrow (\\forall a)y)$. "
                "Что даёт эта схема при " + " и при ".join(f"$y = {Y}$" for Y in ys) + "?",
                "; ".join(f"$(x \\rightarrow {Y}) \\dashv\\vdash (x \\rightarrow (\\forall a){wrap(Y)})$" for Y in ys),
                "Схема 4 (с. 131): подстановка в метапеременную $y$.", "с. 131, гл. 7, § 21", "кванторы и условные высказывания")


# ---------------------------------------------------------------- гл. 8 теория предикации
def P(s, a="a", b="b"):
    return {"+": EL(a, b), "n": ("pn", a, b), "q": ("pq", a, b)}[s]


def pval(f, st):
    k = f[0]
    if k == "el":
        return int(st[(f[1], f[2])] == "+")
    if k == "pn":
        return int(st[(f[1], f[2])] == "n")
    if k == "pq":
        return int(st[(f[1], f[2])] == "q")
    if k == "neg":
        return 1 - pval(f[1], st)
    if k == "imp":
        return int(not pval(f[1], st) or pval(f[2], st))
    vs = [pval(g, st) for g in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs)) if k == "wdis" else int(sum(vs) == 1)


def ppairs(f, acc=None):
    acc = set() if acc is None else acc
    k = f[0]
    if k in ("el", "pn", "pq"):
        acc.add((f[1], f[2]))
    elif k == "neg":
        ppairs(f[1], acc)
    elif k == "imp":
        ppairs(f[1], acc)
        ppairs(f[2], acc)
    else:
        for g in f[1]:
            ppairs(g, acc)
    return acc


def ptaut(p, q=None, states="+nq", restrict=True):
    prs = sorted(ppairs(p) | (ppairs(q) if q is not None else set()))
    for combo in itertools.product(states, repeat=len(prs)):
        st = dict(zip(prs, combo))
        if q is None:
            if not pval(p, st):
                return False
        elif pval(p, st) and not pval(q, st):
            return False
    if q is not None and restrict and not ppairs(q) <= ppairs(p):
        return False
    return True


AP = {"A1": (P("+"), C(N(P("n")), N(P("q")))), "A2": (C(N(P("n")), N(P("q"))), P("+")), "A3": (P("n"), C(N(P("+")), N(P("q")))),
      "A4": (C(N(P("+")), N(P("q"))), P("n")), "A5": (P("q"), C(N(P("+")), N(P("n")))), "A6": (C(N(P("+")), N(P("n"))), P("q"))}
for k_, (p, q) in AP.items():
    assert ptaut(p, q)
TP = [(N(P("+")), W(P("n"), P("q")), "T1"), (N(P("n")), W(P("+"), P("q")), "T2"), (N(P("q")), W(P("+"), P("n")), "T3"),
      (P("+"), N(P("n")), "T4"), (P("+"), N(P("q")), "T5"), (P("n"), N(P("+")), "T6"), (P("n"), N(P("q")), "T7")]
for p, q, n_ in TP:
    assert ptaut(p, q) and (n_ not in ("T1", "T2", "T3") or ptaut(q, p))
TP5 = [(("dis", (P("+"), P("n"), P("q"))), "T6"), (W(P("+"), P("n"), P("q")), "T7"), (N(C(P("+"), P("n"))), "T8"),
       (N(C(P("+"), P("q"))), "T9"), (N(C(P("n"), P("q"))), "T10")]
for f_, _ in TP5:
    assert ptaut(f_)
PP = "Буквы $a$, $b$ — термины ($a$ — субъект, $b$ — предикат); $\\urcorner$ — внутреннее отрицание, $?$ — неопределённость."


def p_rand(depth=2, pairs=(("a", "b"),)):
    if depth == 0 or rnd.random() < 0.35:
        s, t = rnd.choice(pairs)
        return P(rnd.choice("+nq"), s, t)
    k = rnd.choice(["neg", "conj", "wdis"])
    if k == "neg":
        return N(p_rand(depth - 1, pairs))
    a1, a2 = p_rand(depth - 1, pairs), p_rand(depth - 1, pairs)
    while a1 == a2:
        a2 = p_rand(depth - 1, pairs)
    return (k, (a1, a2))


def p_taut_card(lvl, sec=1, classical=False, typ="C"):
    its = []
    want = [True, False, True, False]
    rnd.shuffle(want)
    for w in want:
        for _ in range(500):
            p, q = p_rand(1), p_rand(2)
            if ptaut(p, q, "+n" if classical else "+nq") == w and repr((p, q)) not in USED:
                USED.add(repr((p, q)))
                its.append((p, q))
                break
    st = "+n" if classical else "+nq"
    cond = (f"{PP} Тавтологии ли формулы {'в классическом случае (§ 3 гл. 8)' if classical else 'в $S^s_p$ (интерпретация § 2 гл. 8)'}?\n\n" +
            items([f"${FT(p, q)}$" for p, q in its]))
    sols = []
    for p, q in its:
        if ptaut(p, q, st):
            sols.append("тавтология")
        else:
            prs = sorted(ppairs(p) | ppairs(q))
            for combo in itertools.product(st, repeat=len(prs)):
                s_ = dict(zip(prs, combo))
                if pval(p, s_) and not pval(q, s_):
                    nm = {"+": "$(a \\leftarrow b)$", "n": "$(a \\urcorner\\!\\leftarrow b)$", "q": "$(a? \\leftarrow b)$"}[combo[0]]
                    sols.append(f"не тавтология: истинно только {nm} — посылка 1, заключение 0")
                    break
    base = ("Из трёх высказываний $(a \\leftarrow b)$, $(a \\urcorner\\!\\leftarrow b)$, $(a? \\leftarrow b)$ истинно ровно одно "
            "(интерпретация § 2, пп. 1–3; T6 $S^5_p$)." if not classical else
            "В классическом случае неопределённость исключается и $(a \\urcorner\\!\\leftarrow b)$ равнозначно $\\sim(a \\leftarrow b)$ (с. 134).")
    return card(8, sec, lvl, typ, "iso", cond, answers(["да" if s == "тавтология" else "нет" for s in sols]),
                base + "\n" + "\n".join(f"{L[i]}) {s}." for i, s in enumerate(sols)), "с. 132–134, гл. 8, § 1–3", "предикация",
                system="S^s_p")


def ap_rec(lvl, typ="R"):
    ks = rnd.sample(sorted(AP), 4)
    return card(8, 1, lvl, typ, "iso", f"{PP} Каким аксиомным схемам $S^i_p$ (§ 1 гл. 8, с. 132) соответствуют формулы?\n\n" +
                items([f"${FT(*AP[k])}$" for k in ks]), answers(ks), "С. 132.", "с. 132, гл. 8, § 1", "предикация, аксиомы", system="S^s_p")


def tp_rec(lvl, typ="C"):
    its = rnd.sample(TP, 3)
    def show(p, q, n):
        return f"${T(p)} \\dashv\\vdash {T(q)}$" if n in ("T1", "T2", "T3") else f"${FT(p, q)}$"
    return card(8, 1, lvl, typ, "iso", f"{PP} Укажите номера теоремных схем $S^s_p$ (с. 133):\n\n" + items([show(*t) for t in its]),
                answers([n for _, _, n in its]), "С. 133.", "с. 133, гл. 8, § 1", "предикация, теоремы", system="S^s_p")


def tp5_rec(lvl, typ="C"):
    its = rnd.sample(TP5, 3)
    return card(8, 1, lvl, typ, "iso", f"{PP} Укажите номера теоремных схем $S^5_p$ (с. 133):\n\n" + items([f"${FT(f)}$" for f, _ in its]),
                answers([n for _, n in its]), "С. 133.", "с. 133, гл. 8, § 1", "предикация, теоремы", system="S^5_p")


def p_deriv(lvl):
    p, q, n = rnd.choice(TP[3:])
    src = {"T4": ("A1", "(a \\leftarrow b) \\vdash \\sim(a \\urcorner\\!\\leftarrow b)\\sim(a? \\leftarrow b)"),
           "T5": ("A1", "(a \\leftarrow b) \\vdash \\sim(a \\urcorner\\!\\leftarrow b)\\sim(a? \\leftarrow b)"),
           "T6": ("A3", "(a \\urcorner\\!\\leftarrow b) \\vdash \\sim(a \\leftarrow b)\\sim(a? \\leftarrow b)"),
           "T7": ("A3", "(a \\urcorner\\!\\leftarrow b) \\vdash \\sim(a \\leftarrow b)\\sim(a? \\leftarrow b)")}[n]
    return card(8, 1, lvl, "D", "iso", f"{PP} Выведите {n} $S^s_p$: ${FT(p, q)}$.",
                f"${src[1]}$ [{src[0]}]; отбрасывание конъюнкта [$S^s$]; транзитивность.",
                "С. 132–133.", "с. 132–133, гл. 8, § 1", "предикация, вывод", answ="proof", system="S^s_p")


E801 = [("«$\\sim(a \\urcorner\\!\\leftarrow b) \\vdash (a \\leftarrow b)$ доказуема в $S^s_p$ — двойное отрицание снимается»", "по MT2 § 2 (с. 134) "
         "формула недоказуема: при $(a? \\leftarrow b)$ посылка истинна, заключение ложно; $\\sim$ и $\\urcorner$ — разные отрицания"),
        ("«$\\vdash (a \\leftarrow b) \\vee (a \\urcorner\\!\\leftarrow b)$ — теорема $S^5_p$»", "по MT2 § 2 (с. 134) недоказуема (не тавтология); "
         "теорема — T7: $\\vdash (a \\leftarrow b) \\vee (a \\urcorner\\!\\leftarrow b) \\vee (a? \\leftarrow b)$"),
        ("«$(a \\leftarrow b) \\vdash (a \\leftarrow b)(c \\leftarrow d) \\vee \\sim(c \\leftarrow d)$ доказуема в $S^s_p$, так как это тавтология»",
         "по MT1 § 1 (с. 132) в заключение доказуемой формулы не входят элементарные высказывания, отсутствующие в посылке"),
        ("«Элементарными для теории предикации являются высказывания $(a \\leftarrow b)$, $(a \\urcorner\\!\\leftarrow b)$ и $(a? \\leftarrow b)$»",
         "по D2 (с. 132) элементарны высказывания вида $(a \\leftarrow b)$; $(a \\leftarrow b)$ входит в $(a \\urcorner\\!\\leftarrow b)$ и $(a? \\leftarrow b)$"),
        ("«A2 — $(a \\leftarrow b) \\vdash \\sim(a \\urcorner\\!\\leftarrow b)\\sim(a? \\leftarrow b)$»", "это A1; A2 — обратная формула "
         "$\\sim(a \\urcorner\\!\\leftarrow b)\\sim(a? \\leftarrow b) \\vdash (a \\leftarrow b)$ (с. 132)"),
        ("«T4 $(a \\leftarrow b) \\vdash \\sim(a \\urcorner\\!\\leftarrow b)$ обратима: доказуема и $\\sim(a \\urcorner\\!\\leftarrow b) \\vdash (a \\leftarrow b)$»",
         "обратная формула по MT2 § 2 (с. 134) недоказуема — не тавтология"),
        ("«A5 — $(a? \\leftarrow b) \\vdash \\sim(a \\leftarrow b)(a \\urcorner\\!\\leftarrow b)$»", "A5 — $(a? \\leftarrow b) \\vdash \\sim(a \\leftarrow b)\\sim(a \\urcorner\\!\\leftarrow b)$ (с. 132)"),
        ("«$\\vdash (a \\leftarrow b) \\vee (a \\urcorner\\!\\leftarrow b) \\vee (a? \\leftarrow b)$ — теорема $S^s_p$»", "это T7 системы $S^5_p$ (с. 133)"),
        ("«Высказывание $(a \\leftarrow b)(a \\urcorner\\!\\leftarrow b)$ противоречиво лишь в классическом случае»", "T8 $S^5_p$: "
         "$\\vdash \\sim((a \\leftarrow b)(a \\urcorner\\!\\leftarrow b))$ (с. 133) — и в неклассическом случае"),
        ("«T1 — $\\sim(a \\leftarrow b) \\dashv\\vdash (a \\urcorner\\!\\leftarrow b)$»", "T1 — $\\sim(a \\leftarrow b) \\dashv\\vdash (a \\urcorner\\!\\leftarrow b) \\vee (a? \\leftarrow b)$ (с. 133)"),
        ("«$(a? \\leftarrow b) \\vdash (a \\urcorner\\!\\leftarrow b)$: неопределённость означает отсутствие признака»", "по A5 из $(a? \\leftarrow b)$ "
         "следует $\\sim(a \\urcorner\\!\\leftarrow b)$; формула студента не тавтология (с. 132–133)")]


def e801c(lvl, sec=1):
    for _ in range(800):
        p, q = p_rand(1), p_rand(2)
        if ptaut(p, q, "+n") and not ptaut(p, q, "+nq") and repr(("e", p, q)) not in USED:
            USED.add(repr(("e", p, q)))
            break
    return card(8, sec, lvl, "E", "open", f"{PP} Студент: «${FT(p, q)}$ доказуема в $S^s_p$: если отождествить $(a \\urcorner\\!\\leftarrow b)$ с "
                "$\\sim(a \\leftarrow b)$, получается тавтология». Найдите ошибку.", "Неверно: так рассуждают в классическом случае (§ 3); в $S^s_p$ "
                "при истинном $(a? \\leftarrow b)$ посылка истинна, а заключение ложно — формула не тавтология и по MT1 § 2 недоказуема.",
                "Гл. 8, § 2–3 (с. 133–134).", "с. 133–134, гл. 8, § 2–3", "предикация, диагностика", system="S^s_p")


def e801(lvl, sec=1):
    if rnd.random() < 0.4:
        return e801c(lvl, sec)
    s, w = rnd.choice(E801)
    return card(8, sec, lvl, "E", "open", f"{PP} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 8, § 1–2.", "с. 132–134, гл. 8, § 1–2",
                "предикация, диагностика", system="S^s_p")


def m801(lvl, d, i):
    if d:
        return e801(lvl)
    if lvl == 1:
        return ap_rec(1)
    if lvl == 2:
        return [ap_rec, tp_rec, tp5_rec][i % 3](2, "C" if i % 3 else "R")
    if lvl == 3:
        return [tp_rec, tp5_rec, p_deriv, ap_rec][i % 4](3) if i % 4 != 3 else ap_rec(3, "C")
    if lvl == 4:
        return p_deriv(4) if i % 2 == 0 else tp5_rec(4)
    if lvl in (5, 6):
        return p_taut_card(lvl)
    return p_taut_card(7, typ="S")


INT8 = [("$(a \\leftarrow b)$ приписано 1", "$(a \\urcorner\\!\\leftarrow b)$ — 0", "1"),
        ("$(a \\urcorner\\!\\leftarrow b)$ приписано 1", "$(a \\leftarrow b)$ — 0", "1"),
        ("$(a \\leftarrow b)$ приписано 0", "значение $(a \\urcorner\\!\\leftarrow b)$ остаётся неопределённым (независимым от первого)", "2"),
        ("нужно значение $(a? \\leftarrow b)$", "оно равно значению $\\sim(a \\leftarrow b)\\sim(a \\urcorner\\!\\leftarrow b)$", "3")]


def m802(lvl, d, i):
    if d:
        return e801(lvl, 2).replace("гл. 8, § 1–2\"", "гл. 8, § 2\"")
    if lvl in (1, 2):
        its = rnd.sample(INT8, 3)
        return card(8, 2, lvl, "R" if lvl == 1 else "C", "iso", f"{PP} Что следует по интерпретации § 2 гл. 8 (с. 133)? Укажите пункт.\n\n" +
                    items([s for s, _, _ in its]), answers([f"{a} (п. {n})" for _, a, n in its]), "С. 133.", "с. 133, гл. 8, § 2", "предикация, интерпретация")
    if lvl == 3:
        return p_taut_card(3, 2)
    if lvl == 4:
        return card(8, 2, 4, "C", "iso", f"{PP} По второй интерпретации (с. 133) $(a \\urcorner\\!\\leftarrow b)$ равнозначно $\\sim(a \\leftarrow b)x$, где "
                    "$x$ — элементарное высказывание, не входящее в формулу. Найдите значение $(a \\urcorner\\!\\leftarrow b)$, если $(a \\leftarrow b) = 1$.",
                    "0 — независимо от значения $x$.", "С. 133–134: $\\sim(a \\leftarrow b) = 0$, значит, $\\sim(a \\leftarrow b)x = 0$.", "с. 133–134, гл. 8, § 2",
                    "предикация, интерпретация")
    if lvl == 5:
        return card(8, 2, 5, "C", "open", f"{PP} По второй интерпретации покажите, что при $(a \\leftarrow b) = 0$ высказывание $(a \\urcorner\\!\\leftarrow b)$ "
                    "может принять и значение 1, и значение 0.", "$\\sim(a \\leftarrow b) = 1$, и $\\sim(a \\leftarrow b)x$ зависит только от $x$: при "
                    "$x = 1$ — 1, при $x = 0$ — 0.", "С. 134.", "с. 133–134, гл. 8, § 2", "предикация, интерпретация")
    if lvl == 6:
        return p_taut_card(6, 2)
    return card(8, 2, 7, "S", "transfer", f"{PP} Сравните неклассический и классический случаи для формулы $\\sim(a \\urcorner\\!\\leftarrow b) \\vdash (a \\leftarrow b)$.",
                "Неклассический ($S^s_p$): недоказуема, не тавтология (MT2 § 2); классический: доказуема — отрицания совпадают (§ 3).",
                "С. 134.", "с. 134, гл. 8, § 2–3", "предикация, интерпретация")


def m803(lvl, d, i):
    if d:
        s, w = rnd.choice([("«В классическом случае теория предикации нужна, чтобы различать $\\sim$ и $\\urcorner$»", "в классическом случае она "
                            "излишня: отрицания совпадают, неопределённость исключается (с. 134)"),
                           ("«Классический случай получается добавлением к A1–A6 схемы $\\sim(a \\leftarrow b) \\vdash (a? \\leftarrow b)$»", "добавляется "
                            "$(a \\urcorner\\!\\leftarrow b) \\vdash \\sim(a \\leftarrow b)$ (с. 134)")])
        return card(8, 3, lvl, "E", "open", f"{PP} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 8, § 3.", "с. 134, гл. 8, § 3",
                    "предикация, классический случай, диагностика")
    if lvl == 2:
        return card(8, 3, 2, "R", "iso", f"{PP} Какой вид принимают аксиомные схемы A1–A6 в классическом случае (§ 3 гл. 8)?",
                    "$(a \\leftarrow b) \\dashv\\vdash \\sim\\sim(a \\leftarrow b)$ и $\\sim(a \\leftarrow b) \\dashv\\vdash \\sim(a \\leftarrow b)$.", "С. 134.",
                    "с. 134, гл. 8, § 3", "предикация, классический случай")
    if lvl == 3:
        return card(8, 3, 3, "D", "iso", f"{PP} Какую схему можно добавить к A1–A6, чтобы получить тот же эффект, что и в классическом случае?",
                    "$(a \\urcorner\\!\\leftarrow b) \\vdash \\sim(a \\leftarrow b)$.", "С. 134.", "с. 134, гл. 8, § 3", "предикация, классический случай")
    return p_taut_card(lvl, 3, classical=True, typ="S" if lvl == 7 else "C")


BAS8 = [("(a \\leftarrow b) \\vdash \\sim(a \\urcorner\\!\\leftarrow b)", "$a \\vdash b$"), ("(a \\leftarrow b)(a? \\leftarrow c) \\vdash \\sim(a \\leftarrow c)", "$ab \\vdash c$"),
        ("(a \\urcorner\\!\\leftarrow b) \\vdash \\sim(a \\leftarrow b)\\sim(a? \\leftarrow b)", "$c \\vdash ab$"),
        ("(a \\leftarrow b) \\vee (a? \\leftarrow b) \\vdash \\sim(a \\urcorner\\!\\leftarrow b)", "$a \\vee b \\vdash c$"),
        ("\\sim(a \\leftarrow b) \\vdash (a \\urcorner\\!\\leftarrow b) \\vee (a? \\leftarrow b)", "$c \\vdash a \\vee b$"),
        ("\\vdash \\sim((a \\leftarrow b)(a \\urcorner\\!\\leftarrow b))", "$\\vdash z$")]


def m804(lvl, d, i):
    if d:
        s, w = rnd.choice([("«По MT1 § 4 любая базисная тавтология $x \\vdash y$ доказуема в $S^s_p$»", "требуется, чтобы в $x$ и $y$ входили "
                            "одинаковые элементарные для теории предикации высказывания (с. 135)"),
                           ("«Базисная формула $\\vdash z$ — тавтология, значит, она доказуема в $S^s_p$»", "по MT1 § 4 она доказуема в $S^5_p$ (с. 135); "
                            "в $S^s_p$ нет формул вида $\\vdash z$")])
        return card(8, 4, lvl, "E", "open", f"{PP} Студент: {s}. Найдите ошибку.", f"Неверно: {w}.", "Гл. 8, § 4.", "с. 134–135, гл. 8, § 4",
                    "предикация, полнота, диагностика", system="S^s_p")
    if lvl in (3, 4):
        its = rnd.sample(BAS8, 3)
        return card(8, 4, lvl, "C", "iso", f"{PP}; $c$ — термин. К какому виду базисных формул (D1 § 4 гл. 8, с. 134–135) относится каждая формула?\n\n" +
                    items([f"${s}$" for s, _ in its]), answers([k for _, k in its]), "D1: $a, b, c$ — элементарные для теории предикации "
                    "высказывания, их отрицания (внешние и внутренние) и неопределённые формы.", "с. 134–135, гл. 8, § 4", "предикация, полнота")
    its = []
    for _ in range(3):
        p, q = p_rand(1), p_rand(1)
        its.append((p, q))
    return card(8, 4, lvl, "S" if lvl == 7 else "C", "open", f"{PP} Базисные формулы. Доказуемы ли они в $S^s_p$ по MT1 § 4 (тавтология и одинаковые "
                "элементарные высказывания в посылке и заключении)?\n\n" + items([f"${FT(p, q)}$" for p, q in its]),
                answers(["да" if ptaut(p, q) else "нет" for p, q in its]), "MT1 § 4 (с. 135); MT1 § 2 (с. 134): доказуемые формулы — тавтологии. "
                "Ровно одно из $(a \\leftarrow b)$, $(a \\urcorner\\!\\leftarrow b)$, $(a? \\leftarrow b)$ истинно.", "с. 134–135, гл. 8, § 2, 4",
                "предикация, полнота", system="S^s_p")


def m805(lvl, d, i):
    v_ = {2: ("Что означает по D2 § 5 гл. 8 (с. 135), что предикат $b$ дедуктивно включается в $c$?",
              "Доказуема $(a \\leftarrow c) \\vdash (a \\leftarrow b)$.", "D2, с. 135."),
          3: ("Предикаты «квадрат» ($b$) и «прямоугольник» ($c$): доказуема $(a \\leftarrow b) \\vdash (a \\leftarrow c)$ и недоказуема обратная. Какие "
              "определения § 5 гл. 8 применимы к паре $b$, $c$?", "$b$ и $c$ дедуктивно связаны (D1); $c$ дедуктивно включается в $b$ (D2); $b$ "
              "дедуктивно сильнее $c$ (D4); не эквивалентны (D3).", "D1–D4, с. 135."),
          4: ("Что нужно доказать, чтобы установить, что предикат $b$ дедуктивно категорически сильнее $c$ (D5), в неклассическом и в "
              "классическом случае?", "Неклассический: $(a \\leftarrow b) \\vdash (a \\leftarrow c)$, $(a \\urcorner\\!\\leftarrow c) \\vdash (a \\urcorner\\!\\leftarrow b)$ "
              "и $(a? \\leftarrow c) \\vdash \\sim(a \\leftarrow b)$; классический: $(a \\leftarrow b) \\vdash (a \\leftarrow c)$ и $\\sim(a \\leftarrow c) \\vdash \\sim(a \\leftarrow b)$.",
              "D5, с. 135.")}[lvl]
    return card(8, 5, lvl, {2: "R", 3: "C", 4: "D"}[lvl], "iso", v_[0], v_[1], v_[2], "с. 135, гл. 8, § 5", "предикация, дедуктивные связи",
                form="nat" if lvl == 3 else "sym")


# ---------------------------------------------------------------- ручные ступени 8–10
H = []


def hand(ch, sec, lvl, cond, ans, sol, src, tags, system=None, typ=None):
    H.append(card(ch, sec, lvl, typ or ("I" if lvl == 10 else "M"), "transfer", cond, ans, sol, src, tags, form="meta", answ="proof",
                  system=system, gen=False))


def hand_cards():
    s = "S^s_cq"
    # 07.05: L8 3, L9 2, L10 1
    hand(7, 5, 8, "Покажите, что при семантических правилах для A1 (исключающее правило, затем общее, с. 101) все аксиомы $S^s_{cq}$, кроме A1, "
         "имеют значение 1.", "В A2–A7 ни один термин не входит свободно в заключение, не входя свободно в посылку; по общему правилу их "
         "значения — значения бескванторных форм $x \\vdash x$, $xy \\vdash xy$, $x \\vee y \\vdash x \\vee y$, $x \\vdash \\sim\\sim x$, $\\sim\\sim x \\vdash x$ — 1.",
         "С. 101; бескванторные формы — с. 101 (§ 4).", "с. 101–102, гл. 7, § 4–5", "кванторы, независимость", s)
    hand(7, 5, 8, "Покажите, что при семантических правилах для A2 правило R1 (если $x \\vdash y$, то $(\\forall a)x \\vdash (\\forall a)y$) из формул со "
         "значением 1 даёт формулы со значением 1.", "R1 не меняет свободных вхождений, кроме вхождений $a$, которые в обеих частях "
         "становятся связанными; если исключающее правило не применялось к $x \\vdash y$, то оно не применяется и к результату, а "
         "бескванторная форма не меняется.", "С. 101–102.", "с. 101–102, гл. 7, § 5", "кванторы, независимость", s)
    hand(7, 5, 8, "Разберите пример с. 102: почему формула $(\\forall b)((b \\leftarrow c)(b \\leftarrow d)) \\vdash (\\forall b)(b \\leftarrow c)$ доказуема в "
         "$S^s_{cq}$ с помощью R1 и почему по правилу для R1 она имеет значение 0?", "Из $zv \\vdash z$ ($S^s$) по R1. По исключающему "
         "правилу для R1: $(\\forall b)zv = 1$, а в $z = (b \\leftarrow c)$ есть термин $c$, отсутствующий в $v = (b \\leftarrow d)$, значит "
         "$(\\forall b)z = 0$.", "С. 102.", "с. 102, гл. 7, § 5", "кванторы, независимость", s)
    hand(7, 5, 9, "Докажите: при правилах для A1 значение 1 сохраняется правилами $S^s$ (транзитивность). Указание: проследите свободные "
         "вхождения терминов в $x$, $y$, $z$ для $x \\vdash y$, $y \\vdash z$ и $x \\vdash z$.", "Если термин свободен в $z$ и не свободен в "
         "$x$, то он либо не свободен в $y$ (тогда $y \\vdash z$ имеет значение 0), либо свободен в $y$ (тогда $x \\vdash y$ — 0); иначе — по "
         "общему правилу транзитивность сохраняется для бескванторных форм.", "С. 101.", "с. 101, гл. 7, § 5", "кванторы, независимость", s)
    hand(7, 5, 9, "По правилу для A5 (с. 101) ограничение на вхождение $a$ в $x$ отбрасывается. Объясните, как это правило служит доказательству независимости A5: что должно выполняться для прочих аксиомных схем и правил и что — для A5?",
         "Критерии: правило для A5 отбрасывает ограничение (с. 101); "
         "показано, что аксиомы, кроме A5, и правила сохраняют избранное свойство, а A5 — нет.", "С. 101.", "с. 101, гл. 7, § 5",
         "кванторы, независимость", s)
    hand(7, 5, 10, "Исследуйте, можно ли доказать независимость A6 и A7 без исключающих правил, только с помощью интерпретационной формы § 7.",
         "Критерии: замечено, что A6, A7 — тавтологии и при интерпретации § 7 их значение 1; поэтому нужна интерпретация, при которой "
         "они ложны; разобраны правила с. 101.", "С. 101, 105.", "с. 101, 105, гл. 7, § 5, 7", "кванторы, независимость", s)
    # 07.06: L8, L9
    hand(7, 6, 8, "По образцу доказательства MT*1 (с. 103) докажите MT*2: если $x \\vdash y$ доказуема и множества элементарных высказываний $x$ "
         "и $y$ совпадают, то доказуема $\\sim(\\exists a)y \\vdash \\sim(\\exists a)x$.", "По T3–T9 $\\sim y \\vdash \\sim x$; по R1 "
         "$(\\forall a)\\sim y \\vdash (\\forall a)\\sim x$; по A6, A7 — $\\sim(\\exists a)\\sim\\sim y \\vdash \\sim(\\exists a)\\sim\\sim x$ и замена $\\sim\\sim$.",
         "С. 103: «аналогично для MT*2 (только используется R1, A6 и A7)».", "с. 103, гл. 7, § 6", "кванторы, метатеоремы", s)
    hand(7, 6, 9, "Докажите MT3 § 6 из MT1 и MT2: если $x \\vdash y \\vee z$ и $z \\vdash v$ доказуемы и множества элементарных высказываний "
         "совпадают, то $x \\vdash y \\vee v$ доказуема.", "По MT2: $\\sim v \\vdash \\sim z$ и $\\sim(y \\vee z) \\vdash \\sim x$; по $S^s$: "
         "$\\sim y \\sim v \\vdash \\sim y\\sim z$; транзитивность — $\\sim y\\sim v \\vdash \\sim x$; по MT2 — $x \\vdash \\sim(\\sim y\\sim v)$, то есть $x \\vdash y \\vee v$.",
         "С. 103: «следствие MT1 и MT2».", "с. 102–103, гл. 7, § 6", "кванторы, метатеоремы", s)
    # 07.07: L8, L9
    hand(7, 7, 8, "Докажите, что A3 $(\\forall a)x(\\exists a)y \\vdash (\\exists a)(xy)$ при $x = (a \\leftarrow b)$, $y = (a \\leftarrow c)$ — тавтология "
         "при любом числе $n$ отмеченных терминов.", "Интерпретационная форма: $\\prod_i (ia \\leftarrow b) \\cdot \\bigvee_j (ja \\leftarrow c) \\vdash "
         "\\bigvee_k (ka \\leftarrow b)(ka \\leftarrow c)$. Если посылка истинна, найдётся $j$ с $(ja \\leftarrow c) = 1$; так как $(ja \\leftarrow b) = 1$, "
         "истинен член $k = j$.", "D2, D3 § 7 (с. 105).", "с. 105, гл. 7, § 7", "кванторы, интерпретация")
    hand(7, 7, 9, "Докажите по прямой интерпретации (с. 106), что A1 $(\\forall a)x \\vdash x$ — тавтология (D*3).", "Если посылке приписано 1, "
         "по п. 1 и $x$ приписывается 1, значит, заключение 1; иных комбинаций со значением посылки 1 правила не допускают.", "С. 106.",
         "с. 106, гл. 7, § 7", "кванторы, интерпретация")
    # 07.08: L8 11, L9 8, L10 3
    for n_ in (3, 4):
        zs = "".join(f"z^{j}" for j in range(1, n_ + 1))
        steps = [f"(\\forall a)z^1(\\forall a)z^2 \\vdash (\\forall a)(z^1z^2)"]
        acc = "z^1z^2"
        for j in range(3, n_ + 1):
            steps.append(f"(\\forall a)({acc})(\\forall a)z^{j} \\vdash (\\forall a)(({acc})z^{j})")
            acc = f"({acc})z^{j}"
        hand(7, 8, 8, f"По образцу доказательства MT3 (с. 111) докажите доказуемость в $S^s_{{cq}}$ формулы " +
             "$" + "".join(f"(\\forall a)z^{j}" for j in range(1, n_ + 1)) + f" \\vdash (\\forall a)({zs})$.",
             "Последовательно доказуемы: " + "; ".join(f"${s_}$" for s_ in steps) + " (T19 § 6); по $S^s$ (R1, R2 и замена равнозначных) — "
             "искомая формула.", "С. 111.", "с. 111, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "По образцу доказательства MT4 (с. 112) докажите доказуемость $(\\forall a)(z^1 \\vee z^2 \\vee z^3) \\vdash (\\forall a)z^1 \\vee (\\exists a)z^2 \\vee (\\exists a)z^3$.",
         "K$^1 = \\forall$: берём $(\\forall a)(z^1 \\vee (z^2 \\vee z^3)) \\vdash (\\forall a)z^1 \\vee (\\exists a)(z^2 \\vee z^3)$ (A4); далее $(\\exists a)(z^2 \\vee z^3) "
         "\\vdash (\\exists a)z^2 \\vee (\\exists a)z^3$ (T22); по MT1 § 6 — искомая.", "С. 112.", "с. 112, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "По образцу MT4 (с. 112) докажите $(\\forall a)(z^1 \\vee z^2 \\vee z^3) \\vdash (\\exists a)z^1 \\vee (\\forall a)z^2 \\vee (\\exists a)z^3$.",
         "K$^1 = \\exists$: $(\\forall a)(z^1 \\vee (z^2 \\vee z^3)) \\vdash (\\exists a)z^1 \\vee (\\forall a)(z^2 \\vee z^3)$ (T32); для $(\\forall a)(z^2 \\vee z^3)$ — "
         "A4: $\\vdash (\\forall a)z^2 \\vee (\\exists a)z^3$; MT1 § 6.", "С. 112: «во втором случае проделываем то же… для $(\\forall a)(z^2 \\vee \\ldots \\vee z^n)$».",
         "с. 112, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "По образцу MT4 (с. 112–113) докажите $(\\exists a)(z^1 \\vee z^2 \\vee z^3) \\vdash (\\exists a)z^1 \\vee (\\exists a)z^2 \\vee (\\exists a)z^3$.",
         "$(\\exists a)(z^1 \\vee (z^2 \\vee z^3)) \\vdash (\\exists a)z^1 \\vee (\\exists a)(z^2 \\vee z^3)$ (T22); $(\\exists a)(z^2 \\vee z^3) \\vdash (\\exists a)z^2 \\vee (\\exists a)z^3$ "
         "(T22); MT1 § 6.", "С. 113.", "с. 112–113, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "По образцу MT5 (с. 113) докажите $(\\forall a)z^1 \\vee (\\forall a)z^2 \\vee (\\forall a)z^3 \\vdash (\\forall a)(z^1 \\vee z^2 \\vee z^3)$.",
         "$(\\forall a)z^2 \\vee (\\forall a)z^3 \\vdash (\\forall a)(z^2 \\vee z^3)$ (T24), отсюда $(\\forall a)z^1 \\vee (\\forall a)z^2 \\vee (\\forall a)z^3 \\vdash "
         "(\\forall a)z^1 \\vee (\\forall a)(z^2 \\vee z^3)$ ($S^s$); снова T24: $\\vdash (\\forall a)(z^1 \\vee (z^2 \\vee z^3))$; $S^s$.", "С. 113.",
         "с. 113, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "По образцу MT2 (с. 111) докажите $(\\forall a)(z^1z^2z^3) \\vdash (\\forall a)z^1(\\exists a)z^2(\\forall a)z^3$.",
         "Формулы $A^i$: $(\\forall a)(z^1z^2z^3) \\vdash (\\forall a)z^1$, $\\vdash (\\exists a)z^2$, $\\vdash (\\forall a)z^3$ — тавтологии. Каждая сводится к "
         "$B^i$: $(\\forall a)(z^i(z_1z_2)) \\vdash (K^ia)z^i$, которая следует из базисной $(\\forall a)(z^i(z_1z_2)) \\vdash (K^ia)z^i(\\forall a)(z_1z_2)$ (MT1); "
         "R3 (объединение заключений) даёт формулу.", "С. 111.", "с. 111, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "По образцу MT6 (с. 114), случай 3, докажите $(\\forall a)(\\exists b)(\\forall c)(\\exists d)z \\vdash (\\forall a)(\\forall c)(\\exists b)(\\exists d)z$, "
         "считая её тавтологией.", "Отличие — порядок двух средних кванторов; базисная тавтология $(\\exists b)(\\forall c)(\\exists d)z \\vdash (\\forall c)(\\exists b)(\\exists d)z$ "
         "(T15 при $x = (\\exists d)z$); по R1 с $a$ — искомая.", "С. 114.", "с. 114, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "По образцу MT6 (с. 114), случай 4, докажите $(\\forall a)(\\forall b)(\\forall c)z \\vdash (\\forall c)(\\forall b)(\\forall a)z$.",
         "Цепочка перестановок двух соседних кванторов: $(\\forall a)(\\forall b)(\\forall c)z \\vdash (\\forall b)(\\forall a)(\\forall c)z \\vdash (\\forall b)(\\forall c)(\\forall a)z \\vdash "
         "(\\forall c)(\\forall b)(\\forall a)z$; каждая — базисная тавтология (T14), при необходимости под R1; транзитивность $S^s$.", "С. 114.",
         "с. 114, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "Восстановите рассуждение для случая $2 \\vdash 2$ доказательства MT7 (с. 115) при одинаковых $a$ и $b$.", "$(\\forall a)z \\vdash (\\forall a)v$ "
         "— тавтология лишь при условии, что $z \\vdash v$ — тавтология; если $z \\vdash v$ доказуема, то формула доказуема по R1.", "С. 115.",
         "с. 115, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 8, "Восстановите рассуждение для случая $3 \\vdash 3$ доказательства MT7 (с. 116) при одинаковых $a$ и $b$.", "Тавтология лишь при "
         "условии, что $z \\vdash v$ — тавтология; если она доказуема, $(\\exists a)z \\vdash (\\exists a)v$ доказуема по R2.", "С. 116.",
         "с. 116, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 9, "Докажите: если K есть $\\exists$, то $(\\exists a)(z^1z^2) \\vdash (K^1a)z^1(K^2a)z^2$ — тавтология лишь при K$^1$ = K$^2$ = $\\exists$. "
         "Используйте интерпретационную форму при двух отмеченных терминах.", "Для $(\\exists a)(z^1z^2) \\vdash (\\forall a)z^1$: $z^1(1a)z^2(1a) = 1$, "
         "$z^1(2a) = 0$ — посылка 1, заключение 0; аналогично для K$^2$. При $\\exists$, $\\exists$ — T21.", "С. 105, 110–111.", "с. 105, 110–111, гл. 7, § 7–8",
         "кванторы, полнота", s)
    hand(7, 8, 9, "Докажите утверждение из MT4 (с. 112): при K $= \\forall$ формула $(\\forall a)(z^1 \\vee z^2 \\vee z^3) \\vdash (\\forall a)z^1 \\vee (\\forall a)z^2 \\vee (\\exists a)z^3$ "
         "не тавтология (два K$^i$ суть $\\forall$). Используйте два отмеченных термина.", "Пусть $z^1(1a) = 1$, $z^2(2a) = 1$, остальные 0 и $z^3 = 0$: "
         "посылка 1 (в каждом $ia$ истинен член дизъюнкции), $(\\forall a)z^1 = 0$, $(\\forall a)z^2 = 0$, $(\\exists a)z^3 = 0$.", "С. 112: «в чём легко "
         "убедиться, допустив два отмеченных термина».", "с. 105, 112, гл. 7, § 7–8", "кванторы, полнота", s)
    hand(7, 8, 9, "Докажите утверждение из MT5 (с. 113): при K $= \\forall$ формула $(\\forall a)z^1 \\vee (\\exists a)z^2 \\vee (\\forall a)z^3 \\vdash (\\forall a)(z^1 \\vee z^2 \\vee z^3)$ "
         "не тавтология.", "При двух отмеченных терминах: $z^2(1a) = 1$, остальное 0: посылка 1 ($(\\exists a)z^2$), а $z^1(2a) \\vee z^2(2a) \\vee z^3(2a) = 0$ — "
         "заключение 0.", "С. 113: «в чём легко убедиться на примере случая двух отмеченных терминов и $n = 3$».", "с. 105, 113, гл. 7, § 7–8",
         "кванторы, полнота", s)
    hand(7, 8, 9, "Докажите, что из подслучаев случая 1 MT1 § 8 (с. 108) формулы $(\\forall a)\\sim y \\vdash y$ и $(\\exists a)\\sim y \\vdash y$ не "
         "тавтологии, а $(\\forall a)y \\vdash y$ — тавтология ($y$ содержит $a$ свободно).", "При одном отмеченном термине обе первые формулы "
         "дают $\\sim y(1a) \\vdash y(1a)$ — при $y(1a) = 0$ посылка 1, заключение 0. Для $(\\forall a)y \\vdash y$ по п. 1 D2 получаем "
         "$(\\forall a)y \\vdash (\\forall a)y$ или $(\\exists a)(\\forall a)y \\vdash (\\exists a)y$, то есть (п. 2) $(\\forall a)y \\vdash (\\exists a)y$ — тавтологии "
         "при любом $n \\geq 1$; доказуема по A1.", "С. 105, 108.", "с. 105, 108, гл. 7, § 7–8", "кванторы, полнота", s)
    hand(7, 8, 9, "Докажите, что из подслучаев случая 3 MT1 § 8 (с. 109) формула $(\\exists a)z \\vdash (\\forall a)z$ не тавтология, а $(\\forall a)z \\vdash (\\exists a)z$ — "
         "тавтология ($z = (a \\leftarrow b)$).", "При двух отмеченных терминах: $(1a \\leftarrow b) \\vee (2a \\leftarrow b) \\vdash (1a \\leftarrow b)(2a \\leftarrow b)$ — "
         "при $(1a \\leftarrow b) = 1$, $(2a \\leftarrow b) = 0$ ложна. Обратная: конъюнкция влечёт дизъюнкцию при любом $n \\geq 1$; доказуема (T27).",
         "С. 105, 109.", "с. 105, 109, гл. 7, § 7–8", "кванторы, полнота", s)
    hand(7, 8, 9, "Докажите, что из подслучаев случая 2 MT1 § 8 только $x \\vdash (\\exists a)x$ — тавтология, а $x \\vdash (\\forall a)x$ (при свободном $a$) — нет.",
         "При $x = (a \\leftarrow b)$ по D2 п. 1 формула заменяется на $(\\forall a)x \\vdash (\\forall a)(\\forall a)x$ или $(\\exists a)x \\vdash (\\exists a)(\\forall a)x$; "
         "во втором варианте при двух отмеченных терминах $x(1a) = 1$, $x(2a) = 0$ посылка 1, заключение 0.", "С. 105, 108.", "с. 105, 108, гл. 7, § 7–8",
         "кванторы, полнота", s)
    hand(7, 8, 9, "Докажите, что базисные формулы с отрицанием перед квантором сводятся к формулам 1–8 без таких отрицаний (с. 108).", "Используются "
         "доказуемые $(\\forall a)x \\dashv\\vdash \\sim(\\exists a)\\sim x$, $(\\exists a)x \\dashv\\vdash \\sim(\\forall a)\\sim x$, $\\sim\\sim x \\dashv\\vdash x$ и законы де Моргана; "
         "отрицание переносится внутрь, меняя квантор.", "С. 108.", "с. 108, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 9, "Докажите, что формулы $(Ka)x \\dashv\\vdash x$ и $(K^1a)x \\dashv\\vdash (K^2a)x$ доказуемы, если $a$ не входит свободно в $x$ (с. 108).",
         "$(\\forall a)x \\vdash x$ (A1), $x \\vdash (\\forall a)x$ (T17); $x \\vdash (\\exists a)x$ (A2), $(\\exists a)x \\vdash x$ (T18); отсюда и вторая пара "
         "транзитивностью.", "С. 104, 108.", "с. 104, 108, гл. 7, § 6, 8", "кванторы, полнота", s)
    hand(7, 8, 10, "Проверьте доказательство MT1 § 8 в случае 6 (с. 109–110): постройте для каждого из восьми подслучаев интерпретационную "
         "форму при двух отмеченных терминах и сравните с утверждением книги.", "Критерии: восемь форм построены верно; для нетавтологий даны "
         "контрпримеры; совпадение с с. 110 (тавтологии — 1, 5, 6, 7).", "С. 109–110.", "с. 105, 109–110, гл. 7, § 7–8", "кванторы, полнота", s)
    hand(7, 8, 10, "Исследуйте случай 8 MT1 § 8 для трёх кванторов: какие перестановки $(K^1a)(K^2b)(K^3c)z \\vdash \\ldots$ дают тавтологии? Сформулируйте "
         "закономерность.", "Критерии: использованы случай 8 (с. 110) и MT6; закономерность сформулирована (перестановка $\\exists$ влево через $\\forall$ "
         "недопустима) и проверена на интерпретационных формах.", "С. 110, 114.", "с. 110, 114, гл. 7, § 8", "кванторы, полнота", s)
    hand(7, 8, 10, "Оцените, насколько полно доказательство MT7 § 8 (с. 114–116) охватывает случаи $i \\vdash k$: составьте таблицу 5×5 со ссылками "
         "на книгу.", "Критерии: все 25 клеток; для каждой — «теорема $S^s$», «базисный», «MT2–MT5», «исключается» или разбор с условием; "
         "ссылки на с. 115–116.", "С. 114–116.", "с. 114–116, гл. 7, § 8", "кванторы, полнота", s)
    # 07.09: L8 9, L9 6, L10 2
    for (case, txt, ans_) in [
        ("$1 \\vdash 2$", "$x \\vdash (\\forall b)v$", "тавтология лишь при условии, что $b$ не входит свободно в $v$; если при этом $x \\vdash v$ доказуема, то "
         "формула доказуема в силу T17 § 6"),
        ("$1 \\vdash 3$", "$x \\vdash (\\exists b)v$", "если $x \\vdash v$ доказуема, формула доказуема в силу A2"),
        ("$1 \\vdash 4$", "$x \\vdash v^1 \\vee \\ldots \\vee v^m$", "тавтология, если и только если найдётся $v^i$ с тавтологией $x \\vdash v^i$; если она "
         "доказуема, то по $S^s$ доказуема формула"),
        ("$1 \\vdash 5$", "$x \\vdash v^1 \\cdot \\ldots \\cdot v^m$", "тавтология, если и только если все $x \\vdash v^i$ — тавтологии; если они доказуемы, "
         "формула доказуема по $S^s$"),
        ("$2 \\vdash 1$", "$(\\forall a)z \\vdash x$", "если $z \\vdash x$ доказуема, то формула доказуема в силу A1"),
        ("$4 \\vdash 1$", "$z^1 \\vee \\ldots \\vee z^n \\vdash y$", "тавтология при условии, что каждая $z^i \\vdash y$ — тавтология; если все они доказуемы, "
         "формула доказуема по MT2 § 6 и $S^s$"),
        ("$5 \\vdash 1$", "$z^1 \\cdot \\ldots \\cdot z^n \\vdash y$", "тавтология при условии, что найдётся $z^i$ с тавтологией $z^i \\vdash y$; если она "
         "доказуема, формула доказуема по $S^s$"),
        ("$2 \\vdash 4$", "$(\\forall a)z \\vdash v^1 \\vee \\ldots \\vee v^m$", "тавтология при условии, что найдётся $w$: $z \\vdash w$ — тавтология, "
         "$(\\forall a)w \\vdash (v^1 \\vee \\ldots \\vee v^m)$ — тавтология из числа $2 \\vdash 4$ MT7 § 8; если обе доказуемы, формула доказуема по $S^s$"),
        ("$4 \\vdash 2$", "$z^1 \\vee \\ldots \\vee z^n \\vdash (\\forall b)v$", "тавтология при условии, что найдётся $w$: $w \\vdash v$ — тавтология, а "
         "$z^1 \\vee \\ldots \\vee z^n \\vdash (\\forall b)w$ — тавтология из числа $4 \\vdash 2$ MT7 § 8; если обе доказуемы — доказуема")]:
        hand(7, 9, 8, f"Восстановите рассуждение доказательства MT5 § 9 (с. 118–119) для случая {case}: ${txt}$.", ans_[0].upper() + ans_[1:] + ".",
             "С. 118–119.", "с. 118–119, гл. 7, § 9", "кванторы, разрешимость", s)
    hand(7, 9, 9, "Докажите MT1 § 9 (с. 117): если контрольная форма $x^* \\vdash y^*$ — тавтология, то $x \\vdash y$ — тавтология.", "Контрольная "
         "форма получается заменой $\\sim a$ элементарным $b$, не входящим в формулу. Если $x^* \\vdash y^*$ — 1 при всех значениях $a$, $b$, то и при "
         "$b = \\sim a$, то есть $x \\vdash y$ — тавтология.", "С. 117.", "с. 117, гл. 7, § 9", "кванторы, разрешимость", s)
    hand(7, 9, 9, "Приведите пример, показывающий, что обращение MT1 § 9 неверно («но не всегда наоборот», с. 117).", "Например, $(a \\leftarrow b) \\vee "
         "\\sim(a \\leftarrow b)$ в заключении: $x \\vdash (a \\leftarrow b) \\vee \\sim(a \\leftarrow b)$ при $x$ без кванторов — тавтология, а после замены "
         "$\\sim(a \\leftarrow b)$ новым элементарным $d$ получаем $x \\vdash (a \\leftarrow b) \\vee d$ — не тавтология (такие формулы и выделяются п. 2 D1).",
         "С. 116–117.", "с. 116–117, гл. 7, § 9", "кванторы, разрешимость", s)
    hand(7, 9, 9, "Докажите сведение второго случая MT5 § 9 к первому (с. 118): если $x^* \\vdash y^*$ доказуема, а $y^* \\vdash x^*$ нет, рассмотрите "
         "$x \\vdash yx$.", "Если $x \\vdash y$ — тавтология, то $x \\vdash yx$ — тавтология, и наоборот; $x^* \\vdash y^*x^*$ доказуема и $y^*x^* \\vdash x^*$ "
         "доказуема — множества элементарных высказываний совпадают (первый случай); из доказуемости $x \\vdash yx$ следует доказуемость $x \\vdash y$.",
         "С. 118.", "с. 118, гл. 7, § 9", "кванторы, разрешимость", s)
    hand(7, 9, 9, "Докажите MT6 § 9 из MT1–MT5.", "Если контрольная форма $x^* \\vdash y^*$ — тавтология, то по MT1 $x \\vdash y$ — тавтология; если "
         "бескванторная форма $x^{**} \\vdash y^{**}$ доказуема в $S^s$, то по MT5 (для формулы, совпадающей со своей контрольной формой) "
         "доказуема контрольная форма, а по MT4 — сама формула.", "С. 119–120.", "с. 117–120, гл. 7, § 9", "кванторы, разрешимость", s)
    hand(7, 9, 9, "Докажите MT4 § 9: если доказуема контрольная форма, то доказуема и формула.", "Доказательство $x^* \\vdash y^*$ превращается в "
         "доказательство $x \\vdash y$ заменой элементарных высказываний, подставленных вместо $\\sim a$, обратно на $\\sim a$ (подстановка сохраняет "
         "доказуемость, ср. MT1 § 19).", "С. 117.", "с. 117, гл. 7, § 9", "кванторы, разрешимость", s)
    hand(7, 9, 9, "Объясните, почему процедура § 9 (с. 120) осуществима для любой формулы: обоснуйте конечность каждого шага.", "Шаг 1: "
         "бескванторная форма строится конечным числом исключений; доказуемость в $S^s$ решается критерием гл. 5. Шаг 2: контрольная форма — "
         "конечная замена; тавтологичность устанавливается интерпретацией (§ 7: число отмеченных терминов не ограничено, но доказательство "
         "проводится индукцией, с. 106).", "С. 106, 120.", "с. 106, 120, гл. 7, § 7, 9", "кванторы, разрешимость", s)
    hand(7, 9, 10, "Примените процедуру § 9 к пяти формулам по вашему выбору из случаев 3–8 MT1 § 8 и к двум формулам с отрицаниями "
         "элементарных высказываний. Сопоставьте результаты со списками книги.", "Критерии: оба шага выполнены; контрольная форма построена "
         "по D1; результаты совпадают с с. 109–110.", "С. 109–110, 116, 120.", "с. 109–120, гл. 7, § 8–9", "кванторы, разрешимость", s)
    hand(7, 9, 10, "Исследуйте, зачем при построении контрольной формы (п. 2 D1, с. 116–117) $\\sim a$ заменяется новым элементарным высказыванием. "
         "Что произойдёт без этой замены?", "Критерии: связь с MT2 (ни одно высказывание не входит вместе с отрицанием), с ограничением MT5; "
         "пример, где без замены процедура дала бы неверный ответ.", "С. 116–117.", "с. 116–118, гл. 7, § 9", "кванторы, разрешимость", s)
    # 07.13: L8 3, L9 2, L10 1
    hand(7, 13, 8, "По образцу § 13 докажите: правила R1, R2 сохраняют свойство «бескванторная форма доказуема в $S^s$» в $S^s_{nq}$.",
         "R1, R2 навешивают одну и ту же кванторную группу на обе части; по D1 § 13 она исключается (п. 3), бескванторная форма не меняется.",
         "С. 123–124.", "с. 123–124, гл. 7, § 13", "кванторы, непротиворечивость", "S^s_nq")
    hand(7, 13, 8, "Проверьте, что бескванторные формы $A^18$ и $A^19$ доказуемы в $S^s$.", "$x \\vdash \\sim\\sim x\\sim(\\sim x\\sim\\sim x)$: $\\sim(\\sim x\\sim\\sim x)$ "
         "— тавтология $S^s$, $x \\vdash \\sim\\sim x$; одно элементарное высказывание $x$. Обратная — аналогично.", "С. 124.", "с. 124, гл. 7, § 13",
         "кванторы, непротиворечивость", "S^s_nq")
    hand(7, 13, 8, "Докажите непротиворечивость $S^s_{nq}$ в смысле: не доказуемы одновременно $x \\vdash y$ и $x \\vdash \\sim y$ при непротиворечивом $x^*$.",
         "Бескванторные формы обеих доказуемы в $S^s$; при истинном $x^*$ истинны $y^*$ и $\\sim y^*$ — невозможно.", "С. 124; ср. гл. 1, § 6.",
         "с. 124, гл. 7, § 13", "кванторы, непротиворечивость", "S^s_nq")
    hand(7, 13, 9, "Докажите, что бескванторная форма D1 § 13 переводит формулы с $(?\\exists b)$ в формулы $S^s$ с тем же множеством элементарных "
         "высказываний.", "Пп. 1–3 заменяют кванторные выражения на $\\sim$-комбинации того же $z$; новых элементарных высказываний не появляется.",
         "С. 123.", "с. 123, гл. 7, § 13", "кванторы, непротиворечивость", "S^s_nq")
    hand(7, 13, 9, "Покажите, что метод бескванторных форм не позволяет отличить $S^s_{nq}$ от $S^s_{cq}$ на формуле $\\sim(\\exists a)\\sim x \\vdash (\\forall a)x$.",
         "Её бескванторная форма $\\sim\\sim x \\vdash x$ доказуема в $S^s$, но формула недоказуема в $S^s_{nq}$ (MT3 § 15) и доказуема в $S^s_{cq}$ (A7): "
         "критерий лишь необходимый.", "С. 99, 124, 126.", "с. 124, 126, гл. 7, § 13, 15", "кванторы, непротиворечивость", "S^s_nq")
    hand(7, 13, 10, "Исследуйте: можно ли построить бескванторную форму для $S^s_{nq}$, отличающую $(\\urcorner\\forall a)x$ от $\\sim(\\forall a)x$ (например, "
         "с тремя значениями)? Сравните с интерпретацией § 15.", "Критерии: предложена форма, сохраняющая различие; проверены аксиомные схемы; "
         "сопоставление с с. 125.", "С. 123–125.", "с. 123–125, гл. 7, § 13, 15", "кванторы, непротиворечивость", "S^s_nq")
    # 07.18: L8 3, L9 2, L10 1
    hand(7, 18, 8, "Покажите, почему схема 2 § 18 ($(\\exists a)\\sim x \\vdash (\\exists a)\\sim x$) отпадает как зависимая.", "Это частный случай $x \\vdash x$ "
         "системы $S^s$.", "С. 128.", "с. 128, гл. 7, § 18", "кванторы, полнота", "S^s_nq")
    hand(7, 18, 8, "Покажите, почему схемы 1 и 4 § 18 отпадают как зависимые.", "$(\\forall a)x \\vdash (\\forall a)\\sim\\sim x$ и обратная получаются по R1 из "
         "$x \\vdash \\sim\\sim x$ и $\\sim\\sim x \\vdash x$ системы $S^s$.", "С. 128.", "с. 128, гл. 7, § 18", "кванторы, полнота", "S^s_nq")
    hand(7, 18, 8, "Покажите, почему схемы 3 и 6 § 18 отпадают как зависимые.", "Они получаются друг из друга перестановкой конъюнктов и заменой "
         "$(\\forall a)\\sim\\sim x$ на $(\\forall a)x$ (R1 и $S^s$).", "С. 128.", "с. 128, гл. 7, § 18", "кванторы, полнота", "S^s_nq")
    hand(7, 18, 9, "Докажите, что при правилах с. 127–128 из того, что одно из $(\\forall b)z$ и $(\\exists b)\\sim z$ имеет значение 1, следует, что "
         "$\\sim(\\forall b)z\\sim(\\exists b)\\sim z$ не может быть истинно вместе с ними.", "Если $(\\forall b)z = 1$, то по п. 1 $(\\exists b)\\sim z = 0$, но "
         "$\\sim(\\forall b)z = 0$ — конъюнкция 0; аналогично для второго.", "С. 127–128.", "с. 127–128, гл. 7, § 18", "кванторы, полнота", "S^s_nq")
    hand(7, 18, 9, "Объясните, почему после замены § 18 в схемах не остаётся операторов $\\urcorner$ и $?$ при кванторах и какова роль новых "
         "семантических правил.", "Все четыре замены выражают $(\\urcorner Kb)$, $(?Kb)$ через $\\forall$, $\\exists$, $\\sim$; новые правила (с. 127–128) "
         "сохраняют неклассичность: $(\\forall b)z$ и $(\\exists b)\\sim z$ могут быть оба ложны.", "С. 127–128.", "с. 127–128, гл. 7, § 18",
         "кванторы, полнота", "S^s_nq")
    hand(7, 18, 10, "Исследуйте полноту системы, полученной в § 18: какие базисные формулы (по аналогии с D1 § 8) нужно рассмотреть и какие из них "
         "доказуемы?", "Критерии: определение базисных формул; разбор хотя бы трёх случаев; использование схем 7, 8, 10, 11, 13–15.", "С. 127–128.",
         "с. 127–128, гл. 7, § 18", "кванторы, полнота", "S^s_nq")
    # 07.19: L8 2, L9 1
    hand(7, 19, 8, "Обоснуйте MT1 § 19: если $x \\vdash y$ без кванторов доказуема в $S^s$, то доказуема и $z \\vdash v$, полученная подстановкой $b$ на место "
         "элементарного $a$.", "Если $x \\vdash y$ — аксиома, то $z \\vdash v$ — аксиома (схемы); если теорема — в доказательстве везде заменяем $a$ на $b$.",
         "С. 129.", "с. 129, гл. 7, § 19", "кванторы, подстановка")
    hand(7, 19, 8, "Докажите теорему 3 § 19 при $c = a$: $(\\forall a)(a \\leftarrow b) \\vdash \\sim(\\exists a)\\sim(a \\leftarrow b)$.", "Пример A6 $S^s_{cq}$ при "
         "$x = (a \\leftarrow b)$.", "С. 99, 129.", "с. 99, 129, гл. 7, § 2, 19", "кванторы, подстановка", "S^s_cq")
    hand(7, 19, 9, "Докажите, что система с аксиомами T1–T14 § 19, аксиомами $S^s$ и правилами $S^s$, $S^s_{cq}$ и MT1–MT5 эквивалентна $S^s_{cq}$ "
         "(эскиз, с. 130).", "T1–T14 доказуемы в $S^s_{cq}$; обратно, любой пример схемы $S^s_{cq}$ получается из T1–T14 подстановками MT2–MT5.",
         "С. 130.", "с. 129–130, гл. 7, § 19", "кванторы, подстановка")
    # 08.01: L8, L9
    hand(8, 1, 8, "Докажите MT1 § 1 гл. 8: если $x \\vdash y$ доказуема в $S^s_p$, то в $y$ нет элементарных для теории предикации высказываний, "
         "отсутствующих в $x$.", "В A1–A6 обе части содержат одно элементарное $(a \\leftarrow b)$; правила $S^s$ сохраняют свойство (MT2 § 4 гл. 1).",
         "С. 132.", "с. 132, гл. 8, § 1", "предикация", "S^s_p")
    hand(8, 1, 9, "Докажите, что в $S^5_p$ T6 $\\vdash (a \\leftarrow b) : (a \\urcorner\\!\\leftarrow b) : (a? \\leftarrow b)$ следует из T7–T10.", "T7 — хотя бы одно "
         "истинно; T8–T10 — никакие два не истинны вместе; вместе — ровно одно, что и выражает строгая дизъюнкция.", "С. 133.", "с. 133, гл. 8, § 1",
         "предикация", "S^5_p")
    # 08.04: L8 2, L9 1
    hand(8, 4, 8, "По MT1 § 4 гл. 8 разберите базисные формулы вида $a \\vdash b$ с одним элементарным высказыванием: какие из девяти пар "
         "$\\{(a \\leftarrow b), (a \\urcorner\\!\\leftarrow b), (a? \\leftarrow b)\\}$ (и их внешних отрицаний) дают тавтологии?", "Тавтологии: "
         "$u \\vdash u$; $u \\vdash \\sim w$ при $u \\neq w$ (T4–T7 и аналоги); $\\sim u \\vdash \\sim u$; остальные — нет.", "С. 133–135.",
         "с. 133–135, гл. 8, § 1, 4", "предикация, полнота", "S^s_p")
    hand(8, 4, 8, "Покажите, что каждая базисная тавтология вида $c \\vdash a \\vee b$ с одним элементарным высказыванием доказуема в $S^s_p$.",
         "Например, $\\sim(a \\leftarrow b) \\vdash (a \\urcorner\\!\\leftarrow b) \\vee (a? \\leftarrow b)$ — T1; остальные — T2, T3 или $S^s$.", "С. 133, 135.",
         "с. 133–135, гл. 8, § 1, 4", "предикация, полнота", "S^s_p")
    hand(8, 4, 9, "Докажите: базисная формула $\\vdash z$ с одним элементарным высказыванием, являющаяся тавтологией, доказуема в $S^5_p$.",
         "$z$ — функция трёх взаимоисключающих и исчерпывающих высказываний (T6); тавтология $z$ сводится по $S^5$ к комбинации T7–T10.",
         "С. 133, 135.", "с. 133–135, гл. 8, § 1, 4", "предикация, полнота", "S^5_p")
    # 17.08: L8 2, L9, L10
    hand(17, 8, 8, "Докажите в $S^s_{if}$: $(x \\rightarrow y)(y \\rightarrow z)\\sim z \\vdash \\sim x$.", "A3: $(x \\rightarrow y)(y \\rightarrow z) \\vdash (x \\rightarrow z)$; "
         "присоединяя $\\sim z$ (R1, R2 общей теории дедукции): $\\vdash (x \\rightarrow z)\\sim z$; T4: $(x \\rightarrow z)\\sim z \\vdash \\sim x$; R1.", "Гл. 6, § 6 (с. 90–91).",
         "гл. 1–6", "смешанный, условность")
    hand(17, 8, 8, "Докажите, что в $S^5_{if}$ доказуема $\\vdash (xy \\rightarrow x \\vee z)$.", "$xy \\supset x \\vee z$ — тавтология, по MT5 § 8 гл. 6 "
         "$\\vdash (xy \\rightarrow x \\vee z)$ доказуема.", "Гл. 6, § 8 (с. 92).", "гл. 1–6", "смешанный, условность")
    hand(17, 8, 9, "Докажите: если $\\vdash (x \\rightarrow y)$ доказуема в $S^5_{if}$ ($x$, $y$ без $\\rightarrow$), то $x \\vdash y$ — тавтология общей теории дедукции, "
         "но не обязательно доказуема в $S^s$.", "По MT2 § 8 $x \\supset y$ — тавтология. Пример: $\\vdash (x \\rightarrow y \\vee \\sim y)$ (парадокс, § 10): "
         "$x \\vdash y \\vee \\sim y$ вводит новое $y$ и недоказуема в $S^s$ (ограничение $S^s$).", "Гл. 5, § 2; гл. 6, § 8, 10.", "гл. 1–6",
         "смешанный, условность")
    hand(17, 8, 10, "Сопоставьте парадоксы материальной импликации ($S^5$), строгой импликации ($S^6$?) и условных высказываний ($S^5_{if}$, § 10 гл. 6). "
         "Какие из них устраняются переходом к $S^s$ и почему это не устраняет парадоксы § 10?", "Критерии: формулы парадоксов приведены; "
         "показано, что $S^s$ запрещает новые элементарные высказывания; разобран довод с. 94.", "Гл. 4–6.", "гл. 1–6", "смешанный, исследование")


# ---------------------------------------------------------------- сборка
def build(ch, sec, levels, diag, maker):
    out, nd = [], 0
    left = sum(n for l_, n in enumerate(levels, 1) if l_ >= 2)
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            if lvl >= 2:
                left -= 1
            d = nd < diag and lvl >= 2 and ((i + lvl) % 2 == 0 or left < diag - nd)
            c = fresh(lambda: maker(lvl, d, i))
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def relabel(c, sec, src):
    for st in ("iso", "open", "transfer", "vary", "complete"):
        c = c.replace(f"step: {st}\n", "step: mixed\n")
    c = re.sub(r'source: ".*"', f'source: "{src}"', c, count=1)
    c = re.sub(r"chapter: \d+\nsection: \d+", f"chapter: 17\nsection: {sec}", c, count=1)
    return re.sub(r'system: ".*"\n', "", c, count=1)


def mixed09():
    out = []
    makers = [lambda: G6.aq_rec(2), lambda: t_rec(2, "C"), lambda: ap_rec(2, "C"), lambda: nq_rec(2, "C"), lambda: G6.ax_rec(2), lambda: G6.free_card(2)]
    for i, mk in enumerate(makers):
        out.append(relabel(fresh(mk), 9, "гл. 1–7"))
    return out


def main():
    cards = []
    cards += build(7, 5, [0, 0, 0, 1, 2, 2, 2], 4, m705)
    cards += build(7, 6, [1, 3, 4, 5, 8, 6, 3], 8, m706)
    cards += build(7, 7, [1, 3, 6, 2, 2, 3, 2], 5, m707)
    cards += build(7, 8, [0, 2, 4, 9, 6, 8, 6], 14, m708)
    cards += build(7, 9, [0, 1, 3, 7, 4, 6, 4], 10, m709)
    cards += build(7, 10, [1, 1, 1, 2, 3, 2, 1], 3, m710)
    cards += build(7, 11, [1, 1, 1, 2, 3, 2, 1], 3, m711)
    cards += build(7, 12, [0, 1, 2, 2, 3, 3, 1], 3, m712)
    cards += build(7, 13, [0, 1, 1, 2, 2, 2, 2], 4, m713)
    cards += build(7, 14, [0, 1, 1, 2, 3, 2, 1], 2, m714)
    cards += build(7, 15, [1, 2, 3, 1, 1, 1, 1], 2, m715)
    cards += build(7, 16, [0, 1, 1, 2, 3, 2, 1], 2, m716)
    cards += build(7, 17, [0, 1, 1, 2, 3, 2, 1], 2, m717)
    cards += build(7, 18, [0, 0, 1, 2, 1, 2, 1], 3, m718)
    cards += build(7, 19, [0, 0, 1, 2, 1, 2, 1], 2, m719)
    cards += build(7, 20, [0, 1, 1, 2, 3, 2, 1], 2, m720)
    cards += build(7, 21, [0, 1, 1, 2, 3, 2, 1], 2, m721)
    cards += build(8, 1, [1, 3, 4, 5, 8, 6, 3], 8, m801)
    cards += build(8, 2, [1, 2, 3, 1, 1, 1, 1], 2, m802)
    cards += build(8, 3, [0, 1, 1, 2, 3, 2, 1], 2, m803)
    cards += build(8, 4, [0, 0, 1, 2, 1, 2, 1], 2, m804)
    cards += build(8, 5, [0, 1, 1, 1], 0, m805)
    cards += G6.mixed(8, [0, 0, 0, 1, 9, 11, 6], 8, "гл. 1–6", ["if", "s", "if", "w", "n"])
    cards += mixed09()
    hand_cards()
    cards += H
    (ROOT / "drafts" / "51-60-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(cards), "из них ручных", len(H))


if __name__ == "__main__":
    main()
