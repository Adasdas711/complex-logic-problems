#!/usr/bin/env python3
"""Серии для занятий 81–90: гл. 12, § 11–12; гл. 13 (логика отношений); гл. 14 (нормативные предикаты);
Приложение (правила приписывания значений); смешанные 17.12–17.17. Пишет drafts/81-90-gen.md.
Ступени 8–10 — здесь же, по доказательствам книги (без пометки generated).
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
from ifq import ALL, EL, EX, C, N, V, W  # noqa: E402

spec = importlib.util.spec_from_file_location("g10_12", ROOT / "scripts" / "gen" / "g10_12.py")
G10 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G10)
G8, G7 = G10.G8, G10.G7
G6 = G7.G6
for m_, s_ in ((G10, 8190), (G8, 8191), (G7, 8192), (G6, 8193), (G6.G, 8194)):
    m_.rnd.seed(s_)
rnd = random.Random(8195)
card, fresh, items, answers, build, relabel = G7.card, G7.fresh, G7.items, G7.answers, G7.build, G7.relabel
USED = G7.USED
L = G7.L
T = G7.T
permute, E, epick, sub_vars, wrapx = G10.permute, G10.E, G10.epick, G10.sub_vars, G10.wrapx
nxt = G8.nxt


def steps(st):
    return "\n".join(f"{n + 1}. {s}" for n, s in enumerate(st))


def hide_step(st):
    j = rnd.randrange(len(st))
    m = re.search(r"\[([^\[\]]*)\]$", st[j])
    while not m:
        j = (j + 1) % len(st)
        m = re.search(r"\[([^\[\]]*)\]$", st[j])
    sh = [re.sub(r"\[[^\[\]]*\]$", "[…]", s) if n == j else s for n, s in enumerate(st)]
    return steps(sh), f"Шаг {j + 1}: {m.group(1)}."


# ================================================================ 12.11 модальности и кванторы
def mtrans(f, mode):
    """MT1 (mode=1): (α∀a)z → (αNa)z, (α∃a)z → (αMa)z; MT2 (mode=2): → αN(↓z), αM(↓z)."""
    k = f[0]
    if k in ("all", "ex"):
        op = "N" if k == "all" else "M"
        inner = mtrans(f[2], mode)
        if mode == 1:
            return f"(\\mathrm{{{op}}}{f[1]}){inner if f[2][0] in ('el', 'all', 'ex', 'neg') else '(' + inner + ')'}"
        return f"{op}(\\downarrow {inner if f[2][0] in ('el',) else '(' + inner + ')'})"
    if k == "el":
        return T(f)
    if k == "neg":
        g = f[1]
        s = mtrans(g, mode)
        return "\\sim " + (s if g[0] in ("el", "all", "ex", "neg") else f"({s})")
    if k == "conj":
        return "".join(mtrans(a, mode) if a[0] in ("el", "all", "ex", "neg") else f"({mtrans(a, mode)})" for a in f[1])
    if k == "wdis":
        return " \\vee ".join(mtrans(a, mode) for a in f[1])
    raise ValueError(k)


def m1211(lvl, d, i):
    if d:
        pool = [("«по MT1 § 11 гл. 12 $(\\forall a)z$ заменяется на $(\\mathrm{M}a)z$»", "по MT1 $(\\alpha\\forall a)z$ заменяется на $(\\alpha\\mathrm{N}a)z$, а "
                 "$(\\alpha\\exists a)z$ — на $(\\alpha\\mathrm{M}a)z$ (с. 176)"),
                ("«по MT2 § 11 из доказуемой формулы теории кванторов получается формула с модальными операторами $\\mathrm{N}$, $\\mathrm{M}$»",
                 "по MT2 получаются формулы с модальными предикатами: $(\\alpha\\forall a)z$ → $\\alpha N(\\downarrow z)$, $(\\alpha\\exists a)z$ → $\\alpha M(\\downarrow z)$ (с. 176)")]
        return epick(pool, 12, 11, lvl, "Буквы $a, b$ — термины; $z$ — высказывание.", "с. 176, гл. 12, § 11", "модальности и кванторы, диагностика")
    k, j, p, q = rnd.choice(G7.ALLC)
    t = j in G7.PROOF[k]
    mode = 1 if lvl <= 4 or i % 2 else 2
    tp, tq = mtrans(p, mode), mtrans(q, mode)
    if t:
        return card(12, 11, lvl, "D" if lvl <= 4 else "C", "iso", f"Буквы $a, b, c$ — термины. В теории кванторов доказуема ${G7.FT(p, q)}$ ({G7.PROOF[k][j]}). "
                    f"Какая формула теории модальностей доказуема по MT{mode} § 11 гл. 12 (с. 176)?", f"${tp} \\vdash {tq}$",
                    "MT1: замены $(\\alpha\\forall a)z$ → $(\\alpha\\mathrm{N}a)z$, $(\\alpha\\exists a)z$ → $(\\alpha\\mathrm{M}a)z$; MT2: → $\\alpha N(\\downarrow z)$, $\\alpha M(\\downarrow z)$.",
                    "с. 176, гл. 12, § 11", "модальности и кванторы")
    return card(12, 11, lvl, "S" if lvl == 7 else "C", "open", f"Буквы $a, b, c$ — термины. Доказуема ли формула ${tp} \\vdash {tq}$ теории модальностей? "
                f"Воспользуйтесь MT{mode} § 11 гл. 12 («и наоборот»).", f"Нет: она получается по MT{mode} из ${G7.FT(p, q)}$, которая не тавтология "
                f"({G7.CASEP[k]}) и недоказуема в $S^s_{{cq}}$.", "MT1, MT2 (с. 176) действуют в обе стороны.", "с. 109–110, 176, гл. 7, 12",
                "модальности и кванторы")


# ================================================================ 12.12 вероятностная логика
PRB = "Буквы $x, y, x^i$ — высказывания; $p(\\downarrow x)$ — вероятность того, что наступит $\\downarrow x$."
AP12 = {"A1": "\\vdash 0 \\leq p(\\downarrow x) \\leq 1", "A2": "\\vdash (p(\\downarrow x) = 0) \\to \\urcorner \\mathrm{M}(\\downarrow x)", "A3": "\\vdash \\urcorner \\mathrm{M}(\\downarrow x) \\to (p(\\downarrow x) = 0)",
        "A4": "\\vdash (p(\\downarrow x) = 1) \\to N(\\downarrow x)", "A5": "\\vdash N(\\downarrow x) \\to (p(\\downarrow x) = 1)", "A6": "\\vdash \\mathrm{M}(\\downarrow x) \\to (0 < p(\\downarrow x))",
        "A7": "\\vdash (0 < p(\\downarrow x)) \\to M(\\downarrow x)", "A8": "\\vdash M(\\downarrow \\sim x) \\to (p(\\downarrow x) < 1)", "A9": "\\vdash (p(\\downarrow x) < 1) \\to M(\\downarrow \\sim x)",
        "A10": "\\vdash p\\downarrow(x^1 \\cdot \\ldots \\cdot x^n) \\leq \\min(p(\\downarrow x^1), \\ldots, p(\\downarrow x^n))", "A11": "\\vdash p\\downarrow(x^1 \\vee \\ldots \\vee x^n) \\geq \\max(p(\\downarrow x^1), \\ldots, p(\\downarrow x^n))",
        "A13": "\\vdash (p(\\downarrow (x \\to y)) = \\alpha) \\to (x \\to (p(\\downarrow y) = \\alpha))", "A14": "\\vdash (x \\to (p(\\downarrow y) = \\alpha)) \\to (p\\downarrow(x \\to y) = \\alpha)"}


def prob_bound(lvl, typ="C"):
    n = rnd.choice([2, 3])
    ps = sorted(rnd.sample([0.1, 0.2, 0.25, 0.3, 0.4, 0.5, 0.6, 0.7, 0.75, 0.8, 0.9], n))
    rnd.shuffle(ps)
    kind = rnd.choice(["conj", "dis"])
    xs = " \\cdot ".join(f"x^{k + 1}" for k in range(n)) if kind == "conj" else " \\vee ".join(f"x^{k + 1}" for k in range(n))
    given = ", ".join(f"$p(\\downarrow x^{k + 1}) = {str(v).replace('.', ',')}$" for k, v in enumerate(ps))
    if kind == "conj":
        ans = f"$p\\downarrow({xs}) \\leq {str(min(ps)).replace('.', ',')}$ (A10)"
    else:
        ans = f"$p\\downarrow({xs}) \\geq {str(max(ps)).replace('.', ',')}$ (A11)"
    return card(12, 12, lvl, typ, "iso", f"{PRB} Дано: {given}. Какую оценку для $p\\downarrow({xs})$ дают аксиомные схемы $S^{{mp}}_n$ (§ 12 гл. 12, с. 177)?",
                ans, "A10: $p\\downarrow(x^1 \\cdot \\ldots \\cdot x^n) \\leq \\min(\\ldots)$; A11: $p\\downarrow(x^1 \\vee \\ldots \\vee x^n) \\geq \\max(\\ldots)$.", "с. 177, гл. 12, § 12",
                "вероятностная логика")


def prob_prod(lvl, typ="C"):
    a_, b_ = rnd.choice([(0.5, 0.4), (0.8, 0.5), (0.9, 0.6), (0.3, 0.5), (0.6, 0.5), (0.7, 0.2)])
    ev = rnd.choice([("«пойдёт дождь»", "«матч перенесут»"), ("«поезд опоздает»", "«пассажир опоздает на пересадку»"), ("«выпадет снег»", "«дороги закроют»")])
    r = round(a_ * b_, 4)
    return card(12, 12, lvl, typ, "iso", f"{PRB} Пусть $x$ — {ev[0]}, $y$ — {ev[1]}. Если $x$, то вероятность $y$ равна {str(a_).replace('.', ',')}; вероятность $x$ равна "
                f"{str(b_).replace('.', ',')}. Какую вероятность $y$ даёт соглашение A*12 (с. 177)? Какую оценку даёт A12?",
                f"По A*12 $p(\\downarrow y) = {str(r).replace('.', ',')}$; по A12 $p(\\downarrow y) \\leq {str(min(a_, b_)).replace('.', ',')}$.",
                "A12: $\\vdash (x \\to (p(\\downarrow y) = \\alpha))(p(\\downarrow x) = \\beta) \\to (p(\\downarrow y) \\leq \\min(\\alpha, \\beta))$; A*12: $\\ldots \\to (p(\\downarrow y) = \\alpha \\cdot \\beta)$ "
                "(с. 177).", "с. 177, гл. 12, § 12", "вероятностная логика", form="nat")


def prob_mod(lvl, typ="C"):
    v_ = rnd.choice([("$p(\\downarrow x) = 0$", "$\\urcorner \\mathrm{M}(\\downarrow x)$ (A2)"), ("$p(\\downarrow x) = 1$", "$N(\\downarrow x)$ (A4)"),
                     ("$0 < p(\\downarrow x)$", "$M(\\downarrow x)$ (A7)"), ("$p(\\downarrow x) < 1$", "$M(\\downarrow \\sim x)$ (A9)"),
                     ("$\\urcorner \\mathrm{M}(\\downarrow x)$", "$p(\\downarrow x) = 0$ (A3)"), ("$N(\\downarrow x)$", "$p(\\downarrow x) = 1$ (A5)"),
                     ("$M(\\downarrow \\sim x)$", "$p(\\downarrow x) < 1$ (A8)")])
    return card(12, 12, lvl, typ, "iso", f"{PRB} Что следует по аксиомным схемам $S^{{mp}}_n$ (с. 177) из {v_[0]}?", v_[1] + ".", "С. 177.", "с. 177, гл. 12, § 12",
                "вероятностная логика")


E1212 = [("«вероятность конъюнкции не меньше наибольшей из вероятностей конъюнктов»", "по A10 (с. 177) — не больше наименьшей"),
         ("«вероятность дизъюнкции не больше наименьшей из вероятностей»", "по A11 (с. 177) — не меньше наибольшей"),
         ("«если $0 < p(\\downarrow x)$, то необходимо $x$»", "по A7 (с. 177) следует лишь $M(\\downarrow x)$ — возможно $x$"),
         ("«соглашение A*12 единственно возможное»", "по с. 177 возможны различные соглашения для случаев A12; A*12 — лишь одно из них"),
         ("«$p(\\downarrow x) < 1$ означает, что $x$ невозможно»", "по A9 (с. 177) отсюда следует $M(\\downarrow \\sim x)$: возможно $\\sim x$")]


def m1212(lvl, d, i):
    if d:
        return epick(E1212, 12, 12, lvl, PRB, "с. 176–177, гл. 12, § 12", "вероятностная логика, диагностика")
    if lvl == 1:
        return card(12, 12, 1, "R", "iso", "Какие предикаты вероятности вводит алфавит $S^{mp}_n$ (§ 12 гл. 12, с. 176)?", "$p = \\alpha$, $p > \\alpha$, $p < \\alpha$, "
                    "$p \\geq \\alpha$, $p \\leq \\alpha$, где $0 \\leq \\alpha \\leq 1$ («возможно со степенью $\\alpha$», «со степенью большей, чем $\\alpha$» и т. д.).",
                    "С. 176.", "с. 176, гл. 12, § 12", "вероятностная логика", form="meta", answ="text")
    if lvl == 2:
        ks = rnd.sample(sorted(AP12), 3)
        return card(12, 12, 2, "C", "iso", f"{PRB} Каким аксиомным схемам $S^{{mp}}_n$ (с. 177) соответствуют формулы?\n\n" + items([f"${AP12[k]}$" for k in ks]),
                    answers(ks), "С. 177.", "с. 177, гл. 12, § 12", "вероятностная логика")
    if lvl in (3, 4):
        return [prob_mod, prob_bound][i % 2](lvl, "D" if lvl == 4 else "C")
    if lvl == 5:
        return prob_bound(5) if i == 0 else prob_prod(5)
    if lvl == 6:
        return [prob_prod, prob_bound, prob_mod][i % 3](6)
    return [prob_prod, prob_bound][i % 2](7, "S")


# ================================================================ гл. 13
RL = "Буквы $a, b, c$ — термины; признак (или порядок) сравнения подразумевается один и тот же."
AI13 = {1: "\\vdash (a \\urcorner\\!> a)", 2: "(a > b) \\vdash (b \\urcorner\\!> a)", 3: "(a \\urcorner\\!> b) \\vdash ((b > a) : (a = b))", 4: "(a ?> b) \\vdash (b ?> a)",
        5: "(a > b)(b > c) \\vdash (a > c)", 6: "(a > b)(b = c) \\vdash (a > c)", 7: "(a \\urcorner\\!> b)(b \\urcorner\\!> c) \\vdash (a \\urcorner\\!> c)",
        8: "(a ?> b)(b = c) \\vdash (a ?> c)", 9: "(a < b) \\vdash (b > a)", 10: "(a > b) \\vdash (b < a)", 11: "(a \\urcorner\\!< b) \\vdash (a > b) : (a = b)",
        12: "(a > b) : (a = b) \\vdash (a \\urcorner\\!< b)", 13: "(a ?< b) \\vdash (b ?> a)", 14: "(b ?> a) \\vdash (a ?< b)", 15: "(a = b) \\vdash (a \\urcorner\\!> b)(b \\urcorner\\!> a)",
        16: "(a \\urcorner\\!> b)(b \\urcorner\\!> a) \\vdash (a = b)", 17: "(a \\urcorner\\!= b) \\vdash (a > b) : (b > a)", 18: "(a > b) : (b > a) \\vdash (a \\urcorner\\!= b)"}
T13 = {1: "\\vdash \\sim(a > a)", 2: "(a > b) \\vdash \\sim(b > a)", 3: "(a ?> b) \\vdash \\sim(a > b)", 4: "\\vdash \\sim((a > b)(b > a))", 5: "\\vdash \\sim((a > b)(a \\urcorner\\!> b))"}
ACI = {1: "\\vdash \\sim(a > a)", 2: "(a > b) \\vdash \\sim(b > a)", 3: "\\sim(a > b) \\vdash (b > a) : (a = b)", 4: "(a > b)(b > c) \\vdash (a > c)", 5: "(a > b)(b = c) \\vdash (a > c)",
       6: "\\sim(a > b)\\sim(b > c) \\vdash \\sim(a > c)", 7: "(a < b) \\vdash (b > a)", 8: "(a > b) \\vdash (b < a)", 9: "(a = b) \\vdash \\sim(a > b)\\sim(b > a)",
       10: "\\sim(a > b)\\sim(b > a) \\vdash (a = b)"}
AII13 = {1: "(a \\leftarrow c)(b \\urcorner\\!\\leftarrow c) \\vdash (a(> c)b)", 2: "(a \\urcorner\\!\\leftarrow c)(b \\urcorner\\!\\leftarrow c) \\vdash (a(= c)b)",
         3: "(a? \\leftarrow c)(b? \\leftarrow c) \\vdash (a(= c)b)", 4: "(a \\leftarrow c)(b? \\leftarrow c) \\vdash (a?(> c)b)", 5: "(a? \\leftarrow c)(b \\urcorner\\!\\leftarrow c) \\vdash (a?(> c)b)"}


def cval(f, v):
    k = f[0]
    if k == "gt":
        return int(v[f[1]] > v[f[2]])
    if k == "lt":
        return int(v[f[1]] < v[f[2]])
    if k == "eq":
        return int(v[f[1]] == v[f[2]])
    if k == "neg":
        return 1 - cval(f[1], v)
    vs = [cval(g, v) for g in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs)) if k == "wdis" else int(sum(vs) == 1)


def ctaut(p, q):
    for vals in itertools.product(range(3), repeat=3):
        v = dict(zip("abc", vals))
        if cval(p, v) and not cval(q, v):
            return False, v
    return True, None


def ctex(f):
    k = f[0]
    if k in ("gt", "lt", "eq"):
        return f"({f[1]} {'>' if k == 'gt' else '<' if k == 'lt' else '='} {f[2]})"
    if k == "neg":
        return "\\sim " + ctex(f[1]) if f[1][0] in ("gt", "lt", "eq") else f"\\sim({ctex(f[1])})"
    if k == "conj":
        return "".join(ctex(g) if g[0] in ("gt", "lt", "eq", "neg") else f"({ctex(g)})" for g in f[1])
    sep = " \\vee " if k == "wdis" else " : "
    return sep.join(ctex(g) if g[0] not in ("wdis", "dis") else f"({ctex(g)})" for g in f[1])


def crand(depth=1, letters="abc"):
    if depth == 0 or rnd.random() < 0.4:
        a, b = rnd.sample(letters, 2)
        return (rnd.choice(["gt", "gt", "lt", "eq"]), a, b)
    k = rnd.choice(["neg", "conj", "wdis", "dis"])
    if k == "neg":
        return ("neg", crand(0, letters))
    x1, x2 = crand(depth - 1, letters), crand(depth - 1, letters)
    while x1 == x2:
        x2 = crand(depth - 1, letters)
    return (k, (x1, x2))


def ccheck_card(lvl, typ="C", sec=2):
    its = []
    for want in rnd.sample([True, True, False, False], 3):
        for _ in range(800):
            p, q = crand(1), crand(1)
            if ctaut(p, q)[0] == want and repr(("cmp", p, q)) not in USED and p != q:
                USED.add(repr(("cmp", p, q)))
                its.append((p, q))
                break
    sol = []
    for p, q in its:
        t, v = ctaut(p, q)
        sol.append("тавтология" if t else "не тавтология: при " + ", ".join(f"${k_} = {vv}$" for k_, vv in sorted(v.items())) + " посылка 1, заключение 0; по MT1 § 4 недоказуема")
    return card(13, sec, lvl, typ, "open", f"{RL} Классический случай. Тавтологии ли формулы при интерпретации § 4 гл. 13 (значения — натуральные числа; "
                "$a > b$ — значение $a$ больше значения $b$; $\\sim$ — обычное отрицание)?\n\n" + items([f"${ctex(p)} \\vdash {ctex(q)}$" for p, q in its]),
                answers(["да" if s == "тавтология" else "нет" for s in sol]), "\n".join(f"{L[k]}) {s}." for k, s in enumerate(sol)) +
                "\n\nИнтерпретация: § 4 гл. 13 (с. 182); $a < b$ равнозначно $b > a$ (схемы 9, 10).", "с. 179–182, гл. 13, § 2, 4", "логика сравнения", system="S^r1_c")


def ai13_rec(lvl, typ="R", D=None, name="AI", sysn="S^{r1}_n"):
    D = D or AI13
    ks = rnd.sample(sorted(D), 3)
    return card(13, 2, lvl, typ, "iso", f"{RL} Каким схемам {name} системы ${sysn}$ (§ 2 гл. 13, с. 179–181) соответствуют формулы?\n\n" + items([f"${D[k]}$" for k in ks]),
                answers([f"{name}.{k}" if name != "T" else f"T{k}" for k in ks]), "С. 179–181.", "с. 179–181, гл. 13, § 2", "логика сравнения")


READS = [("(a > b)", "«$a$ превосходит $b$»"), ("(a \\urcorner\\!> b)", "«$a$ не превосходит $b$»"), ("(a ?> b)", "«$a$ неопределённо превосходит $b$»"),
         ("(a < b)", "«$a$ уступает $b$»"), ("(a \\urcorner\\!< b)", "«$a$ не уступает $b$»"), ("(a = b)", "«$a$ тождественно $b$»"),
         ("(a \\urcorner\\!= b)", "«$a$ не тождественно $b$»"), ("(a(> c)b)", "«$a$ превосходит $b$ по признаку $c$»")]


def read13(lvl, typ="C", sec=2):
    its = rnd.sample(READS, 3)
    w = "признаку" if sec == 2 else "порядку относительно"
    return card(13, sec, lvl, typ, "iso", f"{RL} Прочитайте высказывания {'сравнения' if sec == 2 else 'порядка'} (§ {sec} гл. 13):\n\n" + items([f"${s}$" for s, _ in its]),
                answers([r if sec == 2 else r.replace("по признаку $c$", "по порядку относительно $c$") for _, r in its]),
                f"С. {179 if sec == 2 else 181}: «по {w} $c$»; $c$ опускается.", f"с. {179 if sec == 2 else 181}, гл. 13, § {sec}", "логика сравнения")


def nat13(lvl, typ="C"):
    P_ = rnd.choice([("«тяжёлый»", "свинец", "алюминий"), ("«высокий»", "Эльбрус", "Казбек"), ("«тёплый»", "июль", "март"), ("«длинный»", "Волга", "Ока")])
    v_ = rnd.choice([("(a \\leftarrow c)(b \\urcorner\\!\\leftarrow c)", "(a(> c)b)", "AII.1", f"{P_[1]} обладает признаком {P_[0]}, а {P_[2]} им не обладает",
                      f"{P_[1]} превосходит {P_[2]} по признаку {P_[0]}"),
                     ("(a \\urcorner\\!\\leftarrow c)(b \\urcorner\\!\\leftarrow c)", "(a(= c)b)", "AII.2", f"ни {P_[1]}, ни {P_[2]} не обладают признаком {P_[0]}",
                      f"{P_[1]} тождественно {P_[2]} по признаку {P_[0]}")])
    return card(13, 2, lvl, typ, "iso", f"{RL} Пусть $a$ — {P_[1]}, $b$ — {P_[2]}, $c$ — признак {P_[0]}. Известно: {v_[3]}. Что следует по схемам AII § 2 гл. 13 (с. 180)?",
                f"${v_[1]}$: {v_[4]} ({v_[2]}).", f"{v_[2]}: ${v_[0]} \\vdash {v_[1]}$.", "с. 180, гл. 13, § 2", "логика сравнения", form="nat")


def deriv13(lvl, typ="D"):
    v_ = rnd.choice([("(a < b)(b > c) \\vdash (a > c)", None),
                     ("(a < b) \\vdash \\sim(a > b)", ["$(a < b) \\vdash (b > a)$ [AI.9]", "$(b > a) \\vdash \\sim(a > b)$ [T2]", "транзитивность [$S^s$]"]),
                     ("(a > b)(b > c)(c = d) \\vdash (a > d)", ["$(a > b)(b > c) \\vdash (a > c)$ [AI.5]", "$(a > c)(c = d) \\vdash (a > d)$ [AI.6]", "объединение и транзитивность [$S^s$]"]),
                     ("(b < a)(c < b) \\vdash (a > c)", ["$(b < a) \\vdash (a > b)$ [AI.9]", "$(c < b) \\vdash (b > c)$ [AI.9]", "$(a > b)(b > c) \\vdash (a > c)$ [AI.5]",
                                                          "объединение и транзитивность [$S^s$]"]),
                     ("(a > b) \\vdash \\sim(a = b) \\cdot (b < a)", None)])
    if v_[1] is None:
        v_ = ("(b < a)(c < b) \\vdash (a > c)", ["$(b < a) \\vdash (a > b)$ [AI.9]", "$(c < b) \\vdash (b > c)$ [AI.9]", "$(a > b)(b > c) \\vdash (a > c)$ [AI.5]",
                                                  "объединение и транзитивность [$S^s$]"])
    st = v_[1]
    goal, st = permute([v_[0]] + st, "abc")[0], permute([v_[0]] + st, "abc")[1:]
    goal2 = permute(["$" + v_[0] + "$"] + v_[1], "abcd")
    goal, st = goal2[0][1:-1], goal2[1:]
    if lvl == 4:
        sh, a_ = hide_step(st)
        return card(13, 2, 4, "D", "complete", f"{RL} Буква $d$ — тоже термин. Восстановите пропущенное основание в выводе ${goal}$ в $S^{{r1}}_n$:\n\n{sh}", a_,
                    steps(st), "с. 179–180, гл. 13, § 2", "логика сравнения, вывод", system="S^r1_n")
    return card(13, 2, lvl, typ, "iso", f"{RL} Буква $d$ — тоже термин. Выведите в $S^{{r1}}_n$ формулу ${goal}$.", "См. решение.", steps(st) + "\n\nС. 179–180.",
                "с. 179–180, гл. 13, § 2", "логика сравнения, вывод", answ="proof", system="S^r1_n")


E1302 = [("«AI.2: $(a > b) \\vdash (b \\urcorner\\!> a)$ можно обратить: $(b \\urcorner\\!> a) \\vdash (a > b)$»", "по AI.3 (с. 179) из $(b \\urcorner\\!> a)$ следует лишь $(a > b) : (b = a)$"),
         ("«AI.3: $(a \\urcorner\\!> b) \\vdash (b > a)$»", "AI.3 — $(a \\urcorner\\!> b) \\vdash ((b > a) : (a = b))$ (с. 179)"),
         ("«из $(a ?> b)$ следует $(b \\urcorner\\!> a)$»", "по AI.4 (с. 179) следует $(b ?> a)$"),
         ("«AI.7: $(a \\urcorner\\!> b)(b \\urcorner\\!> c) \\vdash (a > c)$»", "AI.7 — $\\ldots \\vdash (a \\urcorner\\!> c)$ (с. 179)"),
         ("«в классическом случае $\\sim(a > b) \\vdash (b > a)$»", "AcI.3 — $\\sim(a > b) \\vdash (b > a) : (a = b)$ (с. 180); $(b > a)$ не следует: возможно $a = b$"),
         ("«AII.1: $(a \\leftarrow c)(b \\leftarrow c) \\vdash (a(> c)b)$»", "AII.1 — $(a \\leftarrow c)(b \\urcorner\\!\\leftarrow c) \\vdash (a(> c)b)$ (с. 180); если оба обладают признаком, "
          "превосходства по нему не следует"),
         ("«AI.15: $(a = b) \\vdash (a > b)(b > a)$»", "AI.15 — $(a = b) \\vdash (a \\urcorner\\!> b)(b \\urcorner\\!> a)$ (с. 180)"),
         ("«$(a > b)(b > c) \\vdash (c < a)$ — схема AI.5»", "AI.5 — $(a > b)(b > c) \\vdash (a > c)$; формула студента выводится из AI.5 и AI.10, но схемой не является")]


def m1302(lvl, d, i):
    if d:
        if i % 3 == 0:
            for _ in range(500):
                p, q = crand(1), crand(1)
                t, v = ctaut(p, q)
                if not t and repr(("ce", p, q)) not in USED:
                    USED.add(repr(("ce", p, q)))
                    break
            return E(13, 2, lvl, RL + " Классический случай.", f"«${ctex(p)} \\vdash {ctex(q)}$ доказуема в $S^{{r1}}_c$: так всегда бывает с отношением превосходства»",
                     "при значениях " + ", ".join(f"${k_} = {vv}$" for k_, vv in sorted(v.items())) + " (интерпретация § 4) посылка истинна, заключение ложно; по MT1 § 4 "
                     "формула недоказуема", "с. 180–182, гл. 13, § 2, 4", "логика сравнения, диагностика", "S^r1_c")
        return epick(E1302, 13, 2, lvl, RL, "с. 179–180, гл. 13, § 2", "логика сравнения, диагностика", letters="abc")
    if lvl == 1:
        return ai13_rec(1)
    if lvl == 2:
        return [ai13_rec, read13][i % 2](2, "C")
    if lvl == 3:
        return [read13, nat13, lambda l: ai13_rec(l, "C", ACI, "AcI", "S^{r1}_c"), lambda l: ai13_rec(l, "C", T13, "T")][i % 4](3)
    if lvl == 4:
        return [deriv13, nat13, lambda l: ai13_rec(l, "C", AII13, "AII")][i % 3](4)
    if lvl == 5:
        return [ccheck_card, deriv13, nat13][i % 3](5)
    if lvl == 6:
        return ccheck_card(6)
    return ccheck_card(7, "S")


def m1303(lvl, d, i):
    if d:
        pool = [("«в логике порядка $(a(> c)b)$ — $c$ есть предикат»", "в логике порядка $c$ — субъект (D1 § 3, с. 181); предикат — в логике сравнения"),
                ("«схемы логики порядка отличаются от схем AI логики сравнения по существу»", "по с. 181 они имеют тот же вид, лишь вместо предиката $c$ фигурирует субъект $c$")]
        return epick(pool, 13, 3, lvl, RL, "с. 181, гл. 13, § 3", "логика порядка, диагностика")
    if lvl == 2:
        return read13(2, "R", sec=3)
    if lvl == 3:
        return read13(3, "C", sec=3)
    if lvl in (4, 5):
        k = rnd.choice(sorted(AI13))
        s = AI13[k]
        cc = rnd.choice(["c", "d"])
        out = s.replace("\\urcorner\\!>", f"\\urcorner(> {cc})").replace("?>", f"?(> {cc})").replace("\\urcorner\\!<", f"\\urcorner(< {cc})").replace("?<", f"?(< {cc})")
        out = re.sub(r"(?<![(\\?])> ", f"(> {cc})", out).replace("(< ", "(< ").replace(" < ", f"(< {cc})").replace(" = ", f"(= {cc})").replace("\\urcorner\\!=", f"\\urcorner(= {cc})")
        return card(13, 3, lvl, "D", "iso", f"{RL} Буква {cc} — субъект (порядок относительно {cc}). Запишите схему AI.{k} логики сравнения (${s}$) как схему логики порядка $S^{{r2}}_n$ "
                    "в полной записи $a\\alpha(> c)b$.", f"${out}$", "С. 181: схемы логики порядка имеют тот же вид, что AI логики сравнения, с субъектом $c$ вместо предиката.",
                    "с. 179–181, гл. 13, § 2–3", "логика порядка", system="S^r2_n")
    return ccheck_card(lvl, "S" if lvl == 7 else "C", sec=3).replace("Классический случай.", "Логика порядка, классический случай (с. 181).")


def ival(a_, b_, rel):
    return {"gt": a_ > b_, "ngt": a_ <= b_, "lt": a_ < b_, "nlt": a_ >= b_, "eq": a_ == b_, "neq": a_ != b_}[rel]


RELS = [("gt", "a > b", "п. 2"), ("ngt", "a \\urcorner\\!> b", "п. 2"), ("lt", "a < b", "п. 3, схема 9: $b > a$"), ("nlt", "a \\urcorner\\!< b", "п. 3, схема 11: $(a > b) : (a = b)$"),
        ("eq", "a = b", "п. 4, схема 15: $(a \\urcorner\\!> b)(b \\urcorner\\!> a)$"), ("neq", "a \\urcorner\\!= b", "п. 4, схема 17: $(a > b) : (b > a)$")]


def m1304(lvl, d, i):
    if d:
        pool = [("«по интерпретации § 4 $a ?> b$ имеет значение 1, если значения $a$ и $b$ равны»", "$a ?> b$ имеет значение 1, если соотношение $a$ и $b$ не известно; при "
                 "равных значениях истинно $a \\urcorner\\!> b$ (с. 182)"),
                ("«$(a > c^1) b \\vdash (a > c^2) b$ доказуема при любых $c^1$, $c^2$»", "по MT2 § 4 (с. 182) при различных $c^1$, $c^2$ она недоказуема: значения независимы (п. 5)")]
        return epick(pool, 13, 4, lvl, RL, "с. 182, гл. 13, § 4", "логика отношений, интерпретация, диагностика")
    a_, b_ = rnd.sample(range(1, 10), 2) if rnd.random() < 0.75 else (rnd.choice(range(1, 10)),) * 2
    its = rnd.sample(RELS, 3 if lvl < 7 else 4)
    if lvl == 1:
        return card(13, 4, 1, "R", "iso", f"{RL} Какова область значения субъектов в интерпретации § 4 гл. 13?", "Множество натуральных чисел (с. 182).", "С. 182.",
                    "с. 182, гл. 13, § 4", "логика отношений, интерпретация")
    return card(13, 4, lvl, {7: "S"}.get(lvl, "C"), "iso", f"{RL} По интерпретации § 4 гл. 13 (с. 182) значение $a$ — число {a_}, значение $b$ — число {b_}; соотношение известно. "
                "Найдите значения высказываний:\n\n" +
                items([f"${s}$" for _, s, _ in its]), answers([str(int(ival(a_, b_, r))) for r, _, _ in its]), "\n".join(f"{L[k]}) {w}." for k, (_, _, w) in enumerate(its)),
                "с. 179–182, гл. 13, § 2, 4", "логика отношений, интерпретация")


RELP = [("«первый ближе второго»", True), ("«первый раньше второго»", True), ("«первый правее второго»", True), ("«первый находится между вторым и третьим»", True),
        ("«первый тяжелее второго»", True), ("«красный»", False), ("«существует»", False), ("«обязательно»", False), ("«возможно»", False)]
DERP = [("«находится между»", True), ("«структура»", True), ("«ряд»", True), ("«существует»", False), ("«обязательно»", False), ("«возможно»", False), ("«случайно»", False)]
Q1301 = [("Какие две группы предикатов отношений выделяет § 1 гл. 13?", "Предикаты сравнения и предикаты порядка (с. 178)."),
         ("При каком условии имеют силу правила логики отношений (§ 1 гл. 13)?", "Если способы сравнения и упорядочивания известны и стандартны для предметов "
          "данного рода; в рамках одного утверждения предполагается тождество этих способов (с. 178)."),
         ("Определяет ли книга выражения «способ сравнения» и «способ упорядочивания»?", "Нет, они здесь не определяются (с. 178)."),
         ("Где рассматриваются свойства предикатов отношений (§ 1 гл. 13)?", "В логике отношений (с. 178).")]
Q1305 = [("Через что определяются производные термины порядка (§ 5 гл. 13)?", "Через предикаты порядка § 3 (с. 182)."),
         ("Где рассматривались производные термины порядка (§ 5 гл. 13)?", "В работах [3, 7] (с. 182).")]


def m1305(lvl, d, i, sec=5):
    if d:
        pool = [("«“находится между” — простой предикат, не связанный с предикатами порядка»", "по § 5 (с. 182) это порядковый термин, определяемый через предикаты порядка"),
                ("«производные термины порядка подробно определены в § 5»", "по с. 182 они рассматривались в работах [3, 7]; в книге лишь названы")]
        return epick(pool, 13, 5, lvl, RL, "с. 182, гл. 13, § 5", "производные термины порядка, диагностика")
    k = nxt("q1305")
    if k < len(Q1305):
        a, b = Q1305[k]
        return card(13, 5, lvl, "R" if lvl == 1 else "C", "iso", a, b, "Гл. 13, § 5.", "с. 182, гл. 13, § 5", "логика отношений", form="meta", answ="text")
    its = rnd.sample(DERP, 4)
    return card(13, 5, lvl, "R" if lvl == 1 else "C", "iso", "Какие из терминов § 5 гл. 13 называет производными терминами порядка (определяемыми через предикаты порядка)?\n\n" +
                items([s for s, _ in its]), answers(["да" if t_ else "нет" for _, t_ in its]), "С. 182: «находится между», «структура», «ряд» и т. п.", "с. 182, гл. 13, § 5",
                "логика отношений", form="nat")


def m1301(lvl, d, i):
    if d:
        pool = [("«правила логики отношений имеют силу при любых способах сравнения»", "по с. 178 — лишь при условии, что способы известны и стандартны; в рамках одного "
                 "утверждения предполагается их тождество"),
                ("«выражения “способ сравнения” и “способ упорядочивания” строго определены в § 1 гл. 13»", "по с. 178 они здесь не определяются"),
                ("«в одном утверждении можно сравнивать по разным способам для разных предикатов»", "по с. 178 в рамках одного утверждения предполагается тождество способов "
                 "установления порядка и сравнения для всех фигурирующих в нём предикатов")]
        return epick(pool, 13, 1, lvl, RL, "с. 178, гл. 13, § 1", "предикаты отношений, диагностика")
    k = nxt("q1301")
    if k < len(Q1301):
        a, b = Q1301[k]
        return card(13, 1, lvl, "R" if lvl == 1 else "C", "iso", a, b, "Гл. 13, § 1.", "с. 178, гл. 13, § 1", "логика отношений", form="meta", answ="text")
    its = rnd.sample(RELP, 4)
    return card(13, 1, lvl, "R" if lvl == 1 else "C", "iso", "Какие из предикатов относятся к предикатам отношений в смысле § 1 гл. 13?\n\n" + items([s for s, _ in its]),
                answers(["да" if t_ else "нет" for _, t_ in its]), "С. 178: предикаты вида «первый ближе второго», «первый раньше второго», «первый правее второго», "
                "«первый находится между вторым и третьим» и т. п.", "с. 178, гл. 13, § 1", "логика отношений", form="nat")


# ---- 13.06 S^r3
SR3 = {1: "\\sim(Rx)y \\vdash (Rx)\\sim y", 2: "(Rx)\\sim y \\vdash \\sim(Rx)y", 3: "(Rx)y(Rx)z \\vdash (Rx)(yz)", 4: "(Rx)(yz) \\vdash (Rx)y(Rx)z",
       5: "(Rx)y \\vee (Rx)z \\vdash (Rx)(y \\vee z)", 6: "(Rx)(y \\vee z) \\vdash (Rx)y \\vee (Rx)z", 7: "((R^1x)(R^2y))z \\vdash (R^1x)z(R^2y)z",
       8: "(R^1x)z(R^2y)z \\vdash ((R^1x)(R^2y))z", 9: "((R^1x) \\vee (R^2y))z \\vdash (R^1x)z \\vee (R^2y)z", 10: "(R^1x)z \\vee (R^2y)z \\vdash ((R^1x) \\vee (R^2y))z",
       11: "(R(x \\vee y))z \\vdash ((Rx) \\vee (Ry))z", 12: "((Rx) \\vee (Ry))z \\vdash (R(x \\vee y))z", 13: "(R(xy))z \\vdash ((Rx)(Ry))z", 14: "((Rx)(Ry))z \\vdash (R(xy))z",
       15: "(R^1x)y(aR^1b \\to bR^2a) \\vdash (R^2y)x"}
SR = "Буквы $x, y, z$ — высказывания (вертикальные стрелки опущены); $R, R^1, R^2$ — знаки порядка («до этого», «после этого», «через три часа» и т. п.)."


def sr3_rec(lvl, typ="R"):
    ks = rnd.sample(sorted(SR3), 3)
    return card(13, 6, lvl, typ, "iso", f"{SR} Каким аксиомным схемам $S^{{r3}}$ (§ 6 гл. 13, с. 183) соответствуют формулы?\n\n" + items([f"${SR3[k]}$" for k in ks]),
                answers([f"{k}" for k in ks]), "С. 183.", "с. 183, гл. 13, § 6", "система Sr3", system="S^r3")


def subst_tokens(s, mp):
    out = []
    for tok in re.findall(r"\\[A-Za-z]+|.", s, flags=re.S):
        if tok in mp:
            v = mp[tok]
            out.append(v if re.fullmatch(r"[a-z]", v) else f"({v})")
        else:
            out.append(tok)
    return "".join(out)


def sr3_sub(lvl, typ="D"):
    k = rnd.choice([1, 2, 3, 4, 5, 6])
    s = SR3[k]
    X, Y, Z = rnd.sample(["u", "v", "uv", "\\sim u", "u \\vee v", "w"], 3)
    out = subst_tokens(s, {"x": X, "y": Y, "z": Z})
    return card(13, 6, lvl, typ, "iso", f"{SR} Буквы $u, v, w$ — высказывания. Подставьте в схему {k} $S^{{r3}}$ (${s}$) вместо $x$ — ${X}$, $y$ — ${Y}$, $z$ — ${Z}$ (используйте нужные).",
                f"${out}$", "С. 183.", "с. 183, гл. 13, § 6", "система Sr3", system="S^r3")


def sr3_der(lvl, typ="D"):
    v_ = rnd.choice([("(Rx)(yz) \\vdash (Rx)y \\vee (Rx)z", ["$(Rx)(yz) \\vdash (Rx)y(Rx)z$ [4]", "$(Rx)y(Rx)z \\vdash (Rx)y \\vee (Rx)z$ [$S^s$]", "транзитивность [$S^s$]"]),
                     ("(Rx)(yz) \\vdash (Rx)(y \\vee z)", ["$(Rx)(yz) \\vdash (Rx)y(Rx)z$ [4]", "$(Rx)y(Rx)z \\vdash (Rx)y \\vee (Rx)z$ [$S^s$]", "$(Rx)y \\vee (Rx)z \\vdash (Rx)(y \\vee z)$ [5]",
                                                         "транзитивность [$S^s$]"]),
                     ("\\sim(Rx)\\sim y \\vdash (Rx)y", ["$\\sim(Rx)\\sim y \\vdash (Rx)\\sim\\sim y$ [1, подстановка $\\sim y$]", "замена $\\sim\\sim y$ на $y$ [$S^s$, R3]"]),
                     ("(Rx)\\sim(y \\vee z) \\vdash \\sim(Rx)y\\sim(Rx)z", ["$(Rx)\\sim(y \\vee z) \\vdash \\sim(Rx)(y \\vee z)$ [2]",
                       "$(Rx)y \\vee (Rx)z \\vdash (Rx)(y \\vee z)$ [5]", "контрапозиция 2 (множества элементарных высказываний совпадают) [$S^s$]: $\\sim(Rx)(y \\vee z) \\vdash \\sim((Rx)y \\vee (Rx)z)$",
                       "закон де Моргана и транзитивность [$S^s$]"]),
                     ("(R(xy))z \\vdash (Rx)z", ["$(R(xy))z \\vdash ((Rx)(Ry))z$ [13]", "$((Rx)(Ry))z \\vdash (Rx)z(Ry)z$ [7 при $R^1 = R^2 = R$]",
                                                  "$(Rx)z(Ry)z \\vdash (Rx)z$ [$S^s$]", "транзитивность [$S^s$]"])])
    pp = permute(["$" + v_[0] + "$"] + v_[1], "xyz")
    v_ = (pp[0][1:-1], pp[1:])
    if lvl == 4:
        sh, a_ = hide_step(v_[1])
        return card(13, 6, 4, "D", "complete", f"{SR} Восстановите пропущенное основание в выводе ${v_[0]}$ в $S^{{r3}}$:\n\n{sh}", a_, steps(v_[1]), "с. 183, гл. 13, § 6",
                    "система Sr3, вывод", system="S^r3")
    return card(13, 6, lvl, typ, "iso", f"{SR} Выведите в $S^{{r3}}$ формулу ${v_[0]}$ ($(Rx)y$ рассматривайте как высказывание при шагах $S^s$).", "См. решение.",
                steps(v_[1]) + "\n\nС. 183.", "с. 183, гл. 13, § 6", "система Sr3, вывод", answ="proof", system="S^r3")


THUN = [("«Гром прогремел через пять секунд после того, как сверкнула молния»", "$(Rx)y$: $x$ — «сверкнула молния», $y$ — «прогремел гром», $R$ — «через пять секунд после»"),
        ("«Через три часа после начала дождя река вышла из берегов»", "$(Rx)y$: $x$ — «начался дождь», $y$ — «река вышла из берегов», $R$ — «через три часа после»"),
        ("«В десяти метрах от дома растёт дуб»", "$(Rx)y$: $x$ — «стоит дом», $y$ — «растёт дуб», $R$ — «в десяти метрах от»"),
        ("«До того как выпал снег, ударили морозы»", "$(Rx)y$: $x$ — «выпал снег», $y$ — «ударили морозы», $R$ — «до этого»"),
        ("«Через минуту после звонка начался урок»", "$(Rx)y$: $x$ — «прозвенел звонок», $y$ — «начался урок», $R$ — «через минуту после»"),
        ("«После того как включили свет, все проснулись»", "$(Rx)y$: $x$ — «включили свет», $y$ — «все проснулись», $R$ — «после этого»"),
        ("«За два дня до выборов объявили итоги опроса»", "$(Rx)y$: $x$ — «прошли выборы», $y$ — «объявили итоги опроса», $R$ — «за два дня до»")]


def sr3_nat(lvl, typ="C"):
    s, f = THUN[nxt("thun") % len(THUN)]
    return card(13, 6, lvl, typ, "iso", f"Запишите в символике § 6 гл. 13 высказывание {s}.", f, "D1 § 6 (с. 183): $(R\\downarrow x)(\\downarrow y)$ — «$\\downarrow y$ имеет место в отношении $R$ к "
                "$\\downarrow x$»; стрелки опускаются.", "с. 183, гл. 13, § 6", "система Sr3", form="nat")


E1306 = [("«схема 1: $\\sim(Rx)y \\vdash \\sim(Rx)\\sim y$»", "схема 1 — $\\sim(Rx)y \\vdash (Rx)\\sim y$ (с. 183)"),
         ("«схема 4: $(Rx)(y \\vee z) \\vdash (Rx)y(Rx)z$»", "схема 4 — $(Rx)(yz) \\vdash (Rx)y(Rx)z$; для дизъюнкции — схема 6: $(Rx)(y \\vee z) \\vdash (Rx)y \\vee (Rx)z$ (с. 183)"),
         ("«схема 15 верна без условия $aR^1b \\to bR^2a$»", "в посылку схемы 15 входит $(aR^1b \\to bR^2a)$ (с. 183)"),
         ("«$(Rx)y$ читается: “$\\downarrow x$ имеет место в отношении $R$ к $\\downarrow y$”»", "читается: «$\\downarrow y$ имеет место в отношении $R$ к $\\downarrow x$» (с. 183)"),
         ("«по схеме 13: $((Rx)(Ry))z \\vdash (R(xy))z$»", "это схема 14; схема 13 — обратная: $(R(xy))z \\vdash ((Rx)(Ry))z$ (с. 183)")]


def m1306(lvl, d, i):
    if d:
        return epick(E1306, 13, 6, lvl, SR, "с. 183, гл. 13, § 6", "система Sr3, диагностика", "S^r3", letters="xyz")
    if lvl == 1:
        return sr3_rec(1)
    if lvl == 2:
        return [sr3_rec, sr3_sub, sr3_nat][i % 3](2, "C" if i % 3 != 1 else "D")
    if lvl == 3:
        return [sr3_sub, sr3_nat, sr3_rec, sr3_der][i % 4](3) if i % 4 != 2 else sr3_rec(3, "C")
    if lvl in (4, 5):
        return [sr3_der, sr3_sub, sr3_nat][i % 3](lvl)
    if lvl == 6:
        return [sr3_der, sr3_sub][i % 2](6, "C")
    return sr3_der(7, "S")


# ---- 13.07
OC = {"AI.1": "(x(R^1x)y)(aR^1b \\to bR^2a) \\vdash (y(R^2y)x)", "AI.2": "(x \\vee (R^1x)y)(aR^1b \\to bR^2a) \\vdash (y \\vee (R^2y)x)",
      "T1": "\\sim(x(Rx)y) \\dashv\\vdash \\sim x \\vee (Rx)\\sim y", "T2": "\\sim(x \\vee (Rx)y) \\dashv\\vdash \\sim x(Rx)\\sim y", "AIII.1": "(x(Rx)y \\to y(Ry)x)(y(Ry)x \\to x(Rx)y) \\vdash xy",
      "AIII.2": "xy \\vdash (x(Rx)y \\to y(Ry)x)(y(Ry)x \\to x(Rx)y)"}


def m1307(lvl, d, i):
    if d:
        pool = [("«для упорядоченных конъюнкций имеет силу $x(Rx)y \\vdash y(Ry)x$»", "по с. 184 такие формулы не имеют силы; имеют силу лишь формулы вида AI"),
                ("«обычную конъюнкцию нельзя рассматривать как частный случай упорядоченной»", "по с. 185 можно, приняв аксиомные схемы AIII")]
        return epick(pool, 13, 7, lvl, SR, "с. 184–185, гл. 13, § 7", "упорядоченные конъюнкции, диагностика")
    if lvl in (1, 2, 3):
        ks = rnd.sample(sorted(OC), 2)
        return card(13, 7, lvl, "R" if lvl == 1 else "C", "iso", f"{SR} Укажите схемы § 7 гл. 13 (с. 184–185):\n\n" + items([f"${OC[k]}$" for k in ks]), answers(ks), "С. 184–185.",
                    "с. 184–185, гл. 13, § 7", "упорядоченные конъюнкции")
    ex = rnd.choice([("«Он открыл дверь и затем вошёл»", "$x(Rx)y$ — упорядоченная конъюнкция («$x$ и затем $y$»)"),
                     ("«Сначала проверь данные или затем перезапусти расчёт»", "$x \\vee (Rx)y$ — упорядоченная дизъюнкция")])
    return card(13, 7, lvl, "C", "iso", f"{SR} Как записать по § 7 гл. 13 высказывание {ex[0]}? Почему его нельзя переставить как обычную конъюнкцию (дизъюнкцию)?",
                ex[1] + "; формулы вида $x(Rx)y \\vdash y(Ry)x$ и $x \\vee (Rx)y \\vdash y \\vee (Ry)x$ не имеют силы (с. 184).", "С. 184.", "с. 184, гл. 13, § 7",
                "упорядоченные конъюнкции", form="nat")


# ---- 13.08 логика изменения
CH = "Буквы $x, y, z, v$ — термины вида $\\downarrow x$ (стрелки опущены); $x \\Rightarrow y$ — «ситуация с $x$ превратилась в ситуацию с $y$»; $\\alpha$ — $\\urcorner$, $?$ или их отсутствие."
SITCH = [("$x \\Rightarrow y$ имеет значение 1", "$x$ имеет значение 0 и $y$ имеет значение 1", "1"), ("$y$ имеет значение 0", "$x \\Rightarrow y$ имеет значение 0", "1"),
         ("нужно значение $x \\urcorner\\!\\Rightarrow y$", "оно равно значению $x \\Rightarrow \\sim y$", "2"), ("нужно значение $x ?\\Rightarrow y$", "оно равно значению $\\sim x\\sim y$", "3"),
         ("нужно значение $(R(x \\Rightarrow y))(y \\Rightarrow z)$ ($R$ — «вслед за этим»)", "оно равно значению $x \\Rightarrow z$", "4"),
         ("нужно значение $(R(x \\Rightarrow y))(z \\Rightarrow v)$ ($R$ — «одновременно с этим»)", "оно равно значению $xz \\Rightarrow yv$", "5")]
ACH = {"AII.1": "(x \\Rightarrow y) \\vdash y", "AII.2": "(x \\urcorner\\!\\Rightarrow y) \\vdash (x \\Rightarrow \\sim y)", "AII.3": "(x \\Rightarrow \\sim y) \\vdash (x \\urcorner\\!\\Rightarrow y)",
       "AII.4": "(x ?\\Rightarrow y) \\vdash \\sim x\\sim y", "AII.5": "\\sim x\\sim y \\vdash (x ?\\Rightarrow y)", "AIII.1": "(x \\Rightarrow y)(R(x \\Rightarrow y))(y \\Rightarrow z) \\vdash (x \\Rightarrow z)",
       "AIII.2": "(x \\Rightarrow y)(R(x \\Rightarrow y))(z \\Rightarrow v) \\vdash (xz \\Rightarrow yv)", "AI.1": "Q(a)(R(Q(a)))\\urcorner Q(a) \\vdash (Q(a) \\Rightarrow \\urcorner Q(a))",
       "AI.2": "(Q(a) \\Rightarrow \\urcorner Q(a)) \\vdash Q(a)(R(Q(a)))\\urcorner Q(a)"}


def m1308(lvl, d, i):
    if d:
        pool = [("«если $x \\Rightarrow y$ имеет значение 1, то $x$ и $y$ имеют значение 1»", "по п. 1 интерпретации (с. 187) $x$ имеет значение 0, $y$ — 1"),
                ("«$x \\urcorner\\!\\Rightarrow y$ равнозначно $\\sim(x \\Rightarrow y)$»", "по п. 2 (с. 187) — $x \\Rightarrow \\sim y$"),
                ("«для классического случая AII.4 и AII.5 сохраняются с заменой $?$ на $\\sim$»", "они исключаются (с. 186)"),
                ("«элементарные высказывания изменения — любые $x \\Rightarrow y$»", "по D1 (с. 185) — только $Q(a) \\Rightarrow \\urcorner Q(a)$ и $\\urcorner Q(a) \\Rightarrow Q(a)$"),
                ("«AIII.1 верна, если $R$ — “одновременно с этим”»", "в AIII.1 $R$ — «вслед за этим» (с. 186)")]
        return epick(pool, 13, 8, lvl, CH, "с. 185–187, гл. 13, § 8", "логика изменения, диагностика", "S^ch")
    if lvl in (1, 2, 3):
        if i % 2 == 0 or lvl == 1:
            its = rnd.sample(SITCH, 3)
            return card(13, 8, lvl, "R" if lvl == 1 else "C", "iso", f"{CH} Что следует по интерпретации § 8 гл. 13 (с. 187)? Укажите пункт.\n\n" + items([s for s, _, _ in its]),
                        answers([f"{w} (п. {n})" for _, w, n in its]), "С. 187.", "с. 187, гл. 13, § 8", "логика изменения")
        ks = rnd.sample(sorted(ACH), 3)
        return card(13, 8, lvl, "C", "iso", f"{CH} $Q$ — предикат. Каким аксиомным схемам $S^{{ch}}$ (с. 186) соответствуют формулы?\n\n" + items([f"${ACH[k]}$" for k in ks]), answers(ks),
                    "С. 186.", "с. 186, гл. 13, § 8", "логика изменения", system="S^ch")
    if lvl in (4, 5):
        Q_ = rnd.choice(["Q", "P"])
        a = rnd.choice(["a", "b"])
        k = rnd.choice(["AI.1", "AI.2", "AII.2", "AII.1"])
        if k.startswith("AI."):
            out = ACH[k].replace("Q(a)", f"{Q_}({a})")
            return card(13, 8, lvl, "D", "iso", f"{CH} Запишите схему {k} $S^{{ch}}$ для предиката ${Q_}$ и термина ${a}$.", f"${out}$", "С. 186; AI означают, что предикат превращения "
                        "производен от предикатов порядка.", "с. 186, гл. 13, § 8", "логика изменения", system="S^ch")
        X, Y = rnd.sample(["u", "\\sim u", "uv", "u \\vee v", "w"], 2)
        out = sub_vars(ACH[k], {"x": wrapx(X), "y": wrapx(Y)}).replace("\\sim (", "\\sim(")
        return card(13, 8, lvl, "D", "iso", f"{CH} Буквы $u, v, w$ — термины-ситуации. Подставьте в {k} (${ACH[k]}$) вместо $x$ — ${X}$, вместо $y$ — ${Y}$.", f"${out}$",
                    "С. 186.", "с. 186, гл. 13, § 8", "логика изменения", system="S^ch")
    ks = rnd.sample(["AII.1", "AII.2", "AII.3", "AII.4", "AII.5", "AIII.1"], 3)
    def fate(k):
        if k in ("AII.4", "AII.5"):
            return "исключается"
        s = ACH[k].replace("\\urcorner\\!", "\\sim ")
        return f"${s}$"
    return card(13, 8, lvl, "S" if lvl == 7 else "C", "transfer", f"{CH} Что происходит со схемами $S^{{ch}}$ в классическом случае (с. 186)?\n\n" + items([f"{k}. ${ACH[k]}$" for k in ks]),
                answers([fate(k) for k in ks]), "С. 186: в AI, AII, AIII $\\urcorner$ заменяется на $\\sim$, AII.4 и AII.5 исключаются.", "с. 186, гл. 13, § 8", "логика изменения")


# ---- 13.09 физическое следование
PH = {"AI.1": "(x \\to (Rx)y) \\vdash (\\forall(\\downarrow x))((Rx)y)", "AI.2": "(\\forall(\\downarrow x))((Rx)y) \\vdash (x \\to (Rx)y)", "AI.3": "(x \\to (Rx)y) \\vdash N(\\downarrow ((Rx)y))",
      "AI.4": "N(\\downarrow ((Rx)y)) \\vdash (x \\to (Rx)y)", "AI.5": "(x \\urcorner\\!\\to (Rx)y) \\vdash (\\exists(\\downarrow x))((Rx)\\sim y)", "AI.6": "(\\exists(\\downarrow x))((Rx)\\sim y) \\vdash (x \\urcorner\\!\\to (Rx)y)",
      "AI.7": "(x \\urcorner\\!\\to (Rx)y) \\vdash M(\\downarrow ((Rx)\\sim y))", "AI.8": "M(\\downarrow ((Rx)\\sim y)) \\vdash (x \\urcorner\\!\\to (Rx)y)",
      "T1 (AI)": "(x ?\\to (Rx)y) \\dashv\\vdash (?\\forall(\\downarrow x))((Rx)y)", "T2 (AI)": "(x ?\\to (Rx)y) \\dashv\\vdash ?N(\\downarrow ((Rx)y))",
      "AII.3": "(x \\to (Rx)y)(y \\to z) \\vdash (x \\to (Rx)z)", "T1 (AII)": "(x \\to (Rx)(yz)) \\dashv\\vdash (x \\to (Rx)y)(x \\to (Rx)z)",
      "T2 (AII)": "(x \\to (Rx)y) \\vee (x \\to (Rx)z) \\vdash (x \\to (Rx)(y \\vee z))"}
PHX = "Буквы $x, y, z$ — высказывания; $R$ — отношение порядка; $x\\alpha \\to (Rx)y$ — высказывание о физическом следовании."


def ph_rec(lvl, typ="C"):
    ks = rnd.sample(sorted(PH), 3)
    return card(13, 9, lvl, typ, "iso", f"{PHX} Укажите схемы $S^{{ph}}$ (§ 9 гл. 13, с. 187–188):\n\n" + items([f"${PH[k]}$" for k in ks]), answers(ks), "С. 187–188.",
                "с. 187–188, гл. 13, § 9", "физическое следование", system="S^ph")


def ph_nat(lvl, typ="C"):
    ev = rnd.choice([("«нагреть металлический стержень»", "«стержень удлинится»"), ("«бросить камень вверх»", "«камень упадёт»"), ("«замкнуть цепь»", "«лампа загорится»")])
    v_ = rnd.choice([("AI.3", f"«Если {ev[0][1:-1]}, то после этого {ev[1][1:-1]}» ($x \\to (Rx)y$)", "$N(\\downarrow ((Rx)y))$: необходимо, что после $x$ наступает $y$"),
                     ("AI.1", f"«Если {ev[0][1:-1]}, то после этого {ev[1][1:-1]}»", "$(\\forall(\\downarrow x))((Rx)y)$: всякий раз после $x$ наступает $y$"),
                     ("AI.7", f"«{ev[0][1:-1].capitalize()} не обязывает признать, что после этого {ev[1][1:-1]}» ($x \\urcorner\\!\\to (Rx)y$)", "$M(\\downarrow ((Rx)\\sim y))$: возможно, что после $x$ "
                      "не наступит $y$")])
    return card(13, 9, lvl, typ, "iso", f"{PHX} Пусть $x$ — {ev[0]}, $y$ — {ev[1]}. Что следует по {v_[0]} § 9 гл. 13 из высказывания {v_[1]}?", v_[2] + ".", f"{v_[0]} (с. 187).",
                "с. 187, гл. 13, § 9", "физическое следование", form="nat", system="S^ph")


def m1309(lvl, d, i):
    if d:
        pool = [("«AI.3: $N(\\downarrow ((Rx)y)) \\vdash (x \\urcorner\\!\\to (Rx)y)$»", "AI.4 — $N(\\downarrow ((Rx)y)) \\vdash (x \\to (Rx)y)$ (с. 187)"),
                ("«из $x \\urcorner\\!\\to (Rx)y$ следует $(\\exists(\\downarrow x))((Rx)y)$»", "по AI.5 следует $(\\exists(\\downarrow x))((Rx)\\sim y)$ (с. 187)"),
                ("«AII.3: $(x \\to (Rx)y)(y \\to z) \\vdash (x \\to z)$»", "AII.3 — $\\ldots \\vdash (x \\to (Rx)z)$: отношение порядка сохраняется (с. 188)"),
                ("«T2 (AII) обратима: $(x \\to (Rx)(y \\vee z)) \\vdash (x \\to (Rx)y) \\vee (x \\to (Rx)z)$»", "в книге дана лишь T2 (с. 188); ср. ошибочность "
                 "$(x \\rightarrow y \\vee z) \\vdash (x \\rightarrow y) \\vee (x \\rightarrow z)$ для условности (гл. 6, с. 88)"),
                ("«AI.1: $(x \\to (Rx)y) \\vdash (\\exists(\\downarrow x))((Rx)y)$»", "AI.1 — $\\ldots \\vdash (\\forall(\\downarrow x))((Rx)y)$ (с. 187)"),
                ("«из $(x \\to (Rx)y)$ следует $M(\\downarrow ((Rx)y))$ по AI.3»", "по AI.3 следует $N(\\downarrow ((Rx)y))$ — необходимо (с. 187)"),
                ("«T2 (AI): $(x ?\\to (Rx)y) \\dashv\\vdash ?M(\\downarrow ((Rx)y))$»", "T2 — $\\ldots \\dashv\\vdash ?N(\\downarrow ((Rx)y))$; с $?M$ — T4, и там $\\sim y$: $?M(\\downarrow ((Rx)\\sim y))$ (с. 187)")]
        return epick(pool, 13, 9, lvl, PHX, "с. 187–188, гл. 13, § 9", "физическое следование, диагностика", "S^ph")
    if lvl == 1:
        return card(13, 9, 1, "R", "iso", "Какие высказывания § 9 гл. 13 называет высказываниями о физическом следовании?", "Условные высказывания вида $x\\alpha \\to (Rx)y$ (с. 187).",
                    "С. 187.", "с. 187, гл. 13, § 9", "физическое следование")
    if lvl in (2, 3, 4):
        return ph_rec(lvl)
    return ph_nat(lvl, "S" if lvl == 7 else "C") if i % 2 == 0 or lvl == 7 else ph_rec(lvl)


# ================================================================ гл. 14
NR = "Буква $a$ — название действия, $\\tilde a$ — противоположное действие; $O$ — «обязательно», $P$ — «разрешено», $\\text{З}$ — «запрещено», $\\text{Б}$ — «безразлично», $\\text{Н}$ — «необязательно»."
AN = {"AI.1": "O(a) \\vdash P(a)", "AI.2": "\\urcorner P(a) \\vdash \\urcorner O(a)", "AI.3": "?P(a) \\vdash \\sim O(a)", "AII.1": "O(a) \\dashv\\vdash \\urcorner P(\\tilde a)",
      "AII.2": "\\urcorner O(a) \\dashv\\vdash P(\\tilde a)", "AII.3": "?O(a) \\dashv\\vdash ?P(\\tilde a)", "AIII.1": "\\text{З}(a) \\dashv\\vdash \\urcorner P(a)", "AIII.2": "\\urcorner \\text{З}(a) \\dashv\\vdash P(a)",
      "AIII.3": "?\\text{З}(a) \\dashv\\vdash ?P(a)", "AIV.1": "\\text{Б}(a) \\dashv\\vdash P(a)P(\\tilde a)", "AIV.2": "\\urcorner \\text{Б}(a) \\dashv\\vdash \\urcorner P(a) \\vee \\urcorner P(\\tilde a)",
      "AIV.3": "?\\text{Б}(a) \\dashv\\vdash (?P(a) \\vee ?P(\\tilde a))\\sim\\urcorner P(a)\\sim\\urcorner P(\\tilde a)", "AV.1": "\\text{Н}(a) \\dashv\\vdash \\urcorner O(a)",
      "AV.2": "\\urcorner \\text{Н}(a) \\dashv\\vdash O(a)", "AV.3": "?\\text{Н}(a) \\dashv\\vdash ?O(a)"}
TOP = {("O", ""): "\\urcorner P(\\tilde a)", ("O", "\\urcorner"): "P(\\tilde a)", ("O", "?"): "?P(\\tilde a)", ("З", ""): "\\urcorner P(a)", ("З", "\\urcorner"): "P(a)", ("З", "?"): "?P(a)",
       ("Б", ""): "P(a)P(\\tilde a)", ("Б", "\\urcorner"): "\\urcorner P(a) \\vee \\urcorner P(\\tilde a)", ("Н", ""): "P(\\tilde a)", ("Н", "\\urcorner"): "\\urcorner P(\\tilde a)", ("Н", "?"): "?P(\\tilde a)"}
TSRC = {("O", ""): "AII.1", ("O", "\\urcorner"): "AII.2", ("O", "?"): "AII.3", ("З", ""): "AIII.1", ("З", "\\urcorner"): "AIII.2", ("З", "?"): "AIII.3", ("Б", ""): "AIV.1",
        ("Б", "\\urcorner"): "AIV.2", ("Н", ""): "AV.1 и AII.2", ("Н", "\\urcorner"): "AV.2 и AII.1", ("Н", "?"): "AV.3 и AII.3"}
CLN = {"1": "O(a) \\vdash P(a)", "2": "\\sim P(a) \\vdash \\sim O(a)", "3": "O(a) \\dashv\\vdash \\sim P(\\tilde a)", "4": "\\text{З}(a) \\dashv\\vdash \\sim P(a)", "5": "\\text{Б}(a) \\dashv\\vdash P(a)P(\\tilde a)",
       "6": "\\text{Н}(a) \\dashv\\vdash \\sim O(a)"}
ACTS = ["курение в зале", "проезд на красный свет", "оплата проезда", "переход улицы", "пользование библиотекой", "уплата налога", "сдача экзамена"]


def ptex(pred, al):
    p = "O" if pred == "O" else f"\\text{{{pred}}}"
    return f"{al + ' ' if al == '\\urcorner' else al}{p}(a)"


def to_p(lvl, typ="D"):
    pred, al = rnd.choice(sorted(TOP))
    return card(14, 0, lvl, typ, "iso", f"{NR} Выразите ${ptex(pred, al)}$ через предикат $P$ по аксиомным схемам $S^n_n$ (гл. 14, с. 190).", f"${TOP[(pred, al)]}$ ({TSRC[(pred, al)]})",
                "С. 190: $O$ и $P$, $\\text{З}$ и $P$, $\\text{Н}$ и $O$ логически взаимозаменимы; $\\text{Б}$ определяется через $P$.", "с. 190, гл. 14", "нормативные предикаты", system="S^n_n")


def an_rec(lvl, typ="R"):
    ks = rnd.sample(sorted(AN), 3)
    return card(14, 0, lvl, typ, "iso", f"{NR} Каким аксиомным схемам $S^n_n$ (гл. 14, с. 189–190) соответствуют формулы?\n\n" + items([f"${AN[k]}$" for k in ks]), answers(ks),
                "С. 189–190.", "с. 189–190, гл. 14", "нормативные предикаты", system="S^n_n")


def nat14(lvl, typ="C"):
    act = rnd.choice(ACTS)
    v_ = rnd.choice([("запрещено", "не разрешено", "AIII.1: $\\text{З}(a) \\dashv\\vdash \\urcorner P(a)$"), ("обязательно", "разрешено", "AI.1: $O(a) \\vdash P(a)$"),
                     ("обязательно", "противоположное действие не разрешено", "AII.1: $O(a) \\dashv\\vdash \\urcorner P(\\tilde a)$"),
                     ("безразлично", "разрешено и само действие, и противоположное", "AIV.1: $\\text{Б}(a) \\dashv\\vdash P(a)P(\\tilde a)$"),
                     ("необязательно", "не обязательно (в смысле $\\urcorner$)", "AV.1: $\\text{Н}(a) \\dashv\\vdash \\urcorner O(a)$"),
                     ("не разрешено", "не обязательно", "AI.2: $\\urcorner P(a) \\vdash \\urcorner O(a)$")])
    return card(14, 0, lvl, typ, "iso", f"{NR} Действие $a$ — {act}. Что следует по схемам $S^n_n$ из высказывания «$a$ {v_[0]}»?", f"«$a$ {v_[1]}» — {v_[2]}.", "С. 189–190.",
                "с. 189–190, гл. 14", "нормативные предикаты", form="nat", system="S^n_n")


def cl14(lvl, typ="C"):
    ks = rnd.sample(sorted(AN), 3)
    def fate(k):
        s = AN[k]
        if "?" in s:
            return "исключается"
        return "$" + s.replace("\\urcorner ", "\\sim ").replace("\\urcorner", "\\sim ") + "$"
    return card(14, 0, lvl, typ, "transfer", f"{NR} Что происходит со схемами $S^n_n$ при переходе к классической системе $S^n_c$ (с. 190)?\n\n" + items([f"{k}. ${AN[k]}$" for k in ks]),
                answers([fate(k) for k in ks]), "С. 190: исключается всё, что связано с $?$, и $\\urcorner$ заменяется на $\\sim$; схемы $S^n_c$: " +
                "; ".join(f"{n}. ${s}$" for n, s in CLN.items()) + ".", "с. 190, гл. 14", "нормативные предикаты")


def rel14(lvl, typ="C"):
    q = [("Как связаны предикаты $O$ и $P$ согласно AI (с. 190)?", "Дедуктивно связаны, причём $O$ категорически сильнее $P$."),
         ("Как связаны $O$ и $P$ согласно AII (с. 190)?", "Логически взаимозаменимы."), ("Как связаны $\\text{З}$ и $P$ согласно AIII?", "Логически взаимозаменимы (с. 190)."),
         ("Как связаны $\\text{Н}$ и $O$ согласно AV?", "Логически взаимозаменимы (с. 190)."), ("Через какой предикат определяется $\\text{Б}$?", "Через $P$ (AIV, с. 190)."),
         ("Почему нормативная логика сама по себе тривиальна (с. 191)?", "Сложности возникают из-за неясности терминологии и неявных допущений, в частности неявно "
          "предполагаемых кванторов."), ("Как фактически употребляется высказывание «Действие $a$ разрешено» (с. 191)?", "Как «Всякое действие, называемое $a$, разрешено»."),
         ("Что можно установить в рамках логики о нормативных предикатах (с. 189)?", "Лишь их взаимоотношения: отнести их к определённым логическим типам "
          "(дедуктивно связанные, логически взаимозаменимые и т. п.).")]
    a, b = q[nxt("rel14") % len(q)]
    return card(14, 0, lvl, typ, "iso", a, b, "Гл. 14.", "с. 189–191, гл. 14", "нормативные предикаты", form="meta", answ="text")


def der14(lvl, typ="D"):
    v_ = rnd.choice([("\\text{З}(a) \\vdash \\urcorner O(a)", ["$\\text{З}(a) \\vdash \\urcorner P(a)$ [AIII.1]", "$\\urcorner P(a) \\vdash \\urcorner O(a)$ [AI.2]", "транзитивность [$S^s$]"]),
                     ("O(\\tilde a) \\vdash \\text{З}(a)", ["$O(\\tilde a) \\vdash \\urcorner P(\\tilde{\\tilde a})$ [AII.1 для $\\tilde a$]", "$\\tilde{\\tilde a}$ заменяется на $a$ [AI.10 гл. 9]",
                                                         "$\\urcorner P(a) \\vdash \\text{З}(a)$ [AIII.1]", "транзитивность [$S^s$]"]),
                     ("\\text{Б}(a) \\vdash P(a)", ["$\\text{Б}(a) \\vdash P(a)P(\\tilde a)$ [AIV.1]", "отбрасывание конъюнкта [$S^s$]"]),
                     ("\\urcorner \\text{Н}(a) \\vdash P(a)", ["$\\urcorner \\text{Н}(a) \\vdash O(a)$ [AV.2]", "$O(a) \\vdash P(a)$ [AI.1]", "транзитивность [$S^s$]"]),
                     ("\\text{Н}(a) \\vdash P(\\tilde a)", ["$\\text{Н}(a) \\vdash \\urcorner O(a)$ [AV.1]", "$\\urcorner O(a) \\vdash P(\\tilde a)$ [AII.2]", "транзитивность [$S^s$]"]),
                     ("O(a) \\vdash \\urcorner \\text{З}(a)", ["$O(a) \\vdash P(a)$ [AI.1]", "$P(a) \\vdash \\urcorner \\text{З}(a)$ [AIII.2]", "транзитивность [$S^s$]"]),
                     ("\\text{Б}(a) \\vdash \\urcorner \\text{З}(a)", ["$\\text{Б}(a) \\vdash P(a)P(\\tilde a)$ [AIV.1]", "отбрасывание конъюнкта [$S^s$]", "$P(a) \\vdash \\urcorner \\text{З}(a)$ [AIII.2]",
                                                                        "транзитивность [$S^s$]"]),
                     ("\\text{Б}(a) \\vdash \\text{Н}(a)", ["$\\text{Б}(a) \\vdash P(a)P(\\tilde a)$ [AIV.1]", "отбрасывание конъюнкта: $P(\\tilde a)$ [$S^s$]", "$P(\\tilde a) \\vdash \\urcorner O(a)$ [AII.2]",
                                                                "$\\urcorner O(a) \\vdash \\text{Н}(a)$ [AV.1]", "транзитивность [$S^s$]"]),
                     ("\\text{З}(a) \\vdash \\urcorner \\text{Б}(a)", ["$\\text{З}(a) \\vdash \\urcorner P(a)$ [AIII.1]", "$\\urcorner P(a) \\vdash \\urcorner P(a) \\vee \\urcorner P(\\tilde a)$ — "
                                                                        "в $S^s$ недопустимо (новое высказывание); вместо этого: схема AIV.2 справа налево применяется к дизъюнкции, полученной иначе"]),
                     ("\\urcorner \\text{Н}(a) \\vdash \\urcorner P(\\tilde a)", ["$\\urcorner \\text{Н}(a) \\vdash O(a)$ [AV.2]", "$O(a) \\vdash \\urcorner P(\\tilde a)$ [AII.1]", "транзитивность [$S^s$]"])])
    if "недопустимо" in v_[1][-1]:
        v_ = ("\\urcorner \\text{Н}(a) \\vdash \\urcorner \\text{З}(a)", ["$\\urcorner \\text{Н}(a) \\vdash O(a)$ [AV.2]", "$O(a) \\vdash P(a)$ [AI.1]", "$P(a) \\vdash \\urcorner \\text{З}(a)$ [AIII.2]",
                                                                      "транзитивность [$S^s$]"])
    if lvl == 4:
        sh, a_ = hide_step(v_[1])
        return card(14, 0, 4, "D", "complete", f"{NR} Восстановите пропущенное основание в выводе ${v_[0]}$ в $S^n_n$:\n\n{sh}", a_, steps(v_[1]), "с. 189–190, гл. 14",
                    "нормативные предикаты, вывод", system="S^n_n")
    return card(14, 0, lvl, typ, "iso", f"{NR} Выведите в $S^n_n$ формулу ${v_[0]}$.", "См. решение.", steps(v_[1]) + "\n\nС. 189–190.", "с. 189–190, гл. 14",
                "нормативные предикаты, вывод", answ="proof", system="S^n_n")


E14 = [("«$O(a) \\dashv\\vdash \\urcorner P(a)$»", "по AII.1 $O(a) \\dashv\\vdash \\urcorner P(\\tilde a)$: обязательно то, противоположность чему не разрешена (с. 190)"),
       ("«$\\text{З}(a) \\dashv\\vdash \\urcorner O(a)$»", "по AIII.1 $\\text{З}(a) \\dashv\\vdash \\urcorner P(a)$; $\\urcorner O(a)$ равнозначно $\\text{Н}(a)$ (AV.1, с. 190)"),
       ("«$P(a) \\vdash O(a)$ — разрешённое обязательно»", "по AI.1 наоборот: $O(a) \\vdash P(a)$; $O$ категорически сильнее $P$ (с. 190)"),
       ("«$\\text{Б}(a) \\dashv\\vdash P(a) \\vee P(\\tilde a)$»", "по AIV.1 $\\text{Б}(a) \\dashv\\vdash P(a)P(\\tilde a)$ (с. 190)"),
       ("«в $S^n_c$ сохраняется $?P(a) \\vdash \\sim O(a)$»", "в классическом случае исключается всё, что связано с $?$ (с. 190)"),
       ("«$\\text{Н}(a) \\dashv\\vdash \\urcorner P(a)$»", "по AV.1 $\\text{Н}(a) \\dashv\\vdash \\urcorner O(a)$ (с. 190)"),
       ("«нормативные предикаты подчиняются особым правилам, отличным от общих правил логики»", "по с. 189 на них распространяются общие правила, относящиеся к любым предикатам"),
       ("«$\\urcorner \\text{Б}(a) \\dashv\\vdash \\urcorner P(a)\\urcorner P(\\tilde a)$»", "по AIV.2 $\\urcorner \\text{Б}(a) \\dashv\\vdash \\urcorner P(a) \\vee \\urcorner P(\\tilde a)$ (с. 190)")]


def nat14e(lvl):
    act = rnd.choice(ACTS)
    v_ = rnd.choice([("«$a$ запрещено; значит, $a$ обязательно не выполнять, а противоположное — запрещено»", "из $\\text{З}(a)$ по AIII.1 следует $\\urcorner P(a)$; по AII.1 (для $\\tilde a$) "
                      "это равнозначно $O(\\tilde a)$, а не запрету $\\tilde a$"),
                     ("«$a$ разрешено, значит, обязательно»", "из $P(a)$ не следует $O(a)$; по AI.1 только $O(a) \\vdash P(a)$"),
                     ("«$a$ необязательно; значит, $a$ запрещено»", "$\\text{Н}(a)$ равнозначно $\\urcorner O(a)$ и $P(\\tilde a)$ (AV.1, AII.2): разрешено противоположное, а не запрещено $a$")])
    return E(14, 0, lvl, NR + f" Действие $a$ — {act}.", v_[0], v_[1], "с. 189–190, гл. 14", "нормативные предикаты, диагностика", form="nat")


def m1400(lvl, d, i):
    if d:
        return nat14e(lvl) if i % 3 == 0 else epick(E14, 14, 0, lvl, NR, "с. 189–191, гл. 14", "нормативные предикаты, диагностика", "S^n_n")
    if lvl == 1:
        return an_rec(1)
    if lvl == 2:
        return [an_rec, to_p, rel14][i % 3](2, "C" if i % 3 != 1 else "D")
    if lvl == 3:
        return [to_p, nat14, rel14, an_rec][i % 4](3) if i % 4 != 3 else an_rec(3, "C")
    if lvl == 4:
        return [der14, to_p, nat14, rel14][i % 4](4)
    if lvl == 5:
        return [der14, nat14, cl14, to_p][i % 4](5)
    if lvl == 6:
        return [cl14, der14, nat14][i % 3](6, "C")
    return cl14(7, "S")


# ================================================================ Приложение
AP = "Буквы $a, b$ — высказывания (в приложении буквами обозначаются и высказывания); $a^i$ — высказывания; кванторы — по термину $a$."


def star(f):
    """Предварительное преобразование x → x* (с. 192)."""
    k = f[0]
    if k == "neg":
        g = f[1]
        if g[0] == "conj":
            return W(*[star(N(h)) for h in g[1]])
        if g[0] == "wdis":
            return C(*[star(N(h)) for h in g[1]])
        if g[0] == "neg":
            return star(g[1])
        if g[0] == "ex":
            return star(ALL(g[1], N(g[2])))
        return N(star(g))
    if k == "ex":
        return N(ALL(f[1], star(N(f[2]))))
    if k == "all":
        return ALL(f[1], star(f[2]))
    if k in ("conj", "wdis"):
        return (k, tuple(star(h) for h in f[1]))
    return f


def ap_rand(depth=2):
    if depth == 0 or rnd.random() < 0.25:
        return V(rnd.choice("xyz"))
    k = rnd.choice(["neg", "neg", "conj", "wdis", "q"])
    if k == "neg":
        return N(ap_rand(depth - 1))
    if k == "q":
        return rnd.choice([ALL, EX])("a", ap_rand(depth - 1))
    a1, a2 = ap_rand(depth - 1), ap_rand(depth - 1)
    while a1 == a2:
        a2 = ap_rand(depth - 1)
    return (k, (a1, a2))


def star_card(lvl, typ="D"):
    for _ in range(500):
        f = ap_rand(2 if lvl <= 2 else 3)
        s = star(f)
        if s != f and repr(("st", f)) not in USED:
            USED.add(repr(("st", f)))
            break
    return card(15, 0, lvl, typ, "iso", "Буквы $x, y, z$ — высказывания (в них может входить термин $a$). Выполните предварительное преобразование приложения (с. 192): "
                f"образуйте $x^*$ для $x = {T(f)}$.", f"${T(s)}$", "С. 192: $\\sim(a^1 \\ldots a^n)$ → $\\sim a^1 \\vee \\ldots \\vee \\sim a^n$; $\\sim(a^1 \\vee \\ldots \\vee a^n)$ → "
                "$\\sim a^1 \\ldots \\sim a^n$; $\\sim\\sim a$ → $a$; $(\\exists a)b$ → $\\sim(\\forall a)\\sim b$. Получаемые высказывания равнозначны исходным.",
                "с. 192, Приложение", "приписывание значений")


def lits(f):
    k = f[0]
    if k == "v":
        return [[(f[1], 1)]]
    if k == "neg" and f[1][0] == "v":
        return [[(f[1][1], 0)]]
    if k == "conj":
        out = []
        for h in f[1]:
            out += lits(h)
        return out
    if k == "wdis":
        res = [[]]
        for h in f[1]:
            cl = lits(h)
            res = [r + c for r in res for c in cl]
        return res
    raise ValueError(k)


def ltex(l_):
    return l_[0] if l_[1] else f"\\sim {l_[0]}"


def repr_card(lvl, typ="C"):
    for _ in range(500):
        f = G6.G.rnd_f("xy", 2, "w")
        try:
            cls = lits(star(f))
        except ValueError:
            continue
        if 1 < len(cls) <= 4 and all(len(c) <= 3 for c in cls) and repr(("rp", f)) not in USED:
            USED.add(repr(("rp", f)))
            break
    forms = []
    for c in cls:
        c2 = list(dict.fromkeys(c))
        if len(c2) == 1:
            c2 = c2 * 2
        cc, dd = c2[0], c2[1:]
        forms.append(f"\\sim {ltex(cc)} \\vdash {' \\vee '.join(ltex(x) for x in dd)}".replace("\\sim \\sim ", ""))
    taut = all(any((n, 1) in c and (n, 0) in c for n in "xyz") for c in cls)
    return card(15, 0, lvl, typ, "iso", f"Буквы $x, y$ — элементарные высказывания. Найдите представительство высказывания ${Q.tex(f)}$ в классе формул следования (D3 приложения, "
                "с. 194) и установите по MT1 (с. 195), тавтология ли оно.", "Формулы: " + "; ".join(f"${s}$" for s in forms) + ". " + ("Все — тавтологии, высказывание — тавтология." if taut else
                "Не все — тавтологии, высказывание не тавтология."),
                f"$x^* = {Q.tex(star(f))}$; по D3 (пп. 1–3) оно приводится к множеству формул вида $c \\vee d$: " + "; ".join(" \\vee ".join(f"${ltex(x)}$" for x in c) for c in cls) +
                " (элементарное $a$ заменяется на $a \\vee a$); по п. 4 $c \\vee d$ заменяется на $\\sim c \\vdash d$. MT1: высказывание — тавтология тогда и только тогда, когда "
                "тавтологии все формулы его представительства.", "с. 192, 194–195, Приложение", "приписывание значений")


QR = [("вхождению $(\\forall a)b$ в высказывание приписали значение 1", "всем остальным вхождениям $(\\forall a)b$ в это высказывание приписывается 1", "1"),
      ("$(\\forall a)b$ приписали значение 1", "$b$ приписывается значение 1", "2"), ("$(\\forall a)b$ приписали значение 0", "значение $b$ ещё не определяется", "2"),
      ("$b$ приписали значение 0", "$(\\forall a)b$ приписывается значение 0", "3"), ("$b$ приписали значение 1", "значение $(\\forall a)b$ этим ещё не определяется", "3"),
      ("приписав $x$ значение 1, мы вынуждены приписать 1 высказыванию $b$ в $y$", "$(\\forall a)b$ в $y$ приписывается значение 1", "4"),
      ("приписав $x$ значение 1, мы не вынуждены приписывать 1 высказыванию $b$", "$(\\forall a)b$ приписывается значение 0", "5"),
      ("$x$ есть противоречие по этим правилам", "$x \\vdash y$ есть тавтология", "правило для формул следования"),
      ("$y$ есть тавтология по этим правилам", "$x \\vdash y$ есть тавтология", "правило для формул следования")]


def qr_card(lvl, typ="C"):
    its = rnd.sample(QR, 3)
    return card(15, 0, lvl, typ, "iso", "Буквы $a$ — термин, $b$ — высказывание; формула $x \\vdash y$ приведена к виду $x^* \\vdash y^*$. Что следует по правилам прямой интерпретации "
                "приложения (с. 192–193)?\n\n" + items([s for s, _, _ in its]), answers([f"{w} ({n if not n.isdigit() else 'правило ' + n})" for _, w, n in its]),
                "С. 192–193.", "с. 192–193, Приложение", "приписывание значений")


def mt23(lvl, typ="C"):
    for _ in range(300):
        f = G6.G.rnd_f("xy", 2, "w")
        if repr(("mt23", f)) not in USED:
            USED.add(repr(("mt23", f)))
            break
    q = rnd.choice([("\\forall a", "MT2"), ("\\exists a", "MT2"), ("\\forall a)(\\exists b", "MT3")])
    t = Q.is_taut(f)
    return card(15, 0, lvl, typ, "iso", f"Буквы $x, y$ — высказывания. Тавтология ли высказывание $({q[0]})({Q.tex(f)})$ (приложение, с. 195)?", "Да" if t else "Нет",
                f"{q[1]}: высказывание $(\\forall a)x$ (и $(\\exists a)x$, и $(K^1a^1) \\ldots (K^na^n)x$) — тавтология тогда и только тогда, когда $x$ — тавтология. " +
                ("$" + Q.tex(f) + "$ — тавтология." if t else f"$" + Q.tex(f) + "$ не тавтология: при " + G6.G.SY.env_text(Q.counter(f)) + " — 0."),
                "с. 195, Приложение", "приписывание значений")


def ren_card(lvl, typ="C"):
    base = rnd.choice([EL("a", "c"), C(EL("a", "c"), EL("a", "d")), W(EL("a", "c"), N(EL("a", "d")))])
    q = rnd.choice([ALL, EX])
    x = q("a", base)
    good = rnd.random() < 0.5
    nb = rnd.choice(["b", "e"])
    if good:
        y = q(nb, Q_sub(base, "a", nb))
        ok, why = True, f"$y$ получается заменой $(Ka)z$ на $(K{nb})v$, где $v$ — из $z$ заменой $a$ на ${nb}$, и ${nb}$ не входит в $z$"
    else:
        kind = rnd.choice(["free", "clash"])
        if kind == "clash":
            y = q("c", Q_sub(base, "a", "c"))
            ok, why = False, "новый термин $c$ уже входит в $z$ — условие $D^i$ нарушено"
        else:
            y = q(nb, base)
            ok, why = False, f"$a$ в $z$ не заменён на ${nb}$ — это не переименование"
    return card(15, 0, lvl, typ, "open", f"Буквы $a, b, c, d, e$ — термины. Является ли ${G7.FT(x, y)}$ формулой переименования (доказуемой в $S^i$, определение $D^i$, с. 197)?",
                "Да" if ok else "Нет", why[0].upper() + why[1:] + ".", "с. 197, Приложение", "приписывание значений, переименование")


def Q_sub(f, a, b):
    k = f[0]
    if k == "el":
        return EL(b if f[1] == a else f[1], b if f[2] == a else f[2])
    if k == "neg":
        return N(Q_sub(f[1], a, b))
    if k in ("all", "ex"):
        return f if f[1] == a else (k, f[1], Q_sub(f[2], a, b))
    return (k, tuple(Q_sub(g, a, b) for g in f[1]))


SYS15 = [("$S^6_{cq}$", "система с аксиомной схемой A5, принятой в § 11 гл. 7 ($S^{6}$ вместо $S^s$); для неё есть процедура разрешимости (с. 195–196)"),
         ("$S^k$", "$S^6_{cq}$ без квантификации предикатов плюс схемы $A^k$: $(\\forall a)x \\vdash y$ и $y \\vdash (\\exists a)x$ ($y$ — из $x$ заменой свободных $a$ на $b$); "
          "эквивалентна классическому исчислению предикатов (MT9, MT10, с. 196–197)"),
         ("$S^i$", "формула $x \\vdash y$ доказуема, если и только если $y$ — переименование $x$ (определение $D^i$, с. 197)"),
         ("$S^r$", "$x \\vdash y$ доказуема, если найдётся цепочка $x \\vdash v$, $v \\vdash y$ из $S^6_{cq}$ или $S^i$, либо $x \\vdash y$ — аксиома $A^k$ (определение $D^r$, с. 197)")]


def sys15(lvl, typ="C"):
    its = rnd.sample(SYS15, 2)
    return card(15, 0, lvl, typ, "iso", "Как определяются системы приложения (с. 195–197)?\n\n" + items([s for s, _ in its]), answers([w for _, w in its]), "С. 195–197.",
                "с. 195–197, Приложение", "приписывание значений", form="meta", answ="text")


def ex194(lvl, typ="C"):
    v_ = rnd.choice([("(\\forall a)(\\exists b)x \\vdash (\\exists b)(\\forall a)x", "(\\forall a)\\sim(\\forall b)\\sim x \\vdash \\sim(\\forall b)\\sim(\\forall a)x", "не тавтология"),
                     ("(\\forall a)x(\\exists a)y \\vdash (\\exists a)(xy)", "(\\forall a)x\\sim(\\forall a)\\sim y \\vdash \\sim(\\forall a)(\\sim x \\vee \\sim y)", "тавтология")])
    return card(15, 0, lvl, typ, "iso", f"Буквы $a, b$ — термины; $x, y$ — высказывания. Приведите формулу ${v_[0]}$ к виду $x^* \\vdash y^*$ (приложение, с. 192, 194) и скажите, каков "
                "результат разбора в книге.", f"${v_[1]}$; {v_[2]}.", "С. 194: разбор двух примеров по правилам прямой интерпретации.", "с. 192, 194, Приложение", "приписывание значений")


E15 = [("«при преобразовании $x \\to x^*$ $(\\exists a)b$ заменяется на $\\sim(\\exists a)\\sim b$»", "заменяется на $\\sim(\\forall a)\\sim b$ (с. 192)"),
       ("«если $(\\forall a)b$ приписали значение 0, то и $b$ приписывается 0»", "по правилу 2 (с. 192) значение $b$ этим ещё не определяется"),
       ("«если $b$ приписали значение 1, то $(\\forall a)b$ имеет значение 1»", "по правилу 3 (с. 192) значение $(\\forall a)b$ этим ещё не определяется"),
       ("«$(\\forall a)x$ — тавтология, если $x$ истинно хотя бы при одном значении $a$»", "по MT2 (с. 195) $(\\forall a)x$ — тавтология тогда и только тогда, когда $x$ — тавтология"),
       ("«$S^6_{cq}$ эквивалентна классическому исчислению предикатов»", "по с. 196 ещё нет: $(\\forall a)P(a) \\supset P(b)$ общезначима, но не тавтология в смысле книги; эквивалентна "
        "классическому исчислению система $S^k$ (MT9, MT10)"),
       ("«формула $(\\forall a)(a \\leftarrow c) \\vdash (\\forall c)(c \\leftarrow c)$ — переименование»", "по $D^i$ (с. 197) новый термин не должен входить в $z$; $c$ входит в $(a \\leftarrow c)$"),
       ("«изложенный способ приписывания значений требует гипотезы о непустоте области значения субъектов»", "по с. 195 он делает эту гипотезу излишней"),
       ("«$x \\vdash y$ — тавтология, если она принимает значение 1 хотя бы при одном варианте приписывания»", "по D1 (с. 193) — для всех вариантов приписывания значений")]


def e15c(lvl):
    for _ in range(500):
        f = ap_rand(2)
        s = star(f)
        if s != f and f[0] in ("neg", "ex") and repr(("e15", f)) not in USED:
            USED.add(repr(("e15", f)))
            break
    if f[0] == "ex":
        wrong = N(EX(f[1], star(N(f[2]))))
        why = "$(\\exists a)b$ заменяется на $\\sim(\\forall a)\\sim b$, а не на $\\sim(\\exists a)\\sim b$"
    else:
        g = f[1]
        if g[0] == "conj":
            wrong = C(*[star(N(h)) for h in g[1]])
            why = "$\\sim(a^1 \\ldots a^n)$ заменяется дизъюнкцией $\\sim a^1 \\vee \\ldots \\vee \\sim a^n$"
        elif g[0] == "wdis":
            wrong = W(*[star(N(h)) for h in g[1]])
            why = "$\\sim(a^1 \\vee \\ldots \\vee a^n)$ заменяется конъюнкцией $\\sim a^1 \\ldots \\sim a^n$"
        else:
            wrong = N(N(star(g[1]))) if g[0] == "neg" else N(star(g))
            why = "$\\sim\\sim a$ заменяется на $a$; $(\\exists a)b$ — на $\\sim(\\forall a)\\sim b$"
    if wrong == s:
        wrong = N(s) if s[0] != "neg" else s[1]
    return card(15, 0, lvl, "E", "open", f"Буквы $x, y, z$ — высказывания. Студент выполнил предварительное преобразование приложения для $x = {T(f)}$ и получил ${T(wrong)}$. Найдите ошибку.",
                f"Неверно: {why} (с. 192). Правильно: ${T(s)}$.", "С. 192.", "с. 192, Приложение", "приписывание значений, диагностика")


def m1500(lvl, d, i):
    if d:
        if i % 3 != 1:
            return e15c(lvl)
        return epick(E15, 15, 0, lvl, AP, "с. 192–197, Приложение", "приписывание значений, диагностика")
    if lvl == 1:
        return [lambda l: star_card(l, "R"), lambda l: qr_card(l, "R"), lambda l: sys15(l, "R")][i % 3](1)
    if lvl == 2:
        return [star_card, qr_card, sys15, mt23][i % 4](2) if i % 4 != 0 else star_card(2)
    if lvl == 3:
        return [star_card, repr_card, mt23, qr_card, ren_card][i % 5](3) if i % 5 != 0 else star_card(3)
    if lvl == 4:
        return [repr_card, ren_card, ex194][i % 3](4)
    if lvl == 5:
        return [repr_card, ren_card, mt23][i % 3](5)
    if lvl == 6:
        return [repr_card, ren_card, sys15][i % 3](6) if i % 3 != 2 else repr_card(6)
    return repr_card(7, "S")


# ================================================================ ручные ступени 8–10
H = []


def hand(ch, sec, lvl, cond, ans, sol, src, tags, system=None):
    H.append(card(ch, sec, lvl, "I" if lvl == 10 else "M", "transfer", cond, ans, sol, src, tags, form="meta", answ="proof", system=system, gen=False))


def hand_cards():
    hand(12, 12, 8, "Покажите по схемам A2–A5, A7, A9 $S^{mp}_n$, что $p(\\downarrow x) = 1$ влечёт $N(\\downarrow x)$, а $p(\\downarrow x) = 0$ — $\\urcorner\\mathrm{M}(\\downarrow x)$; сравните с "
         "интерпретацией модальностей § 5.", "A4: $(p = 1) \\to N(\\downarrow x)$; A2: $(p = 0) \\to \\urcorner\\mathrm{M}(\\downarrow x)$; по § 5 $N(\\downarrow x)$ равнозначно $\\urcorner M(\\downarrow \\sim x)$ — "
         "согласие: при вероятности 1 противоположное невозможно.", "С. 173, 177.", "с. 173, 177, гл. 12, § 5, 12", "вероятностная логика")
    hand(12, 12, 8, "Выведите из A10 и A1: если $p(\\downarrow x) = 0$, то $p\\downarrow(xy) = 0$.", "A10: $p\\downarrow(xy) \\leq \\min(p(\\downarrow x), p(\\downarrow y)) = 0$; A1: $p\\downarrow(xy) \\geq 0$; "
         "значит, $= 0$.", "С. 177.", "с. 177, гл. 12, § 12", "вероятностная логика")
    hand(12, 12, 9, "Докажите: из A11 и A1 следует, что если $p(\\downarrow x) = 1$, то $p\\downarrow(x \\vee y) = 1$.", "A11: $p\\downarrow(x \\vee y) \\geq \\max(1, p(\\downarrow y)) = 1$; A1: $\\leq 1$.",
         "С. 177.", "с. 177, гл. 12, § 12", "вероятностная логика")
    hand(12, 12, 9, "Покажите, что соглашение A*12 согласуется с A12.", "A12 требует $p(\\downarrow y) \\leq \\min(\\alpha, \\beta)$; при $0 \\leq \\alpha, \\beta \\leq 1$ $\\alpha\\beta \\leq \\min(\\alpha, \\beta)$.",
         "С. 177.", "с. 177, гл. 12, § 12", "вероятностная логика")
    hand(12, 12, 10, "Исследуйте, какие ещё соглашения (кроме A*12) возможны для случаев A12 (с. 177). Сравните их на примерах из физики или медицины.", "Критерии: не менее двух "
         "соглашений, удовлетворяющих A12; примеры; обсуждение независимости событий.", "С. 177.", "с. 177, гл. 12, § 12", "вероятностная логика, исследование")
    hand(12, 12, 10, "Исследуйте связь A13, A14 § 12 гл. 12 с теорией условных высказываний (гл. 6): какие формулы гл. 6 позволяют переносить вероятности через $\\to$?",
         "Критерии: разобраны A13, A14; указаны схемы гл. 6 (A1, A3 $S^s_{if}$); обсуждены ограничения.", "С. 90–91, 177.", "с. 90–91, 177, гл. 6, 12", "вероятностная логика, исследование")
    hand(13, 2, 8, "Выведите T4 § 2 гл. 13 $\\vdash \\sim((a > b)(b > a))$ из T2 средствами $S^5$.", "T2: $(a > b) \\vdash \\sim(b > a)$; отсюда $(a > b)(b > a) \\vdash \\sim(b > a)(b > a)$ "
         "(противоречие) и $\\vdash \\sim((a > b)(b > a))$ по $S^5$.", "С. 180.", "с. 180, гл. 13, § 2", "логика сравнения", "S^r1_n")
    hand(13, 2, 9, "Докажите, что классические схемы AcI.1–AcI.10 (с. 180–181) — тавтологии при интерпретации § 4 (без неизвестных соотношений).", "Значения — натуральные числа; "
         "$>$ — строгий порядок: иррефлексивен (AcI.1), асимметричен (2), из $\\sim(a > b)$ — $b > a$ или $a = b$ (3), транзитивен (4–6); $<$ — обратное отношение (7, 8); равенство — "
         "отсутствие превосходства в обе стороны (9, 10).", "С. 180–182.", "с. 180–182, гл. 13, § 2, 4", "логика сравнения", "S^r1_c")
    hand(13, 6, 8, "Выведите в $S^{r3}$ формулу $(Rx)(y \\vee z) \\dashv\\vdash (Rx)y \\vee (Rx)z$ и $(Rx)(yz) \\dashv\\vdash (Rx)y(Rx)z$, указав схемы.", "Схемы 5, 6 и 3, 4.", "С. 183.",
         "с. 183, гл. 13, § 6", "система Sr3", "S^r3")
    hand(13, 6, 9, "Докажите в $S^{r3}$: $\\sim(Rx)(yz) \\vdash (Rx)\\sim y \\vee (Rx)\\sim z$.", "Схема 1 (для $yz$): $\\sim(Rx)(yz) \\vdash (Rx)\\sim(yz)$; замена $\\sim(yz)$ на $\\sim y \\vee \\sim z$ "
         "(R3 $S^s$); схема 6: $(Rx)(\\sim y \\vee \\sim z) \\vdash (Rx)\\sim y \\vee (Rx)\\sim z$; транзитивность.", "С. 183.", "с. 183, гл. 13, § 6", "система Sr3", "S^r3")
    hand(13, 8, 8, "Покажите по интерпретации § 8 гл. 13, что AII.1 $(x \\Rightarrow y) \\vdash y$ — тавтология, а AII.2, AII.3 связывают равнозначные высказывания.", "П. 1: при "
         "$x \\Rightarrow y = 1$ $y = 1$. П. 2: $x \\urcorner\\!\\Rightarrow y$ равнозначно $x \\Rightarrow \\sim y$.", "С. 187.", "с. 187, гл. 13, § 8", "логика изменения", "S^ch")
    for lvl_, c_, a_ in [(8, "Покажите, как из AI.1 и AI.3 $S^{ph}$ получить $(\\forall(\\downarrow x))((Rx)y) \\vdash N(\\downarrow ((Rx)y))$.", "AI.2: $(\\forall(\\downarrow x))((Rx)y) \\vdash (x \\to (Rx)y)$; "
                          "AI.3: $(x \\to (Rx)y) \\vdash N(\\downarrow ((Rx)y))$; транзитивность."),
                         (8, "Выведите T1 (AII) $(x \\to (Rx)(yz)) \\vdash (x \\to (Rx)y)(x \\to (Rx)z)$, используя AI.3, AI.4, схему 4 $S^{r3}$ и средства гл. 12.",
                          "AI.3: $(x \\to (Rx)(yz)) \\vdash N(\\downarrow ((Rx)(yz)))$; схема 4 $S^{r3}$ $(Rx)(yz) \\vdash (Rx)y(Rx)z$ и R1 гл. 12: $N(\\downarrow ((Rx)(yz))) \\vdash N(\\downarrow ((Rx)y(Rx)z))$; "
                          "T1 § 3 гл. 12: $\\vdash N(\\downarrow ((Rx)y))N(\\downarrow ((Rx)z))$; AI.4 для каждого конъюнкта; объединение и транзитивность ($S^s$)."),
                         (9, "Докажите в $S^{ph}$: $(x \\urcorner\\!\\to (Rx)y) \\dashv\\vdash M(\\downarrow ((Rx)\\sim y))$ и сопоставьте с AVII.2 гл. 12.", "AI.7, AI.8; в гл. 12 AVII.2: "
                          "$M(\\downarrow (x\\sim y)) \\vdash (x \\urcorner\\!\\rightarrow y)$ — аналог без отношения порядка."),
                         (9, "Докажите: если $(x \\to (Rx)y)$ и $(y \\to z)$, то $(\\forall(\\downarrow x))((Rx)z)$.", "AII.3: $(x \\to (Rx)z)$; AI.1: $(\\forall(\\downarrow x))((Rx)z)$."),
                         (10, "Сравните физическое следование ($S^{ph}$) с логическим следованием и условностью (гл. 6): какие формулы гл. 6 не переносятся на $x \\to (Rx)y$ и почему?",
                          "Критерии: роль отношения порядка $R$; примеры из AII.1 (изменение порядка $R^1$ на $R^2$); ссылки на с. 84–88, 187–188."),
                         (10, "Исследуйте, как в $S^{ph}$ выражаются законы науки вида «всякий раз после $x$ наступает $y$», и сопоставьте с замечанием гл. 14 о неявных кванторах.",
                          "Критерии: использованы AI.1–AI.4; связь с с. 191; пример закона.")]:
        hand(13, 9, lvl_, c_, a_, "Гл. 13, § 9.", "с. 187–188, гл. 13, § 9", "физическое следование", "S^ph")
    hand(14, 0, 8, "Докажите в $S^n_n$: $O(a) \\vdash \\urcorner \\text{З}(a)\\urcorner P(\\tilde a)$.", "AI.1 и AIII.2: $O(a) \\vdash P(a) \\vdash \\urcorner\\text{З}(a)$; AII.1: $O(a) \\vdash \\urcorner P(\\tilde a)$; "
         "объединение заключений.", "С. 189–190.", "с. 189–190, гл. 14", "нормативные предикаты", "S^n_n")
    hand(14, 0, 9, "Докажите: в $S^n_n$ из $\\text{Б}(a)$ следуют $\\urcorner O(a)$ и $\\urcorner O(\\tilde a)$.", "AIV.1: $\\text{Б}(a) \\vdash P(a)P(\\tilde a)$; AII.2: $P(\\tilde a) \\vdash \\urcorner O(a)$; "
         "AII.2 для $\\tilde a$ и замена $\\tilde{\\tilde a}$ на $a$: $P(a) \\vdash \\urcorner O(\\tilde a)$.", "С. 190; гл. 9, AI.10.", "с. 139–140, 190, гл. 9, 14", "нормативные предикаты", "S^n_n")
    hand(15, 0, 8, "Проведите по образцу с. 194 разбор формулы $(\\forall a)(xy) \\vdash (\\forall a)x$ по правилам прямой интерпретации приложения.", "Посылке 1 — по правилу 2 $xy = 1$, "
         "значит $x = 1$; по правилу 4 (вынуждены приписать $x$ значение 1) $(\\forall a)x = 1$. Вариантов с заключением 0 нет — тавтология.", "С. 192–194.", "с. 192–194, Приложение",
         "приписывание значений")
    hand(15, 0, 8, "Восстановите доказательство MT6 приложения: если $x \\vdash y$ — тавтология, то она доказуема в $S^6_{cq}$.", "Если в $y$ есть элементарные высказывания, отсутствующие "
         "в $x$, рассмотрим $x \\vee \\sim zz \\vdash y$, где $z$ содержит их: она — тавтология и по полноте $S^s_{cq}$ доказуема в $S^6_{cq}$; $x \\vdash x \\vee \\sim zz$ доказуема в силу $S^6$; "
         "транзитивность (с. 195–196).", "С. 195–196.", "с. 195–196, Приложение", "приписывание значений")
    hand(15, 0, 9, "Докажите MT8 приложения: если $\\vdash x$ — тавтология, то она доказуема в $S^6_{cq}$.", "$x$ — тавтология; $\\sim(\\sim yy) \\vdash x$ — тавтология и доказуема в $S^6_{cq}$ (MT6); "
         "$\\vdash \\sim(\\sim yy)$ доказуема; по $S^6$ — $\\vdash x$ (с. 196).", "С. 196.", "с. 196, Приложение", "приписывание значений")
    # смешанные
    hand(17, 12, 8, "Докажите в $S^1_k$: $(\\forall a)(a \\in Kb)(\\forall b)(b \\in Kc)(\\forall c)(c \\in Kd) \\vdash (\\forall a)(a \\in Kd)$.", "Дважды T1 $S^1_k$ (транзитивность классов) и $S^s$.",
         "Гл. 10, § 2.", "гл. 1–10", "смешанный, классы")
    hand(17, 12, 8, "Найдите термин $t$, для которого $\\vdash ((\\overline{Ka}) \\cup (Kb)) \\cap (Kc) \\rightleftharpoons Kt$, и проверьте результат по MT2–MT3 § 2 гл. 9 для включения $Kt$ в $K(\\sim a \\vee b)$.",
         "$t = (\\sim a \\vee b)c$ (A1–A3 § 9 гл. 10); $\\vdash (\\sim a \\vee b) \\rightharpoonup (\\sim a \\vee b)c$ доказуема: $(\\sim a \\vee b)c \\supset \\sim a \\vee b$ — тавтология, общие термины есть.",
         "Гл. 9, § 2; гл. 10, § 9.", "гл. 1–10", "смешанный, классы")
    hand(17, 12, 9, "Докажите: если $\\vdash (a \\rightharpoonup b)$ доказуема в $S^1_t$, то по семантике § 2 гл. 9 класс $Kb$ «включается» в $Ka$ в смысле $b \\supset a$; приведите пример с T5 $S^1_k$.",
         "$a \\rightharpoonup b$ равнозначна $b \\supset a$ (с. 141); T5 $\\vdash ab \\in Ka$ согласуется с AI.2 $\\vdash a \\rightharpoonup ab$.", "Гл. 9–10.", "гл. 1–10", "смешанный")
    hand(17, 12, 10, "Сравните силлогистику классов (§ 4 гл. 10) и силлогистику предикатов (§ 4 гл. 9) на модусе Barbara: запишите его в обеих и оцените громоздкость.",
         "Критерии: запись T1 $S^s_k$; перевод через схемы A1, A*2 § 4 гл. 9 и схему § 5 гл. 10; вывод о громоздкости (с. 146).", "Гл. 9–10.", "гл. 1–10", "смешанный, исследование")
    hand(17, 13, 8, "Докажите в $S^e_n$: $E(abc) \\vdash E(c)$.", "AVII.1 для $(ab)c$: $E((ab)c) \\vdash E(ab)E(c)$; отбрасывание конъюнкта.", "Гл. 11.", "гл. 1–11", "смешанный, существование")
    hand(17, 13, 9, "Докажите: $\\vdash U(\\downarrow x)$ доказуема в $S^e_n$ тогда и только тогда, когда $\\vdash x$ доказуема в $S^5$.", "MT1 § 4 гл. 11, п. 1: $\\vdash U(\\downarrow x)$ — лишь по R1, "
         "то есть когда $\\vdash x$ доказуема; в $S^5$ доказуемы именно тавтологии (MT4 § 3 гл. 4).", "Гл. 4, 11.", "гл. 1–11", "смешанный, существование")
    hand(17, 14, 8, "Докажите в $S^{m1}_n$: $N(\\downarrow (xy)) \\vdash M(\\downarrow x)$.", "T1 § 3: $N(\\downarrow (xy)) \\vdash N(\\downarrow x)N(\\downarrow y)$; AI.1, AI.2: $N(\\downarrow x) \\vdash M(\\downarrow x)$; $S^s$.",
         "Гл. 12.", "гл. 1–12", "смешанный, модальность")
    hand(17, 14, 9, "Докажите по MT2 § 11 гл. 12: из T27 § 6 гл. 7 следует $N(\\downarrow z) \\vdash M(\\downarrow z)$, и сравните с выводом в $S^{m1}_n$.", "T27: $(\\forall a)x \\vdash (\\exists a)x$; по MT2 — "
         "$N(\\downarrow x) \\vdash M(\\downarrow x)$; в $S^{m1}_n$ — AI.1, AI.2 и транзитивность.", "Гл. 7, 12.", "гл. 1–12", "смешанный, модальность")
    hand(17, 14, 10, "Исследуйте аналогию между системами $S^e_n$ (гл. 11) и $S^{m1}_n$ (гл. 12): составьте таблицу соответствий схем ($E$ — $M$, $U$ — $N$ и т. п.) и укажите, где аналогия нарушается.",
         "Критерии: не менее пяти пар схем; T1–T6 § 9 гл. 12; места расхождения обоснованы.", "Гл. 11–12.", "гл. 1–12", "смешанный, исследование")
    hand(17, 15, 8, "Докажите в $S^{r1}_c$: $\\sim(a > b)\\sim(b > a) \\vdash \\sim(a > c) \\vee \\sim(c > b) \\vee \\ldots$ — точнее: $(a = b)(b > c) \\vdash (a > c)$.", "AcI.9 и AcI.3? — нет, проще: "
         "по AI.6-аналогу $(b = a)$... Решение: $(a = b) \\vdash \\sim(a > b)\\sim(b > a)$ (AcI.9); по интерпретации § 4 $a = b$ — равные значения, и из $b > c$ — $a > c$; в системе — "
         "схема AcI.5 с перестановкой: $(b > c)(c = \\ldots)$.", "Гл. 13.", "гл. 1–13", "смешанный, отношения")
    hand(17, 15, 9, "Докажите в $S^{r3}$ и $S^{ch}$: из $(x \\Rightarrow y)$ следует $y$, а из $(Rx)(yz)$ — $(Rx)y$.", "AII.1 $S^{ch}$; схема 4 $S^{r3}$ и $S^s$.", "Гл. 13, § 6, 8.", "гл. 1–13",
         "смешанный, отношения")


def fix_hand():
    # исправление неудачной формулировки (одна карточка 17.15)
    for k, c in enumerate(H):
        if "chapter: 17\nsection: 15\nlevel: 8" in c:
            H[k] = card(17, 15, 8, "M", "transfer", "Докажите в $S^{r1}_c$: $(a > b)(b > c)(c > d) \\vdash (a > d)$ и $(d < c)(c < b) \\vdash (b > d)$.",
                        "AcI.4 дважды и $S^s$; для второй — AcI.7: $(d < c) \\vdash (c > d)$, $(c < b) \\vdash (b > c)$, затем AcI.4: $(b > c)(c > d) \\vdash (b > d)$.",
                        "Гл. 13, § 2 (с. 180–181).", "гл. 1–13", "смешанный, отношения", form="meta", answ="proof", gen=False)


# ================================================================ сборка
def mixed(sec, levels, diag, src, makers, emk):
    out, nd = [], 0
    left = sum(levels[1:])
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            if lvl >= 2:
                left -= 1
            dd = nd < diag and lvl >= 3 and (i % 2 == 0 or left < diag - nd)
            mk = (lambda: emk[(i + lvl) % len(emk)](lvl)) if dd else (lambda: makers[(i * 3 + lvl) % len(makers)](lvl))
            c = relabel(fresh(mk), sec, src)
            c = re.sub(r"level: \d+", f"level: {lvl}", c, count=1)
            if lvl == 7:
                c = re.sub(r"type: [CDR]\n", "type: S\n", c, count=1)
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def main():
    cards = []
    cards += build(12, 11, [0, 0, 1, 2, 3, 2, 1], 2, m1211)
    cards += build(12, 12, [1, 1, 2, 1, 2, 3, 5], 5, m1212)
    cards += build(13, 1, [2, 3, 3, 1, 0, 1, 0], 2, m1301)
    cards += build(13, 2, [1, 3, 4, 5, 8, 6, 3], 8, m1302)
    cards += build(13, 3, [0, 1, 1, 2, 3, 2, 1], 2, m1303)
    cards += build(13, 4, [1, 2, 3, 1, 1, 1, 1], 2, m1304)
    cards += build(13, 5, [2, 3, 3, 1, 0, 1, 0], 2, m1305)
    cards += build(13, 6, [1, 3, 4, 5, 8, 6, 3], 8, m1306)
    cards += build(13, 7, [2, 3, 3, 1, 0, 1, 0], 2, m1307)
    cards += build(13, 8, [1, 2, 3, 3, 5, 4, 2], 5, m1308)
    cards += build(13, 9, [1, 1, 2, 1, 2, 3, 5], 5, m1309)
    cards += build(14, 0, [1, 5, 6, 7, 12, 9, 5], 12, m1400)
    cards += build(15, 0, [3, 10, 19, 6, 6, 10, 6], 16, m1500)
    m10 = [lambda l: G8.kval_card(l), lambda l: G8.syl_status(l)]
    cards += mixed(12, [0, 0, 0, 0, 0, 0, 1], 0, "гл. 1–10", m10, [])
    m11 = [lambda l: G10.ae_sub(l, "C"), lambda l: G10.u_card(l, "C", sec=2), lambda l: G10.avi_card(l, "C"), lambda l: G10.sit11(l), lambda l: G10.der11(l), lambda l: G10.ux_card(l),
           lambda l: G10.ec_der(l, "C")]
    e11 = [lambda l: G10.m1102(l, True, 0), lambda l: G10.m1106(l, True, 0), lambda l: G10.m1107(l, True, 0), lambda l: G10.m1101(l, True, 0), lambda l: G10.m1105(l, True, 0),
           lambda l: G10.m1103(l, True, 0)]
    cards += mixed(13, [0, 3, 4, 1, 5, 6, 4], 6, "гл. 1–11", m11, e11)
    m12 = [lambda l: G10.am_sub(l, "C"), lambda l: G10.rmod(l, "C"), lambda l: G10.chain_mod(l, "C"), lambda l: G10.av_card(l, "C"), lambda l: G10.m1209(l, False, 1),
           lambda l: G10.m1206(l, False, 0), lambda l: G10.m1205(l, False, 0)]
    e12 = [lambda l: G10.m1202(l, True, 0), lambda l: G10.m1207(l, True, 0), lambda l: G10.m1203(l, True, 0), lambda l: G10.m1210(l, True, 0), lambda l: G10.m1208(l, True, 0)]
    cards += mixed(14, [0, 3, 5, 1, 6, 8, 5], 8, "гл. 1–12", m12, e12)
    m13 = [lambda l: ccheck_card(l), lambda l: sr3_sub(l, "C"), lambda l: sr3_der(l, "C"), lambda l: m1304(l, False, 0), lambda l: nat13(l), lambda l: ph_rec(l), lambda l: deriv13(l, "C")]
    e13 = [lambda l: m1302(l, True, 0), lambda l: m1306(l, True, 1), lambda l: m1308(l, True, 1), lambda l: m1309(l, True, 1)]
    cards += mixed(15, [0, 3, 4, 1, 5, 6, 4], 6, "гл. 1–13", m13, e13)
    m14 = [lambda l: to_p(l, "C"), lambda l: der14(l, "C"), lambda l: nat14(l), lambda l: cl14(l)]
    e14 = [lambda l: nat14e(l), lambda l: m1400(l, True, 1)]
    cards += mixed(16, [0, 1, 1, 1, 2, 2, 1], 2, "гл. 1–14", m14, e14)
    m15 = [lambda l: star_card(l, "C"), lambda l: repr_card(l), lambda l: mt23(l), lambda l: ren_card(l)]
    e15 = [lambda l: m1500(l, True, 0)]
    cards += mixed(17, [0, 1, 2, 1, 2, 3, 1], 2, "гл. 1–15, приложение", m15, e15)
    hand_cards()
    fix_hand()
    cards += H
    (ROOT / "drafts" / "81-90-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(cards), "из них ручных", len(H))


if __name__ == "__main__":
    main()
