#!/usr/bin/env python3
"""Серии для занятий 71–80: гл. 10, § 8–9; гл. 11 (логика существования); гл. 12, § 1–11 (модальная логика);
смешанные 17.10 (окончание), 17.11, 17.12 (начало). Пишет drafts/71-80-gen.md.
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
from ifq import C, N, V, W  # noqa: E402

spec = importlib.util.spec_from_file_location("g08_10", ROOT / "scripts" / "gen" / "g08_10.py")
G8 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G8)
G7 = G8.G7
G6 = G7.G6
for m_, s_ in ((G8, 7180), (G7, 7181), (G6, 7182), (G6.G, 7183)):
    m_.rnd.seed(s_)
rnd = random.Random(7184)
card, fresh, items, answers, build, relabel = G7.card, G7.fresh, G7.items, G7.answers, G7.build, G7.relabel
USED = G7.USED
L = G7.L
ttex = G8.ttex


def permute(strs, letters):
    p = dict(zip(letters, rnd.sample(letters, len(letters))))

    def rm(m):
        return re.sub(r"(?<![\\A-Za-z])([" + letters + r"])(?![A-Za-z])", lambda q: p[q.group(1)], m.group(0))
    return [re.sub(r"\$[^$]+\$", rm, s) for s in strs]


def E(ch, sec, lvl, pre, claim, why, src, tags, system=None, letters=None, form="sym"):
    if letters:
        pre, claim, why = permute([pre, claim, why], letters)
    return card(ch, sec, lvl, "E", "open", f"{pre} Студент: {claim}. Найдите ошибку.".strip(), f"Неверно: {why}.",
                f"{src[0].upper() + src[1:]}.", src, tags, form=form, system=system)


def epick(pool, ch, sec, lvl, pre, src, tags, system=None, letters=None):
    s, w = rnd.choice(pool)
    return E(ch, sec, lvl, pre, s, w, src, tags, system, letters)


def rec_card(ch, sec, lvl, typ, pre, D, prefix, src, tags, system=None, k=3, num_name=None):
    ks = rnd.sample(sorted(D, key=str), k)
    return card(ch, sec, lvl, typ, "iso", f"{pre} Каким схемам ({src.split(',')[0]}) соответствуют формулы? Укажите номера.\n\n" +
                items([f"${D[x]}$" for x in ks]), answers([f"{prefix}{x}" for x in ks]), src[0].upper() + src[1:] + ".", src, tags, system=system)


def sub_vars(s, mapping):
    """Подстановка вместо метапеременных-слов (x, y, a, b) в TeX-строке."""
    keys = "".join(mapping)

    def rm(q):
        return mapping[q.group(1)]
    return re.sub(r"(?<![\\A-Za-z])([" + keys + r"])(?![A-Za-z])", rm, s)


# ================================================================ 10.08 нормальные классы
NK = "Буква $a$ — термин; $Ka$ — класс $a$; $nk$ — термин «нормальный класс»."
Q108 = [("Как определяется нормальный класс в форме D*1 (с. 159)?", "Пусть $nk$ будет термином таким, что $nk \\rightharpoonup Ka$ (или $Ka \\in Knk$), "
         "если и только если $a$ есть термин и при этом $\\sim(Ka \\in Ka)$."),
        ("Какова область значения переменной $a$ в D*1 § 8 гл. 10?", "Термины, не зависящие по значению от $nk$ (с. 159)."),
        ("Что забывают при получении парадокса класса нормальных классов (с. 159)?", "Что на место $a$ не может быть подставлен термин $nk$ и любой "
         "другой термин, определяемый через $nk$."),
        ("Какой вид придают определению, получая утверждение A (с. 159)?", "Если $a$ есть термин и $\\sim(Ka \\in Ka)$, то $Ka \\in Knk$; если $a$ есть "
         "термин и $Ka \\in Ka$, то $\\sim(Ka \\in Knk)$."),
        ("Какие утверждения B получают, подставляя $nk$ на место $a$ (с. 159)?", "Если $\\sim(Knk \\in Knk)$, то $(Knk \\in Knk)$; если $(Knk \\in Knk)$, "
         "то $\\sim(Knk \\in Knk)$."),
        ("Какое следствие D1 верно (с. 159–160)?", "Если $a$ есть термин, не зависящий по значению от $nk$, и $\\sim(Ka \\in Ka)$, то $Ka \\in Knk$; если "
         "$Ka \\in Ka$, то при том же условии $\\sim(Ka \\in Knk)$."),
        ("Почему нельзя получить утверждение B (с. 160)?", "Термин $nk$ зависит по значению от самого себя: мы не можем знать значение $nk$, не "
         "определив $nk$."),
        ("Решён ли в книге вопрос о принятии $nk \\rightharpoonup Knk$ (с. 160)?", "Нет, он остаётся открытым: приняв $nk \\rightharpoonup Knk$ и D1, мы ещё не "
         "получаем противоречия; не получится его и при D1 и $\\sim(Knk \\in Knk)$.")]
E108 = [("«определение “класс нормален, если он не является элементом самого себя” пригодно»", "по с. 159 оно непригодно: в нём не выражено, что "
         "класс есть всегда класс чего-то"),
        ("«из D1 следует $Knk \\in Knk$ или $\\sim(Knk \\in Knk)$ — противоречие неизбежно»", "по с. 159–160 на место $a$ нельзя подставить $nk$; "
         "утверждение A неверно, и утверждение B получить нельзя"),
        ("«принять $nk \\rightharpoonup Knk$ вместе с D1 — значит получить противоречие»", "по с. 160 противоречия при этом ещё не получается; вопрос "
         "остаётся открытым")]


def m1008(lvl, d, i):
    if d:
        return epick(E108, 10, 8, lvl, NK, "с. 159–160, гл. 10, § 8", "парадокс нормальных классов, диагностика")
    q, a = Q108[G8.nxt("q108") % len(Q108)]
    return card(10, 8, lvl, {2: "R", 7: "S"}.get(lvl, "C"), "iso", q, a, "Гл. 10, § 8.", "с. 159–160, гл. 10, § 8", "парадокс нормальных классов",
                form="meta", answ="text")


# ================================================================ 10.09 производные классы
def crand(depth=2):
    if depth == 0 or rnd.random() < 0.3:
        return ("K", rnd.choice("abc"))
    k = rnd.choice(["comp", "cup", "cap"])
    if k == "comp":
        return ("comp", crand(depth - 1))
    return (k, crand(depth - 1), crand(depth - 1))


def ctex(f):
    k = f[0]
    if k == "K":
        return f"(K{f[1]})"
    if k == "comp":
        return f"(\\overline{{{ctex(f[1])[1:-1] if f[1][0] == 'K' else ctex(f[1])}}})"
    op = "\\cup" if k == "cup" else "\\cap"
    return f"({ctex(f[1])} {op} {ctex(f[2])})"


def cterm(f):
    """Термин t такой, что класс равнозначен K t (по A1–A3 § 9 гл. 10)."""
    k = f[0]
    if k == "K":
        return V(f[1])
    if k == "comp":
        return N(cterm(f[1]))
    a, b = cterm(f[1]), cterm(f[2])
    return W(a, b) if k == "cup" else C(a, b)


def kt_(t):
    return f"K{ttex(t)}" if t[0] == "v" else f"K({ttex(t)})"


def m1009(lvl, d, i):
    if d:
        pool = [("«по A1 § 9 гл. 10 дополнение к $(Ka)$ равнозначно $(K\\tilde a)$»", "по A1 $\\vdash (\\overline{Ka}) \\rightleftharpoons (K\\sim a)$ (с. 160)"),
                ("«$(Ka) \\cup (Kb)$ равнозначно $K(ab)$»", "по A2 $(Ka) \\cup (Kb) \\rightleftharpoons K(a \\vee b)$; $K(ab)$ — произведение $(Ka) \\cap (Kb)$ (A3, с. 160)"),
                ("«$(Ka) \\cap (Kb)$ называют суммой классов»", "это произведение; сумма — $(Ka) \\cup (Kb)$ (с. 160)")]
        return epick(pool, 10, 9, lvl, "Буквы $a, b$ — субъекты.", "с. 160, гл. 10, § 9", "производные классы, диагностика", letters="ab")
    if lvl == 1:
        its = rnd.sample([("$(\\overline{Ka})$", "дополнение к $(Ka)$"), ("$(Ka) \\cup (Kb)$", "сумма $(Ka)$ и $(Kb)$"), ("$(Ka) \\cap (Kb)$", "произведение $(Ka)$ и $(Kb)$"),
                          ("$(Ka)$", "термин класса (D1, п. 1)")], 2)
        return card(10, 9, 1, "R", "iso", "Буквы $a, b$ — субъекты. Как называются термины классов (§ 9 гл. 10, с. 160)?\n\n" + items([s for s, _ in its]),
                    answers([w for _, w in its]), "С. 160.", "с. 160, гл. 10, § 9", "производные классы")
    for _ in range(200):
        f = crand(2 if lvl <= 3 else 3)
        if f[0] != "K" and repr(f) not in USED:
            USED.add(repr(f))
            break
    return card(10, 9, lvl, "D" if lvl <= 4 else "C", "iso", f"Буквы $a, b, c$ — субъекты. По аксиомным схемам A1–A3 § 9 гл. 10 (с. 160) найдите термин $t$, для "
                f"которого $\\vdash {ctex(f)} \\rightleftharpoons {kt_(cterm(f))[0]}t$ (запишите $Kt$).", f"${kt_(cterm(f))}$",
                "A1: $\\vdash (\\overline{Ka}) \\rightleftharpoons (K\\sim a)$; A2: $\\vdash ((Ka) \\cup (Kb)) \\rightleftharpoons (K(a \\vee b))$; A3: $\\vdash ((Ka) \\cap (Kb)) \\rightleftharpoons (K(ab))$; "
                "преобразования ведутся изнутри наружу.", "с. 160, гл. 10, § 9", "производные классы")


# ================================================================ гл. 11
EX = "Буквы $a, b, c$ — термины; $x, y$ — высказывания; $E$ — «существует», $U$ — «универсально»."


def m1101(lvl, d, i):
    if d:
        pool = [("«$E$ и $U$ — дедуктивно эквивалентные предикаты»", "по с. 161 они логически взаимозаменимы, и $E$ категорически сильнее $U$"),
                ("«правила логики существования зависят от способов, которыми устанавливается смысл предиката $E$ в каждой науке»",
                 "по с. 161 рассматриваемые в логике правила от них не зависят"),
                ("«$\\urcorner b(a)$ — сокращение для $\\sim(a \\leftarrow b)$»", "это сокращение для $a \\urcorner\\!\\leftarrow b$ (с. 161)")]
        return epick(pool, 11, 1, lvl, EX, "с. 161, гл. 11, § 1", "существование, диагностика")
    if lvl == 1 or (lvl == 2 and i == 0):
        q = rnd.choice([("Что такое экзистенциальные высказывания (§ 1 гл. 11)?", "Высказывания, содержащие экзистенциальные предикаты (с. 161)."),
                        ("Как связаны предикаты $E$ и $U$ (§ 1 гл. 11)?", "Они логически взаимозаменимы; $E$ категорически сильнее $U$ (с. 161).")])
        return card(11, 1, lvl, "R", "iso", q[0], q[1], "С. 161.", "с. 161, гл. 11, § 1", "существование", form="meta", answ="text")
    s, p_ = rnd.sample("abcd", 2)
    form = rnd.choice([("", "\\leftarrow"), ("\\urcorner ", "\\urcorner\\!\\leftarrow"), ("? ", "? \\leftarrow")])
    if form[0] == "? ":
        full, short = f"{s}? \\leftarrow {p_}", f"?\\,{p_}({s})"
    else:
        full, short = f"{s} {form[1]} {p_}", f"{form[0]}{p_}({s})"
    if i % 2:
        return card(11, 1, lvl, "D", "iso", f"Запишите сокращённо по § 1 гл. 11 (с. 161) высказывание ${full}$.", f"${short}$",
                    "С. 161: $a \\leftarrow b$, $a \\urcorner\\!\\leftarrow b$, $a? \\leftarrow b$ изображаются $b(a)$, $\\urcorner b(a)$, $?\\,b(a)$.", "с. 161, гл. 11, § 1",
                    "существование, обозначения")
    return card(11, 1, lvl, "D", "iso", f"Что означает запись ${short}$ по § 1 гл. 11 (с. 161)? Запишите полностью.", f"${full}$",
                "С. 161.", "с. 161, гл. 11, § 1", "существование, обозначения")


AE1 = {"AI.1": "E(a^1, \\ldots, a^n) \\vdash E(a^1) \\cdot \\ldots \\cdot E(a^n)", "AI.2": "E(a^1) \\cdot \\ldots \\cdot E(a^n) \\vdash E(a^1, \\ldots, a^n)",
       "AI.3": "\\urcorner E(a^1, \\ldots, a^n) \\vdash \\urcorner E(a^1) \\vee \\ldots \\vee \\urcorner E(a^n)", "AI.4": "\\urcorner E(a^1) \\vee \\ldots \\vee \\urcorner E(a^n) \\vdash \\urcorner E(a^1, \\ldots, a^n)",
       "AI.5": "U(a^1, \\ldots, a^n) \\vdash U(a^1) \\cdot \\ldots \\cdot U(a^n)", "AI.6": "U(a^1) \\cdot \\ldots \\cdot U(a^n) \\vdash U(a^1, \\ldots, a^n)",
       "AII.1": "E(a)\\urcorner E(a \\downarrow b) \\vdash E(a\\urcorner \\downarrow b)", "AII.2": "E(a)?E(a \\downarrow b) \\vdash E(a? \\downarrow b)",
       "AII.3": "E(a)\\sim E(a \\downarrow b) \\vdash E(a\\sim \\downarrow b)", "AIII.1": "(\\exists a)E(a) \\vdash E(a)", "AIII.2": "\\sim E(a) \\vdash (\\forall a)\\sim E(a)",
       "AIV.1": "U(a) \\vdash \\urcorner E(\\sim a)", "AIV.2": "\\urcorner E(\\sim a) \\vdash U(a)", "AIV.3": "\\urcorner U(a) \\vdash E(\\sim a)", "AIV.4": "E(\\sim a) \\vdash \\urcorner U(a)",
       "AIV.5": "U(a) \\vdash E(a)", "AV.1": "\\vdash \\urcorner E(\\sim aa)", "AV.2": "\\vdash \\urcorner E(a\\tilde a)",
       "AVI.1": "(\\exists a)x \\vdash E(a \\downarrow x)", "AVI.2": "E(a \\downarrow x) \\vdash (\\exists a)x", "AVI.3": "(\\urcorner\\exists a)x \\vdash \\urcorner E(a \\downarrow x)",
       "AVI.4": "\\urcorner E(a \\downarrow x) \\vdash (\\urcorner\\exists a)x", "AVII.1": "E(ab) \\vdash E(a)E(b)", "AVII.2": "E(a \\vee b) \\dashv\\vdash E(a) \\vee E(b)",
       "AVII.3": "\\urcorner E(a) \\vee \\urcorner E(b) \\vdash \\urcorner E(ab)", "AVII.4": "\\urcorner E(a \\vee b) \\dashv\\vdash \\urcorner E(a)\\urcorner E(b)",
       "AVII.5": "U(a)E(b) \\vdash E(ab)", "AVII.6": "U(a \\vee b) \\vdash U(a) \\vee E(b)", "AVIII.1": "x \\vdash E(\\downarrow x)", "AVIII.2": "U(\\downarrow x) \\vdash x",
       "AVIII.3": "E(\\downarrow x) \\vdash E(a \\downarrow x)", "AVIII.4": "E(a \\downarrow x) \\vdash E(\\downarrow x)", "AVIII.5": "E(a \\downarrow x) \\vdash E(a)",
       "AVIII.6": "\\urcorner E(a) \\vdash \\urcorner E(a \\downarrow x)", "AVIII.7": "?E(a) \\vdash \\sim E(a \\downarrow x)"}
COND = {"AVI.1": "$E$ не входит в $x$", "AVI.2": "$E$ не входит в $x$", "AVI.3": "$E$ не входит в $x$", "AVI.4": "$E$ не входит в $x$",
        "AVIII.3": "$a$ входит свободно в $x$", "AVIII.4": "$a$ входит свободно в $x$", "AVIII.5": "$E$ не входит в $x$", "AVIII.6": "$E$ не входит в $x$",
        "AVIII.7": "$E$ не входит в $x$"}


def ae_rec(lvl, typ="R"):
    ks = rnd.sample(sorted(AE1), 4)
    return card(11, 2, lvl, typ, "iso", f"{EX} Каким аксиомным схемам $S^e_n$ (§ 2 гл. 11, с. 162–163) соответствуют формулы?\n\n" + items([f"${AE1[k]}$" for k in ks]),
                answers(ks), "С. 162–163." + (" Условия: " + "; ".join(f"{k} — {COND[k]}" for k in ks if k in COND) + "." if any(k in COND for k in ks) else ""),
                "с. 162–163, гл. 11, § 2", "существование, аксиомы", system="S^e_n")


TERMP = ["b", "bc", "\\sim b", "(b \\vee c)", "\\tilde b", "(b \\downarrow (b \\leftarrow c))"]
XP = ["(a \\leftarrow c)", "\\sim(a \\leftarrow c)", "(a \\leftarrow c)(a \\leftarrow d)", "(\\forall b)(a \\leftarrow b)"]


def ae_sub(lvl, typ="D"):
    k = rnd.choice([k for k in AE1 if "^" not in AE1[k]])
    s = AE1[k]
    has_x = re.search(r"(?<![\\A-Za-z])x(?![A-Za-z])", s)
    mp = {}
    if re.search(r"(?<![\\A-Za-z])b(?![A-Za-z])", s):
        mp["b"] = rnd.choice(["c", "d", "cd", "(c \\vee d)", "\\sim c"])
    if re.search(r"(?<![\\A-Za-z])a(?![A-Za-z])", s) and not has_x:
        mp["a"] = rnd.choice(["c", "cd", "\\sim c", "(c \\vee d)"])
    if has_x:
        mp["x"] = rnd.choice(XP)
    if not mp:
        mp["a"] = "cd"
    out = sub_vars(s, mp)
    out = re.sub(r"\((\\sim )?\(([^()]*)\)\)", lambda m: f"({m.group(1) or ''}({m.group(2)}))", out)
    out = out.replace("E(\\sim cd)", "E(\\sim(cd))").replace("E(\\sim c \\vee d)", "E(\\sim(c \\vee d))")
    desc = ", ".join(f"вместо ${v}$ — ${t}$" for v, t in mp.items())
    return card(11, 2, lvl, typ, "iso", f"Буквы $a, b, c, d$ — термины; $x$ — высказывание. Подставьте в схему {k} $S^e_n$ (${s}$) {desc}" +
                (f" (условие схемы: {COND[k]})" if k in COND else "") + ".", f"${out}$", "С. 162–163; буквы схем — метапеременные.",
                "с. 162–163, гл. 11, § 2", "существование, аксиомы", system="S^e_n")


DER11 = {
    "T1": ("E(abc) \\vdash E(a)", ["$E((ab)c) \\vdash E(ab)E(c)$ [AVII.1]", "$E(ab)E(c) \\vdash E(ab)$ [$S^s$]", "$E(ab) \\vdash E(a)E(b)$ [AVII.1]",
                                   "$E(a)E(b) \\vdash E(a)$ [$S^s$]", "$E(abc) \\vdash E(a)$ [$S^s$: 1–4; $abc$ есть $(ab)c$ — AI.4 гл. 9]"]),
    "T2": ("\\urcorner E(a \\vee b \\vee c) \\dashv\\vdash \\urcorner E(a)\\urcorner E(b)\\urcorner E(c)", ["$\\urcorner E((a \\vee b) \\vee c) \\dashv\\vdash \\urcorner E(a \\vee b)\\urcorner E(c)$ [AVII.4]",
            "$\\urcorner E(a \\vee b) \\dashv\\vdash \\urcorner E(a)\\urcorner E(b)$ [AVII.4]", "замена равнозначного во второй части 1 [$S^s$]"]),
    "T13": ("\\urcorner E(\\sim a) \\vdash E(a)", ["$\\urcorner E(\\sim a) \\vdash U(a)$ [AIV.2]", "$U(a) \\vdash E(a)$ [AIV.5]", "$\\urcorner E(\\sim a) \\vdash E(a)$ [$S^s$: 1, 2]"]),
    "T15": ("U(a) \\vdash E(a)\\urcorner E(\\sim a)", ["$U(a) \\vdash E(a)$ [AIV.5]", "$U(a) \\vdash \\urcorner E(\\sim a)$ [AIV.1]", "$U(a) \\vdash E(a)\\urcorner E(\\sim a)$ [$S^s$: 1, 2]"]),
    "T4": ("\\urcorner E(a) \\vee \\urcorner E(b) \\vee \\urcorner E(c) \\vdash \\urcorner E(abc)", ["$\\urcorner E(a) \\vee \\urcorner E(b) \\vdash \\urcorner E(ab)$ [AVII.3]",
            "$\\urcorner E(a) \\vee \\urcorner E(b) \\vee \\urcorner E(c) \\vdash \\urcorner E(ab) \\vee \\urcorner E(c)$ [$S^s$: 1]",
            "$\\urcorner E(ab) \\vee \\urcorner E(c) \\vdash \\urcorner E((ab)c)$ [AVII.3]", "транзитивность; $(ab)c$ есть $abc$ [$S^s$]"]),
}


def der11(lvl, hide=False):
    k = rnd.choice(sorted(DER11))
    goal, st = DER11[k]
    sub = rnd.random() < 0.5 and k in ("T13", "T15")
    if sub:
        t_ = rnd.choice(["bc", "(b \\vee c)"])
        goal = goal.replace("a)", f"{t_})").replace("\\sim a", f"\\sim {t_ if t_.startswith('(') else '(' + t_ + ')'}")
        st = [s.replace("a)", f"{t_})").replace("\\sim a", f"\\sim {t_ if t_.startswith('(') else '(' + t_ + ')'}") for s in st]
    if hide:
        j = rnd.randrange(len(st))
        sh = [re.sub(r"\[[^\[\]]*\]$", "[…]", s) if n == j else s for n, s in enumerate(st)]
        m = re.search(r"\[([^\[\]]*)\]$", st[j])
        if not m:
            j = 0
            sh = [re.sub(r"\[[^\[\]]*\]$", "[…]", s) if n == 0 else s for n, s in enumerate(st)]
            m = re.search(r"\[([^\[\]]*)\]$", st[0])
        return card(11, 2, lvl, "D", "complete", f"{EX} Восстановите пропущенное основание в выводе ${goal}$ в $S^e_n$ ({k} § 3 гл. 11{', с подстановкой' if sub else ''}):\n\n" +
                    "\n".join(f"{n + 1}. {s}" for n, s in enumerate(sh)), f"Шаг {j + 1}: {m.group(1)}.", "\n".join(f"{n + 1}. {s}" for n, s in enumerate(st)),
                    "с. 162–164, гл. 11, § 2–3", "существование, вывод", system="S^e_n")
    return card(11, 2, lvl, "D", "iso", f"{EX} Выведите в $S^e_n$ формулу ${goal}$ ({k} § 3 гл. 11).", f"Вывод из {len(st)} шагов (см. решение).",
                "\n".join(f"{n + 1}. {s}" for n, s in enumerate(st)), "с. 162–164, гл. 11, § 2–3", "существование, вывод", answ="proof", system="S^e_n")


def avi_card(lvl, typ="D", sec=None):
    X = rnd.choice(["(a \\leftarrow b)", "\\sim(a \\leftarrow b)", "(a \\leftarrow b)(a \\leftarrow c)", "(a \\urcorner\\!\\leftarrow c)", "(a \\leftarrow b) \\vee (c \\leftarrow a)",
                    "(\\forall b)(a \\leftarrow b)"])
    q = rnd.choice(["ex", "nex", "E", "nE"])
    wrap = X if not (" \\vee " in X or ")(" in X) else f"({X})"
    if q == "ex":
        f, g, n = f"(\\exists a){wrap}", f"E(a \\downarrow {wrap})", "AVI.1"
    elif q == "nex":
        f, g, n = f"(\\urcorner\\exists a){wrap}", f"\\urcorner E(a \\downarrow {wrap})", "AVI.3"
    elif q == "E":
        f, g, n = f"E(a \\downarrow {wrap})", f"(\\exists a){wrap}", "AVI.2"
    else:
        f, g, n = f"\\urcorner E(a \\downarrow {wrap})", f"(\\urcorner\\exists a){wrap}", "AVI.4"
    return card(11, sec or (2 if lvl <= 4 else 5), lvl, typ, "iso", f"{EX} Преобразуйте высказывание ${f}$ по схемам AVI § 2 гл. 11 (с. 163) "
                + ("в бескванторную формулу с предикатом существования." if q in ("ex", "nex") else "в формулу с квантором без предиката существования."),
                f"${g}$ ({n})", "С. 163: $E$ не входит в $x$ — условие выполнено. § 5 (с. 165): формулы с кванторами всегда могут быть заменены "
                "бескванторными с предикатами существования.", "с. 163, 165, гл. 11, § 2, 5", "существование, кванторы", system="S^e_n")


E1102 = [("«AVII.1: $E(a)E(b) \\vdash E(ab)$»", "AVII.1 — $E(ab) \\vdash E(a)E(b)$; обратная формула по MT2 § 6 (с. 166) недоказуема — не тавтология"),
         ("«по AVII.3 $\\urcorner E(ab) \\vdash \\urcorner E(a) \\vee \\urcorner E(b)$»", "AVII.3 идёт в обратную сторону; формула студента по MT2 § 6 (с. 166) "
          "недоказуема"),
         ("«AIV.5: $E(a) \\vdash U(a)$»", "AIV.5 — $U(a) \\vdash E(a)$ (с. 162): $E$ сильнее $U$ по категоричности, но не следует из $U$ наоборот"),
         ("«AVI.1 $(\\exists a)x \\vdash E(a \\downarrow x)$ верна для любого $x$»", "по с. 163 — если $E$ не входит в $x$"),
         ("«AVIII.3 $E(\\downarrow x) \\vdash E(a \\downarrow x)$ верна для любого $x$»", "по с. 163 — если $a$ входит свободно в $x$"),
         ("«AIII.2: $\\sim E(a) \\vdash (\\exists a)\\sim E(a)$»", "AIII.2 — $\\sim E(a) \\vdash (\\forall a)\\sim E(a)$ (с. 162)"),
         ("«AIV.1: $U(a) \\vdash \\sim E(\\sim a)$»", "в $S^e_n$ AIV.1 — $U(a) \\vdash \\urcorner E(\\sim a)$ с внутренним отрицанием (с. 162); с $\\sim$ — "
          "в классической системе $S^e_c$ (с. 167)"),
         ("«правило R1 $S^e_n$: если $x \\vdash y$, то $U(\\downarrow x) \\vdash U(\\downarrow y)$»", "R1 — если $\\vdash x$, то $\\vdash U(\\downarrow x)$ (с. 163)"),
         ("«AV.1 $\\vdash \\urcorner E(\\sim aa)$ и AV.2 $\\vdash \\urcorner E(a\\tilde a)$ — одна и та же схема»", "в AV.1 — отрицание $\\sim a$, в AV.2 — "
          "противоположный предмет $\\tilde a$; это разные термины (гл. 9, с. 138)"),
         ("«AVII.6: $U(a \\vee b) \\vdash U(a) \\vee U(b)$»", "AVII.6 — $U(a \\vee b) \\vdash U(a) \\vee E(b)$ (с. 163)")]


def m1102(lvl, d, i):
    if d:
        return epick(E1102, 11, 2, lvl, EX, "с. 162–166, гл. 11, § 2, 6", "существование, диагностика", "S^e_n", letters="ab")
    if lvl == 1:
        return ae_rec(1)
    if lvl == 2:
        return [ae_rec, ae_sub][i % 2](2, "C" if i % 2 == 0 else "D")
    if lvl == 3:
        return [ae_sub, avi_card, ae_rec][i % 3](3) if i % 3 != 2 else ae_rec(3, "C")
    if lvl == 4:
        return der11(4, hide=True) if i % 2 == 0 else ae_sub(4)
    if lvl == 5:
        return [der11, ae_sub, avi_card][i % 3](5) if i % 3 != 2 else avi_card(5).replace("chapter: 11\nsection: 5", "chapter: 11\nsection: 2")
    if lvl == 6:
        return u_card(6, sec=2) if i % 2 == 0 else ae_sub(6, "C")
    return u_card(7, "S", sec=2)


T113 = {1: "E(abc) \\vdash E(a)", 2: "\\urcorner E(a \\vee b \\vee c) \\dashv\\vdash \\urcorner E(a)\\urcorner E(b)\\urcorner E(c)", 3: "U(ab) \\dashv\\vdash U(a)U(b)",
        4: "\\urcorner E(a) \\vee \\urcorner E(b) \\vee \\urcorner E(c) \\vdash \\urcorner E(abc)", 5: "\\vdash (a \\rightharpoonup b)E(b) \\to E(a)",
        6: "\\vdash (a \\rightharpoonup b)\\urcorner E(a) \\to \\urcorner E(b)", 7: "\\vdash (a \\rightharpoonup b)?E(a) \\to \\sim E(b)", 8: "\\vdash \\urcorner E(\\sim aab)",
        9: "\\vdash U(a \\vee \\sim a)", 10: "\\vdash U(a \\vee \\sim a \\vee b)", 11: "\\sim E(\\downarrow x) \\vdash \\sim x", 12: "U(a) \\vdash \\urcorner U(\\sim a)",
        13: "\\urcorner E(\\sim a) \\vdash E(a)", 14: "\\sim E(a) \\vdash \\sim U(a)", 15: "U(a) \\vdash E(a)\\urcorner E(\\sim a)", 16: "U(\\downarrow x) \\vdash \\urcorner U(\\downarrow \\sim x)",
        17: "(\\forall a)x \\vdash \\urcorner E(a \\downarrow \\sim x)", 18: "(\\urcorner\\forall a)x \\vdash E(a \\downarrow \\sim x)", 19: "\\vdash U(\\downarrow (x \\vee \\sim x))",
        20: "\\vdash U(\\downarrow (x \\vee \\sim x \\vee y))", 21: "\\vdash \\urcorner E(\\downarrow (\\sim xx))", 24: "U(a) \\vdash (\\forall a)\\sim E(\\sim a)",
        25: "\\vdash \\sim(?\\exists a)E(a)"}


def m1103(lvl, d, i):
    if d:
        pool = [("«T5 § 3 гл. 11: $\\vdash (a \\rightharpoonup b)E(a) \\to E(b)$»", "T5 — $\\vdash (a \\rightharpoonup b)E(b) \\to E(a)$ (с. 164): $a \\rightharpoonup b$ — «$b$ есть $a$»"),
                ("«T13 $\\urcorner E(\\sim a) \\vdash E(a)$ обратима»", "в § 3 (с. 164) дана лишь эта формула; обратная $E(a) \\vdash \\urcorner E(\\sim a)$ там не утверждается, а "
                 "по интерпретации § 6 (пп. 6, 10) из $E(a) = 1$ значение $\\urcorner E(\\sim a)$ не определено"),
                ("«T9: $\\vdash E(a \\vee \\sim a)$»", "T9 — $\\vdash U(a \\vee \\sim a)$ (с. 164)")]
        return epick(pool[:1] + pool[2:], 11, 3, lvl, EX, "с. 164, гл. 11, § 3", "существование, диагностика", "S^e_n", letters="ab")
    if lvl in (2, 3):
        ks = rnd.sample(sorted(T113), 3)
        return card(11, 3, lvl, "R" if lvl == 2 else "C", "iso", f"{EX} Укажите номера следствий $S^e_n$ (§ 3 гл. 11, с. 164):\n\n" + items([f"${T113[k]}$" for k in ks]),
                    answers([f"{k}" for k in ks]), "С. 164.", "с. 164, гл. 11, § 3", "существование, теоремы", system="S^e_n")
    return der11(lvl, hide=(lvl == 4)).replace("chapter: 11\nsection: 2", "chapter: 11\nsection: 3") if i % 2 == 0 else u_card(lvl, "S" if lvl == 7 else "C", sec=3)


# ---- 11.04 теорема универсальности
def u_card(lvl, typ="C", sec=4):
    its = []
    for want in rnd.sample([True, True, False, False], 3):
        for _ in range(400):
            t = G8.rterm(2)
            if Q.is_taut(t) == want and repr(("U", t)) not in USED and t[0] != "v":
                USED.add(repr(("U", t)))
                its.append(t)
                break
    def arg(t):
        return ttex(t) if t[0] in ("v", "conj") else ttex(t)
    cond = (f"{EX} Термины $a, b, c$ здесь простые. Доказуема ли в $S^e_n$ формула $\\vdash U(t)$ для каждого термина $t$ "
            "(MT1 § 4 гл. 11, с. 164–165)?\n\n" + items([f"$t = {arg(t)}$" for t in its]))
    sol = "\n".join(f"{L[k]}) $t^* = {ttex(Q.tex and t)}$ (буквы — высказывания) — " + ("тавтология; доказуема" if Q.is_taut(t) else "не тавтология; недоказуема") + "."
                    for k, t in enumerate(its))
    return card(11, sec, lvl, typ, "open", cond, answers(["да" if Q.is_taut(t) else "нет" for t in its]),
                sol + "\n\nMT1, п. 2: $\\vdash U(a)$ доказуема тогда и только тогда, когда тавтологией является $a^*$, полученное заменой терминов высказываниями "
                "(разные — разными, одинаковые — одинаковыми).", "с. 164–165, гл. 11, § 4", "существование, универсальность", system="S^e_n")


def ux_card(lvl, typ="C"):
    its = []
    for want in rnd.sample([True, False, True], 3):
        for _ in range(400):
            f = G6.G.rnd_f("xy", 2, "w")
            if Q.is_taut(f) == want and repr(("Ux", f)) not in USED:
                USED.add(repr(("Ux", f)))
                its.append(f)
                break
    return card(11, 4, lvl, typ, "open", f"{EX} Доказуема ли в $S^e_n$ формула $\\vdash U(\\downarrow z)$ (MT1 § 4 гл. 11, п. 1) для каждого $z$?\n\n" +
                items([f"$z = {Q.tex(f)}$" for f in its]), answers(["да" if Q.is_taut(f) else "нет" for f in its]),
                "MT1, п. 1 (с. 164): если $a$ есть $\\downarrow x$, то $x$ должно быть тавтологией; доказуемые $\\vdash U(\\downarrow x)$ получаются лишь по R1.\n" +
                "\n".join(f"{L[k]}) " + ("тавтология." if Q.is_taut(f) else "не тавтология: при " + G6.G.SY.env_text(G6.G.SY.counter(f, None) if False else Q.counter(f)) + " — 0.")
                          for k, f in enumerate(its)), "с. 164–165, гл. 11, § 4", "существование, универсальность", system="S^e_n")


def m1104(lvl, d, i):
    if d:
        pool = [("«$\\vdash U(a \\vee b)$ доказуема: $a$ и $b$ — разные термины, так что $a \\vee b$ “покрывает всё”»", "по MT1 (с. 164–165) нужно, чтобы "
                 "$a^* = p \\vee q$ (разные термины — разными высказываниями) было тавтологией; это не так"),
                ("«$\\vdash U(\\downarrow (x \\vee y))$ доказуема по R1, потому что $x \\vee y$ “часто истинно”»", "R1 применяется лишь к доказуемой $\\vdash z$; "
                 "$x \\vee y$ не тавтология (MT1, п. 1, с. 164)"),
                ("«MT1 § 4 доказывается тем, что $a_1 \\vee \\ldots \\vee a_k \\vdash a_1 \\vee \\sim a_1$ в $S^s$»", "по с. 165 используются формулы общей теории "
                 "дедукции $a_1 \\vee \\ldots \\vee a_k \\vdash a_1 \\vee \\sim a_1$ и $a_1 \\vee \\sim a_1 \\vdash a_1 \\vee \\ldots \\vee a_k$ для канонической формы, "
                 "являющейся тавтологией; итог — $\\vdash U(\\downarrow(a_1 \\vee \\sim a_1))$")]
        return epick(pool[:2], 11, 4, lvl, EX, "с. 164–165, гл. 11, § 4", "универсальность, диагностика", "S^e_n")
    if lvl == 3:
        return u_card(3, "D")
    if lvl in (4, 6):
        return ux_card(lvl) if i % 2 == 0 else u_card(lvl)
    return u_card(lvl, "S" if lvl == 7 else "C")


# ---- 11.05
def m1105(lvl, d, i):
    if d:
        pool = [("«формулы вида $E(a)$ всегда можно заменить формулами с кванторами без предиката существования»", "по с. 165 — лишь когда $a \\rightleftharpoons (b \\downarrow x)$; "
                 "иначе элиминировать предикат существования нельзя"),
                ("«$(\\exists a)E(a \\downarrow x) \\vdash E(a \\downarrow x)$ — пример AVI.1»", "AVI.1 — $(\\exists a)x \\vdash E(a \\downarrow x)$, где $E$ не входит в $x$ (с. 163); здесь "
                 "$E$ входит в формулу под квантором")]
        return epick(pool, 11, 5, lvl, EX, "с. 163, 165, гл. 11, § 2, 5", "существование и кванторы, диагностика", "S^e_n")
    if lvl == 2:
        return card(11, 5, 2, "R", "iso", f"{EX} Какое важное следствие вытекает из аксиомных схем AIII и AVI (§ 5 гл. 11, с. 165)?",
                    "1) Формулы с кванторами всегда могут быть заменены бескванторными формулами с предикатами существования; 2) формулы $\\alpha E(a)$ и "
                    "$\\alpha U(a)$ могут быть заменены формулами с кванторами без предикатов существования лишь в случаях, когда $a \\rightleftharpoons (b \\downarrow x)$.",
                    "С. 165.", "с. 165, гл. 11, § 5", "существование и кванторы", form="meta", answ="text")
    if lvl in (3, 4, 5, 6):
        return avi_card(lvl, "D" if lvl <= 4 else "C", sec=5)
    return card(11, 5, 7, "S", "transfer", f"{EX} Можно ли элиминировать предикат существования в $E(a \\downarrow (a \\leftarrow b))$ и в $E(c)$, где $c$ — простой "
                "термин (§ 5 гл. 11)?", "В первом случае да: по AVI.2 $E(a \\downarrow (a \\leftarrow b)) \\vdash (\\exists a)(a \\leftarrow b)$ и по AVI.1 обратно; во втором — нет, "
                "если $c$ невозможно представить в виде $(b \\downarrow x)$.", "С. 163, 165.", "с. 163, 165, гл. 11, § 2, 5", "существование и кванторы")


# ---- 11.06 интерпретация
SIT11 = [("$a$ и $b$ оба имеют значение 1", "значение $ab$ остаётся неопределённым", "5"), ("$ab$ имеет значение 0", "значения $a$ и $b$ остаются неопределёнными", "5"),
         ("$a$ имеет значение 0", "$ab$ имеет значение 0", "5"), ("$ab$ имеет значение 1", "$a$ и $b$ имеют значение 1", "5"),
         ("$a$ имеет значение 1", "$\\sim a$ имеет значение 0", "6"), ("$\\sim a$ имеет значение 0", "$a$ имеет значение 1", "6"),
         ("$E(a)$ имеет значение 1", "$a$ имеет значение 1", "10"), ("$a$ не может принять значение 1", "$E(a)$ имеет значение 0", "10"),
         ("значения $a$ и $b$ равны", "равны значения $E(a)$ и $E(b)$, а также $\\urcorner E(a)$ и $\\urcorner E(b)$", "8"),
         ("$a$ не может принять значение 1", "$?E(a)$ имеет значение 0", "13"), ("нужно значение $U(a)$", "оно равно значению $\\urcorner E(\\sim a)$", "11"),
         ("нужно значение $E(a \\vee b)$", "оно равно значению $E(a) \\vee E(b)$", "4"), ("нужно значение $E(a^1, \\ldots, a^n)$", "оно равно значению $E(a^1) \\cdot \\ldots \\cdot E(a^n)$", "2"),
         ("нужно значение $(\\exists a)E(a)$", "оно равно значению $E(a)$ (п. 12 при отсутствии $\\alpha$)", "12")]


def sit11(lvl, typ="C"):
    its = rnd.sample(SIT11, 3)
    return card(11, 6, lvl, typ, "iso", f"{EX} Что следует по семантической интерпретации § 6 гл. 11 (с. 165–166)? Укажите номер правила.\n\n" + items([s for s, _, _ in its]),
                answers([f"{w} (п. {n})" for _, w, n in its]), "С. 165–166.", "с. 165–166, гл. 11, § 6", "существование, интерпретация")


MT2V = [("E(a)E(b) \\vdash E(ab)", "a", "b", "E"), ("E(c)E(d) \\vdash E(cd)", "c", "d", "E"), ("E(b)E(c) \\vdash E(bc)", "b", "c", "E"),
        ("\\sim E(ab) \\vdash \\sim E(a) \\vee \\sim E(b)", "a", "b", "N"), ("\\sim E(cd) \\vdash \\sim E(c) \\vee \\sim E(d)", "c", "d", "N"),
        ("\\sim E(bc) \\vdash \\sim E(b) \\vee \\sim E(c)", "b", "c", "N")]


def mt2_11(lvl, typ="C"):
    f, p_, q_, kind = MT2V[G8.nxt("mt211") % len(MT2V)]
    sol = (f"Пусть ${p_}$ и ${q_}$ имеют значение 1; по п. 5 значение ${p_}{q_}$ остаётся неопределённым — пусть ${p_}{q_}$ не может принять значение 1. "
           f"По п. 10 $E({p_}) = E({q_}) = 1$, $E({p_}{q_}) = 0$. Тогда " +
           ("посылка имеет значение 1, заключение — 0." if kind == "E" else f"$\\sim E({p_}{q_}) = 1$, а $\\sim E({p_}) \\vee \\sim E({q_}) = 0$.") + " С. 166.")
    return card(11, 6, lvl, typ, "open", f"Буквы $a, b, c, d$ — термины; $E$ — «существует». Покажите по интерпретации § 6 гл. 11, что формула ${f}$ не тавтология "
                "и потому недоказуема в $S^e_n$ (MT1, MT2 § 6, с. 166).", "При значениях из решения посылка истинна, заключение ложно.", sol,
                "с. 165–166, гл. 11, § 6", "существование, интерпретация", system="S^e_n")


E1106 = [("«если $a$ и $b$ имеют значение 1, то и $ab$ имеет значение 1»", "по п. 5 (с. 166) значение $ab$ остаётся неопределённым"),
         ("«если $E(a)$ имеет значение 0, то $a$ имеет значение 1»", "по п. 10 при $E(a) = 0$ и $a$ имеет значение 0"),
         ("«$U(a)$ равнозначно $E(a)$»", "по п. 11 $U(a)$ равнозначно $\\urcorner E(\\sim a)$ (с. 166)"),
         ("«$E(a)E(b) \\vdash E(ab)$ доказуема в $S^e_n$»", "по MT2 § 6 (с. 166) она недоказуема — не тавтология"),
         ("«$x \\rightarrow y$ при интерпретации § 6 равнозначна $y \\supset x$»", "по п. 3 (с. 166) — равнозначна $x \\supset y$"),
         ("«если $ab$ имеет значение 0, то хотя бы одно из $a$, $b$ имеет значение 0»", "по п. 5 при $ab = 0$ значения $a$ и $b$ остаются неопределёнными")]


def m1106(lvl, d, i):
    if d:
        return epick(E1106, 11, 6, lvl, EX, "с. 165–166, гл. 11, § 6", "существование, интерпретация, диагностика", letters="ab")
    if lvl in (1, 2, 3, 4):
        return sit11(lvl, "R" if lvl == 1 else "C")
    if lvl == 5:
        return mt2_11(5) if i == 0 else sit11(5)
    return mt2_11(lvl, "S" if lvl == 7 else "C")


# ---- 11.07 S^e_c
EC = {"AII*": "E(a)\\sim E(a \\downarrow x) \\vdash E(a \\downarrow \\sim x)", "AIV*.1": "U(a) \\vdash \\sim E(\\sim a)", "AIV*.2": "\\sim E(\\sim a) \\vdash U(a)",
      "AIV*.3": "U(a) \\vdash E(a)", "AV*": "\\vdash \\sim E(\\sim aa)"}
ECN = {"AII*": "вместо схем AII", "AIV*.1": "вместо AIV (п. 1)", "AIV*.2": "вместо AIV (п. 2)", "AIV*.3": "вместо AIV (п. 3)", "AV*": "вид, который принимает AV"}


def ec_rec(lvl, typ="C"):
    ks = rnd.sample(sorted(EC), 3)
    return card(11, 7, lvl, typ, "iso", f"{EX} Какое место в системе $S^e_c$ (§ 7 гл. 11, с. 167) занимают схемы?\n\n" + items([f"${EC[k]}$" for k in ks]),
                answers([ECN[k] for k in ks]), "С. 167.", "с. 167, гл. 11, § 7", "существование, классический случай", system="S^e_c")


KEEP = [("AI", "остаются первые четыре"), ("AII", "заменяются схемой $E(a)\\sim E(a \\downarrow x) \\vdash E(a \\downarrow \\sim x)$"), ("AIII", "остаётся лишь первая"),
        ("AIV", "заменяются тремя схемами: $U(a) \\vdash \\sim E(\\sim a)$, $\\sim E(\\sim a) \\vdash U(a)$, $U(a) \\vdash E(a)$ (и аналоги для $\\downarrow x$)"),
        ("AV", "принимает вид $\\vdash \\sim E(\\sim aa)$"), ("AVI", "остаются первые две"), ("R1", "остаётся без изменения")]


def keep_card(lvl, typ="C"):
    its = rnd.sample(KEEP, 3)
    return card(11, 7, lvl, typ, "iso", f"{EX} Что происходит с группами схем $S^e_n$ при переходе к классической системе $S^e_c$ (§ 7 гл. 11, с. 167)?\n\n" +
                items([n for n, _ in its]), answers([w for _, w in its]), "С. 167.", "с. 167, гл. 11, § 7", "существование, классический случай", system="S^e_c")


def ec_der(lvl, typ="D"):
    v_ = rnd.choice([("\\sim E(\\sim a) \\vdash E(a)", ["$\\sim E(\\sim a) \\vdash U(a)$ [AIV*.2]", "$U(a) \\vdash E(a)$ [AIV*.3]", "транзитивность [$S^s$]"]),
                     ("U(a) \\vdash E(a)\\sim E(\\sim a)", ["$U(a) \\vdash E(a)$ [AIV*.3]", "$U(a) \\vdash \\sim E(\\sim a)$ [AIV*.1]", "объединение заключений [$S^s$]"]),
                     ("\\sim E(\\downarrow \\sim x) \\vdash U(\\downarrow x)", ["это вторая схема в п. 2 списка, заменяющего AIV (с. 167)"])])
    t_ = rnd.choice(["a", "bc", "(b \\vee c)"])
    goal = v_[0].replace("\\sim a", f"\\sim {t_}" if len(t_) == 1 else f"\\sim{t_ if t_.startswith('(') else '(' + t_ + ')'}").replace("(a)", f"({t_})" if not t_.startswith("(") else t_)
    steps = [s.replace("\\sim a", f"\\sim {t_}" if len(t_) == 1 else f"\\sim{t_ if t_.startswith('(') else '(' + t_ + ')'}").replace("(a)", f"({t_})" if not t_.startswith("(") else t_) for s in v_[1]]
    return card(11, 7, lvl, typ, "iso", f"{EX} Выведите в $S^e_c$ формулу ${goal}$ (схемы $S^e_c$ — с. 167; AIV*.1–3 — схемы, принимаемые вместо AIV).",
                "См. решение.", "\n".join(f"{n + 1}. {s}" for n, s in enumerate(steps)), "с. 167, гл. 11, § 7", "существование, классический случай",
                answ="proof", system="S^e_c")


def transfer11(lvl, typ="C"):
    pool = [("U(a) \\vdash \\urcorner E(\\sim a)", "$S^e_n$: да (AIV.1); $S^e_c$: внутреннего отрицания нет — соответствующая схема $U(a) \\vdash \\sim E(\\sim a)$"),
            ("\\sim E(\\sim a) \\vdash U(a)", "$S^e_c$: да (схема, заменяющая AIV.2); $S^e_n$: аналог AIV.2 с $\\urcorner$: $\\urcorner E(\\sim a) \\vdash U(a)$"),
            ("\\vdash \\urcorner E(\\sim aa)", "$S^e_n$: да (AV.1); в $S^e_c$ AV принимает вид $\\vdash \\sim E(\\sim aa)$"),
            ("(\\exists a)E(a) \\vdash E(a)", "в обеих: AIII.1 (в $S^e_c$ из AIII остаётся лишь первая)"),
            ("\\sim E(a) \\vdash (\\forall a)\\sim E(a)", "$S^e_n$: да (AIII.2); в $S^e_c$ AIII.2 не сохраняется среди аксиом (с. 167)")]
    its = rnd.sample(pool, 2)
    return card(11, 7, lvl, typ, "transfer", f"{EX} Как обстоит дело с формулами в $S^e_n$ и $S^e_c$ (§ 2, 7 гл. 11)?\n\n" + items([f"${s}$" for s, _ in its]),
                answers([w for _, w in its]), "С. 162–163, 167.", "с. 162–167, гл. 11, § 2, 7", "существование, классический случай")


E1107 = [("«в $S^e_c$ из схем AI остаются все»", "остаются первые четыре (с. 167)"),
         ("«в $S^e_c$ AV принимает вид $\\vdash \\urcorner E(\\sim aa)$»", "в классическом случае — $\\vdash \\sim E(\\sim aa)$ (с. 167)"),
         ("«в $S^e_c$ вместо AIV принимаются две схемы»", "принимаются три: $U(a) \\vdash \\sim E(\\sim a)$, $\\sim E(\\sim a) \\vdash U(a)$, $U(a) \\vdash E(a)$ (с. 167)"),
         ("«в $S^e_c$ вместо AII принимается $E(a)\\sim E(a \\downarrow x) \\vdash E(a\\sim \\downarrow x)$»", "принимается $E(a)\\sim E(a \\downarrow x) \\vdash E(a \\downarrow \\sim x)$ (с. 167)"), ("«в $S^e_c$ AIII сохраняется полностью»", "остаётся лишь первая (с. 167)"),
         ("«в $S^e_c$ сохраняется $U(a) \\vdash \\urcorner E(\\sim a)$»", "в классическом случае внутреннего отрицания нет: принимается $U(a) \\vdash \\sim E(\\sim a)$ (с. 167)"),
         ("«в $S^e_c$ правило R1 заменяется»", "правило R1 остаётся без изменения (с. 167)"), ("«в $S^e_c$ от AVI остаются три первые схемы»", "остаются первые две (с. 167)")]


def m1107(lvl, d, i):
    if d:
        return epick(E1107, 11, 7, lvl, EX, "с. 167, гл. 11, § 7", "существование, классический случай, диагностика", "S^e_c")
    if lvl == 1:
        return card(11, 7, 1, "R", "iso", f"{EX} Для какого случая предназначена система $S^e_c$ (§ 7 гл. 11)?", "Для классического (с. 167).", "С. 167.",
                    "с. 167, гл. 11, § 7", "существование, классический случай", system="S^e_c")
    if lvl in (2, 3):
        return [ec_rec, keep_card][i % 2](lvl)
    if lvl == 4:
        return [keep_card, ec_der, ec_rec][i % 3](4) if i % 3 != 1 else ec_der(4)
    if lvl == 5:
        return [ec_der, keep_card, transfer11, ec_rec][i % 4](5)
    if lvl == 6:
        return transfer11(6) if i % 2 == 0 else ec_der(6, "C")
    return transfer11(7, "S")


# ================================================================ гл. 12
MO = "Буквы $x, y$ — высказывания; $M$ — «возможно», $N$ — «необходимо», $C$ — «случайно»; $\\alpha$ — наличие $\\urcorner$ или $?$ или отсутствие обоих."


def m1201(lvl, d, i):
    if d:
        pool = [("«модальные предикаты — это только “возможно” и “необходимо”»", "по § 1 гл. 12 (с. 168) к ним относятся также «случайно» и «вероятно со степенью»"),
                ("«модальные предикаты не подчиняются общим правилам для предикатов»", "по с. 168 к ним относится всё, сказанное о предикатах вообще; кроме того, у них "
                 "есть специфические свойства")]
        return epick(pool, 12, 1, lvl, MO, "с. 168, гл. 12, § 1", "модальность, диагностика")
    WL = [("«возможно»", True), ("«необходимо»", True), ("«случайно»", True), ("«вероятно со степенью 0,3»", True), ("«существует»", False), ("«универсально»", False),
          ("«имеет признак»", False), ("«класс»", False)]
    if lvl in (1, 2, 3):
        its = rnd.sample(WL, 4)
        return card(12, 1, lvl, "R" if lvl == 1 else "C", "iso", "Какие из предикатов § 1 гл. 12 относит к модальным?\n\n" + items([s for s, _ in its]),
                    answers(["модальный" if t else "нет" for _, t in its]), "С. 168; $E$, $U$ — экзистенциальные (гл. 11).", "с. 161, 168, гл. 11–12", "модальность", form="nat")
    if lvl == 6:
        return card(12, 1, 6, "C", "iso", "Какие символы вводит алфавит системы $S^{m1}_n$ (§ 2 гл. 12) и как они читаются?", "$M$ — «возможно», $N$ — «необходимо», "
                    "$C$ — «случайно» (с. 168).", "С. 168.", "с. 168, гл. 12, § 2", "модальность", form="meta", answ="text")
    return card(12, 1, lvl, "C", "iso", "Что § 2 гл. 12 называет модальными высказываниями (D2) и какие предикаты модальны по D1?",
                "Модальные высказывания — содержащие модальные предикаты; модальные предикаты суть $M$, $N$ и $C$ и только они (с. 168).", "С. 168.",
                "с. 168, гл. 12, § 1–2", "модальность", form="meta", answ="text")


AM1 = {"AI.1": "N(\\downarrow x) \\vdash x", "AI.2": "x \\vdash M(\\downarrow x)", "AII.1": "N(\\downarrow x) \\vdash \\urcorner M(\\downarrow \\sim x)", "AII.2": "\\urcorner M(\\downarrow x) \\vdash N(\\downarrow \\sim x)",
       "AII.3": "\\urcorner N(\\downarrow x) \\vdash M(\\downarrow \\sim x)", "AII.4": "M(\\downarrow x) \\vdash \\urcorner N(\\downarrow \\sim x)",
       "AIII.1": "C(\\downarrow x) \\vdash M(\\downarrow x)M(\\downarrow \\sim x)", "AIII.2": "M(\\downarrow x)M(\\downarrow \\sim x) \\vdash C(\\downarrow x)",
       "AIII.3": "\\urcorner C(\\downarrow x) \\vdash M(\\downarrow x)\\urcorner M(\\downarrow \\sim x)", "AIII.4": "M(\\downarrow x)\\urcorner M(\\downarrow x) \\vdash \\urcorner C(\\downarrow x)",
       "AIII.5": "?C(\\downarrow x) \\vdash M(\\downarrow x)?M(\\downarrow \\sim x)", "AIII.6": "M(\\downarrow x)?M(\\downarrow \\sim x) \\vdash ?C(\\downarrow x)",
       "AIV.1": "M(\\downarrow (x \\vee y)) \\vdash M(\\downarrow x) \\vee M(\\downarrow y)", "AIV.2": "M(\\downarrow x) \\vee M(\\downarrow y) \\vdash M(\\downarrow (x \\vee y))",
       "AIV.3": "N(\\downarrow x)N(\\downarrow y) \\vdash N(\\downarrow (xy))", "AIV.4": "N(\\downarrow x)M(\\downarrow y) \\vdash M(\\downarrow (xy))",
       "AIV.5": "N(\\downarrow (x \\vee y)) \\vdash N(\\downarrow x) \\vee M(\\downarrow y)", "AIV.6": "M(\\downarrow x)?M(\\downarrow y) \\vdash ?M(\\downarrow (xy))",
       "AIV.7": "N(\\downarrow x)?N(\\downarrow y) \\vdash ?N(\\downarrow (xy))", "AIV.8": "?M(\\downarrow x)?M(\\downarrow y) \\vdash ?M(\\downarrow (xy))",
       "AIV.9": "?N(\\downarrow x)?N(\\downarrow y) \\vdash ?N(\\downarrow (xy))", "AV.3": "M(a, b) \\vdash M(a)M(b)", "AV.4": "M(a)M(b) \\vdash M(a, b)",
       "AV.5": "N(a, b) \\vdash N(a)N(b)", "AV.6": "N(a)N(b) \\vdash N(a, b)", "AV.7": "\\urcorner M(a, b) \\vdash \\urcorner M(a) \\vee \\urcorner M(b)",
       "AV.8": "\\urcorner M(a) \\vee \\urcorner M(b) \\vdash \\urcorner M(a, b)", "AV.9": "\\urcorner N(a, b) \\vdash \\urcorner N(a) \\vee \\urcorner N(b)",
       "AV.10": "\\urcorner N(a) \\vee \\urcorner N(b) \\vdash \\urcorner N(a, b)", "AVII.1": "(x \\rightarrow y) \\vdash \\urcorner M(\\downarrow (x\\sim y))",
       "AVII.2": "M(\\downarrow (x\\sim y)) \\vdash (x \\urcorner\\!\\rightarrow y)", "AVII.3": "(x \\rightarrow y)N(\\downarrow x) \\vdash N(\\downarrow y)",
       "AVII.4": "(x \\rightarrow y)M(\\downarrow x) \\vdash M(\\downarrow y)", "AVII.5": "(x \\rightarrow y)\\urcorner M(\\downarrow y) \\vdash \\urcorner M(\\downarrow x)",
       "AVII.6": "(x \\rightarrow y)\\urcorner N(\\downarrow y) \\vdash \\urcorner N(\\downarrow x)", "AVII.7": "(x \\rightarrow y)?M(\\downarrow y) \\vdash \\sim M(\\downarrow x)",
       "AVII.8": "(x \\rightarrow y)?N(\\downarrow y) \\vdash \\sim N(\\downarrow x)"}
XM = ["z", "\\sim z", "zv", "z \\vee v", "(a \\leftarrow b)", "\\sim(a \\leftarrow b)", "(\\forall a)(a \\leftarrow b)"]


def am_rec(lvl, typ="R"):
    ks = rnd.sample(sorted(AM1), 4)
    return card(12, 2, lvl, typ, "iso", f"{MO} Каким аксиомным схемам $S^{{m1}}_n$ (§ 2 гл. 12, с. 168–170) соответствуют формулы?\n\n" + items([f"${AM1[k]}$" for k in ks]),
                answers(ks), "С. 168–170.", "с. 168–170, гл. 12, § 2", "модальность, аксиомы", system="S^m1_n")


def wrapx(s):
    return s if re.fullmatch(r"\\sim [a-z]|[a-z]|\([^()]*\)|\\sim\([^()]*\)|\(\\forall a\)\([^()]*\)", s) else f"({s})"


def am_sub(lvl, typ="D"):
    k = rnd.choice([k for k in AM1 if not k.startswith("AV.")])
    s = AM1[k]
    X, Y = rnd.sample(XM, 2)
    mp = {"x": wrapx(X), "y": wrapx(Y)}
    out = sub_vars(s, mp)
    out = out.replace("\\sim (", "\\sim(")
    has_y = re.search(r"(?<![\\A-Za-z])y(?![A-Za-z])", s)
    return card(12, 2, lvl, typ, "iso", f"Буквы $z, v$ — высказывания; $a, b$ — термины. Подставьте в схему {k} $S^{{m1}}_n$ (${s}$) вместо $x$ — ${X}$" +
                (f", вместо $y$ — ${Y}$" if has_y else "") + ".", f"${out}$", "С. 168–170; буквы схем — метапеременные.", "с. 168–170, гл. 12, § 2",
                "модальность, аксиомы", system="S^m1_n")


def rmod(lvl, typ="D", sec=2, sysn="S^{m1}_n", sysk="S^m1_n", src="с. 170, гл. 12, § 2"):
    for _ in range(500):
        a, b = G6.G.rnd_f("xy", 2, "w"), G6.G.rnd_f("xy", 2, "w")
        if a != b and Q.strong(a, b) and repr(("rm", a, b)) not in USED:
            USED.add(repr(("rm", a, b)))
            break
    r = rnd.choice(["R1", "R2"])
    op = "N" if r == "R1" else "M"
    return card(12, sec, lvl, typ, "iso", f"{MO} В $S^s$ доказуема ${Q.ftex(a, b)}$. Какую формулу $S^{{{'m1' if sec == 2 else 'm0'}}}_n$ даёт правило {r} "
                f"(${'если' } x \\vdash y$, то ${op}(\\downarrow x) \\vdash {op}(\\downarrow y)$)? Почему исходная формула доказуема в $S^s$?",
                f"${op}(\\downarrow {wrapx(Q.tex(a))}) \\vdash {op}(\\downarrow {wrapx(Q.tex(b))})$",
                f"{r} (с. {170 if sec == 2 else 174}). Исходная формула — сильная тавтология: тавтология, и в заключение не входят элементарные высказывания, "
                "отсутствующие в посылке (гл. 5, § 2).", src, "модальность, правила", system=sysk)


def chain_mod(lvl, typ="D"):
    v_ = rnd.choice([("N(\\downarrow x) \\vdash M(\\downarrow x)", ["$N(\\downarrow x) \\vdash x$ [AI.1]", "$x \\vdash M(\\downarrow x)$ [AI.2]", "транзитивность [$S^s$]"]),
                     ("C(\\downarrow x) \\vdash M(\\downarrow \\sim x)", ["$C(\\downarrow x) \\vdash M(\\downarrow x)M(\\downarrow \\sim x)$ [AIII.1]", "отбрасывание конъюнкта [$S^s$]"]),
                     ("N(\\downarrow (xy)) \\vdash N(\\downarrow x)", ["$xy \\vdash x$ [$S^s$]", "$N(\\downarrow (xy)) \\vdash N(\\downarrow x)$ [R1]"]),
                     ("M(\\downarrow (xy)) \\vdash M(\\downarrow x)", ["$xy \\vdash x$ [$S^s$]", "$M(\\downarrow (xy)) \\vdash M(\\downarrow x)$ [R2]"]),
                     ("N(\\downarrow x)N(\\downarrow y) \\vdash N(\\downarrow (yx))", ["$N(\\downarrow x)N(\\downarrow y) \\vdash N(\\downarrow (xy))$ [AIV.3]", "$xy \\vdash yx$ [$S^s$]",
                      "$N(\\downarrow (xy)) \\vdash N(\\downarrow (yx))$ [R1: 2]", "транзитивность [$S^s$]"]),
                     ("N(\\downarrow x)M(\\downarrow y) \\vdash M(\\downarrow y)", ["$N(\\downarrow x)M(\\downarrow y) \\vdash M(\\downarrow (xy))$ [AIV.4]", "$xy \\vdash y$ [$S^s$]",
                      "$M(\\downarrow (xy)) \\vdash M(\\downarrow y)$ [R2: 2]", "транзитивность [$S^s$]"])])
    X = rnd.choice(["z", "(a \\leftarrow b)", "zv", "\\sim z"])
    goal = sub_vars(v_[0], {"x": wrapx(X)})
    st = [sub_vars(s, {"x": wrapx(X)}) for s in v_[1]]
    hide = lvl == 4
    if hide:
        j = rnd.randrange(len(st))
        m = re.search(r"\[([^\[\]]*)\]$", st[j])
        sh = [re.sub(r"\[[^\[\]]*\]$", "[…]", s) if n == j else s for n, s in enumerate(st)]
        return card(12, 2, lvl, "D", "complete", f"{MO} Буквы $z, v$ — высказывания. Восстановите пропущенное основание в выводе ${goal}$ в $S^{{m1}}_n$:\n\n" +
                    "\n".join(f"{n + 1}. {s}" for n, s in enumerate(sh)), f"Шаг {j + 1}: {m.group(1)}.", "\n".join(f"{n + 1}. {s}" for n, s in enumerate(st)),
                    "с. 168–170, гл. 12, § 2", "модальность, вывод", system="S^m1_n")
    return card(12, 2, lvl, typ, "iso", f"{MO} Буквы $z, v$ — высказывания. Выведите в $S^{{m1}}_n$ формулу ${goal}$.", "См. решение.",
                "\n".join(f"{n + 1}. {s}" for n, s in enumerate(st)) + "\n\nС. 168–170.", "с. 168–170, гл. 12, § 2", "модальность, вывод", answ="proof", system="S^m1_n")


AVQ = [("\\alpha Q(a) \\vdash \\alpha Q(\\downarrow (E(a)))", "AV.1"), ("\\alpha Q(\\downarrow (E(a))) \\vdash \\alpha Q(a)", "AV.2")]


def av_card(lvl, typ="D"):
    f, n = rnd.choice(AVQ)
    al = rnd.choice(["", "\\urcorner ", "?"])
    q = rnd.choice(["M", "N", "C"])
    a = rnd.choice(["a", "bc", "(b \\vee c)"])
    out = f.replace("\\alpha Q", f"{al}{q}").replace("(a)", f"({a})" if not a.startswith("(") else a).replace("(E(a))", f"(E({a}))")
    out = out.replace(f"(E(({a[1:-1]})))", f"(E({a}))") if a.startswith("(") else out
    return card(12, 2, lvl, typ, "iso", f"Буквы $a, b, c$ — термины. Запишите пример схемы {n} $S^{{m1}}_n$ (${f}$, $Q$ — модальный предикат) при "
                f"$Q = {q}$, $\\alpha$ — " + ({"": "отсутствие операторов", "\\urcorner ": "$\\urcorner$", "?": "$?$"}[al]) + f", $a$ — ${a}$.",
                f"${out}$", "С. 169: $\\alpha$ — наличие одного из $\\urcorner$ и $?$ или отсутствие обоих.", "с. 169, гл. 12, § 2", "модальность, аксиомы", system="S^m1_n")


E1202 = [("«AI.1: $x \\vdash N(\\downarrow x)$»", "AI.1 — $N(\\downarrow x) \\vdash x$; из $x$ следует лишь $M(\\downarrow x)$ (AI.2, с. 168)"),
         ("«AII.1: $N(\\downarrow x) \\vdash \\urcorner M(\\downarrow x)$»", "AII.1 — $N(\\downarrow x) \\vdash \\urcorner M(\\downarrow \\sim x)$ (с. 168)"),
         ("«AIII.2: $M(\\downarrow x) \\vdash C(\\downarrow x)$»", "AIII.2 — $M(\\downarrow x)M(\\downarrow \\sim x) \\vdash C(\\downarrow x)$ (с. 169)"),
         ("«AIV.1 даёт $M(\\downarrow (xy)) \\vdash M(\\downarrow x)M(\\downarrow y)$»", "AIV.1 — о дизъюнкции: $M(\\downarrow (x \\vee y)) \\vdash M(\\downarrow x) \\vee M(\\downarrow y)$; "
          "для конъюнкции есть T2 § 3 (с. 171), выводимая по R2"),
         ("«AIV.3: $M(\\downarrow x)M(\\downarrow y) \\vdash M(\\downarrow (xy))$»", "AIV.3 — для $N$: $N(\\downarrow x)N(\\downarrow y) \\vdash N(\\downarrow (xy))$ (с. 169)"),
         ("«R1: если $x \\vdash y$, то $M(\\downarrow x) \\vdash M(\\downarrow y)$»", "это R2; R1 — для $N$ (с. 170)"),
         ("«по R1 из $x \\vdash x \\vee y$ получаем $N(\\downarrow x) \\vdash N(\\downarrow (x \\vee y))$»", "R1 применяется к доказуемой $x \\vdash y$; $x \\vdash x \\vee y$ "
          "в $S^s$ недоказуема (новое $y$ в заключении, гл. 5, § 2)"),
         ("«AVII.1: $\\urcorner M(\\downarrow (x\\sim y)) \\vdash (x \\rightarrow y)$»", "AVII.1 — $(x \\rightarrow y) \\vdash \\urcorner M(\\downarrow (x\\sim y))$; обратная формула "
          "в $S^{mi}_n$ недоказуема (§ 10, с. 175)"),
         ("«$\\alpha$ в AV.1 может означать $\\sim$»", "по с. 169 $\\alpha$ — наличие одного из $\\urcorner$ и $?$ или отсутствие обоих"),
         ("«AVII.7: $(x \\rightarrow y)?M(\\downarrow y) \\vdash ?M(\\downarrow x)$»", "AVII.7 — $(x \\rightarrow y)?M(\\downarrow y) \\vdash \\sim M(\\downarrow x)$ (с. 170)")]


def m1202(lvl, d, i):
    if d:
        return epick(E1202, 12, 2, lvl, MO, "с. 168–175, гл. 12, § 2, 10", "модальность, диагностика", "S^m1_n", letters="xy")
    if lvl == 1:
        return am_rec(1)
    if lvl == 2:
        return [am_rec, am_sub, av_card][i % 3](2, "C" if i % 3 == 0 else "D")
    if lvl == 3:
        return [am_sub, av_card, rmod, am_rec][i % 4](3) if i % 4 != 3 else am_rec(3, "C")
    if lvl == 4:
        return [chain_mod, rmod, am_sub][i % 3](4)
    if lvl == 5:
        return [chain_mod, rmod, am_sub, av_card][i % 4](5)
    if lvl == 6:
        return [rmod, chain_mod, am_sub][i % 3](6, "C")
    return rmod(7, "S")


T123 = {1: "N(\\downarrow (xy)) \\vdash N(\\downarrow x)N(\\downarrow y)", 2: "M(\\downarrow xy) \\vdash M(\\downarrow x)M(\\downarrow y)", 3: "C(\\downarrow (xy)) \\vdash M(\\downarrow x)M(\\downarrow y)",
        4: "\\urcorner N(\\downarrow (xy)) \\vdash \\urcorner N(\\downarrow x) \\vee \\urcorner N(\\downarrow y)", 5: "\\urcorner N(\\downarrow x) \\vee \\urcorner N(\\downarrow y) \\vdash \\urcorner N(\\downarrow (xy))",
        6: "N(\\downarrow x) \\vdash \\urcorner C(\\downarrow x)", 7: "\\urcorner C(\\downarrow x) \\vdash N(\\downarrow x)", 8: "\\alpha C(\\downarrow x) \\vdash M(\\downarrow x)",
        9: "N(\\downarrow x) \\vdash NN(\\downarrow x)", 10: "M(\\downarrow x) \\vdash NM(\\downarrow x)", 11: "MM(\\downarrow x) \\vdash M(\\downarrow x)", 12: "MN(\\downarrow x) \\vdash M(\\downarrow x)",
        13: "\\sim N(\\downarrow x) \\vdash N(\\downarrow (\\sim N(\\downarrow x)))"}


def m1203(lvl, d, i):
    if d:
        pool = [("«T9 § 3 гл. 12: $NN(\\downarrow x) \\vdash N(\\downarrow x)$»", "T9 — $N(\\downarrow x) \\vdash NN(\\downarrow x)$ (с. 171)"),
                ("«T1 § 3 гл. 12 выражает $N(\\downarrow x)N(\\downarrow y) \\vdash N(\\downarrow (xy))$»", "это AIV.3 (с. 169); T1 — обратная: $N(\\downarrow (xy)) \\vdash N(\\downarrow x)N(\\downarrow y)$ (с. 171)"),
                ("«T6 $N(\\downarrow x) \\vdash \\urcorner C(\\downarrow x)$ можно обратить в $\\urcorner C(\\downarrow x) \\vdash M(\\downarrow \\sim x)$»", "по T7 (с. 171) "
                 "$\\urcorner C(\\downarrow x) \\vdash N(\\downarrow x)$; формула студента в списке следствий не значится")]
        return epick(pool[:2], 12, 3, lvl, MO, "с. 169–171, гл. 12, § 2–3", "модальность, диагностика", "S^m1_n", letters="xy")
    if lvl in (2, 3, 4):
        ks = rnd.sample(sorted(T123), 3)
        return card(12, 3, lvl, "R" if lvl == 2 else "C", "iso", f"{MO} Укажите номера следствий $S^{{m1}}_n$ (§ 3 гл. 12, с. 171):\n\n" + items([f"${T123[k]}$" for k in ks]),
                    answers([f"T{k}" for k in ks]), "С. 171.", "с. 171, гл. 12, § 3", "модальность, теоремы", system="S^m1_n")
    k = rnd.choice(["T1", "T2"])
    X, Y = rnd.sample(["z", "v", "(a \\leftarrow b)", "\\sim z"], 2)
    op = "N" if k == "T1" else "M"
    r = "R1" if k == "T1" else "R2"
    st = [f"$xy \\vdash x$ [$S^s$]", f"${op}(\\downarrow (xy)) \\vdash {op}(\\downarrow x)$ [{r}]", f"$xy \\vdash y$ [$S^s$]", f"${op}(\\downarrow (xy)) \\vdash {op}(\\downarrow y)$ [{r}]",
          f"${op}(\\downarrow (xy)) \\vdash {op}(\\downarrow x){op}(\\downarrow y)$ [$S^s$: 2, 4]"]
    st = [sub_vars(s, {"x": X, "y": Y}) for s in st]
    return card(12, 3, lvl, "S" if lvl == 7 else "D", "iso", f"{MO} Буквы $z, v$ — высказывания. Выведите следствие {k} § 3 гл. 12 при $x = {X}$, $y = {Y}$.",
                "См. решение.", "\n".join(f"{n + 1}. {s}" for n, s in enumerate(st)) + "\n\nС. 170–171.", "с. 170–171, гл. 12, § 2–3", "модальность, вывод",
                answ="proof", system="S^m1_n")


MOP = [("$(\\mathrm{M}a)x$", "«возможно, что для $a$ имеет место $x$»: модальный оператор M с термином $a$"),
       ("$\\mathrm{M}$, $\\mathrm{N}$, $\\mathrm{C}$", "модальные операторы, соответствующие словам «возможно», «необходимо», «случайно» как логическим операторам"),
       ("$(\\alpha\\mathrm{Q}a)x \\vdash \\alpha Q(a \\downarrow x)$", "схема AI.1 $S^{m2}_n$: $\\mathrm{Q}$ — модальный оператор, $Q$ — соответствующий модальный предикат"),
       ("$S^{m2}_n$", "система, определяющая свойства модальных операторов: $S^{m1}_n$ плюс схемы AI–AIII § 4"),
       ("$(\\alpha\\mathrm{Q}a)x \\vdash (\\alpha\\mathrm{Q}b)x$", "схема AII.1 $S^{m2}_n$; $a$ и $b$ свободно входят в $x$, $\\mathrm{Q}$ — модальный оператор")]


def m1204(lvl, d, i):
    if d:
        pool = [("«$\\mathrm{M}$ и $M$ — одно и то же»", "$\\mathrm{M}$ — модальный оператор, $M$ — модальный предикат (с. 171–172)"),
                ("«AII.1 $S^{m2}_n$ $(\\alpha\\mathrm{Q}a)x \\vdash (\\alpha\\mathrm{Q}b)x$ верна при любых $a$, $b$»", "по с. 172 — если $a$ и $b$ свободно входят в $x$")]
        return epick(pool, 12, 4, lvl, MO, "с. 171–172, гл. 12, § 4", "модальные операторы, диагностика")
    if lvl in (1, 2):
        s, w = MOP[G8.nxt("mop") % len(MOP)]
        return card(12, 4, lvl, "R" if lvl == 1 else "C", "iso", f"Что обозначает по § 4 гл. 12 (с. 171–172) запись {s}?", w[0].upper() + w[1:] + ".", "С. 171–172.",
                    "с. 171–172, гл. 12, § 4", "модальные операторы")
    q = rnd.choice(["M", "N", "C"])
    al = rnd.choice(["", "\\urcorner ", "?"])
    X = rnd.choice(["(a \\leftarrow b)", "\\sim(a \\leftarrow c)"])
    return card(12, 4, lvl, "D" if lvl == 4 else "C", "iso", f"Буквы $a, b, c$ — термины. Запишите по схеме AI.1 $S^{{m2}}_n$ (с. 171) формулу для $({al}\\mathrm{{{q}}}a){X}$.",
                f"$({al}\\mathrm{{{q}}}a){X} \\vdash {al}{q}(a \\downarrow {X})$", "AI.1: $(\\alpha\\mathrm{Q}a)x \\vdash \\alpha Q(a \\downarrow x)$; $Q$ — предикат, соответствующий "
                "оператору $\\mathrm{Q}$.", "с. 171–172, гл. 12, § 4", "модальные операторы", system="S^m2_n")


INT12 = [("$x$ приписано значение 1", "$M(\\downarrow x)$ приписывается значение 1", "1"), ("$M(\\downarrow x)$ приписано значение 0", "$x$ приписывается значение 0", "1"),
         ("$M(\\downarrow x)$ имеет значение 1", "$x$ может принять значение 1", "1"), ("нужно значение $N(\\downarrow x)$", "оно равно значению $\\urcorner M(\\downarrow \\sim x)$", "2"),
         ("нужно значение $\\urcorner N(\\downarrow x)$", "оно равно значению $M(\\downarrow \\sim x)$", "2"), ("нужно значение $C(\\downarrow x)$", "оно равно значению $M(\\downarrow x)M(\\downarrow \\sim x)$", "3"),
         ("нужно значение $?C(\\downarrow x)$", "оно равно значению $M(\\downarrow x)?M(\\downarrow \\sim x)$", "3"), ("$a$ и $b$ равнозначны", "равнозначны $\\alpha Q(a)$ и $\\alpha Q(b)$", "4"),
         ("нужно значение $(\\alpha\\mathrm{Q}a)x$", "оно равно значению $\\alpha Q(a \\downarrow x)$", "5")]


def m1205(lvl, d, i):
    if d:
        pool = [("«по п. 1 § 5 гл. 12 из $M(\\downarrow x) = 1$ следует $x = 1$»", "по п. 1 тогда $x$ лишь может принять значение 1 (с. 172)"),
                ("«$N(\\downarrow x)$ равнозначно $\\urcorner M(\\downarrow x)$»", "по п. 2 — $\\urcorner M(\\downarrow \\sim x)$ (с. 173)")]
        return epick(pool, 12, 5, lvl, MO, "с. 172–173, гл. 12, § 5", "модальность, интерпретация, диагностика", letters="xy")
    if lvl == 7:
        return card(12, 5, 7, "S", "transfer", f"{MO} Покажите по интерпретации § 5 (пп. 1–2), что схемы AI.1 и AI.2 $S^{{m1}}_n$ — тавтологии (MT1, с. 173).",
                    "AI.2: если $x = 1$, то $M(\\downarrow x) = 1$ (п. 1). AI.1: если $N(\\downarrow x) = 1$, то $\\urcorner M(\\downarrow \\sim x) = 1$ (п. 2), значит, $\\sim x$ не "
                    "может быть 1 (по п. 1: если $\\sim x$ может принять 1, то $M(\\downarrow \\sim x) = 1$); следовательно, $x = 1$.", "С. 172–173.", "с. 172–173, гл. 12, § 5",
                    "модальность, интерпретация", system="S^m1_n")
    its = rnd.sample(INT12, 3)
    return card(12, 5, lvl, "R" if lvl == 1 else "C", "iso", f"{MO} Что следует по интерпретации § 5 гл. 12 (с. 172–173)? Укажите пункт.\n\n" + items([s for s, _, _ in its]),
                answers([f"{w} (п. {n})" for _, w, n in its]), "С. 172–173.", "с. 172–173, гл. 12, § 5", "модальность, интерпретация")


def classical12(s):
    """Переход к S^m1_c (§ 6): внутреннее отрицание → внешнее; формулы с ? исключаются."""
    if "?" in s:
        return None
    return s.replace("\\urcorner ", "\\sim ").replace("\\urcorner", "\\sim ")


def m1206(lvl, d, i):
    if d:
        pool = [("«при переходе к $S^{m1}_c$ формулы с $?$ сохраняются, а $?$ заменяется на $\\sim$»", "формулы со знаком неопределённости исключаются (с. 173)"),
                ("«в $S^{m1}_c$ внешнее отрицание заменяется внутренним»", "наоборот: внутреннее заменяется повсюду на внешнее (с. 173)")]
        return epick(pool, 12, 6, lvl, MO, "с. 173, гл. 12, § 6", "модальность, классический случай, диагностика")
    if lvl == 2:
        return card(12, 6, 2, "R", "iso", f"{MO} Как получается система $S^{{m1}}_c$ классической теории модальностей (§ 6 гл. 12)?",
                    "Из $S^{m1}_n$ исключением формул со знаком неопределённости, заменой повсюду внутреннего отрицания на внешнее и исключением повторений и "
                    "зависимых схем (с. 173).", "С. 173.", "с. 173, гл. 12, § 6", "модальность, классический случай", form="meta", answ="text")
    ks = rnd.sample(sorted(AM1), 3 if lvl < 7 else 4)
    res = [(k, classical12(AM1[k])) for k in ks]
    return card(12, 6, lvl, "S" if lvl == 7 else "C", "transfer", f"{MO} Что происходит со схемами $S^{{m1}}_n$ при переходе к $S^{{m1}}_c$ (§ 6 гл. 12)?\n\n" +
                items([f"{k}. ${AM1[k]}$" for k in ks]), answers(["исключается (содержит $?$)" if r is None else f"${r}$" for _, r in res]),
                "С. 173: формулы с $?$ исключаются, $\\urcorner$ заменяется на $\\sim$; затем исключаются повторения и зависимые схемы.", "с. 173, гл. 12, § 6",
                "модальность, классический случай")


AM0 = {"A1": "N(\\downarrow x) \\vdash x", "A2": "x \\vdash M(\\downarrow x)", "A3": "N(\\downarrow x) \\vdash \\urcorner M(\\downarrow \\sim x)", "A4": "\\urcorner M(\\downarrow \\sim x) \\vdash N(\\downarrow \\sim x)",
       "A5": "\\urcorner N(\\downarrow x) \\vdash M(\\downarrow \\sim x)", "A6": "M(\\downarrow \\sim x) \\vdash \\urcorner N(\\downarrow x)", "A7": "M(\\downarrow (x \\vee y)) \\vdash M(\\downarrow x) \\vee M(\\downarrow y)",
       "A8": "M(\\downarrow x) \\vee M(\\downarrow y) \\vdash M(\\downarrow (x \\vee y))", "A9": "N(\\downarrow x)M(\\downarrow y) \\vdash M(\\downarrow (xy))",
       "A10": "N(\\downarrow x) \\vee N(\\downarrow y) \\vdash N(\\downarrow (x \\vee y))", "A11": "N(\\downarrow (x \\vee y)) \\vdash N(\\downarrow x) \\vee M(\\downarrow y)",
       "A12": "M(\\downarrow x)?M(\\downarrow y) \\vdash ?M(\\downarrow (xy))", "A13": "?M(\\downarrow x)?M(\\downarrow y) \\vdash ?M(\\downarrow (xy))",
       "A14": "N(\\downarrow x) \\vdash N(\\downarrow (N(\\downarrow x)))", "A15": "M(\\downarrow (M(\\downarrow x))) \\vdash M(\\downarrow x)"}


def m1207(lvl, d, i):
    if d:
        pool = [("«в $S^{m0}_c$ сохраняются схемы A12 и A13»", "они исключаются (с. 174)"),
                ("«в $S^{m0}_c$ схемы A3–A6 заменяются одной: $N(\\downarrow x) \\vdash \\sim M(\\downarrow \\sim x)$»", "заменяются двумя: $N(\\downarrow x) \\vdash \\sim M(\\downarrow \\sim x)$ "
                 "и $\\sim M(\\downarrow \\sim x) \\vdash N(\\downarrow x)$ (с. 174)"),
                ("«основная модальная логика включает и предикат $C$»", "по с. 173 в ней рассматриваются отношения $M$ и $N$ и операторов $\\cdot$, $\\vee$, $\\sim$, $\\supset$"),
                ("«A14: $N(\\downarrow (N(\\downarrow x))) \\vdash N(\\downarrow x)$»", "A14 — $N(\\downarrow x) \\vdash N(\\downarrow (N(\\downarrow x)))$ (с. 174)"),
                ("«A10: $N(\\downarrow (x \\vee y)) \\vdash N(\\downarrow x) \\vee N(\\downarrow y)$»", "A10 — $N(\\downarrow x) \\vee N(\\downarrow y) \\vdash N(\\downarrow (x \\vee y))$ (с. 174)")]
        return epick(pool, 12, 7, lvl, MO, "с. 173–174, гл. 12, § 7", "основная модальная логика, диагностика", "S^m0_n", letters="xy")
    if lvl in (1, 2, 3):
        ks = rnd.sample(sorted(AM0, key=lambda k: int(k[1:])), 3)
        return card(12, 7, lvl, "R" if lvl == 1 else "C", "iso", f"{MO} Каким схемам $S^{{m0}}_n$ (§ 7 гл. 12, с. 174) соответствуют формулы?\n\n" + items([f"${AM0[k]}$" for k in ks]),
                    answers(ks), "С. 174.", "с. 174, гл. 12, § 7", "основная модальная логика", system="S^m0_n")
    if lvl in (4, 5, 6):
        if i % 2 == 0:
            return rmod(lvl, "D" if lvl < 6 else "C", sec=7, sysk="S^m0_n", src="с. 174, гл. 12, § 7")
        ks = rnd.sample(["A3", "A4", "A5", "A6", "A12", "A13", "A1", "A7", "A14"], 3)
        def fate(k):
            return {"A12": "исключается", "A13": "исключается", "A3": "заменяется (вместе с A4–A6) двумя схемами", "A4": "заменяется (вместе с A3, A5, A6)",
                    "A5": "заменяется (вместе с A3, A4, A6)", "A6": "заменяется (вместе с A3–A5)"}.get(k, "сохраняется")
        return card(12, 7, lvl, "C", "transfer", f"{MO} Что происходит со схемами $S^{{m0}}_n$ при переходе к $S^{{m0}}_c$ (с. 174)?\n\n" + items([f"{k}. ${AM0[k]}$" for k in ks]),
                    answers([fate(k) for k in ks]), "С. 174: исключаются A12, A13; A3–A6 заменяются на $N(\\downarrow x) \\vdash \\sim M(\\downarrow \\sim x)$ и $\\sim M(\\downarrow \\sim x) \\vdash N(\\downarrow x)$.",
                    "с. 174, гл. 12, § 7", "основная модальная логика", system="S^m0_c")
    if G8.nxt("m1207s") % 2 == 0:
        return card(12, 7, 7, "S", "transfer", f"{MO} Выведите $N(\\downarrow x) \\vdash M(\\downarrow x)$ в $S^{{m0}}_n$ и в $S^{{m0}}_c$.", "В обеих: A1 $N(\\downarrow x) \\vdash x$, A2 "
                    "$x \\vdash M(\\downarrow x)$, транзитивность — эти схемы при переходе к $S^{m0}_c$ сохраняются.", "С. 174.", "с. 174, гл. 12, § 7", "основная модальная логика")
    return card(12, 7, 7, "S", "transfer", f"{MO} Доказуемы ли в $S^{{m0}}_n$ и в $S^{{m0}}_c$ формулы $N(\\downarrow x) \\vdash \\urcorner M(\\downarrow \\sim x)$ и $N(\\downarrow x) \\vdash \\sim M(\\downarrow \\sim x)$?",
                "Первая — A3 $S^{m0}_n$; в $S^{m0}_c$ A3–A6 заменены, и там доказуема вторая (с. 174).", "С. 174.", "с. 174, гл. 12, § 7", "основная модальная логика")


ALM = {"A*1": "LN(\\downarrow x) \\vdash \\sim LM(\\downarrow \\sim x)", "A*2": "\\sim LM(\\downarrow \\sim x) \\vdash LN(\\downarrow x)", "A*3": "LN(\\downarrow x) \\vdash N(\\downarrow x)",
       "A*4": "M(\\downarrow x) \\vdash LM(\\downarrow x)", "A*5": "LC(\\downarrow x) \\vdash LM(\\downarrow x)LM(\\downarrow \\sim x)", "A*6": "LM(\\downarrow x)LM(\\downarrow \\sim x) \\vdash LC(\\downarrow x)"}


def m1208(lvl, d, i):
    if d:
        pool = [("«A*3: $N(\\downarrow x) \\vdash LN(\\downarrow x)$»", "A*3 — $LN(\\downarrow x) \\vdash N(\\downarrow x)$: логически необходимое необходимо (с. 175)"),
                ("«R*1: если $x \\vdash y$, то $LN(\\downarrow x) \\vdash LN(\\downarrow y)$»", "R*1 — если $\\vdash x$, то $\\vdash LN(\\downarrow x)$ (с. 175)")]
        return epick(pool, 12, 8, lvl, MO, "с. 175, гл. 12, § 8", "логические модальности, диагностика", letters="xy")
    if lvl in (1, 2):
        ks = rnd.sample(sorted(ALM), 3)
        return card(12, 8, lvl, "R" if lvl == 1 else "C", "iso", f"{MO} $LM$, $LN$, $LC$ — «логически возможно», «логически необходимо», «логически случайно». Какие схемы § 8 "
                    "гл. 12 (с. 175) записаны?\n\n" + items([f"${ALM[k]}$" for k in ks]), answers(ks), "С. 175.", "с. 175, гл. 12, § 8", "логические модальности")
    if lvl in (3, 5):
        f = rnd.choice(["x \\vee \\sim x", "\\sim(x\\sim x)", "(x \\vee y) \\vee \\sim x"])
        return card(12, 8, lvl, "D", "iso", f"{MO} Доказуема $\\vdash {f}$. Что дают R*1 и A*3 § 8 гл. 12?", f"$\\vdash LN(\\downarrow ({f}))$ (R*1), затем "
                    f"$\\vdash N(\\downarrow ({f}))$ (A*3 и транзитивность).", "С. 175.", "с. 175, гл. 12, § 8", "логические модальности", answ="proof")
    if lvl == 6:
        return card(12, 8, 6, "C", "open", f"{MO} Следует ли из $M(\\downarrow x)$, что $x$ логически возможно, и из $LN(\\downarrow x)$ — что $x$ необходимо (§ 8 гл. 12)?",
                    "Да в обоих случаях: A*4 $M(\\downarrow x) \\vdash LM(\\downarrow x)$ и A*3 $LN(\\downarrow x) \\vdash N(\\downarrow x)$ (с. 175).", "С. 175.", "с. 175, гл. 12, § 8",
                    "логические модальности")
    if G8.nxt("m1208s") % 2 == 1:
        return card(12, 8, 7, "S", "transfer", f"{MO} Сравните схемы A*5, A*6 § 8 ($LC$) со схемами AIII.1, AIII.2 § 2 ($C$). Что общего?", "Строение одинаково: "
                    "$LC(\\downarrow x) \\dashv\\vdash LM(\\downarrow x)LM(\\downarrow \\sim x)$ и $C(\\downarrow x) \\dashv\\vdash M(\\downarrow x)M(\\downarrow \\sim x)$: случайное — возможное вместе со своим "
                    "отрицанием (с. 169, 175).", "С. 169, 175.", "с. 169, 175, гл. 12, § 2, 8", "логические модальности")
    return card(12, 8, 7, "S", "transfer", f"{MO} Сравните схемы $N(\\downarrow x) \\vdash \\urcorner M(\\downarrow \\sim x)$ (AII.1 $S^{{m1}}_n$) и A*1 $LN(\\downarrow x) \\vdash \\sim LM(\\downarrow \\sim x)$: "
                "какое отрицание используется в каждой?", "В AII.1 — внутреннее $\\urcorner$ (неклассический случай); в A*1 — внешнее $\\sim$ (с. 168, 175).",
                "С. 168, 175.", "с. 168, 175, гл. 12, § 2, 8", "логические модальности")


T129 = {"T1": "E(\\downarrow x) \\vdash M(\\downarrow x)", "T2": "N(\\downarrow x) \\vdash E(\\downarrow x)", "T3": "U(\\downarrow x) \\vdash N(\\downarrow x)",
        "T4": "\\urcorner U(\\downarrow x) \\vdash M(\\downarrow \\sim x)", "T5": "C(\\downarrow x) \\vdash \\urcorner U(\\downarrow x)", "T6": "\\urcorner M(\\downarrow x) \\vdash \\urcorner E(\\downarrow x)"}


def m1209(lvl, d, i):
    if d:
        pool = [("«T1 § 9 гл. 12: $M(\\downarrow x) \\vdash E(\\downarrow x)$»", "T1 — $E(\\downarrow x) \\vdash M(\\downarrow x)$ (с. 175)"),
                ("«T3: $N(\\downarrow x) \\vdash U(\\downarrow x)$»", "T3 — $U(\\downarrow x) \\vdash N(\\downarrow x)$ (с. 175)")]
        return epick(pool, 12, 9, lvl, MO, "с. 175, гл. 12, § 9", "модальность и существование, диагностика", letters="xy")
    if lvl in (2, 3):
        ks = rnd.sample(sorted(T129), 3)
        return card(12, 9, lvl, "R" if lvl == 2 else "C", "iso", f"{MO} $E$, $U$ — «существует», «универсально». Укажите номера теоремных схем § 9 гл. 12 (с. 175):\n\n" +
                    items([f"${T129[k]}$" for k in ks]), answers(ks), "С. 175; соотношение определено также AV.1 и AV.2 § 2.", "с. 169, 175, гл. 12, § 2, 9",
                    "модальность и существование")
    ch = rnd.choice([("U(\\downarrow x) \\vdash M(\\downarrow x)", ["$U(\\downarrow x) \\vdash N(\\downarrow x)$ [T3]", "$N(\\downarrow x) \\vdash E(\\downarrow x)$ [T2]",
                       "$E(\\downarrow x) \\vdash M(\\downarrow x)$ [T1]", "транзитивность [$S^s$]"]),
                     ("N(\\downarrow x) \\vdash M(\\downarrow x)", ["$N(\\downarrow x) \\vdash E(\\downarrow x)$ [T2]", "$E(\\downarrow x) \\vdash M(\\downarrow x)$ [T1]", "транзитивность [$S^s$]"]),
                     ("U(\\downarrow x) \\vdash E(\\downarrow x)", ["$U(\\downarrow x) \\vdash N(\\downarrow x)$ [T3]", "$N(\\downarrow x) \\vdash E(\\downarrow x)$ [T2]", "транзитивность [$S^s$]"])])
    X = rnd.choice(["z", "(a \\leftarrow b)", "zv", "\\sim z", "z \\vee v"])
    goal = sub_vars(ch[0], {"x": wrapx(X)})
    st = [sub_vars(s, {"x": wrapx(X)}) for s in ch[1]]
    return card(12, 9, lvl, "S" if lvl == 7 else "D", "iso", f"{MO} Буквы $z, v$ — высказывания. Выведите ${goal}$ из теоремных схем § 9 гл. 12.", "См. решение.",
                "\n".join(f"{n + 1}. {s}" for n, s in enumerate(st)) + "\n\nС. 175.", "с. 175, гл. 12, § 9", "модальность и существование", answ="proof")


NATXY = [("«идёт дождь»", "«улица мокрая»"), ("«число делится на 4»", "«число чётное»"), ("«ключ повернули»", "«дверь открыта»"), ("«вода нагрета до 100 °C»", "«вода кипит»")]


def m1210(lvl, d, i):
    if d:
        p_, q_ = rnd.choice(NATXY)
        v_ = rnd.choice([(f"«“Невозможно, что {p_[1:-1]} и не {q_[1:-1]}” — это просто сокращение для “если {p_[1:-1]}, то {q_[1:-1]}”»",
                          "по § 10 (с. 175) $\\urcorner M(\\downarrow (x\\sim y)) \\vdash (x \\rightarrow y)$ в $S^{mi}_n$ недоказуема (не тавтология), поэтому её нельзя "
                          "рассматривать как сокращение для $(x \\rightarrow y)$"),
                         (f"«в классическом случае из “не возможно, что {p_[1:-1]} и не {q_[1:-1]}” ($\\sim M(\\downarrow (x\\sim y))$) следует “если {p_[1:-1]}, то {q_[1:-1]}”»",
                          "по с. 175 $\\sim M(\\downarrow (x\\sim y)) \\vdash (x \\rightarrow y)$ в $S^{mi}_c$ недоказуема")])
        return E(12, 10, lvl, MO, v_[0], v_[1], "с. 175, гл. 12, § 10", "модальность и условность, диагностика", form="nat")
    if lvl == 2:
        return card(12, 10, 2, "R", "iso", f"{MO} Какие формулы § 10 гл. 12 (с. 175) объявляет недоказуемыми и в каких системах?",
                    "$\\urcorner M(\\downarrow (x\\sim y)) \\vdash (x \\rightarrow y)$ — в $S^{mi}_n$ (не тавтология); $\\sim M(\\downarrow (x\\sim y)) \\vdash (x \\rightarrow y)$ — в $S^{mi}_c$.",
                    "С. 175.", "с. 175, гл. 12, § 10", "модальность и условность")
    p_, q_ = rnd.choice(NATXY)
    if lvl in (3, 4, 5, 6):
        dirn = G8.nxt("m1210") % 2
        if dirn == 0:
            return card(12, 10, lvl, "C", "iso", f"{MO} Пусть $x$ — {p_}, $y$ — {q_}. Что следует из «Если {p_[1:-1]}, то {q_[1:-1]}» по AVII.1 $S^{{m1}}_n$ (с. 170) и следует "
                        "ли обратное (§ 10)?", "Следует $\\urcorner M(\\downarrow (x\\sim y))$ («невозможно, что $x$ и не $y$»); обратное недоказуемо (с. 175).",
                        "AVII.1: $(x \\rightarrow y) \\vdash \\urcorner M(\\downarrow (x\\sim y))$; § 10.", "с. 170, 175, гл. 12, § 2, 10", "модальность и условность", form="nat")
        return card(12, 10, lvl, "C", "iso", f"{MO} Пусть $x$ — {p_}, $y$ — {q_}, и истинно $M(\\downarrow (x\\sim y))$ («возможно, что {p_[1:-1]} и не {q_[1:-1]}»). Что следует по AVII.2 "
                    "$S^{m1}_n$?", "$(x \\urcorner\\!\\rightarrow y)$: признание $x$ не обязывает признать $y$ (с. 170).", "AVII.2 (с. 170).", "с. 170, гл. 12, § 2",
                    "модальность и условность", form="nat")
    return card(12, 10, lvl, "S" if lvl == 7 else "C", "transfer", f"{MO} Можно ли в $S^{{mi}}_n$ и в $S^{{mi}}_c$ считать $(x \\rightarrow y)$ сокращением для "
                "$\\urcorner M(\\downarrow (x\\sim y))$, соответственно $\\sim M(\\downarrow (x\\sim y))$? Обоснуйте.", "Нет: в $S^{mi}_n$ недоказуема $\\urcorner M(\\downarrow (x\\sim y)) "
                "\\vdash (x \\rightarrow y)$, в $S^{mi}_c$ — $\\sim M(\\downarrow (x\\sim y)) \\vdash (x \\rightarrow y)$; доказуема лишь одна сторона (AVII.1).",
                "С. 170, 175.", "с. 170, 175, гл. 12, § 2, 10", "модальность и условность")


def m1211(lvl, d, i):
    f, g = rnd.choice([("(\\forall a)x \\vdash (\\exists a)x", "(\\mathrm{N}a)x \\vdash (\\mathrm{M}a)x"), ("(\\exists a)(\\forall b)x \\vdash (\\forall b)(\\exists a)x", "(\\mathrm{M}a)(\\mathrm{N}b)x \\vdash (\\mathrm{N}b)(\\mathrm{M}a)x")])
    return card(12, 11, 2, "D", "iso", f"Буквы $a, b$ — термины; $x$ — высказывание. По заменам MT1 § 11 гл. 12 ($(\\alpha\\forall a)z$ → $(\\alpha\\mathrm{{N}}a)z$, "
                f"$(\\alpha\\exists a)z$ → $(\\alpha\\mathrm{{M}}a)z$) переведите формулу теории кванторов ${f}$ в формулу теории модальностей.", f"${g}$",
                "MT1 (с. 176): если $(x \\vdash y)^q$ доказуема, то $(x \\vdash y)^m$ доказуема, и наоборот.", "с. 176, гл. 12, § 11", "модальности и кванторы")


# ================================================================ ручные ступени 8–10
H = []


def hand(ch, sec, lvl, cond, ans, sol, src, tags, system=None):
    H.append(card(ch, sec, lvl, "I" if lvl == 10 else "M", "transfer", cond, ans, sol, src, tags, form="meta", answ="proof", system=system, gen=False))


def hand_cards():
    hand(10, 8, 8, "Восстановите рассуждение с. 159: как получают утверждения B из утверждения A и почему это незаконно?", "Подставляют $nk$ на место $a$ в A: «если "
         "$\\sim(Knk \\in Knk)$, то $Knk \\in Knk$; если $Knk \\in Knk$, то $\\sim(Knk \\in Knk)$». Незаконно, так как D*1 — определение с переменной, область значения "
         "которой — термины, не зависящие по значению от $nk$; сам $nk$ к ним не относится.", "С. 159–160.", "с. 159–160, гл. 10, § 8", "парадокс нормальных классов")
    hand(10, 8, 9, "Докажите, что из D1 § 8 гл. 10 нельзя вывести противоречие, присоединив $nk \\rightharpoonup Knk$.", "Следствия D1 касаются лишь терминов $a$, не зависящих "
         "от $nk$; $nk \\rightharpoonup Knk$ и вытекающее $Knk \\in Knk$ к ним не относятся, и из D1 не выводится $\\sim(Knk \\in Knk)$ (с. 160).", "С. 160.", "с. 160, гл. 10, § 8",
         "парадокс нормальных классов")
    hand(10, 8, 10, "Сопоставьте разбор парадокса класса нормальных классов (§ 8 гл. 10) с правилом для определений с переменными (§ 5 гл. 9). Распространите это "
         "правило на другой известный вам парадокс и оцените, устраняет ли оно его.", "Критерии: правило с. 147 сформулировано; показано, где в выводе парадокса "
         "на место переменной подставляется определяемый термин; оценка обоснована ссылками на книгу.", "С. 147, 158–160.", "с. 147, 158–160, гл. 9–10", "парадокс нормальных классов")
    hand(11, 2, 8, "По образцу вывода T1 § 3 гл. 11 докажите в $S^e_n$: $E(abcd) \\vdash E(a)E(d)$.", "$E(((ab)c)d) \\vdash E((ab)c)E(d)$ [AVII.1]; $E((ab)c) \\vdash E(ab)E(c)$, "
         "$E(ab) \\vdash E(a)E(b)$ [AVII.1]; отбрасывание конъюнктов и объединение [$S^s$]; расстановка скобок — AI.4 гл. 9.", "С. 163–164.", "с. 163–164, гл. 11, § 2–3", "существование", "S^e_n")
    hand(11, 2, 9, "Докажите, что все аксиомные схемы AVII $S^e_n$ удовлетворяют условию: в заключение не входят термины, отсутствующие в посылке. Почему это не так для AV и AVIII.1?",
         "AVII.1–6: в обеих частях — $a$, $b$ (или $x$, $y$). AV — формулы вида $\\vdash z$ (посылки нет); AVIII.1 $x \\vdash E(\\downarrow x)$ вводит предикат $E$, но "
         "высказывание $x$ сохраняется.", "С. 162–163.", "с. 162–163, гл. 11, § 2", "существование", "S^e_n")
    hand(11, 2, 10, "Исследуйте, какие из схем AI–AVIII $S^e_n$ при интерпретации § 6 зависят от п. 5 (неопределённость значения $ab$). Предложите изменение п. 5, при котором "
         "MT2 § 6 перестала бы выполняться, и объясните, почему книга его не принимает.", "Критерии: указаны схемы с $ab$ (AVII.1, AVII.3, AVII.5); показано, что "
         "при «$ab = 1$, если $a = b = 1$» $E(a)E(b) \\vdash E(ab)$ стала бы тавтологией; связь со смыслом термина $ab$ (с. 138).", "С. 138, 163, 166.",
         "с. 138, 163–166, гл. 9, 11", "существование, исследование", "S^e_n")
    hand(11, 4, 8, "Восстановите доказательство MT1 § 4 гл. 11 для случая 2 (с. 165): если $a^*$ — тавтология, то $\\vdash U(a)$ доказуема.", "Каноническая форма "
         "$a_1 \\vee \\ldots \\vee a_k$ тавтологии $a^*$ — тавтология; в общей теории дедукции доказуемы $a_1 \\vee \\ldots \\vee a_k \\vdash a_1 \\vee \\sim a_1$ и обратная; "
         "$a_1 \\vee \\sim a_1$ — тавтология; в системе доказуема $\\vdash U(\\downarrow (a_1 \\vee \\sim a_1))$, что и требовалось (с. 165).", "С. 165.",
         "с. 164–165, гл. 11, § 4", "универсальность", "S^e_n")
    hand(11, 4, 8, "Докажите по MT1 § 4 гл. 11, что T10 § 3 $\\vdash U(a \\vee \\sim a \\vee b)$ доказуема, а $\\vdash U(a \\vee b)$ — нет.", "$(a \\vee \\sim a \\vee b)^* = "
         "p \\vee \\sim p \\vee q$ — тавтология; $(a \\vee b)^* = p \\vee q$ — не тавтология (разным терминам — разные высказывания).", "С. 164–165.",
         "с. 164–165, гл. 11, § 3–4", "универсальность", "S^e_n")
    hand(11, 4, 9, "Докажите: если $\\vdash U(a)$ и $\\vdash U(b)$ доказуемы, то доказуема $\\vdash U(ab)$; обратно — тоже. Используйте MT1 § 4 и T3 § 3.", "По MT1 $a^*$ и $b^*$ — "
         "тавтологии, значит, и $a^*b^*$; это $(ab)^*$ — по MT1 $\\vdash U(ab)$. Обратно: T3 $U(ab) \\dashv\\vdash U(a)U(b)$.", "С. 164–165.", "с. 164–165, гл. 11, § 3–4", "универсальность", "S^e_n")
    hand(11, 6, 8, "Покажите по интерпретации § 6 гл. 11, что AI.1, AI.2 и AVII.2 — тавтологии.", "По п. 2 $E(a^1, \\ldots, a^n)$ равнозначна $E(a^1) \\cdot \\ldots \\cdot E(a^n)$ — "
         "AI.1, AI.2 связывают равнозначные высказывания; по п. 4 $E(a \\vee b)$ равнозначна $E(a) \\vee E(b)$ — AVII.2.", "С. 165–166.", "с. 165–166, гл. 11, § 6",
         "существование, интерпретация")
    hand(11, 6, 9, "Докажите MT1 § 6 гл. 11 для схем AVII.1 и AVII.2.", "AVII.1: если $E(ab) = 1$, то по п. 10 $ab = 1$, по п. 5 $a = b = 1$, и $E(a) = E(b) = 1$. AVII.2: по п. 4 "
         "$E(a \\vee b)$ равнозначна $E(a) \\vee E(b)$.", "С. 165–166.", "с. 165–166, гл. 11, § 6", "существование, интерпретация")
    hand(11, 7, 8, "Выведите в $S^e_c$ формулу $U(a) \\vdash E(a)\\sim E(\\sim a)$ и сравните с T15 § 3 ($S^e_n$).", "$U(a) \\vdash E(a)$ [AIV*.3]; $U(a) \\vdash \\sim E(\\sim a)$ [AIV*.1]; "
         "объединение. В $S^e_n$ — T15 $U(a) \\vdash E(a)\\urcorner E(\\sim a)$ с внутренним отрицанием.", "С. 164, 167.", "с. 164, 167, гл. 11, § 3, 7", "существование, классический случай", "S^e_c")
    hand(11, 7, 9, "Докажите, что в $S^e_c$ $U(a)$ и $\\sim E(\\sim a)$ равнозначны, и выведите отсюда $\\vdash U(a \\vee \\sim a)$, считая доказуемой $\\vdash \\sim E(\\sim aa)$ (AV в $S^e_c$).",
         "Схемы AIV*.1, AIV*.2 дают равнозначность. $\\vdash \\sim E(\\sim aa)$; $\\sim aa$ равнозначно $\\sim(a \\vee \\sim a)$; по AIV*.2 — $\\vdash U(a \\vee \\sim a)$.", "С. 167.",
         "с. 167, гл. 11, § 7", "существование, классический случай", "S^e_c")
    hand(12, 2, 8, "Выведите в $S^{m1}_n$: $N(\\downarrow x)N(\\downarrow y) \\vdash M(\\downarrow (xy))$.", "AIV.3: $N(\\downarrow x)N(\\downarrow y) \\vdash N(\\downarrow (xy))$; "
         "AI.1: $N(\\downarrow (xy)) \\vdash xy$; AI.2: $xy \\vdash M(\\downarrow (xy))$; транзитивность.", "С. 168–169.", "с. 168–169, гл. 12, § 2", "модальность", "S^m1_n")
    hand(12, 2, 9, "Докажите: если $x \\dashv\\vdash y$ доказуемы в $S^s$, то в $S^{m1}_n$ доказуемы $N(\\downarrow x) \\dashv\\vdash N(\\downarrow y)$ и $C(\\downarrow x) \\dashv\\vdash C(\\downarrow y)$.",
         "Для $N$ — R1 в обе стороны. Для $C$: $C(\\downarrow x) \\vdash M(\\downarrow x)M(\\downarrow \\sim x)$ [AIII.1]; R2 из $x \\vdash y$ и из $\\sim x \\vdash \\sim y$ (контрапозиция в $S^s$ при "
         "равных множествах, гл. 5, § 2); AIII.2 — $C(\\downarrow y)$; обратно аналогично.", "С. 169–170.", "с. 169–170, гл. 12, § 2", "модальность", "S^m1_n")
    hand(12, 2, 10, "Исследуйте, какие схемы $S^{m1}_n$ зависимы от других (например, AII.4 от AII.3 и правил). Составьте список предположительно независимых схем.",
         "Критерии: хотя бы два вывода одних схем из других; обоснование независимости хотя бы одной схемы по интерпретации § 5.", "С. 168–173.",
         "с. 168–173, гл. 12, § 2, 5", "модальность, исследование", "S^m1_n")
    hand(12, 7, 8, "Выведите в $S^{m0}_n$: $N(\\downarrow x) \\vdash N(\\downarrow (N(\\downarrow x)))M(\\downarrow x)$.", "A14: $N(\\downarrow x) \\vdash N(\\downarrow (N(\\downarrow x)))$; A1: "
         "$N(\\downarrow x) \\vdash x$; A2: $x \\vdash M(\\downarrow x)$; транзитивность и объединение заключений ($S^s$).", "С. 174.", "с. 174, гл. 12, § 7", "основная модальная логика", "S^m0_n")
    hand(12, 8, 8, "Покажите по интерпретации § 5 гл. 12 (п. 1), что T1 § 8 $\\vdash M(\\downarrow x) \\vee M(\\downarrow \\sim x)$ — тавтология.",
         "Если $x$ может принять значение 1, то по п. 1 $M(\\downarrow x) = 1$. Если не может, то $x$ имеет значение 0, $\\sim x$ — значение 1, и по п. 1 (для $\\sim x$) "
         "$M(\\downarrow \\sim x) = 1$. В обоих случаях дизъюнкция истинна.", "С. 172, 175.", "с. 172, 175, гл. 12, § 5, 8", "логические модальности")
    hand(12, 8, 9, "Докажите: если $\\vdash x$ доказуема, то доказуемы $\\vdash LN(\\downarrow x)$, $\\vdash N(\\downarrow x)$ и $\\vdash \\sim LM(\\downarrow \\sim x)$.", "R*1; A*3; A*1 "
         "и транзитивность (правило: из $\\vdash u$ и $u \\vdash w$ — $\\vdash w$).", "С. 175.", "с. 175, гл. 12, § 8", "логические модальности")
    hand(12, 8, 10, "Исследуйте, чем логические модальности ($LM$, $LN$, $LC$) отличаются от модальностей $M$, $N$, $C$ по схемам A*3, A*4. Приведите примеры из математики и "
         "физики.", "Критерии: $LN$ сильнее $N$, $LM$ слабее $M$; примеры обоснованы; ссылки на с. 175.", "С. 175.", "с. 175, гл. 12, § 8", "логические модальности")
    hand(17, 10, 8, "Докажите в $S^s_p$: $(a \\leftarrow b) \\vdash \\sim(a \\urcorner\\!\\leftarrow b)\\sim(a? \\leftarrow b)$ и выведите из неё T4, T5.", "Это A1 $S^s_p$; T4, T5 — отбрасывание "
         "конъюнкта ($S^s$).", "Гл. 8, § 1.", "гл. 1–8", "смешанный, предикация")
    hand(17, 11, 8, "Докажите по MT1–MT3 § 2 гл. 9: $\\vdash (a \\vee b)c \\rightharpoonup ac$ доказуема в $S^1_t$.", "$ac \\supset (a \\vee b)c$ — тавтология, общие термины $a$, $c$ есть "
         "— доказуема (MT3).", "Гл. 9, § 2.", "гл. 1–9", "смешанный, термины")
    hand(17, 11, 9, "Докажите: если $\\vdash (a \\rightharpoonup b)$ и $\\vdash (b \\rightharpoonup c)$ доказуемы в $S^1_t$, то доказуема $\\vdash (a \\rightharpoonup c)$.",
         "AI.7: $\\vdash (a \\rightharpoonup b)(b \\rightharpoonup c) \\to (a \\rightharpoonup c)$; из двух доказуемых формул — $\\vdash (a \\rightharpoonup b)(b \\rightharpoonup c)$; по MT3 § 8 гл. 6 "
         "(из $\\vdash (u \\to w)$ и $\\vdash u$ — $\\vdash w$) получаем $\\vdash (a \\rightharpoonup c)$.", "Гл. 6, § 8; гл. 9, § 2.", "гл. 1–9", "смешанный, термины")


# ================================================================ смешанные
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
                c = c.replace("type: C\n", "type: S\n", 1).replace("type: D\n", "type: S\n", 1)
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def main():
    cards = []
    cards += build(10, 8, [0, 1, 1, 0, 1, 1, 2], 2, m1008)
    cards += build(10, 9, [2, 3, 3, 1, 0, 1, 0], 2, m1009)
    cards += build(11, 1, [2, 3, 3, 1, 0, 1, 0], 2, m1101)
    cards += build(11, 2, [2, 6, 8, 9, 16, 13, 6], 16, m1102)
    cards += build(11, 3, [0, 1, 1, 2, 3, 2, 1], 2, m1103)
    cards += build(11, 4, [0, 0, 1, 2, 1, 2, 1], 2, m1104)
    cards += build(11, 5, [0, 1, 1, 2, 3, 2, 1], 2, m1105)
    cards += build(11, 6, [1, 3, 6, 2, 2, 3, 2], 5, m1106)
    cards += build(11, 7, [1, 3, 4, 5, 8, 6, 3], 8, m1107)
    cards += build(12, 1, [2, 3, 3, 1, 0, 1, 0], 2, m1201)
    cards += build(12, 2, [2, 6, 8, 9, 16, 13, 6], 16, m1202)
    cards += build(12, 3, [0, 1, 1, 2, 3, 2, 1], 2, m1203)
    cards += build(12, 4, [2, 3, 3, 1, 0, 1, 0], 2, m1204)
    cards += build(12, 5, [1, 2, 3, 1, 1, 1, 1], 2, m1205)
    cards += build(12, 6, [0, 1, 1, 2, 3, 2, 1], 2, m1206)
    cards += build(12, 7, [1, 2, 3, 3, 5, 4, 2], 5, m1207)
    cards += build(12, 8, [1, 1, 1, 0, 1, 1, 2], 2, m1208)
    cards += build(12, 9, [0, 1, 1, 2, 3, 2, 1], 2, m1209)
    cards += build(12, 10, [0, 1, 1, 2, 3, 2, 1], 2, m1210)
    cards += build(12, 11, [0, 1], 0, m1211)
    m8 = [G7.p_taut_card, lambda l: G7.prov706(l), lambda l: G7.decide_card(l), lambda l: G7.tp5_rec(l), lambda l: G7.p_deriv(l)]
    e8 = [lambda l: G7.e801(l), lambda l: G7.e801c(l), G7.e708, G7.e706]
    cards += mixed(10, [0, 0, 0, 1, 3, 4, 2], 4, "гл. 1–8", m8, e8)
    m9 = [lambda l: G8.inc_card(l), lambda l: G8.tilde_card(l, "C"), lambda l: G8.ai3_nat(l), lambda l: G8.t9_rec(l), lambda l: G8.d1_card(l, "C"), G7.p_taut_card]
    e9 = [lambda l: G8.ai3_e(l), lambda l: G8.m902(l, True, 0), lambda l: G8.m903(l, True, 1), lambda l: G7.e801c(l)]
    cards += mixed(11, [0, 2, 3, 1, 4, 5, 3], 5, "гл. 1–9", m9, e9)
    m10 = [lambda l: G8.kval_card(l), lambda l: G8.code_card(l), lambda l: G8.syl_status(l), lambda l: G8.a14_card(l, "C"), lambda l: G8.sub_ak(l, "C"),
           lambda l: G8.inc_card(l), lambda l: G8.modus_rec(l)]
    e10 = [lambda l: G8.kval_e(l), lambda l: G8.syl_e(l), lambda l: G8.m1003(l, True, 0), lambda l: G8.m1002(l, True, 1)]
    cards += mixed(12, [0, 3, 5, 2, 7, 8, 4], 8, "гл. 1–10", m10, e10)
    hand_cards()
    cards += H
    (ROOT / "drafts" / "71-80-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(cards), "из них ручных", len(H))


if __name__ == "__main__":
    main()
