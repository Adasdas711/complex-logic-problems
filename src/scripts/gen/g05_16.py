#!/usr/bin/env python3
"""Серии для занятий 31–40: гл. 5, § 5–9; раздел 16 (координаты высказываний); гл. 6, § 1–2; смешанные 17.04–17.06.
Пишет drafts/31-40-gen.md.
"""
import importlib.util
import random
import re
import sys
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import coords as K  # noqa: E402
import systems as SY  # noqa: E402
from s1 import C, D, N, V, atoms  # noqa: E402
from s1w import W, tex  # noqa: E402

spec = importlib.util.spec_from_file_location("g25", ROOT / "scripts" / "gen" / "g02_05.py")
G = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G)
G.rnd.seed(3140)
rnd = random.Random(3141)
L = "абвгдежз"
SEEN = set()
DIAG = {}
USED = set()



def tex_map(s, p):
    """Заменить однобуквенные лексемы по словарю p; команды LaTeX и индексы (^, _) не трогаются."""
    s = re.sub(r"(?<![a-z])(sc|pc|nk)(?![a-z])", lambda q: "\\" + {"sc": "SCname", "pc": "PCname", "nk": "NKname"}[q.group(1)], s)
    toks = re.findall(r"\\[A-Za-z]+|.", s, flags=re.S)
    out, depth, script = [], 0, False
    for i, t in enumerate(toks):
        prev = toks[i - 1] if i else ""
        if t == "{" and (prev in "^_" or depth):
            depth += 1
        elif t == "}" and depth:
            depth -= 1
        elif depth == 0 and prev not in ("^", "_"):
            t = p.get(t, t)
        out.append(t)
    return "".join(out).replace("\\SCname", "sc").replace("\\PCname", "pc").replace("\\NKname", "nk")

def condtext(c):
    return c[c.index("## Условие"):c.index("## Ответ")]


def fresh_card(fn, tries=40):
    c = None
    for _ in range(tries):
        c = fn()
        if c is None:
            continue
        if condtext(c) not in USED:
            break
    USED.add(condtext(c))
    return c


def card(ch, sec, lvl, typ, step, form, ans, tags, body, src, system=None):
    sysl = f'system: "{system}"\n' if system else ""
    return (f"---\nchapter: {ch}\nsection: {sec}\nlevel: {lvl}\ntype: {typ}\nstep: {step}\ncondition: def\nform: {form}\n"
            f"answer: {ans}\nsource: \"{src}\"\n{sysl}generated: true\ntags: [{tags}]\n---\n\n{body}\n")


def uniq(gen):
    for _ in range(400):
        r = gen()
        if r is not None and repr(r) not in SEEN:
            SEEN.add(repr(r))
            return r
    for _ in range(4000):
        r = gen()
        if r is not None:
            return r
    raise RuntimeError


# =============================== РАЗДЕЛ 16 ===============================
LOC = [("окно открыто", "окно закрыто", "t"), ("идёт дождь", "дождя нет", "ts"),
       ("магазин работает", "магазин не работает", "ts"), ("дверь заперта", "дверь не заперта", "t"),
       ("в комнате горит свет", "в комнате нет света", "t"), ("река покрыта льдом", "река не покрыта льдом", "ts"),
       ("поезд стоит на станции", "поезда на станции нет", "t"), ("температура воздуха выше нуля",
                                                                 "температура воздуха не выше нуля", "ts"),
       ("улица освещена", "улица не освещена", "ts"), ("в зале шумно", "в зале тихо", "t")]
UNI = ["все чётные числа делятся на два без остатка", "электрон заряжен отрицательно", "5 больше 3", "человек смертен",
       "квадрат имеет четыре стороны", "7 — простое число", "сумма 2 и 2 равна 4", "треугольник имеет три угла"]
UNI_BOOK = UNI[:4]
TIMES = ["утром", "вечером", "в понедельник", "в субботу", "в 1990 году", "в 2020 году", "в 9 часов", "в полдень"]
PLACES = ["в Москве", "в Омске", "в Лондоне", "в Казани", "на севере города", "на юге города"]
S16 = {1: "Очерки, с. 352–353; LSR, с. 496", 2: "Очерки, с. 372–373; LSR, с. 496–497", 3: "Очерки, с. 373–374",
       4: "Очерки, с. 374–375", 5: "Очерки, с. 375", 6: "Очерки, с. 352–353, 372–375; LSR, с. 496–497"}


def coord(kinds, k=2):
    kind = rnd.choice(kinds)
    return kind, rnd.sample(TIMES if kind == "t" else PLACES, k)


def cap(s):
    return s[0].upper() + s[1:]


def at(s, c):
    return f"{c} {s}"


def err_card(sec, lvl, kind=None):
    """Рассуждения с неучтёнными координатами (и верные — для контроля)."""
    kind = kind or rnd.choice("abcdefgij")
    p, n, ks = rnd.choice(LOC)
    _, (c1, c2) = coord(ks)
    p2, n2, _ = rnd.choice([l for l in LOC if l[0] != p])
    if kind == "a":
        txt = f"«{cap(at(p, c1))}» и «{at(n, c2)}». Эти утверждения противоречат друг другу, значит, одно из них ложно."
        ans = "Ошибка: $[xα^1] \\wedge \\sim[xα^2]$ при разных координатах не противоречие."
        sol = "Очерки, с. 374: утверждения вида $[xv^1] \\wedge \\sim[xv^2]$ не являются противоречиями."
    elif kind == "b":
        txt = f"«{cap(at(p, c1))} или {at(n, c2)}» — истинно по закону исключённого третьего."
        ans = "Ошибка: $[xα^1] \\vee \\sim[xα^2]$ при разных координатах не тавтология."
        sol = "Очерки, с. 374: утверждения вида $[xv^1] \\vee \\sim[xv^2]$ не являются тавтологиями."
    elif kind == "c":
        txt = f"Известно: {at(p, c1)}; {at(p2, c2)}. Значит, {p} и {p2} одновременно."
        ans = "Ошибка: конъюнкцию можно признать истинной лишь при тождестве координат её членов."
        sol = ("Очерки, с. 353: «мы имеем право признать истинным $x \\wedge y$ лишь при условии тождества координат для $x$, $y$ "
               "и $x \\wedge y$». По V.1 (с. 374) из $[xα]$ и $[yα]$ получается $[(x \\wedge y)α]$ — только при одной $α$.")
    elif kind == "d":
        txt = f"{cap(at(p, c1))}. Следовательно, {at(p, c2)}."
        ans = "Ошибка: $Aα \\vdash Aβ$ — не логический закон."
        sol = "LSR, с. 496–497: правило $A \\vdash A$ предполагает тождество координат ($Aα \\vdash Aα$), а $Aα \\vdash Aβ$ законом не является."
    elif kind == "e":
        txt = f"{cap(at(p, c1))}. Следовательно, {p} всегда (при любых координатах)."
        ans = "Ошибка: из $[xα]$ не следует $(\\forall v)[xv]$; следует лишь $(\\exists v)[xv]$."
        sol = "Очерки, с. 352, 374: высказывание локально — его значение меняется с координатами; ср. IV.1 (с. 374)."
    elif kind == "f":
        txt = f"{cap(p)}. Значит, это происходит {c1}."
        ans = "Ошибка: между высказыванием и его координатами логической связи нет."
        sol = "Очерки, с. 353, 372–373; LSR, с. 496–497: не предполагается ни $α \\rightarrow A$, ни $\\sim α \\rightarrow \\sim A$."
    elif kind == "g":
        txt = f"О высказывании «{p}» нельзя утверждать, что оно локально. Значит, оно универсально."
        ans = "Ошибка: из отрицания локальности универсальность не следует — возможен случай неопределённости."
        sol = "Очерки, с. 374–375: $\\sim((\\exists v)x \\wedge (\\exists v)\\sim x)$ равносильно дизъюнкции универсальности и неопределённости."
    elif kind == "i":
        u = rnd.choice(UNI)
        txt = f"{cap(at(u, c1))}. Следовательно, {at(u, c2)}."
        ans = "Ошибки нет: высказывание универсально — его значение не меняется с координатами."
        sol = "Очерки, с. 353: для универсальных высказываний ссылки на координаты можно опускать."
    else:  # j — одинаковые координаты
        txt = f"{cap(at(p, c1))}; {at(p2, c1)}. Значит, {c1} {p} и {p2}."
        ans = "Ошибки нет: координаты одинаковы, конъюнкция законна."
        sol = "Очерки, с. 353; схема V.1 (с. 374): $[xα] \\wedge [yα] \\vdash [(x \\wedge y)α]$."
    body = (f"## Условие\n\nНайдите ошибку в рассуждении или укажите, что её нет.\n\n{txt}\n\n## Ответ\n\n{ans}\n\n"
            f"## Решение\n\n{sol}")
    return card(16, sec, lvl, "E", "iso", "nat", "short", "координаты, диагностика", body, S16[sec])


def multi_err(sec, lvl, n):
    kinds = rnd.sample("abcdefij", n)
    parts = []
    for k in kinds:
        c = err_card(sec, lvl, k)
        t = c[c.index("## Условие") + 12:]
        txt = t.split("\n\n")[1]
        ans = t[t.index("## Ответ") + 10:t.index("## Решение")].strip()
        sol = t[t.index("## Решение") + 12:].strip()
        parts.append((txt, ans, sol))
    body = ("## Условие\n\nВ каких рассуждениях есть ошибка, связанная с координатами? Назовите правило для каждого.\n\n" +
            "\n".join(f"{L[i]}) {t}" for i, (t, _, _) in enumerate(parts)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("нет ошибки" if a.startswith("Ошибки нет") else "ошибка")
                      for i, (_, a, _) in enumerate(parts)) + "\n\n## Решение\n\n" +
            "\n".join(f"{L[i]}) {a} {s}" for i, (_, a, s) in enumerate(parts)))
    return card(16, sec, lvl, "E", "open", "nat", "short", "координаты, диагностика", body, S16[sec])


def classify_card(sec, lvl, typ="R"):
    its = [(u, "универсальное") for u in rnd.sample(UNI, 2)] + [(p, "локальное") for p, _, _ in rnd.sample(LOC, 3)]
    rnd.shuffle(its)
    body = ("## Условие\n\nЛокальное или универсальное высказывание (Очерки, § 17)?\n\n" +
            "\n".join(f"{L[i]}) «{cap(s)}»" for i, (s, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {k}" for i, (_, k) in enumerate(its)) +
            "\n\n## Решение\n\nОчерки, с. 352–353; LSR, D1, с. 496: локальные высказывания меняют значение истинности с "
            "изменением координат (места, времени, условий), универсальные — нет. Примеры универсальных из книги: «Все чётные "
            "числа делятся на два без остатка», «Электрон заряжен отрицательно», «5 > 3», «Человек смертен».")
    return card(16, sec, lvl, typ, "iso", "nat", "short", "координаты, локальность", body, S16[1])


def coord_find(sec, lvl):
    p, _, ks = rnd.choice([l for l in LOC if "s" in l[2]])
    t = rnd.choice(TIMES)
    s = rnd.choice(PLACES)
    body = (f"## Условие\n\nВыделите координаты высказывания «{cap(s)} {t} {p}» и запишите его в виде $[xα]$, где $x$ — «{p}».\n\n"
            f"## Ответ\n\nМесто — «{s}», время — «{t}»; $[[xs]t]$ (или $[[xt]s]$), где $s$ — «{s}», $t$ — «{t}».\n\n"
            "## Решение\n\nОчерки, с. 352: координаты — место, время, условия; § 28 (с. 372–373): «$x$ в $α$» — $[xα]$; "
            "порядок пространственной и временной координат безразличен (II.3, с. 373).")
    return card(16, sec, lvl, "D", "iso", "nat", "short", "координаты, запись", body, S16[2])


def gen_f(depth):
    if depth == 0 or rnd.random() < 0.25:
        return ("at", rnd.choice("xyz"))
    h = rnd.choice(["and", "or", "imp", "neg"])
    if h == "neg":
        return ("neg", gen_f(depth - 1))
    return (h, gen_f(depth - 1), gen_f(depth - 1))


def push_card(sec, lvl, typ="D", step="iso"):
    def g():
        f = gen_f(2)
        if f[0] == "at":
            return None
        k = rnd.choice(["t1", "s1", "v", "u1"])
        if rnd.random() < 0.4:
            k2 = rnd.choice(["t2", "s2"]) if k[0] in "ts" else "v2"
            f = ("co", ("co", f, k), k2 if k[0] == k2[0] or rnd.random() < 0.5 else k2)
        else:
            f = ("co", f, k)
        return f
    f = uniq(g)
    r, used = K.normal(f)
    body = (f"## Условие\n\nБуквы $x, y, z$ — высказывания; $t^i$, $s^i$, $u^i$, $v^i$ — переменные для координат (Очерки, "
            f"с. 373). Перенесите координаты к элементарным высказываниям и упростите по схемам групп V и II:\n\n"
            f"${K.tex(f)}$\n\n## Ответ\n\n${K.tex(r)}$\n\n## Решение\n\nИспользованы схемы: " + ", ".join(used) +
            " (с. 373–374). " + "; ".join(f"{a}: ${K.AXIOMS[a]}$" for a in used) + ".")
    return card(16, sec, lvl, typ, step, "sym", "short", "координаты, схемы V, II", body, S16[3])


def which_axiom(sec, lvl):
    names = rnd.sample(["II.1", "II.2", "II.3", "II.4", "V.1", "V.2", "V.3", "V.4", "IV.1", "IV.2", "VI.1", "I.1"], 5)
    sub = {"x": rnd.choice(["p", "q", "r"])}
    ren = lambda f: tex_map(f, sub)
    body = (f"## Условие\n\nБуквы ${sub['x']}, y$ — высказывания; $s, t, u, v$ (с индексами или без) — переменные для координат; "
            "$a$ — термин. Каким аксиомным схемам ТЛК (Очерки, с. 373–374) соответствуют формулы?\n\n" +
            "\n".join(f"{L[i]}) ${ren(K.AXIOMS[n])}$" for i, n in enumerate(names)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[i]}) {n}" for i, n in enumerate(names)) + "\n\n## Решение\n\nС. 373–374.")
    return card(16, sec, lvl, "R", "iso", "sym", "short", "координаты, аксиомы", body, S16[3])


WRONG_AX = [("[[xt^1]t^2] \\dashv\\vdash [xt^2]", "II.1", "сохраняется внутренняя координата: $[[xt^1]t^2] \\dashv\\vdash [xt^1]$"),
            ("[(\\sim x)v] \\dashv\\vdash [xv]", "V.4", "$[(\\sim x)v] \\dashv\\vdash \\sim[xv]$"),
            ("[(x \\wedge y)v] \\dashv\\vdash [xv] \\vee [yv]", "V.1", "$[(x \\wedge y)v] \\dashv\\vdash [xv] \\wedge [yv]$"),
            ("[xv] \\vdash (\\forall v)[xv]", "IV", "по IV.1 из $(\\exists a)x$ следует лишь $(\\exists v)[xv]$; обобщение по координатам не допускается"),
            ("[xu] \\vdash u \\rightarrow x", "VI.1", "VI.1 идёт в обратную сторону: $(u \\rightarrow x) \\vdash [xu]$; из $[xy]$ не следует $y \\rightarrow x$ (с. 373)"),
            ("[[xs^1]s^2] \\dashv\\vdash [xs^2]", "II.2", "сохраняется внутренняя координата: $[[xs^1]s^2] \\dashv\\vdash [xs^1]$"),
            ("[(x \\rightarrow y)v] \\dashv\\vdash [xv] \\rightarrow y", "V.3", "координата переносится на обе части: $[xv] \\rightarrow [yv]$")]


def wrong_ax(sec, lvl):
    f, n, right = rnd.choice(WRONG_AX)
    body = (f"## Условие\n\nСтудент ссылается на схему {n} ТЛК: ${f}$. Найдите ошибку.\n\n## Ответ\n\nНеверно: {right}.\n\n"
            "## Решение\n\nОчерки, с. 373–374.")
    return card(16, sec, lvl, "E", "iso", "sym", "short", "координаты, аксиомы, диагностика", body, S16[3])


def wf_card(sec, lvl):
    its = [("[xt]", True, "высказывание: $x$ в $t$"), ("[at]", True, "термин (терминная форма $[ak]$)"),
           ("[xy]", True, "высказывание «$x$ при условии $y$»"), ("[ax]", True, "термин «$a$ при условии $x$»"),
           ("[x a]", False, "$a$ — термин, а условие должно быть высказыванием; координаты — переменные $s, t, u, v$"),
           ("[[xs]t]", True, "высказывание с двумя координатами"), ("[\\vdash x\\,t]", False, "в § 28 координаты приписываются высказываниям и терминам, а не формулам следования; ср. I.3")]
    pick = rnd.sample(its[:6], 4)
    body = ("## Условие\n\nБуква $x$ — высказывание (пропозициональная формула), $y$ — высказывание, $a$ — термин, $s, t$ — "
            "переменные для координат. Что представляет собой каждое выражение по § 28 (Очерки, с. 372–373)?\n\n" +
            "\n".join(f"{L[i]}) ${e}$" for i, (e, _, _) in enumerate(pick)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {d}" for i, (_, _, d) in enumerate(pick)) +
            "\n\n## Решение\n\nС. 372–373: «$x$ в $α$» — $[xα]$; «$x$ при $y$» — $[xy]$, где $y$ — высказывание; дополнение к "
            "определению терминной формы: $[ak]$.")
    return card(16, sec, lvl, "R" if lvl == 1 else "D", "iso", "sym", "short", "координаты, язык", body, S16[2])


def kind_var(sec, lvl):
    vs = rnd.sample([("s^1", "пространственная"), ("t^2", "временная"), ("u", "условная"), ("v^1", "любые координаты и их комбинации"),
                     ("t", "временная"), ("s", "пространственная"), ("u^2", "условная")], 4)
    body = ("## Условие\n\nКакой вид координат обозначает каждая переменная алфавита ТЛК (Очерки, с. 373)?\n\n" +
            "\n".join(f"{L[i]}) ${v}$" for i, (v, _) in enumerate(vs)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {d}" for i, (_, d) in enumerate(vs)) + "\n\n## Решение\n\nС. 373, алфавит ТЛК, пп. 1–4.")
    return card(16, sec, lvl, "R", "iso", "sym", "short", "координаты, язык", body, S16[2])


def loc_def(sec, lvl, typ="D"):
    p, _, ks = rnd.choice(LOC)
    _, cs = coord(ks, 4)
    if rnd.random() < 0.6:
        vals = [rnd.choice("ИЛ") for _ in cs]
        if len(set(vals)) == 1:
            vals[0] = "Л" if vals[0] == "И" else "И"
        res = "локально"
        why = "$(\\exists v)x \\wedge (\\exists v)\\sim x$: есть координаты, где оно истинно, и где ложно"
    else:
        v = rnd.choice("ИЛ")
        vals = [v] * 4
        res = "универсально (на рассмотренных координатах)"
        why = "$(\\forall v)x \\vee (\\forall v)\\sim x$: значение одно и то же"
    tab = "\n".join(f"| {c} | {v} |" for c, v in zip(cs, vals))
    body = (f"## Условие\n\nВысказывание $x$ — «{p}». Его значения при разных координатах:\n\n| координаты | значение |\n|---|---|\n"
            f"{tab}\n\nЛокально оно или универсально по определениям Очерков (с. 374), если других координат нет?\n\n## Ответ\n\n"
            f"{cap(res)}.\n\n## Решение\n\nОпределение (с. 374): локально — {'' if res == 'локально' else 'нет; универсально — '}{why}.")
    return card(16, sec, lvl, typ, "iso", "sym", "short", "координаты, локальность", body, S16[4])


def contr_card(sec, lvl):
    p, _, ks = rnd.choice(LOC)
    its = [("[xv^1] \\wedge \\sim[xv^2]", "нет"), ("[xv] \\wedge \\sim[xv]", "да"), ("[Pv^1](a) \\wedge \\sim[Pv^2](a)", "нет"),
           ("(\\forall[av^1])x \\wedge \\sim(\\forall[av^2])x", "нет"), ("[xt] \\wedge [(\\sim x)t]", "да")]
    pick = rnd.sample(its, 4)
    body = ("## Условие\n\nКакие утверждения — противоречия (Очерки, с. 374)?\n\n" +
            "\n".join(f"{L[i]}) ${e}$" for i, (e, _) in enumerate(pick)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {a}" for i, (_, a) in enumerate(pick)) +
            "\n\n## Решение\n\nС. 374: утверждения с разными координатами $v^1$, $v^2$ противоречиями не являются. При одной и "
            "той же координате — противоречие; $[(\\sim x)t] \\dashv\\vdash \\sim[xt]$ по V.4.")
    return card(16, sec, lvl, "C", "iso", "sym", "short", "координаты, противоречия", body, S16[3])


def taut_card16(sec, lvl):
    its = [("[xv^1] \\vee \\sim[xv^2]", "нет"), ("[xv] \\vee \\sim[xv]", "да"), ("[Pv^1](a) \\vee \\sim[Pv^2](a)", "нет"),
           ("(\\forall[av^1])x \\vee \\sim(\\forall[av^2])x", "нет"), ("[xt] \\vee [(\\sim x)t]", "да")]
    pick = rnd.sample(its, 4)
    body = ("## Условие\n\nКакие утверждения — тавтологии (Очерки, с. 374)?\n\n" +
            "\n".join(f"{L[i]}) ${e}$" for i, (e, _) in enumerate(pick)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {a}" for i, (_, a) in enumerate(pick)) +
            "\n\n## Решение\n\nС. 374: при разных координатах — не тавтологии; при одинаковых — закон исключённого третьего; "
            "V.4.")
    return card(16, sec, lvl, "C", "iso", "sym", "short", "координаты, тавтологии", body, S16[3])


def cond_card(sec, lvl, typ="C"):
    cases = [("$u^2$ совпадает с $u^1$", True), ("из $u^1$ следует $u^2$", True), ("$u^1$ и $u^2$ логически независимы", False),
             ("из $u^2$ следует $u^1$ (но не наоборот)", False)]
    pick = rnd.sample(cases, 3)
    body = ("## Условие\n\nПравило $[x(u^1 \\wedge u^2)] \\dashv\\vdash [xu^1]$ правомерно не всегда (Очерки, с. 375). Правомерно ли "
            "оно в каждом случае?\n\n" + "\n".join(f"{L[i]}) {c}" for i, (c, _) in enumerate(pick)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if ok else "нет, в общем случае") for i, (_, ok) in enumerate(pick)) +
            "\n\n## Решение\n\nС. 375: «если $u^2$ есть $u^1$ или из $u^1$ следует $u^2$, то оно правильно». В остальных случаях "
            "условие $u^1 \\wedge u^2$ сильнее $u^1$. Правило $[xu^1u^2] \\dashv\\vdash [xu^1]$ (вложенные условия) имеет силу без "
            "исключения.")
    return card(16, sec, lvl, typ, "iso", "sym", "short", "координаты, условия", body, S16[5])


COND_NL = [("вода кипит при 100 °C", "при нормальном давлении", "на уровне моря"),
           ("металл расширяется", "при нагревании", "в лаборатории"),
           ("растение цветёт", "при достаточном освещении", "весной"),
           ("реакция идёт быстро", "в присутствии катализатора", "при комнатной температуре")]


def cond_nl(sec, lvl, wrong=True):
    x, u1, u2 = rnd.choice(COND_NL)
    if wrong:
        txt = (f"«{cap(x)} {u1} и {u2}». Следовательно, «{x} {u1}» — ведь второе условие можно отбросить.")
        ans = ("Ошибка: смешаны правила. $[xu^1u^2] \\dashv\\vdash [xu^1]$ верно для вложенных условий, а "
               "$[x(u^1 \\wedge u^2)] \\dashv\\vdash [xu^1]$ в общем случае неправомерно: при одном $u^1$ результат может не иметь места.")
        typ = "E"
    else:
        txt = (f"«{cap(u1)} верно: {x} {u2}». Следовательно, «{cap(x)} {u2} {u1}».")
        ans = "Ошибки нет: это перестановка формулировки, условие сохранено."
        typ = "E"
    body = (f"## Условие\n\nНайдите ошибку в рассуждении или укажите, что её нет.\n\n{txt}\n\n## Ответ\n\n{ans}\n\n## Решение\n\n"
            "Очерки, с. 375.")
    return card(16, sec, lvl, typ, "vary", "nat", "short", "координаты, условия, диагностика", body, S16[5])


def transfer16(sec, lvl):
    p, n, ks = rnd.choice(LOC)
    _, (c1, c2) = coord(ks)
    body = (f"## Условие\n\nВ классической логике высказываний $x \\wedge \\sim x$ — противоречие, $x \\vee \\sim x$ — тавтология. "
            f"Пусть $x$ — «{p}». Что можно сказать о «{c1} {p}, а {c2} {n}» и «{c1} {p} или {c2} {n}» в ТЛК? Почему "
            "классический результат не переносится?\n\n## Ответ\n\nПервое — не противоречие, второе — не тавтология: это "
            "$[xα^1] \\wedge \\sim[xα^2]$ и $[xα^1] \\vee \\sim[xα^2]$ при разных координатах.\n\n## Решение\n\nОчерки, с. 374. "
            "Классические законы относятся к высказываниям с тождественными координатами (LSR, с. 496–497).")
    return card(16, sec, lvl, "S", "transfer", "nat", "short", "координаты, классическая логика", body, S16[6])


DEFS = [("локально", "$(\\exists v)x \\wedge (\\exists v)\\sim x$"), ("универсально", "$(\\forall v)x \\vee (\\forall v)\\sim x$"),
        ("не локально", "$\\sim((\\exists v)x \\wedge (\\exists v)\\sim x)$"), ("не универсально", "$\\sim((\\forall v)x \\vee (\\forall v)\\sim x)$"),
        ("о нём нельзя сказать ни что оно локально, ни что универсально",
         "$((?\\forall v)x \\vee (?\\forall v)\\sim x) \\wedge ((?\\exists v)x \\wedge (?\\exists v)\\sim x)$")]


def def_formula(sec, lvl):
    w, f = rnd.choice(DEFS)
    body = (f"## Условие\n\nЗапишите по определениям Очерков (с. 374–375) формулу, выражающую, что высказывание $x$ {w}.\n\n"
            f"## Ответ\n\n{f}\n\n## Решение\n\nС. 374–375.")
    return card(16, sec, lvl, "D", "iso", "sym", "short", "координаты, локальность", body, S16[4])


def neither_card(sec, lvl):
    if rnd.random() < 0.5:
        q, f = ("не локально, то оно универсально", "$\\sim((\\exists v)x \\wedge (\\exists v)\\sim x) \\dashv\\vdash ((\\forall v)x \\vee "
                "(\\forall v)\\sim x) \\vee ((?\\forall v)x \\vee (?\\forall v)\\sim x)$")
    else:
        q, f = ("не универсально, то оно локально", "$\\sim((\\forall v)x \\vee (\\forall v)\\sim x) \\dashv\\vdash ((\\exists v)x \\wedge "
                "(\\exists v)\\sim x) \\vee ((?\\exists v)x \\wedge (?\\exists v)\\sim x)$")
    p = rnd.choice(LOC)[0]
    body = (f"## Условие\n\nСтудент: «Если высказывание «{p}» {q}». Опровергните, сославшись на формулы Очерков (с. 374–375).\n\n"
            f"## Ответ\n\nНеверно: {f}; возможен случай неопределённости.\n\n## Решение\n\nС. 374–375: для эмпирических наук "
            "сохраняется неопределённость, исключаемая для наук дедуктивных.")
    return card(16, sec, lvl, "E", "open", "sym", "short", "координаты, локальность, диагностика", body, S16[4])


def sec16(sec, levels, diag):
    out, nd = [], 0
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            if lvl >= 8:
                continue
            want_d = nd < diag and (sec == 6 or (lvl >= 2 and (i + lvl) % 3 == 0))
            c = fresh_card(lambda: make16(sec, lvl, want_d, i))
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def make16(sec, lvl, d, i):
    if sec == 6:
        if lvl <= 3:
            return err_card(6, lvl)
        if lvl in (4, 5):
            return multi_err(6, lvl, 3)
        return multi_err(6, lvl, 4)
    if d:
        f = {1: [lambda: err_card(sec, lvl)], 2: [lambda: err_card(sec, lvl, rnd.choice("fd"))],
             3: [lambda: wrong_ax(sec, lvl), lambda: err_card(sec, lvl, rnd.choice("ab"))],
             4: [lambda: neither_card(sec, lvl) if i % 4 == 0 else err_card(sec, lvl, rnd.choice("eg"))],
             5: [lambda: cond_nl(sec, lvl, i % 3 != 0)]}[sec]
        return rnd.choice(f)()
    if sec == 1:
        if lvl <= 2:
            return classify_card(1, lvl, "R" if lvl == 1 else "C") if i % 2 == 0 else coord_find(1, lvl)
        if lvl == 3:
            return classify_card(1, lvl, "C") if i % 2 else coord_find(1, lvl)
        if lvl == 7:
            return transfer16(1, lvl)
        return err_card(1, lvl, rnd.choice("ij")).replace("type: E", "type: C").replace(", диагностика", "")
    if sec == 2:
        if lvl == 1:
            return kind_var(2, 1) if i % 2 == 0 else wf_card(2, 1)
        if lvl <= 3:
            return wf_card(2, lvl) if i % 2 else coord_find(2, lvl)
        if lvl == 7:
            return transfer16(2, lvl)
        return push_card(2, lvl, "D")
    if sec == 3:
        if lvl == 1:
            return which_axiom(3, 1)
        if lvl == 2:
            return which_axiom(3, 2).replace("type: R", "type: D") if i % 2 else push_card(3, 2)
        if lvl == 3:
            return [contr_card, taut_card16, push_card][i % 3](3, 3)
        if lvl == 4:
            return push_card(3, 4, "D", "complete")
        if lvl in (5, 6):
            return push_card(3, lvl, "D", "vary") if i % 2 else transfer16(3, lvl).replace("type: S", "type: C")
        return transfer16(3, lvl)
    if sec == 4:
        if lvl == 1:
            return def_formula(4, 1).replace("type: D", "type: R")
        if lvl <= 4:
            return loc_def(4, lvl) if i % 3 else def_formula(4, lvl)
        if lvl == 7:
            return transfer16(4, lvl)
        return loc_def(4, lvl, "C")
    if sec == 5:
        if lvl == 7:
            return cond_card(5, lvl, "S")
        return cond_card(5, lvl) if i % 2 == 0 else cond_nl(5, lvl, False).replace("type: E", "type: C").replace(", диагностика", "")
    raise ValueError


# =============================== ГЛ. 5, § 5–9; ГЛ. 6 ===============================
NN = lambda: ("nn", "x")
QQ = lambda: ("qq", "x")
X = lambda: V("x")


def ntaut2(a, b=None, states="anq"):
    st = [{"x": s} for s in states]
    if b is None:
        return all(SY.nval(a, e) for e in st)
    return all(not SY.nval(a, e) or SY.nval(b, e) for e in st)


ntex = G.ntex
NC = G.NCONV


def n_formulas():
    base = [X(), NN(), QQ(), N(X()), N(NN()), N(QQ())]
    return base


def n_taut_card(lvl, typ="C"):
    def g():
        a, b = rnd.sample(n_formulas() + [W(X(), NN()), W(NN(), QQ()), C(N(X()), N(NN()))], 2)
        return (a, b)
    its = [uniq(g) for _ in range(4)]
    body = (f"## Условие\n\n{NC} Какие формулы — тавтологии в неклассическом случае (ровно одно из $x$, $\\urcorner x$, $?x$ "
            "истинно), а какие — в классическом, где принята $A^n7$ ($\\sim x \\vdash \\urcorner x$, с. 77)?\n\n" +
            "\n".join(f"{L[i]}) ${ntex(a)} \\vdash {ntex(b)}$" for i, (a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if ntaut2(a, b) else "нет") + " / " + ("да" if ntaut2(a, b, "an") else "нет")
                      for i, (a, b) in enumerate(its)) + " (неклассический / классический)" +
            "\n\n## Решение\n\nВ классическом случае по $A^n7$ высказывание $?x$ невозможно: остаются состояния «$x$» и «$\\urcorner x$» "
            "(с. 77). Перебираем состояния.")
    return card(5, 5, lvl, typ, "iso", "sym", "short", "неклассический случай", body, "с. 76–77, гл. 5, § 5", "S_n")


def n_e(lvl):
    pairs = [("\\sim\\urcorner x \\vdash x", "при истинном $?x$ посылка истинна, $x$ ложно (MT3, с. 76)"),
             ("\\vdash x \\vee \\urcorner x", "при истинном $?x$ ложны оба члена (MT3, с. 76)"),
             ("\\sim x \\vdash \\urcorner x", "это $A^n7$ — она принимается только для классического случая (с. 77)")]
    f, why = rnd.choice(pairs)
    body = (f"## Условие\n\n{NC} Студент считает ${f}$ теоремой $S_n^i$. Найдите ошибку.\n\n## Ответ\n\nНедоказуема: {why}.\n\n"
            "## Решение\n\nГл. 5, § 5 (с. 76–77).")
    return card(5, 5, lvl, "E", "open", "sym", "short", "неклассический случай, диагностика", body, "с. 76–77, гл. 5, § 5",
                "S_n")


def rel(a, b):
    if ntaut2(D(a, b)):
        return "классическое"
    if ntaut2(D(a, b, C(N(a), N(b)))):
        return "неклассическое"
    return "ни то ни другое"


def rel_card(lvl, typ="C"):
    pool = n_formulas()

    def g():
        a, b = rnd.sample(pool, 2)
        return (a, b)
    its = []
    while len(its) < 4:
        r = uniq(g)
        if r not in its:
            its.append(r)
    body = (f"## Условие\n\n{NC} По D2, D3 § 6 гл. 5 (с. 79): $x$ и $y$ в классическом отношении, если доказуема $\\vdash x : y$; в "
            "неклассическом — если доказуема $\\vdash x : y : \\sim x\\sim y$, но не $\\vdash x : y$. В каком отношении находятся "
            "пары?\n\n" + "\n".join(f"{L[i]}) ${ntex(a)}$ и ${ntex(b)}$" for i, (a, b) in enumerate(its)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[i]}) {rel(a, b)}" for i, (a, b) in enumerate(its)) +
            "\n\n## Решение\n\nПроверяем, истинно ли ровно одно из $x$, $y$ (или из $x$, $y$, $\\sim x\\sim y$) в каждом из трёх "
            "состояний: истинно $x$, истинно $\\urcorner x$, истинно $?x$. Ср. MT9 (с. 79): $x$ и $\\sim x$ — классическое, $x$ и "
            "$\\urcorner x$ — неклассическое.")
    return card(5, 6, lvl, typ, "iso", "sym", "short", "классические и неклассические отношения", body, "с. 77–79, гл. 5, § 6")


def poss_card(lvl):
    x, y = V("x"), V("y")
    cands = [C(x, y), C(N(x), y), C(x, N(y)), x, y, N(x), N(y), C(N(x), N(y))]
    its = rnd.sample(cands, 4)
    ok = lambda z: SY.provable("s", D(x, y, z), D(x, y)) or any(SY.provable("s", D(x, y, z), t) for t in [x, y, N(x), N(y)])
    body = ("## Условие\n\nБуквы $x, y$ — элементарные высказывания. Расширяет ли каждое высказывание число возможностей по $x$ и "
            "$y$ (D1, MT2, MT4 § 6 гл. 5, с. 77–78)? Проверьте по формулам вида $x : y : z \\vdash \\ldots$\n\n" +
            "\n".join(f"{L[i]}) ${tex(z)}$" for i, z in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("не расширяет" if ok(z) else "расширяет") for i, z in enumerate(its)) +
            "\n\n## Решение\n\nMT2 (с. 78): $xy$, $\\sim xy$, $x\\sim y$, $x$, $y$, $\\sim x$, $\\sim y$ не расширяют — в $S^5$ доказуемы "
            "формулы вида $x : y : z \\vdash x : y$ или $x : y : z \\vdash x$ и т. п. MT4: $\\sim x\\sim y$ расширяет — "
            "$x : y : \\sim x\\sim y \\vdash x : y$ недоказуема (при $x = y = 0$ посылка 1, заключение 0).")
    return card(5, 6, lvl, "C", "iso", "sym", "short", "расширение возможностей", body, "с. 77–79, гл. 5, § 6", "S^5")


def mt2_card(lvl):
    x, y = V("x"), V("y")
    fs = [(D(x, y, C(x, y)), D(x, y)), (D(x, y, C(N(x), y)), x), (D(x, y, C(x, N(y))), y), (D(x, y, x), y),
          (D(x, y, y), x), (D(x, y, N(x)), N(y)), (D(x, y, N(y)), N(x)), (D(x, y, C(N(x), N(y))), D(x, y)),
          (D(x, y, C(N(x), N(y))), x)]
    its = rnd.sample(fs, 4)
    body = ("## Условие\n\nБуквы $x, y$ — элементарные высказывания. Какие формулы доказуемы в $S^5$ (как сильные тавтологии)?\n\n" +
            "\n".join(f"{L[i]}) ${tex(a)} \\vdash {tex(b)}$" for i, (a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if SY.provable("s", a, b) else "нет") for i, (a, b) in enumerate(its)) +
            "\n\n## Решение\n\nСр. списки в MT2 и MT4 § 6 (с. 78). " +
            " ".join(f"{L[i]}) " + SY.reason("s", a, b, tex) + "." for i, (a, b) in enumerate(its)))
    return card(5, 6, lvl, "C", "iso", "sym", "short", "расширение возможностей", body, "с. 78, гл. 5, § 6", "S^5")


def rel_e(lvl):
    body = (f"## Условие\n\n{NC} Студент: «$x$ и $\\urcorner x$ — в классическом отношении: это отрицающие друг друга высказывания». "
            "Найдите ошибку.\n\n## Ответ\n\nПо MT9 (с. 79) они в неклассическом отношении: $\\vdash x : \\urcorner x$ недоказуема "
            "(при истинном $?x$ ложны оба), а $\\vdash x : \\urcorner x : \\sim x\\sim\\urcorner x$ доказуема.\n\n## Решение\n\nD2, D3, "
            "MT9 (с. 79).")
    return card(5, 6, lvl, "E", "open", "sym", "short", "классические и неклассические отношения, диагностика", body,
                "с. 79, гл. 5, § 6")


EXT = [("$\\urcorner$ и ?", "неклассический случай (гл. 5, § 5)"), ("$\\rightarrow$, $\\urcorner$, ?", "теория условных высказываний (гл. 6)")]


def ext_card(lvl, typ="D"):
    e, res = rnd.choice(EXT)
    k = rnd.choice("swmcq")
    body = (f"## Условие\n\nК системе {G.SYSTEX[k]} присоединяются дополнения к алфавиту и аксиомам: {e}. Что получится по § 7 гл. 5 "
            "(с. 79)?\n\n## Ответ\n\n" + f"Вариант раздела «{res}», построенный на {G.SYSTEX[k]}." +
            "\n\n## Решение\n\nС. 79: излагаются только дополнения к общей теории дедукции; в зависимости от выбранной системы "
            "получаются различные системы и варианты данного раздела логики.")
    return card(5, 7, lvl, typ, "iso", "meta", "short", "расширения общей теории дедукции", body, "с. 79, гл. 5, § 7")


def ext_count(lvl):
    ks = rnd.sample("swmcq", rnd.randint(2, 5))
    cases = rnd.choice([("и в классическом, и в неклассическом случае (гл. 5, § 5)", 2), ("только в классическом случае", 1)])
    names = ", ".join(G.SYSTEX[k] for k in ks)
    body = (f"## Условие\n\nСколько вариантов теории условных высказываний получится, если её дополнения (гл. 6) присоединять к "
            f"системам {names} — {cases[0]}?\n\n## Ответ\n\n{len(ks) * cases[1]}.\n\n## Решение\n\n{len(ks)} × {cases[1]}; § 7 гл. 5 "
            "(с. 79): «в зависимости от того, какая система общей теории дедукции будет выбрана, получатся различные системы и "
            "варианты».")
    return card(5, 7, lvl, "C", "vary", "meta", "short", "расширения общей теории дедукции", body, "с. 79, гл. 5, § 7")


def ext_e(lvl):
    v = rnd.choice([("«Теория условных высказываний — одна-единственная система, независимая от выбора системы следования»",
                     "по § 7 гл. 5 при разных системах следования получаются разные системы и варианты раздела"),
                    ("«Дополнения § 5 гл. 5 ($\\urcorner$, ?) можно присоединять только к сильному следованию $S^s$»",
                     "дополнения формулируются для любой системы общей теории дедукции; от выбора системы зависит вариант"),
                    ("«Расширяя общую теорию дедукции, надо заново выписывать все её аксиомы»",
                     "по § 7 гл. 5 излагаются только дополнения к общей теории дедукции (подобно § 5)")])
    body = (f"## Условие\n\nСтудент: {v[0]}. Найдите ошибку.\n\n## Ответ\n\nНеверно: {v[1]}.\n\n## Решение\n\nС. 79.")
    return card(5, 7, lvl, "E", "open", "meta", "short", "расширения общей теории дедукции, диагностика", body, "с. 79, гл. 5, § 7")


def sem_card(lvl, typ="C"):
    a, b = G.pair("c", lambda a, b: True, na="xy", nb="xy")
    t = SY.taut(a, b)
    body = (f"## Условие\n\n{G.CONV_C} По интерпретации § 8 гл. 5 (с. 80) формула $x \\vdash y$ имеет значение 1, если, приписав $x$ "
            f"значение 1, мы вынуждены приписать $y$ значение 1. Какое значение имеет ${G.ftex(a, b)}$?\n\n## Ответ\n\n" +
            ("1" if t else "0") + "\n\n## Решение\n\n" +
            ("При каждой комбинации, где посылка 1, заключение тоже 1." if t else
             f"При {SY.env_text(SY.counter(a, b))} посылка 1, а заключение 0 — приписать заключению 1 мы не вынуждены.") +
            " Такая интерпретация совпадает с прежней (тавтологичность), но и она лишь «техническое» средство (с. 80).")
    return card(5, 8, lvl, typ, "iso", "sym", "short", "семантическая интерпретация", body, "с. 79–80, гл. 5, § 8")


def sem_text(lvl):
    qs = [("Что, по § 8 гл. 5, есть определение условий истинности высказывания «Из $x$ следует $y$»?",
           "Оно истинно, если и только если действительно имеется логическое правило (утверждение), согласно которому из $x$ "
           "следует $y$ (с. 80)."),
          ("Для чего в книге принята интерпретация «$x \\vdash y$ — тавтология, если и только если $x \\supset y$ — тавтология»?",
           "Из «технических» соображений и для удобства сравнения с системами классической математической логики, а не как "
           "определение условий истинности (с. 79–80)."),
          ("Почему семантическая интерпретация знака следования может быть лишь «техническим» средством?",
           "В логике приходится устанавливать сами правила следования, а истинность «Из $x$ следует $y$» определяется наличием "
           "такого правила (с. 80).")]
    q, a = rnd.choice(qs)
    body = f"## Условие\n\n{q}\n\n## Ответ\n\n{a}\n\n## Решение\n\nГл. 5, § 8 (с. 79–80)."
    return card(5, 8, lvl, "R" if lvl == 1 else "D", "iso", "meta", "text", "семантическая интерпретация", body,
                "с. 79–80, гл. 5, § 8")


def sem_e(lvl):
    v = rnd.choice([("«Формула $x \\vdash y$ истинна, потому что $x \\supset y$ — тавтология: это и есть определение условий её "
                     "истинности»", "тавтологичность — лишь техническая интерпретация; «Из $x$ следует $y$» истинно, если имеется "
                     "логическое правило, согласно которому из $x$ следует $y$"),
                    ("«Интерпретация знака следования через тавтологии — главное, что даёт логика»",
                     "по § 8 гл. 5 семантическая интерпретация — лишь «техническое» подсобное средство; главная задача — установить "
                     "сами правила следования"),
                    ("«По интерпретации § 8 $x \\vdash y$ имеет значение 1, если $x$ и $y$ оба истинны»",
                     "значение 1 — если, приписав $x$ значение 1, мы вынуждены приписать $y$ значение 1 (с. 80)")])
    body = (f"## Условие\n\nСтудент: {v[0]}. Найдите ошибку.\n\n## Ответ\n\nНеверно: {v[1]}.\n\n## Решение\n\nС. 79–80.")
    return card(5, 8, lvl, "E", "open", "meta", "short", "семантическая интерпретация, диагностика", body, "с. 79–80, гл. 5, § 8")


# --- операция замены отрицаний (§ 9) ---
def op_star(a, b):
    """Пункты 2–4 (с. 81) для формул, где : не встречается: снять двойные отрицания, заменить ~z на новое v."""
    def dn(f):
        if f[0] == "neg" and f[1][0] == "neg":
            return dn(f[1][1])
        if f[0] == "neg":
            return N(dn(f[1]))
        if f[0] == "v":
            return f
        return (f[0], tuple(dn(g) for g in f[1]))
    a, b = dn(a), dn(b)
    lits = set()

    def collect(f):
        if f[0] == "v":
            lits.add((f[1], 0))
        elif f[0] == "neg" and f[1][0] == "v":
            lits.add((f[1][1], 1))
        elif f[0] == "neg":
            collect(f[1])
        else:
            for g in f[1]:
                collect(g)
    collect(a)
    collect(b)
    both = sorted({n for n, s in lits if (n, 0) in lits and (n, 1) in lits})
    fresh = {n: v for n, v in zip(both, "uwpq")}

    def rep(f):
        if f[0] == "neg" and f[1][0] == "v" and f[1][1] in fresh:
            return V(fresh[f[1][1]])
        if f[0] == "v":
            return f
        if f[0] == "neg":
            return N(rep(f[1]))
        return (f[0], tuple(rep(g) for g in f[1]))
    return rep(a), rep(b), fresh


def op_card(lvl, typ="D"):
    def g():
        a, b = G.rnd_f("xy", 2, "w"), G.rnd_f("xy", 2, "w")
        if not (SY.taut(a, b) and (not any(SY.value(a, e) for e in SY.rows(a)) or SY.is_taut(b))):
            return None
        if ("dis") in repr((a, b)):
            return None
        return (a, b)
    a, b = uniq(g)
    a2, b2, fr = op_star(a, b)
    ok = SY.counter(a2, b2) is not None or any(SY.value(a2, e) for e in SY.rows(a2, b2))
    body = (f"## Условие\n\n{G.CONV_W} Формула ${G.ftex(a, b)}$ — тавтология, у которой посылка — противоречие или заключение — "
            "тавтология. Выполните операцию замены отрицаний § 9 гл. 5 (с. 81, пп. 2–4) и запишите $x^{**} \\vdash y^{**}$.\n\n"
            f"## Ответ\n\n${G.ftex(a2, b2)}$" + (f" (замена: " + ", ".join(f"$\\sim {k}$ на ${v}$" for k, v in fr.items()) + ")"
                                                 if fr else " (замен нет)") +
            "\n\n## Решение\n\nПп. 2–4 (с. 81): снимаются двойные отрицания; если элементарное высказывание входит и без "
            "отрицания, и с отрицанием, его отрицание везде заменяется новым высказыванием, не входящим в формулу. После замены "
            "посылка может принять значение 1, а заключение — 0 (с. 81).")
    return card(5, 9, lvl, typ, "iso", "sym", "short", "полнота, замена отрицаний", body, "с. 80–81, гл. 5, § 9")


def op_appl(lvl):
    its = []
    for want_ in rnd.sample([True, True, False, False], 4):
        def g():
            a, b = G.rnd_f("xy", 2, "w"), G.rnd_f("xy", 2, "w")
            appl = (not any(SY.value(a, e) for e in SY.rows(a))) or SY.is_taut(b)
            return (a, b) if SY.taut(a, b) and appl == want_ else None
        its.append(uniq(g))
    ap = lambda a, b: (not any(SY.value(a, e) for e in SY.rows(a))) or SY.is_taut(b)
    body = (f"## Условие\n\n{G.CONV_W} К каким тавтологиям применима операция замены отрицаний § 9 гл. 5 (с. 81)?\n\n" +
            "\n".join(f"{L[i]}) ${G.ftex(a, b)}$" for i, (a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("применима" if ap(a, b) else "нет") for i, (a, b) in enumerate(its)) +
            "\n\n## Решение\n\nС. 81: операция применяется, если посылка — противоречие или заключение — тавтология (или то и "
            "другое). Пример книги: к $(x \\vee y)\\sim x \\vdash y$ она неприменима.")
    return card(5, 9, lvl, "C", "iso", "sym", "short", "полнота, замена отрицаний", body, "с. 81, гл. 5, § 9")


def op_e(lvl):
    def g():
        a, b = G.rnd_f("xy", 2, "w"), G.rnd_f("xy", 2, "w")
        appl = (not any(SY.value(a, e) for e in SY.rows(a))) or SY.is_taut(b)
        both = {n for n in "xy" if V(n) in G.SY.dnf(a)[0] or True}
        return (a, b) if SY.taut(a, b) and not appl and "neg" in repr(a) + repr(b) else None
    a, b = uniq(g)
    body = (f"## Условие\n\n{G.CONV_W} Студент применяет операцию замены отрицаний § 9 гл. 5 к тавтологии ${G.ftex(a, b)}$. Найдите "
            "ошибку.\n\n## Ответ\n\nОперация неприменима: посылка не противоречие, а заключение не тавтология.\n\n## Решение\n\nС. 81: "
            "операция применяется, только если посылка — противоречие или заключение — тавтология. Пример книги — "
            "$(x \\vee y)\\sim x \\vdash y$.")
    return card(5, 9, lvl, "E", "open", "sym", "short", "полнота, замена отрицаний, диагностика", body, "с. 81, гл. 5, § 9")


def full_s21(lvl):
    x, y = V("x"), V("y")
    a, b = C(W(x, y), N(x)), y
    body = (f"## Условие\n\n{G.CONV_W} Почему, по § 9 гл. 5, система $S_2^1$ не является «достаточно полной»? Проверьте формулу "
            "$(x \\vee y)\\sim x \\vdash y$: тавтология ли она, доказуема ли в $S_2^1$ (критерий MT1, MT2 § 6 гл. 3)?\n\n## Ответ\n\n"
            f"Тавтология — {'да' if SY.taut(a, b) else 'нет'}; в $S_2^1$ — {'доказуема' if SY.s21(a, b) else 'недоказуема'}; "
            "она непарадоксальна, и операция замены к ней неприменима, поэтому её недоказуемость — неполнота.\n\n## Решение\n\n"
            f"ДНФ посылки: ${SY.dnf_tex(SY.dnf(a), tex)}$; для члена $x\\sim x$ нет члена заключения из его составляющих. С. 81.")
    return card(5, 9, lvl, "S", "transfer", "sym", "short", "полнота", body, "с. 81, гл. 5, § 9; с. 56–57, гл. 3, § 6", "S_2^1")


def s21_vs(lvl):
    def g():
        a, b = G.rnd_f("xy", 2, "w"), G.rnd_f("xy", 2, "w")
        return (a, b) if SY.taut(a, b) and SY.provable("w", a, b) and not SY.s21(a, b) else None
    a, b = uniq(g)
    appl = (not any(SY.value(a, e) for e in SY.rows(a))) or SY.is_taut(b)
    body = (f"## Условие\n\n{G.CONV_W} Формула ${G.ftex(a, b)}$ доказуема в $S^w$, но не в $S_2^1$. Говорит ли это о неполноте $S_2^1$ в "
            "смысле § 9 гл. 5?\n\n## Ответ\n\n" +
            ("Нет: к ней применима операция замены отрицаний (посылка — противоречие или заключение — тавтология), и судить надо по "
             "$x^{**} \\vdash y^{**}$." if appl else "Да: формула непарадоксальна (операция замены к ней неприменима), а в $S_2^1$ "
             "недоказуема.") + f"\n\n## Решение\n\nДНФ посылки: ${SY.dnf_tex(SY.dnf(a), tex)}$; заключения: "
            f"${SY.dnf_tex(SY.dnf(b), tex)}$. С. 81; критерий $S_2^1$ — с. 56–57.")
    return card(5, 9, lvl, "S", "transfer", "sym", "short", "полнота", body, "с. 81, гл. 5, § 9; с. 56–57, гл. 3, § 6", "S_2^1")


def cond6(lvl, typ="R"):
    its = [("(x \\rightarrow y)", "высказывание"), ("(x \\urcorner\\!\\rightarrow y)", "высказывание"),
           ("(x? \\rightarrow y)", "высказывание"), ("(a \\rightarrow y)", "не высказывание: $a$ — термин"),
           ("(x \\rightarrow (y \\rightarrow z))", "высказывание"), ("(\\rightarrow x)", "не высказывание: нет антецедента")]
    pick = rnd.sample(its, 4)
    body = ("## Условие\n\nБуквы $x, y, z$ — высказывания, $a$ — термин. Какие выражения — высказывания по D1 § 1 гл. 6 (с. 82)?\n\n" +
            "\n".join(f"{L[i]}) ${e}$" for i, (e, _) in enumerate(pick)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {r}" for i, (_, r) in enumerate(pick)) +
            "\n\n## Решение\n\nD1 (с. 82): $(x \\rightarrow y)$, $(x \\urcorner\\!\\rightarrow y)$, $(x? \\rightarrow y)$ — высказывания, если и "
            "только если $x$ и $y$ — высказывания.")
    return card(6, 1, lvl, typ, "iso", "sym", "short", "условные высказывания", body, "с. 82, гл. 6, § 1")


def antec(lvl, typ="D"):
    pairs = [("(xy \\rightarrow z)", "$xy$", "$z$"), ("(\\sim x \\urcorner\\!\\rightarrow y)", "$\\sim x$", "$y$"),
             ("(x? \\rightarrow (y \\vee z))", "$x$", "$y \\vee z$"), ("((x \\rightarrow y) \\rightarrow x)", "$x \\rightarrow y$", "$x$")]
    pick = rnd.sample(pairs, 3)
    body = ("## Условие\n\nНазовите антецедент и консеквент (D2 § 1 гл. 6, с. 82).\n\n" +
            "\n".join(f"{L[i]}) ${e}$" for i, (e, _, _) in enumerate(pick)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) антецедент {a}, консеквент {c}" for i, (_, a, c) in enumerate(pick)) +
            "\n\n## Решение\n\nD2 (с. 82): $x$ и $y$ — антецедент и консеквент высказываний $(x \\rightarrow y)$, "
            "$(x \\urcorner\\!\\rightarrow y)$, $(x? \\rightarrow y)$.")
    return card(6, 1, lvl, typ, "iso", "sym", "short", "условные высказывания", body, "с. 82, гл. 6, § 1")


def elem6(lvl, typ="D"):
    f = rnd.choice(["((x \\rightarrow y) \\rightarrow (y \\rightarrow x))", "((x \\urcorner\\!\\rightarrow y) \\rightarrow x)",
                    "(y \\rightarrow (x? \\rightarrow y))", "((x \\rightarrow y) \\rightarrow (x \\rightarrow y))"])
    body = ("## Условие\n\nБуквы $x, y$ — высказывания, в которые не входит оператор условности. Какие элементарные высказывания "
            f"(D2 второе, § 1 гл. 6) входят в ${f}$?\n\n## Ответ\n\n$x$ и $y$.\n\n## Решение\n\nП. 1: $x$, $y$ элементарны во внутренних "
            "условных высказываниях; п. 2: если такое высказывание входит в $z$, его элементарные высказывания — элементарные "
            "высказывания $z$ (с. 82).")
    return card(6, 1, lvl, typ, "iso", "sym", "short", "условные высказывания", body, "с. 82, гл. 6, § 1")


def cond6_e(lvl):
    v = rnd.choice([("«$(x \\rightarrow y)$ — формула следования: антецедент — посылка, консеквент — заключение»",
                     "Это высказывание с оператором условности; формула следования $x \\vdash y$ — высказывание о высказываниях с "
                     "предикатом «из первого следует второе» (гл. 6, § 2, с. 83; Введение, § 8)."),
                    ("«$\\urcorner$ в $(x \\urcorner\\!\\rightarrow y)$ — внешнее отрицание всего высказывания»",
                     "$\\urcorner$ — внутреннее отрицание, относящееся к оператору условности (с. 82)."),
                    ("«$(x \\rightarrow a)$, где $a$ — термин, — условное высказывание»",
                     "По D1 (с. 82) и антецедент, и консеквент должны быть высказываниями.")])
    body = f"## Условие\n\nНайдите ошибку: {v[0]}.\n\n## Ответ\n\n{v[1]}\n\n## Решение\n\nГл. 6, § 1–2 (с. 82–83)."
    return card(6, 1, lvl, "E", "open", "sym", "short", "условные высказывания, диагностика", body, "с. 82–83, гл. 6, § 1–2")


def sec6_02():
    out = [card(6, 2, 1, "R", "iso", "nat", "short", "условные высказывания и следование",
                "## Условие\n\nИз чего состоят высказывания «Если $x$, то $y$» и «Из $x$ следует $y$» (гл. 6, § 2)?\n\n## Ответ\n\n"
                "«Если $x$, то $y$» — из высказываний $x$, $y$ и высказывательного оператора; «Из $x$ следует $y$» — из субъектов "
                "«высказывание $x$», «высказывание $y$» и предиката «из первого следует второе».\n\n## Решение\n\nС. 83.",
                "с. 83, гл. 6, § 2"),
           card(6, 2, 2, "E", "iso", "nat", "short", "условные высказывания и следование, диагностика",
                "## Условие\n\nСтудент: «“Если пойдёт дождь, то улица станет мокрой” и “Из того, что пойдёт дождь, следует, что "
                "улица станет мокрой” — одно и то же». Найдите ошибку.\n\n## Ответ\n\nПо § 2 гл. 6 это смешение — грубая ошибка: "
                "первое — условное высказывание, второе — высказывание о следовании; вопрос об истинности первого лишь частично "
                "решается в логике.\n\n## Решение\n\nС. 83: если верно, что из $x$ следует $y$, то верно «Если $x$, то $y$»; но не во "
                "всех случаях, когда истинно «Если $x$, то $y$», истинно «Из $x$ следует $y$».", "с. 83, гл. 6, § 2")]
    return out


def make_ch(sec, lvl, d, i):
    if sec == 5:  # 05.05 остаток
        if d:
            return n_e(lvl)
        return n_taut_card(lvl, "S" if lvl == 7 else "C")
    if sec == 6:
        if d:
            return rel_e(lvl) if i % 2 == 0 else G.e_fake(G.mk(5, 6, "s", "c", "$S^5$", "S^5", "расширение возможностей",
                                                                "с. 77–79, гл. 5, § 6", "гл. 5, § 2, MT1", "", [], 0), lvl)
        if lvl == 1:
            return rel_card(1, "R")
        return [rel_card, poss_card, mt2_card][i % 3](lvl)
    if sec == 7:
        if d:
            return ext_e(lvl)
        return ext_count(lvl) if i % 2 else ext_card(lvl)
    if sec == 8:
        if d:
            return sem_e(lvl)
        if lvl <= 2:
            return sem_text(lvl)
        return sem_card(lvl, "S" if lvl == 7 else "C")
    if sec == 9:
        if d:
            return op_e(lvl) if i % 2 == 0 else G.e_fake(G.mk(5, 9, "w", "w", "$S_2^1$", "S_2^1", "полнота",
                                                               "с. 80–81, гл. 5, § 9", "гл. 3, § 6", "", [], 0), lvl)
        if lvl == 7:
            return full_s21(lvl) if i == 0 else s21_vs(lvl)
        return op_appl(lvl) if i % 2 == 0 else op_card(lvl)
    raise ValueError


def ch_sec(sec, levels, diag, start=None):
    out, nd = [], 0
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            if lvl >= 8:
                continue
            d = nd < diag and lvl >= 2 and (i + lvl) % 2 == 0
            c = fresh_card(lambda: make_ch(sec, lvl, d, i))
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def ch6_01():
    out = []
    lv = [2, 3, 3, 1, 1, 1]
    nd = 0
    for lvl, n in enumerate(lv, 1):
        for i in range(n):
            if nd < 3 and lvl >= 2 and i == 0:
                out.append(cond6_e(lvl))
                nd += 1
                continue
            fn = [lambda: cond6(lvl, "R" if lvl == 1 else "C"), lambda: antec(lvl, "R" if lvl == 1 else "D"),
                  lambda: elem6(lvl)][(i + lvl) % 3]
            out.append(fresh_card(fn))
    return out


# =============================== смешанные ===============================
def mixed(sec, levels, diag, keys, src):
    out, nd = [], 0
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            if lvl >= 8:
                continue
            k = keys[(i + lvl) % len(keys)]
            kk = "w" if k == "d" else k
            cfg = G.mk(17, sec, kk, ["c", "w"][i % 2], G.SYSTEX[kk], None, "смешанный", "смешанный набор", G.SY.MT[kk],
                       G.SY.MT[kk], [], 0)
            d = nd < diag and lvl in (3, 4, 5, 6) and i % 2 == 0
            c = None
            while c is None:
                if k == "d":
                    cfg["key"] = "w"
                    c = G.s21_e(cfg, lvl) if d else G.s21_card(cfg, lvl)
                else:
                    c = G.make(cfg, lvl, d, i, None)
            for st in ("iso", "open", "transfer", "vary", "complete"):
                c = c.replace(f"step: {st}\n", "step: mixed\n")
            import re
            c = re.sub(r'source: ".*"', f'source: "{src}"', c, count=1)
            c = re.sub(r"chapter: \d+\nsection: \d+", f"chapter: 17\nsection: {sec}", c, count=1)
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def main():
    cards = []
    cards += ch_sec(5, [0, 0, 0, 2, 5, 4, 2, 0, 0, 0], 3)
    cards += ch_sec(6, [1, 3, 6, 2, 2, 3, 2, 0, 0, 0], 5)
    cards += ch_sec(7, [0, 1, 1, 2, 3, 2, 1, 0, 0, 0], 2)
    cards += ch_sec(8, [1, 2, 3, 1, 1, 2, 1, 0, 0, 0], 3)
    cards += ch_sec(9, [0, 1, 2, 3, 2, 3, 2, 0, 0, 0], 5)
    cards += sec16(1, [7, 9, 9, 3, 2, 3, 2], 9)
    cards += sec16(2, [7, 9, 9, 3, 2, 3, 2], 9)
    cards += sec16(3, [2, 7, 8, 11, 18, 14, 7], 17)
    cards += sec16(4, [2, 5, 11, 4, 3, 5, 3], 8)
    cards += sec16(5, [1, 1, 3, 1, 3, 4, 5], 6)
    cards += sec16(6, [0, 5, 10, 5, 8, 13, 7], 48)
    cards += ch6_01()
    cards += sec6_02()
    cards += mixed(4, [0, 0, 1, 1, 5, 6, 4], 5, ["s", "w", "d"], "гл. 1–3")
    cards += mixed(5, [0, 2, 3, 1, 4, 6, 3], 6, ["s", "w", "m", "c", "q"], "гл. 1–4")
    cards += mixed(6, [0, 2, 3, 1, 5, 6, 1], 5, ["s", "w", "m", "c", "q"], "гл. 1–5")
    (ROOT / "drafts" / "31-40-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(cards))


if __name__ == "__main__":
    main()
