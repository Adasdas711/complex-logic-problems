#!/usr/bin/env python3
"""Серии для занятий 41–50: гл. 6 (условные высказывания), гл. 7, § 1–5 (кванторы), смешанные 17.06–17.08.
Пишет drafts/41-50-gen.md.
"""
import importlib.util
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import ifq as Q  # noqa: E402
from ifq import ALL, EL, EX, IF, IFN, IFQ, IMP, C, D, N, V, W, tex, ftex  # noqa: E402



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

def load(name, seed):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / "gen" / f"{name}.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    m.rnd.seed(seed)
    return m


G = load("g02_05", 4150)
G16 = load("g05_16", 4151)
rnd = random.Random(4152)
L = "абвгдежз"
USED = set()
x, y, z, v, u = (V(n) for n in "xyzvu")
CV = "Буквы $x, y, z, v$ — высказывания; $\\rightarrow$ — оператор условности «если, то»; $\\supset$ — материальная импликация."


def card(ch, sec, lvl, typ, step, form, ans, tags, body, src, system=None):
    sysl = f'system: "{system}"\n' if system else ""
    return (f"---\nchapter: {ch}\nsection: {sec}\nlevel: {lvl}\ntype: {typ}\nstep: {step}\ncondition: def\nform: {form}\n"
            f"answer: {ans}\nsource: \"{src}\"\n{sysl}generated: true\ntags: [{tags}]\n---\n\n{body}\n")


def cond(c):
    return c[c.index("## Условие"):c.index("## Ответ")]


def fresh(fn, tries=60):
    c = None
    for _ in range(tries):
        c = fn()
        if c is not None and cond(c) not in USED:
            break
    USED.add(cond(c))
    return c


def ren():
    """Случайное переименование x, y, z, v."""
    ls = ["x", "y", "z", "v"]
    p = rnd.sample(ls, 4)
    return dict(zip(ls, p))


def sub(f, m):
    k = f[0]
    if k == "v":
        return V(m.get(f[1], f[1]))
    if k == "el":
        return f
    if k == "neg":
        return N(sub(f[1], m))
    if k in Q.BIN:
        return (k, sub(f[1], m), sub(f[2], m))
    if k in ("all", "ex"):
        return (k, f[1], sub(f[2], m))
    return (k, tuple(sub(a, m) for a in f[1]))


def permute(c, letters):
    """Согласованно переименовать отдельно стоящие буквы в теле карточки (не трогая команды LaTeX)."""
    perm = dict(zip(letters, rnd.sample(letters, len(letters))))
    head, body = c[:c.index("## Условие")], c[c.index("## Условие"):]

    def repl_math(m):
        s = m.group(0)
        return tex_map(s, perm)
    body = re.sub(r"\$[^$]+\$", repl_math, body)
    body = re.sub(r"Буквы \$([a-z](?:, [a-z])+)\$", lambda q: "Буквы $" + ", ".join(sorted(q.group(1).split(", "))) + "$", body)
    return head + body


# ================= гл. 6, § 2–3: условность, следование, материальная импликация =================
PH = {"x": ("идёт дождь", "дождя нет"), "y": ("улица мокрая", "улица сухая"), "z": ("дует ветер", "ветра нет"),
      "v": ("холодно", "не холодно")}


def nl(f):
    k = f[0]
    if k == "v":
        return PH[f[1]][0]
    if k == "neg" and f[1][0] == "v":
        return PH[f[1][1]][1]
    if k == "neg":
        return "неверно, что " + nl(f[1])
    if k == "conj":
        return " и ".join(nl(a) for a in f[1])
    if k == "wdis":
        return " или ".join(nl(a) for a in f[1])
    if k == "if":
        return f"если {nl(f[1])}, то {nl(f[2])}"
    raise ValueError


# (формула-посылка, заключение или None, верна ли для →, обоснование)
BAD = [(C(x, y), IF(x, y), "установив в какой-то ситуации истинность $x$ и $y$, мы ещё не вправе принимать $y$ всякий раз, когда истинно $x$"),
       (C(N(x), N(y)), IF(x, y), "из ложности $x$ и $y$ не следует право принимать $y$ при $x$ (п. 9 § 4: при $x = 0$ значение $x \\rightarrow y$ не зависит от $x$)"),
       (C(N(x), y), IF(x, y), "истинность $y$ при ложном $x$ не даёт права принимать $y$ при $x$"),
       (N(C(x, N(y))), IF(x, y), "отрицание $x\\sim y$ не устанавливает условной связи"),
       (N(IF(x, y)), C(x, N(y)), "отрицание $x \\rightarrow y$ означает лишь, что признание $x$ не даёт права на признание $y$; отсюда не следует $x\\sim y$"),
       (W(N(x), y), IF(x, y), "дизъюнкция $\\sim x \\vee y$ не устанавливает условной связи"),
       (IF(C(x, y), W(z, v)), W(IF(x, z), IF(y, v)), "возможно, верно $xy \\rightarrow z$ или $xy \\rightarrow v$, но неверны оба $x \\rightarrow z$ и $y \\rightarrow v$"),
       (IF(C(x, y), z), W(IF(x, z), IF(y, z)), "например, $xy \\rightarrow xy$ истинно, а $x \\rightarrow xy$ и $y \\rightarrow xy$ могут быть ложными"),
       (IF(x, W(y, z)), W(IF(x, y), IF(x, z)), "если $x$, то какая-то из возможностей $y$, $z$ реализуется, но какая именно, по $x$ судить невозможно (с. 88)")]
GOOD = [(C(IF(x, y), x), y, "A1 § 6"), (C(IF(x, y), N(y)), N(x), "T4 § 6"), (IF(x, y), IF(N(y), N(x)), "A2 § 6"),
        (None, IF(C(x, y), N(IF(x, N(y)))), "с. 85"), (None, IF(IF(x, y), IMP(x, y)), "с. 86"),
        (None, IF(N(IMP(x, y)), N(IF(x, y))), "с. 86")]


def imp_version(f):
    return Q.to_imp(f)


def bad_good_card(lvl, typ="C", nat=False):
    its = rnd.sample([("b", b) for b in BAD], 2) + rnd.sample([("g", g) for g in GOOD], 2)
    rnd.shuffle(its)
    m = {"x": "x", "y": "y", "z": "z", "v": "v"}

    def show(it):
        kind, d = it
        a, b = sub(d[0], m) if d[0] else None, sub(d[1], m)
        if nat and a is not None and all(q[0] != "imp" for q in (a, b)):
            try:
                return f"«{nl(a).capitalize()}; следовательно, {nl(b)}»"
            except ValueError:
                pass
        return f"${ftex(a, b)}$" if a is not None else f"${ftex(b)}$"
    body = (f"## Условие\n\n{CV} Какие утверждения книга (гл. 6, § 3, с. 84–86) считает верными для оператора условности, а какие "
            "— ошибочными?\n\n" + "\n".join(f"{L[i]}) {show(it)}" for i, it in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("верно" if it[0] == "g" else "ошибочно") for i, it in enumerate(its)) +
            "\n\n## Решение\n\n" + "\n".join(f"{L[i]}) " + (f"верно ({it[1][2]})." if it[0] == "g" else f"ошибочно: {it[1][2]}. "
                                                         "Аналог с $\\supset$ — тавтология.") for i, it in enumerate(its)))
    return card(6, 3, lvl, typ, "iso", "nat" if nat else "sym", "short", "условность, материальная импликация", body,
                "с. 84–86, гл. 6, § 3")


def imp_taut_card(lvl):
    its = rnd.sample(BAD, 4)
    m = ren()
    body = (f"## Условие\n\n{CV} Замените в каждой формуле $\\rightarrow$ на $\\supset$. Тавтологии ли полученные формулы?\n\n" +
            "\n".join(f"{L[i]}) ${ftex(sub(a, m), sub(b, m))}$" for i, (a, b, _) in enumerate(its)) + "\n\n## Ответ\n\nВсе четыре — "
            "тавтологии.\n\n## Решение\n\nС. 84–85: «Эти утверждения суть тавтологии и в силу полноты $S^s$ доказуемы в ней. Но "
            "аналогичные утверждения для оператора условности ошибочны».")
    for a, b, _ in its:
        aa, bb = imp_version(sub(a, m)), imp_version(sub(b, m))
        assert Q.is_taut(IMP(aa, bb)), (tex(aa), tex(bb))
    return card(6, 3, lvl, "D", "iso", "sym", "short", "условность, материальная импликация", body, "с. 84–85, гл. 6, § 3")


def bad_e(lvl, nat=True):
    a, b, why = rnd.choice(BAD)
    m = {"x": "x", "y": "y", "z": "z", "v": "v"}
    a, b = sub(a, m), sub(b, m)
    try:
        txt = f"«{nl(a).capitalize()}; следовательно, {nl(b)}»" if nat else f"${ftex(a, b)}$"
    except ValueError:
        txt = f"${ftex(a, b)}$"
    body = (f"## Условие\n\n{CV} Студент: «Рассуждение {txt} правильно: для материальной импликации соответствующая формула — "
            "тавтология». Найдите ошибку.\n\n## Ответ\n\nНеверно: оператор условности нельзя отождествлять с $\\supset$; это "
            f"утверждение для $\\rightarrow$ ошибочно — {why}.\n\n## Решение\n\nГл. 6, § 3 (с. 84–88). Обозначения букв: " +
            ", ".join(f"$x$ → ${m['x']}$" for _ in [0]) + "; рассуждение не тавтология и по интерпретации § 4.")
    body = body.replace(", ".join(f"$x$ → ${m['x']}$" for _ in [0]), "как в формуле")
    return card(6, 3, lvl, "E", "open", "nat" if nat else "sym", "short", "условность, диагностика", body, "с. 84–88, гл. 6, § 3")


def cmp_card(lvl):
    qs = [("Может ли $x \\rightarrow y$ иметь значение 0, когда $x = 1$ и $y = 1$?", "Да (с. 88)."),
          ("Может ли $x \\rightarrow y$ иметь значение 0, когда $x = 0$ и $y = 1$?", "Да (с. 88)."),
          ("Какое значение имеет $x \\rightarrow y$, если $x = 1$, $y = 0$?", "0 — единственный случай, где оно определяется только "
           "значениями $x$ и $y$, как у $x \\supset y$ (с. 88)."),
          ("Если истинно $x \\rightarrow y$, истинно ли $x \\supset y$?", "Да (с. 88; $\\vdash (x \\rightarrow y) \\rightarrow (x \\supset y)$, с. 86)."),
          ("Если истинно $x \\supset y$, истинно ли $x \\rightarrow y$?", "Не обязательно (с. 88).")]
    its = rnd.sample(qs, 3)
    body = (f"## Условие\n\n{CV} Ответьте по интерпретации § 4 гл. 6.\n\n" + "\n".join(f"{L[i]}) {q}" for i, (q, _) in enumerate(its)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[i]}) {a}" for i, (_, a) in enumerate(its)) +
            "\n\n## Решение\n\nС. 88: принятая интерпретация условной импликации отличается от табличного определения "
            "материальной импликации.")
    return card(6, 3, lvl, "S" if lvl == 7 else "C", "transfer", "sym", "short", "условность, материальная импликация", body,
                "с. 86–88, гл. 6, § 3–4")


SENT = [("вода нагрета до 100 °C", "вода кипит"), ("число делится на 4", "число чётное"), ("идёт дождь", "улица мокрая"),
        ("треугольник равносторонний", "его углы равны"), ("ключ повернули", "дверь открыта")]


def ifvs_card(lvl, typ="C"):
    p, q = rnd.choice(SENT)
    its = [(f"«Если {p}, то {q}»", "высказывания «" + p + "», «" + q + "» и оператор «если, то»"),
           (f"«Из того, что {p}, следует, что {q}»", "субъекты «высказывание «" + p + "»», «высказывание «" + q + "»» и предикат "
            "«из первого следует второе»")]
    rnd.shuffle(its)
    body = ("## Условие\n\nИз чего состоит каждое высказывание по § 2 гл. 6 (с. 83)?\n\n" +
            "\n".join(f"{L[i]}) {s}" for i, (s, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {a}" for i, (_, a) in enumerate(its)) + "\n\n## Решение\n\nС. 83: смешение этих высказываний — "
            "грубая ошибка.")
    return card(6, 2, lvl, typ, "iso", "nat", "short", "условность и следование", body, "с. 83, гл. 6, § 2")


def ifvs_e(lvl):
    p, q = rnd.choice(SENT)
    v_ = rnd.choice([(f"«Если {p}, то {q}» истинно, значит, истинно и «Из того, что {p}, следует, что {q}»",
                      "не во всех случаях, когда истинно «Если $x$, то $y$», истинно «Из $x$ следует $y$»"),
                     (f"Истинность «Если {p}, то {q}» решается логикой, как и истинность высказываний о следовании",
                      "вопрос об истинности «Если $x$, то $y$» лишь частично решается в логике — как производный от следования")])
    body = (f"## Условие\n\nСтудент: {v_[0]}. Найдите ошибку.\n\n## Ответ\n\nНеверно: {v_[1]} (§ 2 гл. 6, с. 83).\n\n## Решение\n\n"
            "С. 83: если верно, что из $x$ следует $y$, то верно «Если $x$, то $y$»; в остальных случаях логика не компетентна судить "
            "об истинности условных высказываний.")
    return card(6, 2, lvl, "E", "open", "nat", "short", "условность и следование, диагностика", body, "с. 83, гл. 6, § 2")


# ================= § 4: интерпретация =================
SIT = [("$x \\rightarrow y$ имеет значение 1 и $x$ — 1", "$y$ должно иметь значение 1", "1"),
       ("$x \\rightarrow y$ имеет значение 1 и $y$ — 0", "$x$ должно иметь значение 0", "2"),
       ("$x \\rightarrow y$ имеет значение 0 и $x$ — 1", "значение $y$ не зависит от $x$: рассматриваются оба случая", "3"),
       ("$x \\rightarrow y$ имеет значение 0 и $y$ — 0", "значение $x$ не зависит от значения $y$", "4"),
       ("$x$ имеет значение 0", "значение $x \\rightarrow y$ не зависит от значения $x$", "9"),
       ("$y$ имеет значение 1", "значение $x \\rightarrow y$ не зависит от значения $y$", "9"),
       ("$x \\rightarrow y$ имеет значение 1", "$x \\urcorner\\!\\rightarrow y$ имеет значение 0", "10"),
       ("$x \\rightarrow y$ имеет значение 0", "значение $x \\urcorner\\!\\rightarrow y$ может быть и 1, и 0", "11"),
       ("$x \\rightarrow y$ и $x \\urcorner\\!\\rightarrow y$ имеют значение 0", "$x? \\rightarrow y$ имеет значение 1", "12"),
       ("$x$ приписано 1, и вследствие этого мы вынуждены приписать $y$ значение 1", "$x \\rightarrow y$ должно иметь значение 1", "5"),
       ("$y$ приписано 0, и вследствие этого мы вынуждены приписать $x$ значение 0", "$x \\rightarrow y$ должно иметь значение 1", "6"),
       ("$x$ приписано 1, и это не обязывает приписывать $y$ значение 1", "$x \\rightarrow y$ можно приписать значение 0", "7"),
       ("$y$ приписано 0, и это не обязывает приписывать $x$ значение 0", "$x \\rightarrow y$ можно приписать значение 0", "8")]


def sit_card(lvl, typ="C"):
    its = rnd.sample(SIT, 4)
    m = ren()
    r = lambda s: s.replace("$x", "$@").replace("$y", "$#").replace("@", m["x"]).replace("#", m["y"]).replace(
        "x? ", f"{m['x']}? ").replace(" x \\urcorner", f" {m['x']} \\urcorner").replace("\\rightarrow y", f"\\rightarrow {m['y']}")
    body = ("## Условие\n\nБуквы $x, y, z, v$ — высказывания. Что следует по правилам интерпретации § 4 гл. 6 (с. 86–87)? Укажите "
            "номер правила.\n\n" + "\n".join(f"{L[i]}) {r(s)}" for i, (s, _, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {r(a)} (п. {n})" for i, (_, a, n) in enumerate(its)) + "\n\n## Решение\n\nС. 86–87, пп. 1–12.")
    return card(6, 4, lvl, typ, "iso", "sym", "short", "условность, интерпретация", body, "с. 86–87, гл. 6, § 4")


def rule_card(lvl):
    its = rnd.sample(SIT, 5)
    body = ("## Условие\n\nНазовите номер правила интерпретации § 4 гл. 6 (с. 86–87), которое применяется в ситуации.\n\n" +
            "\n".join(f"{L[i]}) {s}; вывод: {a}" for i, (s, a, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) п. {n}" for i, (_, _, n) in enumerate(its)) + "\n\n## Решение\n\nС. 86–87.")
    return card(6, 4, lvl, "R", "iso", "sym", "short", "условность, интерпретация", body, "с. 86–87, гл. 6, § 4")


EX4 = [(IF(C(x, y), z), W(IF(x, z), IF(y, z)), False, "приписав $xy \\rightarrow z$ значение 1 и $z$ значение 0, мы должны приписать $xy$ "
        "значение 0 (п. 2), но не обязаны приписывать $x$ значение 0 — $xy$ может быть ложно за счёт $y$; поэтому $x \\rightarrow z$ "
        "можно приписать 0 (п. 8), аналогично $y \\rightarrow z$"),
       (IF(x, W(y, z)), W(IF(x, y), IF(x, z)), False, "приписав $x$ и $x \\rightarrow y \\vee z$ значение 1, мы должны приписать $y \\vee z$ "
        "значение 1, но не обязаны приписывать 1 именно $y$ (или $z$): $x \\rightarrow y$ и $x \\rightarrow z$ могут иметь значение 0 (п. 7)"),
       (C(IF(x, y), IF(y, z)), IF(x, z), True, "приписав $(x \\rightarrow y)$, $(y \\rightarrow z)$ и $x$ значение 1, мы вынуждены приписать "
        "$z$ значение 1; значит, и $x \\rightarrow z$ должны приписать 1 (п. 5)"),
       (z, IF(x, z), False, "приписав $z$ значение 1, мы не определяем $x \\rightarrow z$ — оно может иметь значение 0 (п. 9); $z$ получает 1 "
        "не вследствие того, что $x$ приписано 1"),
       (None, IF(C(x, y), x), True, "консеквент принимает значение 1, если антецедент принимает 1; по п. 5 высказывание имеет значение 1")]


def ex4_card(lvl, typ="C"):
    its = rnd.sample(EX4, 3)
    m = {"x": "x", "y": "y", "z": "z", "v": "v"}
    show = lambda a, b: f"${ftex(sub(a, m), sub(b, m))}$" if a is not None else f"${ftex(sub(b, m))}$"
    body = (f"## Условие\n\n{CV} Тавтологии ли формулы при интерпретации § 4 гл. 6? Обоснуйте пунктами правил.\n\n" +
            "\n".join(f"{L[i]}) {show(a, b)}" for i, (a, b, _, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if t else "нет") for i, (_, _, t, _) in enumerate(its)) +
            "\n\n## Решение\n\n" + "\n".join(f"{L[i]}) {w} ." for i, (_, _, _, w) in enumerate(its)) +
            "\n\nС. 87–88.")
    return card(6, 4, lvl, typ, "open", "sym", "short", "условность, интерпретация", body, "с. 87–88, гл. 6, § 4")


def interp_e(lvl):
    v_ = rnd.choice([("«$x$ ложно, значит, $x \\rightarrow y$ истинно — как у материальной импликации»",
                      "по п. 9 при $x = 0$ значение $x \\rightarrow y$ не зависит от $x$: оно может быть и 0"),
                     ("«$x$ и $y$ истинны, значит, $x \\rightarrow y$ истинно»", "$x \\rightarrow y$ может иметь значение 0 и при $x = y = 1$ (с. 88)"),
                     ("«$x \\rightarrow y$ ложно, значит, $x$ истинно и $y$ ложно»", "по п. 3 и п. 4 при $x \\rightarrow y = 0$ значения $x$ и $y$ "
                      "не определяются однозначно; ложность $x \\rightarrow y$ означает лишь, что признание $x$ не даёт права на признание $y$"),
                     ("«$x \\rightarrow y$ и $x \\urcorner\\!\\rightarrow y$ оба ложны — это противоречие»",
                      "по п. 11 значение одного не зависит от значения другого, а по п. 12 тогда истинно $x? \\rightarrow y$"),
                     ("«$x \\rightarrow y$ и $x \\urcorner\\!\\rightarrow y$ могут быть истинны вместе»", "по п. 10 если одно имеет значение 1, "
                      "другое имеет значение 0")])
    body = (f"## Условие\n\n{CV} Студент: {v_[0]}. Найдите ошибку.\n\n## Ответ\n\nНеверно: {v_[1]}.\n\n## Решение\n\nГл. 6, § 4 "
            "(с. 86–88).")
    return permute(card(6, 4, lvl, "E", "open", "sym", "short", "условность, интерпретация, диагностика", body, "с. 86–88, гл. 6, § 4"), "xyzv")


# ================= § 5: классический и неклассический случаи =================
AN = [("A^n1", IF(x, y), C(N(IFN(x, y)), N(IFQ(x, y)))), ("A^n2", C(N(IFN(x, y)), N(IFQ(x, y))), IF(x, y)),
      ("A^n3", IFN(x, y), C(N(IF(x, y)), N(IFQ(x, y)))), ("A^n4", C(N(IF(x, y)), N(IFQ(x, y))), IFN(x, y)),
      ("A^n5", IFQ(x, y), C(N(IF(x, y)), N(IFN(x, y)))), ("A^n6", C(N(IF(x, y)), N(IFN(x, y))), IFQ(x, y)),
      ("A^n7", N(IF(x, y)), IFN(x, y))]


def an_rec(lvl):
    its = rnd.sample(AN, 4)
    body = (f"## Условие\n\n{CV} Каким аксиомным схемам § 5 гл. 6 (с. 89) соответствуют формулы?\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (_, a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) ${n}$" for i, (n, _, _) in enumerate(its)) + "\n\n## Решение\n\nС. 89.")
    return card(6, 5, lvl, "R", "iso", "sym", "short", "условность, неклассический случай", body, "с. 89, гл. 6, § 5")


def an_taut(lvl, typ="C"):
    pool = [IF(x, y), IFN(x, y), IFQ(x, y), N(IF(x, y)), N(IFN(x, y)), N(IFQ(x, y)), W(IF(x, y), IFN(x, y)),
            C(N(IF(x, y)), N(IFN(x, y)))]
    its = []
    while len(its) < 4:
        a, b = rnd.sample(pool, 2)
        if (a, b) not in its:
            its.append((a, b))
    st = lambda a, b, s: "да" if Q.ctaut(a, b, s) else "нет"
    body = (f"## Условие\n\n{CV} Из $x \\rightarrow y$, $x \\urcorner\\!\\rightarrow y$, $x? \\rightarrow y$ истинно ровно одно (пп. 10–12 § 4). "
            "Тавтологии ли формулы в неклассическом случае и в классическом (с $A^n7$: $\\sim(x \\rightarrow y) \\vdash (x \\urcorner\\!\\rightarrow y)$)?\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {st(a, b, ('if', 'ifn', 'ifq'))} / {st(a, b, ('if', 'ifn'))}" for i, (a, b) in enumerate(its)) +
            " (неклассический / классический)\n\n## Решение\n\nПеребираем состояния; в классическом случае $x? \\rightarrow y$ "
            "невозможно (MT1 § 5: доказуема $\\vdash \\sim(x? \\rightarrow y)$).")
    return card(6, 5, lvl, typ, "iso", "sym", "short", "условность, неклассический случай", body, "с. 86–90, гл. 6, § 4–5")


def an_e(lvl):
    v_ = rnd.choice([("$\\sim(x \\urcorner\\!\\rightarrow y) \\vdash (x \\rightarrow y)$", "MT3 § 5 (с. 89): не тавтология — при истинном "
                      "$x? \\rightarrow y$ посылка истинна, заключение ложно"),
                     ("$\\sim(x \\rightarrow y) \\vdash (x \\urcorner\\!\\rightarrow y)$", "это $A^n7$, она принимается только для "
                      "классического случая; в неклассическом не тавтология (MT3, с. 89)")])
    body = (f"## Условие\n\n{CV} Студент считает {v_[0]} теоремой неклассической системы ($S^5$ с $A^n1$–$A^n6$). Найдите ошибку.\n\n"
            f"## Ответ\n\nНедоказуема: {v_[1]}.\n\n## Решение\n\nС. 89.")
    return permute(card(6, 5, lvl, "E", "open", "sym", "short", "условность, неклассический случай, диагностика", body, "с. 89, гл. 6, § 5"), "xyzv")


# ================= § 6–7: S^s_if, S^w_if =================
AX = {"A1": "(x \\rightarrow y)x \\vdash y", "A2": "(x \\rightarrow y) \\vdash (\\sim y \\rightarrow \\sim x)",
      "A3": "(x \\rightarrow y)(y \\rightarrow z) \\vdash (x \\rightarrow z)", "A4": "(x \\rightarrow yz) \\vdash (x \\rightarrow y)(x \\rightarrow z)",
      "A5": "(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))", "A6": "(x \\rightarrow (y \\rightarrow z)) \\vdash (xy \\rightarrow z)",
      "A7": "(x \\rightarrow y)(z \\rightarrow v) \\vdash (xz \\rightarrow yv)", "A8": "(x \\rightarrow y) \\vee (z \\rightarrow v) \\vdash (xz \\rightarrow y \\vee v)",
      "A9": "(x \\rightarrow y) \\vdash (xz \\rightarrow y)"}


def ax_inst(n, X, Y, Z, Vv):
    return {"A1": (C(IF(X, Y), X), Y), "A2": (IF(X, Y), IF(N(Y), N(X))), "A3": (C(IF(X, Y), IF(Y, Z)), IF(X, Z)),
            "A4": (IF(X, C(Y, Z)), C(IF(X, Y), IF(X, Z))), "A5": (IF(C(X, Y), Z), IF(X, IF(Y, Z))),
            "A6": (IF(X, IF(Y, Z)), IF(C(X, Y), Z)), "A7": (C(IF(X, Y), IF(Z, Vv)), IF(C(X, Z), C(Y, Vv))),
            "A8": (W(IF(X, Y), IF(Z, Vv)), IF(C(X, Z), W(Y, Vv))), "A9": (IF(X, Y), IF(C(X, Z), Y))}[n]


def meta4():
    return rnd.sample([x, y, z, v, N(x), N(z), C(x, z)], 4)


T6 = [("T1", "(x \\rightarrow y)(yz \\rightarrow v) \\vdash (xz \\rightarrow v)", "A5, A3, A6"),
      ("T2", "(x \\rightarrow y \\vee z)(z \\rightarrow v) \\vdash (x \\rightarrow y \\vee v)", "A2, T1, A2"),
      ("T3", "(x \\vee y \\rightarrow z)(v \\rightarrow x) \\vdash (v \\vee y \\rightarrow z)", "A2, A4, A3, A7, A2"),
      ("T4", "(x \\rightarrow y)\\sim y \\vdash \\sim x", "A2, A1"), ("T5", "(x \\rightarrow y \\vee z)\\sim y \\vdash (x \\rightarrow z)", "A2, A5, A1, A2"),
      ("T6", "(xy \\rightarrow z)x \\vdash (y \\rightarrow z)", "A5, A1"), ("T7", "(x \\vee y \\rightarrow z) \\vdash (x \\rightarrow z)(y \\rightarrow z)", "A2, A4, A2"),
      ("T8", "(x \\rightarrow z)(y \\rightarrow z) \\vdash (x \\vee y \\rightarrow z)", "A2, A7, A2"),
      ("T9", "(x \\rightarrow y \\vee z) \\vdash (\\sim y \\rightarrow (x \\rightarrow z))", "A2, A5, A3, A2"),
      ("T10", "(\\sim y \\rightarrow (x \\rightarrow z)) \\vdash (x \\rightarrow (y \\vee z))", "A2, A6, A2"),
      ("T11", "(x \\rightarrow y)(v \\rightarrow z) \\vdash (x \\vee v \\rightarrow y \\vee z)", "A2, A7, A2")]


def ax_rec(lvl, sysn="S^s_{if}", with9=False):
    names = rnd.sample(list(AX)[:9 if with9 else 8], 4)
    its = [(n, ax_inst(n, *meta4())) for n in names]
    body = (f"## Условие\n\n{CV} Каким аксиомным схемам ${sysn}$ (с. 90{'–91' if with9 else ''}) соответствуют формулы?\n\n" +
            "\n".join(f"{L[i]}) ${ftex(*f)}$" for i, (_, f) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {n}" for i, (n, _) in enumerate(its)) + "\n\n## Решение\n\nСхемы: " +
            "; ".join(f"{n}: ${AX[n]}$" for n in names) + ".")
    return card(6, 7 if with9 else 6, lvl, "R", "iso", "sym", "short", "условность, аксиомы", body,
                "с. 90–91, гл. 6, § 6–7", "S^s_if")


def ax_sub(lvl, with9=False):
    n = rnd.choice(list(AX)[:9 if with9 else 8])
    X, Y, Z, Vv = meta4()
    a, b = ax_inst(n, X, Y, Z, Vv)
    body = (f"## Условие\n\n{CV} Подставьте в схему {n} (${AX[n]}$) вместо $x$ — ${tex(X)}$, $y$ — ${tex(Y)}$, $z$ — ${tex(Z)}$, $v$ — "
            f"${tex(Vv)}$ (используйте только нужные).\n\n## Ответ\n\n${ftex(a, b)}$\n\n## Решение\n\nС. 90–91; буквы схем — метапеременные.")
    return card(6, 7 if with9 else 6, lvl, "D", "iso", "sym", "short", "условность, аксиомы", body, "с. 90–91, гл. 6, § 6–7",
                "S^s_if")


def t_complete(lvl):
    its = rnd.sample(T6, 3)
    body = (f"## Условие\n\n{CV} По каким аксиомным схемам $S^s_{{if}}$ получаются теоремные схемы (с. 91)? Восстановите списки "
            "оснований.\n\n" + "\n".join(f"{L[i]}) {n}. ${f}$" for i, (n, f, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) [{b}]" for i, (_, _, b) in enumerate(its)) + "\n\n## Решение\n\nС. 91: в квадратных скобках книга "
            "указывает лишь аксиомные и теоремные схемы $S^s_{if}$, позволяющие получить теорему.")
    return card(6, 6, lvl, "D", "complete", "sym", "short", "условность, теоремы", body, "с. 91, гл. 6, § 6", "S^s_if")


def deriv(kind, m):
    X, Y, Z = (V(m[c]) for c in "xyz")
    if kind == "T4":
        return (C(IF(X, Y), N(Y)), N(X)), [
            (IF(X, Y), IF(N(Y), N(X)), "A2"), (C(IF(X, Y), N(Y)), IF(X, Y), "$S^s$"),
            (C(IF(X, Y), N(Y)), IF(N(Y), N(X)), "R1: 2, 1"), (C(IF(X, Y), N(Y)), N(Y), "$S^s$"),
            (C(IF(X, Y), N(Y)), C(IF(N(Y), N(X)), N(Y)), "R2: 3, 4"), (C(IF(N(Y), N(X)), N(Y)), N(X), "A1"),
            (C(IF(X, Y), N(Y)), N(X), "R1: 5, 6")]
    if kind == "T6":
        return (C(IF(C(X, Y), Z), X), IF(Y, Z)), [
            (IF(C(X, Y), Z), IF(X, IF(Y, Z)), "A5"), (C(IF(C(X, Y), Z), X), IF(C(X, Y), Z), "$S^s$"),
            (C(IF(C(X, Y), Z), X), IF(X, IF(Y, Z)), "R1: 2, 1"), (C(IF(C(X, Y), Z), X), X, "$S^s$"),
            (C(IF(C(X, Y), Z), X), C(IF(X, IF(Y, Z)), X), "R2: 3, 4"), (C(IF(X, IF(Y, Z)), X), IF(Y, Z), "A1"),
            (C(IF(C(X, Y), Z), X), IF(Y, Z), "R1: 5, 6")]
    if kind == "chain":
        return (C(IF(X, Y), IF(Y, Z), X), Z), [
            (C(IF(X, Y), IF(Y, Z), X), C(IF(X, Y), IF(Y, Z)), "$S^s$"), (C(IF(X, Y), IF(Y, Z)), IF(X, Z), "A3"),
            (C(IF(X, Y), IF(Y, Z), X), IF(X, Z), "R1: 1, 2"), (C(IF(X, Y), IF(Y, Z), X), X, "$S^s$"),
            (C(IF(X, Y), IF(Y, Z), X), C(IF(X, Z), X), "R2: 3, 4"), (C(IF(X, Z), X), Z, "A1"),
            (C(IF(X, Y), IF(Y, Z), X), Z, "R1: 5, 6")]
    if kind == "split":
        return (IF(X, C(Y, Z)), IF(X, Y)), [
            (IF(X, C(Y, Z)), C(IF(X, Y), IF(X, Z)), "A4"), (C(IF(X, Y), IF(X, Z)), IF(X, Y), "$S^s$"),
            (IF(X, C(Y, Z)), IF(X, Y), "R1: 1, 2")]
    raise ValueError


def opaque(f, tab):
    k = f[0]
    if k in ("if", "ifn", "ifq", "all", "ex", "el"):
        key = repr(f)
        tab.setdefault(key, f"c{len(tab)}")
        return V(tab[key])
    if k == "v":
        return f
    if k == "neg":
        return N(opaque(f[1], tab))
    if k == "imp":
        return IMP(opaque(f[1], tab), opaque(f[2], tab))
    return (k, tuple(opaque(a, tab) for a in f[1]))


def check_lines(lines):
    for i, (a, b, w) in enumerate(lines):
        if w == "$S^s$":
            tab = {}
            A, B = opaque(a, tab), opaque(b, tab)
            assert Q.strong(A, B), (i, tex(a), tex(b))
        elif w.startswith("A"):
            pass
        elif w.startswith("R1"):
            j, k = [int(t) - 1 for t in w[4:].split(", ")]
            assert lines[j][0] == a and lines[j][1] == lines[k][0] and lines[k][1] == b, i
        elif w.startswith("R2"):
            j, k = [int(t) - 1 for t in w[4:].split(", ")]
            assert lines[j][0] == lines[k][0] == a and b == C(lines[j][1], lines[k][1]), i


def show(lines):
    return "\n".join(f"{i + 1}. ${ftex(a, b)}$ [{w}]" for i, (a, b, w) in enumerate(lines))


def deriv_card(lvl, typ="D", hide=None):
    kind = rnd.choice(["T4", "T6", "chain", "split"])
    m = ren()
    goal, lines = deriv(kind, m)
    check_lines(lines)
    if hide:
        hs = sorted(rnd.sample(range(len(lines)), min(hide, len(lines))))
        shown = "\n".join(f"{i + 1}. ${ftex(a, b)}$ [{'…' if i in hs else w}]" for i, (a, b, w) in enumerate(lines))
        body = (f"## Условие\n\n{CV} Восстановите пропущенные основания вывода в $S^s_{{if}}$ ($S^s$ — шаг по правилам общей теории "
                f"дедукции; R1 — транзитивность, R2 — объединение заключений).\n\n{shown}\n\n## Ответ\n\n" +
                "; ".join(f"{i + 1} — {lines[i][2]}" for i in hs) + f"\n\n## Решение\n\n{show(lines)}")
        return card(6, 6, lvl, "D", "complete", "sym", "short", "условность, вывод", body, "с. 90–91, гл. 6, § 6", "S^s_if")
    body = (f"## Условие\n\n{CV} Выведите в $S^s_{{if}}$ формулу ${ftex(*goal)}$ (шаги общей теории дедукции можно обозначать "
            f"«$S^s$»).\n\n## Ответ\n\nВывод из {len(lines)} шагов (см. решение).\n\n## Решение\n\n{show(lines)}")
    return card(6, 6, lvl, typ, "iso", "sym", "proof", "условность, вывод", body, "с. 90–91, гл. 6, § 6", "S^s_if")


def mt_if_card(lvl, typ="C", sysk="s"):
    """Недоказуемость по MT2/MT3 (S^s_if) или MT1 (S^w_if); доказуемость — аксиомы/теоремы."""
    its = []
    for kind in rnd.sample(["ax", "ax", "new", "cond"] if sysk == "s" else ["ax", "a9", "nocommon", "ax"], 4):
        X, Y, Z, Vv = meta4()
        if kind in ("ax", "a9"):
            n = "A9" if kind == "a9" else rnd.choice(list(AX)[:8])
            its.append((ax_inst(n, X, Y, Z, Vv), f"доказуема: схема {n}"))
        elif kind == "new":
            its.append(((C(IF(x, y), x), C(y, z)), "недоказуема: в заключение входит $z$, отсутствующее в посылке (MT2 § 6)"))
        elif kind == "cond":
            its.append(((C(x, y), IF(x, y)), "недоказуема: в заключение входит оператор условности, а в посылку нет (MT3 § 6)"))
        else:
            its.append(((IF(x, y), IF(z, v)), "недоказуема: нет общих элементарных высказываний (MT1 § 7)"))
    sysn = "S^s_{if}" if sysk == "s" else "S^w_{if}"
    body = (f"## Условие\n\n{CV} Доказуемы ли в ${sysn}$ формулы? Обоснуйте схемой или метатеоремой.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(*f)}$" for i, (f, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {w.split(':')[0]}" for i, (_, w) in enumerate(its)) + "\n\n## Решение\n\n" +
            "\n".join(f"{L[i]}) {w}." for i, (_, w) in enumerate(its)))
    return card(6, 6 if sysk == "s" else 7, lvl, typ, "open", "sym", "short", "условность, доказуемость", body,
                "с. 90–91, гл. 6, § 6–7", "S^s_if" if sysk == "s" else "S^w_if")


def if_e(lvl, sec=6):
    v_ = rnd.choice([(f"${ftex(C(x, y), IF(x, y))}$ — теорема $S^s_{{if}}$: это сильная тавтология, если $x \\rightarrow y$ понимать как $x \\supset y$",
                      "по MT3 § 6 (с. 90) оператор условности не может появиться в заключении, если его нет в посылке; кроме того, это "
                      "ошибочное утверждение § 3"),
                     (f"${ftex(IF(x, y), IF(x, C(y, z)))}$ доказуема по A4", "A4 идёт в другую сторону: $(x \\rightarrow yz) \\vdash (x \\rightarrow y)(x \\rightarrow z)$; "
                      "формула студента вводит новое $z$ и по MT2 § 6 недоказуема"),
                     (f"${ftex(C(IF(x, y), y), x)}$ доказуема по A1", "A1 — $(x \\rightarrow y)x \\vdash y$; «утверждение консеквента» — не схема "
                      "$S^s_{if}$"),
                     (f"${ftex(IF(x, y), IF(N(x), N(y)))}$ — это A2", "A2 — $(x \\rightarrow y) \\vdash (\\sim y \\rightarrow \\sim x)$ (контрапозиция), а "
                      "не обращение отрицаний")])
    body = (f"## Условие\n\n{CV} Студент: {v_[0]}. Найдите ошибку.\n\n## Ответ\n\nНеверно: {v_[1]}.\n\n## Решение\n\nС. 90–91.")
    return permute(card(6, sec, lvl, "E", "open", "sym", "short", "условность, диагностика", body, "с. 84–91, гл. 6, § 3–7", "S^s_if"), "xyzv")


def w_t1(lvl):
    body = (f"## Условие\n\n{CV} В $S^w_{{if}}$ (с. 91) доказуема T1: $(x \\rightarrow y) \\vdash (x \\rightarrow y \\vee z)$ [A2, A9, A2]. Восстановите "
            "вывод по этим схемам (шаги общей теории дедукции обозначайте $S^s$).\n\n## Ответ\n\n$(x \\rightarrow y) \\vdash (\\sim y \\rightarrow \\sim x)$ "
            "[A2]; $(\\sim y \\rightarrow \\sim x) \\vdash (\\sim y\\sim z \\rightarrow \\sim x)$ [A9]; $(\\sim y\\sim z \\rightarrow \\sim x) \\vdash "
            "(\\sim\\sim x \\rightarrow \\sim(\\sim y\\sim z))$ [A2]; замена равнозначных: $\\sim\\sim x$ на $x$, $\\sim(\\sim y\\sim z)$ на "
            "$y \\vee z$ [$S^s$]; R1.\n\n## Решение\n\nС. 91. Последний шаг — правило замены равнозначного (R3 общей теории "
            "дедукции).")
    return card(6, 7, lvl, "D", "complete", "sym", "proof", "условность, вывод", body, "с. 91, гл. 6, § 7", "S^w_if")


# ================= § 8–9: S⁵_if, S⁵*_if =================
def s5if_card(lvl, sec=8, typ="C"):
    its = []
    for want in rnd.sample([True, True, False, False], 4):
        for _ in range(500):
            a, b = G.rnd_f("xy", 2, "w"), G.rnd_f("xy", 2, "w")
            if Q.s5if_provable(a, b) == want and repr((a, b)) not in USED:
                USED.add(repr((a, b)))
                its.append((a, b))
                break
    sysn = "S^5_{if}" if sec == 8 else "S^{5*}_{if}"
    body = (f"## Условие\n\n{CV} Доказуемы ли в ${sysn}$ формулы? ($x$ и $y$ здесь без оператора условности.) Пользуйтесь MT2 и MT5 "
            f"§ 8 гл. 6{' и MT1 § 9' if sec == 9 else ''}.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(IF(a, b))}$" for i, (a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if Q.s5if_provable(a, b) else "нет") for i, (a, b) in enumerate(its)) +
            "\n\n## Решение\n\nMT2 (с. 92): если $\\vdash (x \\rightarrow y)$ доказуема, то $x \\supset y$ — тавтология; MT5 (с. 92): если "
            "$\\vdash (x \\supset y)$ доказуема в $S^5$ (то есть $x \\supset y$ — тавтология), то $\\vdash (x \\rightarrow y)$ доказуема в $S^5_{if}$" +
            (". MT1 § 9 (с. 94): формулы $\\vdash (x \\rightarrow y)$ доказуемы в $S^5_{if}$ и $S^{5*}_{if}$ одновременно" if sec == 9 else "") +
            ".\n" + "\n".join(f"{L[i]}) импликация с $\\supset$ вместо $\\rightarrow$ — " + ("тавтология." if Q.s5if_provable(a, b) else
                                                           "не тавтология: при " + G.SY.env_text(G.SY.counter(a, b)) + " — 0.")
                            for i, (a, b) in enumerate(its)))
    return card(6, sec, lvl, typ, "iso", "sym", "short", "условность, S5if", body, "с. 91–94, гл. 6, § 8–9",
                "S^5_if" if sec == 8 else "S^5*_if")


T8 = ["\\vdash ((x \\rightarrow y) \\rightarrow (xz \\rightarrow y))", "\\vdash (x\\sim y \\rightarrow \\sim(x \\rightarrow y))",
      "\\vdash ((x \\rightarrow y) \\rightarrow \\sim(x\\sim y))", "\\vdash ((xy \\rightarrow z)(x\\sim y \\rightarrow z) \\rightarrow (x \\rightarrow z))",
      "\\vdash (y \\rightarrow \\sim x \\vee x)", "\\vdash (\\sim yy \\rightarrow x)", "\\vdash (x \\rightarrow (y \\rightarrow x))",
      "\\vdash (x \\rightarrow (\\sim x \\rightarrow y))", "\\vdash ((x : y) \\rightarrow (x \\rightarrow \\sim y)(\\sim x \\rightarrow y))",
      "\\vdash ((x \\rightarrow \\sim y)(\\sim x \\rightarrow y) \\rightarrow (x : y))", "\\vdash ((x \\vee y) \\rightarrow (\\sim x \\rightarrow y)(\\sim y \\rightarrow x))",
      "\\vdash ((\\sim x \\rightarrow y) \\rightarrow (x \\vee y))", "\\vdash (x \\rightarrow x \\vee y)", "\\vdash ((x \\rightarrow y)(x \\rightarrow \\sim y) \\rightarrow \\sim x)",
      "\\vdash (x \\rightarrow y)(y \\rightarrow z) \\rightarrow (x \\rightarrow z)"]


def t8_rec(lvl):
    idx = rnd.sample(range(15), 4)
    body = (f"## Условие\n\n{CV} Восстановите формулы теоремных схем $S^5_{{if}}$ (с. 92) по номерам: " +
            ", ".join(f"T{i + 1}" for i in idx) + ". Подсказка: среди T1–T15 есть «парадоксы» § 10.\n\n## Ответ\n\n" +
            "; ".join(f"T{i + 1}: ${T8[i]}$" for i in idx) + "\n\n## Решение\n\nС. 92.")
    return card(6, 8, lvl, "R", "iso", "sym", "short", "условность, S5if", body, "с. 92, гл. 6, § 8", "S^5_if")


def mt34_card(lvl):
    a, b = G.rnd_f("xy", 1, "w"), G.rnd_f("xy", 1, "w")
    which = rnd.choice(["MT3", "MT4"])
    if which == "MT3":
        q = f"Доказуемы $\\vdash ({tex(a)} \\rightarrow {tex(b)})$ и $\\vdash {tex(a)}$. Что можно заключить по MT3 § 8?"
        r = f"$\\vdash {tex(b)}$ доказуема."
        s = "MT3 (с. 92): из $(x \\rightarrow y)x \\vdash y$ по R1 — $\\vdash ((x \\rightarrow y)x \\rightarrow y)$, и далее."
    else:
        q = f"Доказуемы $\\vdash ({tex(a)} \\rightarrow {tex(b)})$ и $\\vdash \\sim {tex(b) if b[0] in ('v',) else '(' + tex(b) + ')'}$. Что можно заключить по MT4 § 8?"
        r = f"$\\vdash \\sim {tex(a) if a[0] in ('v',) else '(' + tex(a) + ')'}$ доказуема."
        s = "MT4 (с. 92): доказательство как у MT3 с дополнением: по A2 $S^s_{if}$ доказуема $\\vdash (\\sim y \\rightarrow \\sim x)$."
    body = f"## Условие\n\n{CV} {q}\n\n## Ответ\n\n{r}\n\n## Решение\n\n{s}"
    return card(6, 8, lvl, "D", "iso", "sym", "short", "условность, S5if", body, "с. 92, гл. 6, § 8", "S^5_if")


def r1_card(lvl):
    n = rnd.choice(list(AX)[:8])
    a, b = ax_inst(n, *meta4())
    body = (f"## Условие\n\n{CV} В $S^s_{{if}}$ доказуема ${ftex(a, b)}$ ({n}). Какую формулу даёт правило R1 системы $S^5_{{if}}$ (с. 91)?\n\n"
            f"## Ответ\n\n$\\vdash ({tex(a)} \\rightarrow {tex(b)})$\n\n## Решение\n\nR1: если $x \\vdash y$, то $\\vdash (x \\rightarrow y)$.")
    return card(6, 8, lvl, "D", "iso", "sym", "short", "условность, S5if", body, "с. 91, гл. 6, § 8", "S^5_if")


def mt7_e(lvl, sec=8):
    for _ in range(300):
        a, b = G.rnd_f("xy", 1, "w"), G.rnd_f("xy", 1, "w")
        if not Q.s5if_provable(a, b):
            break
    body = (f"## Условие\n\n{CV} Студент: «$\\vdash ({tex(a)} \\rightarrow {tex(b)})$ доказуема в $S^5_{{if}}$ — ведь условные высказывания "
            "истинны чаще, чем материальные импликации». Проверьте.\n\n## Ответ\n\nНеверно: по MT2 § 8 (с. 92) если "
            f"$\\vdash (x \\rightarrow y)$ доказуема, то $x \\supset y$ — тавтология, а здесь при {G.SY.env_text(G.SY.counter(a, b))} импликация "
            "ложна. Кроме того, истинность $x \\rightarrow y$ влечёт истинность $x \\supset y$, а не наоборот (с. 88).\n\n## Решение\n\nMT2, MT7 "
            "(с. 92–93).")
    return card(6, sec, lvl, "E", "open", "sym", "short", "условность, S5if, диагностика", body, "с. 88, 92–93, гл. 6, § 4, 8",
                "S^5_if")


def mt7_card(lvl):
    t = rnd.choice(T8[:8] + T8[12:])
    t2 = t.replace("\\rightarrow", "\\supset")
    body = (f"## Условие\n\n{CV} Формула ${t}$ доказуема в $S^5_{{if}}$. Какая формула по MT7 § 8 (с. 93) доказуема в $S^5$?\n\n## Ответ\n\n"
            f"${t2}$\n\n## Решение\n\nMT7: все вхождения оператора условности заменяются на $\\supset$. Обратное MT7 неверно (с. 93).")
    return card(6, 8, lvl, "D", "iso", "sym", "short", "условность, S5if", body, "с. 93, гл. 6, § 8", "S^5_if")


S9T = ["\\vdash ((x \\rightarrow y)x \\rightarrow y)", "\\vdash ((x \\rightarrow y) \\rightarrow (\\sim y \\rightarrow \\sim x))",
       "\\vdash ((x \\rightarrow yz) \\rightarrow (x \\rightarrow y)(x \\rightarrow z))", "\\vdash ((xy \\rightarrow z) \\rightarrow (x \\rightarrow (y \\rightarrow z)))",
       "\\vdash ((x \\rightarrow (y \\rightarrow z)) \\rightarrow (xy \\rightarrow z))", "\\vdash ((x \\rightarrow y)(z \\rightarrow v) \\rightarrow (xz \\rightarrow yv))",
       "\\vdash ((x \\rightarrow y) \\vee (z \\rightarrow v) \\rightarrow (xz \\rightarrow y \\vee v))", "\\vdash ((x \\rightarrow y)(y \\rightarrow z) \\rightarrow (x \\rightarrow z))"]


def s9_rec(lvl):
    idx = rnd.sample(range(8), 3)
    body = (f"## Условие\n\n{CV} Какие аксиомные схемы $S^s_{{if}}$ (с. 90) соответствуют теоремным схемам $S^{{5*}}_{{if}}$ (с. 94)?\n\n" +
            "\n".join(f"{L[i]}) T{k + 1}. ${S9T[k]}$" for i, k in enumerate(idx)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ["A1", "A2", "A4", "A5", "A6", "A7", "A8", "A3"][k] for i, k in enumerate(idx)) +
            "\n\n## Решение\n\nT1–T8 $S^{5*}_{if}$ получаются из A1–A8 $S^s_{if}$ заменой $\\vdash$ на $\\rightarrow$ (с. 90, 94); "
            "поэтому по MT1 § 9 системы $S^5_{if}$ и $S^{5*}_{if}$ доказывают одни и те же $\\vdash (x \\rightarrow y)$.")
    return card(6, 9, lvl, "R" if lvl == 1 else "C", "iso", "sym", "short", "условность, S5*if", body, "с. 90, 93–94, гл. 6, § 6, 9",
                "S^5*_if")


def s9_ax(lvl):
    body = (f"## Условие\n\n{CV} Из чего получается система $S^{{5*}}_{{if}}$ (с. 93)? Выпишите её дополнительные схемы и правило.\n\n## Ответ\n\n"
            "К $S^5$ присоединяются A1. $(x \\rightarrow y)x \\vdash y$; A2. $(x \\rightarrow y)\\sim y \\vdash \\sim x$; A3. "
            "$\\vdash ((xy \\rightarrow z) \\rightarrow (x \\rightarrow (y \\rightarrow z)))$; R1. Если $x \\vdash y$, то $\\vdash (x \\rightarrow y)$.\n\n## Решение\n\nС. 93.")
    return card(6, 9, lvl, "D", "iso", "sym", "short", "условность, S5*if", body, "с. 93, гл. 6, § 9", "S^5*_if")


# ================= § 10–11 =================
PAR = ["\\vdash (x \\rightarrow (y \\rightarrow x))", "\\vdash (x \\rightarrow (\\sim x \\rightarrow y))", "\\vdash (x \\rightarrow y \\vee \\sim y)",
       "\\vdash (\\sim yy \\rightarrow x)"]


def par_card(lvl, typ="C"):
    its = rnd.sample(PAR, 2) + ["\\vdash ((x \\rightarrow y)x \\rightarrow y)", "\\vdash ((x \\rightarrow y)(y \\rightarrow z) \\rightarrow (x \\rightarrow z))"]
    rnd.shuffle(its)
    body = (f"## Условие\n\n{CV} Какие из формул § 10 гл. 6 (с. 94) называет «парадоксами» систем $S^i_{{if}}$?\n\n" +
            "\n".join(f"{L[i]}) ${f}$" for i, f in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("парадокс" if f in PAR else "нет") for i, f in enumerate(its)) +
            "\n\n## Решение\n\nС. 94: «парадоксы», подобные парадоксам материальной и строгой импликации: $\\vdash (x \\rightarrow (y \\rightarrow x))$, "
            "$\\vdash (x \\rightarrow (\\sim x \\rightarrow y))$, $\\vdash (x \\rightarrow y \\vee \\sim y)$, $\\vdash (\\sim yy \\rightarrow x)$.")
    return card(6, 10, lvl, typ, "iso", "sym", "short", "условность, парадоксы", body, "с. 94, гл. 6, § 10")


def par_fix(lvl, typ="D"):
    body = (f"## Условие\n\n{CV} Чем книга предлагает заменить A5 системы $S^s_{{if}}$ и A3 системы $S^{{5*}}_{{if}}$, чтобы исключить "
            "парадоксы (с. 95)? Каково ограничение?\n\n## Ответ\n\nA*5. $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$ и A*3. "
            "$\\vdash ((xy \\rightarrow z) \\rightarrow (x \\rightarrow (y \\rightarrow z)))$, где $\\vdash (x \\rightarrow z)$ и $\\vdash (y \\rightarrow z)$ "
            "недоказуемы.\n\n## Решение\n\nС. 95; можно придать вид $(xy \\rightarrow z)\\sim(x \\rightarrow z)\\sim(y \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$.")
    return card(6, 10, lvl, typ, "iso", "sym", "short", "условность, парадоксы", body, "с. 94–95, гл. 6, § 10")


def par_e(lvl):
    body = (f"## Условие\n\n{CV} Студент: «Если исключить из системы формулы $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$, "
            "парадоксы исчезнут и из реальных рассуждений». Найдите ошибку.\n\n## Ответ\n\nПо § 10 (с. 94) это «принципиально ничего "
            "не меняет»: интуитивно несомненно, что если $xy \\rightarrow z$ и $y$ истинно, то $x \\rightarrow z$; исключив парадоксы из "
            "системы, нельзя исключить их из ситуаций применения её правил.\n\n## Решение\n\nС. 94.")
    return permute(card(6, 10, lvl, "E", "open", "sym", "short", "условность, парадоксы, диагностика", body, "с. 94, гл. 6, § 10"), "xyzv")


def lit_rand(names):
    n = rnd.choice(names)
    return N(V(n)) if rnd.random() < 0.3 else V(n)


BASIS = {1: lambda a, b, c, d, e, f: (C(IF(a, b), c), d), 2: lambda a, b, c, d, e, f: (C(IF(a, b), IF(c, d)), IF(e, f)),
         3: lambda a, b, c, d, e, f: (C(IF(a, b), IF(c, d)), IF(C(a, c), C(b, d))),
         4: lambda a, b, c, d, e, f: (C(IF(a, b), IF(c, d)), IF(W(a, c), C(b, d))),
         5: lambda a, b, c, d, e, f: (C(IF(a, b), IF(c, d)), IF(C(a, c), W(b, d))),
         6: lambda a, b, c, d, e, f: (C(IF(a, b), IF(c, d)), IF(W(a, c), W(b, d))),
         7: lambda a, b, c, d, e, f: (W(IF(a, b), IF(c, d)), IF(C(a, c), C(b, d))),
         8: lambda a, b, c, d, e, f: (W(IF(a, b), IF(c, d)), IF(W(a, c), C(b, d))),
         9: lambda a, b, c, d, e, f: (W(IF(a, b), IF(c, d)), IF(C(a, c), W(b, d))),
         10: lambda a, b, c, d, e, f: (W(IF(a, b), IF(c, d)), IF(W(a, c), W(b, d))),
         11: lambda a, b, c, d, e, f: (IF(C(a, b), c), None), 12: lambda a, b, c, d, e, f: (IF(a, C(b, c)), None),
         13: lambda a, b, c, d, e, f: (IF(W(a, b), c), None), 14: lambda a, b, c, d, e, f: (IF(a, W(b, c)), None),
         15: lambda a, b, c, d, e, f: (IF(C(a, b), C(c, d)), None), 16: lambda a, b, c, d, e, f: (IF(C(a, b), W(c, d)), None),
         17: lambda a, b, c, d, e, f: (IF(W(a, b), C(c, d)), None), 18: lambda a, b, c, d, e, f: (IF(W(a, b), W(c, d)), None)}


def basis_inst(n):
    ls = [lit_rand("abcd") for _ in range(6)]
    p, q = BASIS[n](*ls)
    if q is None:
        q = rnd.choice([W(ls[0], ls[1]), C(ls[2], N(ls[3]) if ls[3][0] == "v" else ls[3]), IF(ls[0], ls[2])])
    return p, q


def basis_card(lvl, typ="C"):
    its = []
    for n in rnd.sample(range(1, 19), 3):
        its.append((basis_inst(n), n))
    bad = [(C(IF(IF(V("a"), V("b")), V("c")), V("d")), V("a")), (IF(V("a"), IF(V("b"), V("c"))), V("a")),
           (C(IF(C(V("a"), V("b")), V("c")), V("a")), IF(V("b"), V("c")))]
    its.append((rnd.choice(bad), None))
    rnd.shuffle(its)
    body = ("## Условие\n\nБуквы $a, b, c, d$ — элементарные высказывания. Какие формулы — базисные формулы следования теории "
            "условных высказываний (D1 § 11 гл. 6, с. 96–97)? Укажите номер вида.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(*f)}$" for i, (f, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + (f"вид {n}" if n else "не базисная") for i, (_, n) in enumerate(its)) +
            "\n\n## Решение\n\nD1 (с. 96–97): $a, b, c, d, e, f$ — элементарные высказывания или их отрицания; $z$ — высказывания из "
            "них с операторами $\\cdot$, $\\vee$, $\\sim$, $\\rightarrow$. Вложенные условные высказывания в антецедентах и консеквентах "
            "базисных формул не встречаются.")
    return card(6, 11, lvl, typ, "iso", "sym", "short", "условность, полнота", body, "с. 96–97, гл. 6, § 11")


def full_e(lvl):
    v_ = rnd.choice([("«$(xy \\rightarrow z) \\vdash (xy \\rightarrow y)$ — тавтология без новых элементарных высказываний в заключении, "
                      "значит, полная система обязана её доказывать»", "такая формула неприемлема как правило следования: истинность "
                      "$xy \\rightarrow y$ установлена не путём логического следования из $xy \\rightarrow z$ (с. 95–96); поэтому принято более "
                      "узкое понятие полноты (D2)"),
                     ("«Достаточная полнота (D2) требует доказуемости всех тавтологий»", "D2 (с. 97) требует доказуемости базисных "
                      "формул, являющихся тавтологиями и непарадоксальных, и формул, получаемых из них подстановкой")])
    body = f"## Условие\n\nСтудент: {v_[0]}. Найдите ошибку.\n\n## Ответ\n\nНеверно: {v_[1]}.\n\n## Решение\n\nГл. 6, § 11 (с. 95–97)."
    return permute(card(6, 11, lvl, "E", "open", "sym", "short", "условность, полнота, диагностика", body, "с. 95–97, гл. 6, § 11"), "xyzv")


def full_q(lvl):
    qs = [("Чем решается проблема полноты для формул вида $\\vdash (x \\rightarrow y)$?", "Метатеоремами, сформулированными выше (§ 8–9; с. 95)."),
          ("Почему критерии полноты общей теории дедукции недостаточны для теории условных высказываний?",
           "Есть тавтологии, непарадоксальные в смысле общей теории дедукции, неприемлемые как правила следования, например "
           "$(xy \\rightarrow z) \\vdash (xy \\rightarrow y)$ (с. 95–96)."),
          ("Как выполняется пункт 2 D2 (доказуемость формул, полученных из базисных подстановкой)?", "Благодаря использованию "
           "аксиомных схем (с. 97).")]
    q, a = rnd.choice(qs)
    body = f"## Условие\n\n{q}\n\n## Ответ\n\n{a}\n\n## Решение\n\nГл. 6, § 11."
    return card(6, 11, lvl, "C", "iso", "meta", "text", "условность, полнота", body, "с. 95–97, гл. 6, § 11")


# ================= гл. 7 =================
TT = "Буквы $a, b, c, d$ — термины (субъекты и одноместные предикаты); $x, y$ — высказывания."


def qf_rand(depth=2, terms="abcd"):
    if depth == 0 or rnd.random() < 0.3:
        s, p = rnd.sample(terms, 2)
        return EL(s, p)
    k = rnd.choice(["neg", "conj", "wdis", "all", "ex", "all"])
    if k == "neg":
        return N(qf_rand(depth - 1, terms))
    if k in ("all", "ex"):
        return (k, rnd.choice(terms[:2]), qf_rand(depth - 1, terms))
    return (k, (qf_rand(depth - 1, terms), qf_rand(depth - 1, terms)))


def free_card(lvl, typ="C"):
    f = None
    while f is None or not Q.groups(f):
        f = qf_rand(3)
    ts = sorted(Q.terms(f))
    body = (f"## Условие\n\n{TT} Дано высказывание ${tex(f)}$. Для каждого термина укажите: свободен ли он в высказывании по D4 и есть "
            "ли у него свободные вхождения по D5 (§ 1 гл. 7, с. 98–99).\n\n## Ответ\n\n" +
            "; ".join(f"${t}$ — " + ("свободен" if Q.free_d4(t, f) else "не свободен") + ", " +
                      ("есть свободные вхождения" if Q.free_occ(t, f) else "свободных вхождений нет") for t in ts) +
            "\n\n## Решение\n\nD4: термин свободен, если входит в высказывание, а кванторные группы с ним не входят. D5: вхождение "
            "связано, если стоит в области действия кванторной группы с этим термином; иначе свободно.")
    return card(7, 1, lvl, typ, "iso", "sym", "short", "кванторы, свободные термины", body, "с. 98–99, гл. 7, § 1")


def deg_card7(lvl, typ="C"):
    its = []
    for _ in range(4):
        q = rnd.choice(["all", "ex"])
        t = rnd.choice("ab")
        g = qf_rand(1)
        its.append((q, t, g))
    show = lambda q, t, g: tex((q, t, g))
    body = (f"## Условие\n\n{TT} Вырождена ли кванторная группа в каждом высказывании (D6 § 1 гл. 7, с. 99)?\n\n" +
            "\n".join(f"{L[i]}) ${show(*it)}$" for i, it in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("вырождена" if Q.degenerate(it) else "не вырождена") for i, it in enumerate(its)) +
            "\n\n## Решение\n\nD6: $(Ka)$ вырождена в $(Ka)x$, если в $x$ нет свободных вхождений $a$.")
    return card(7, 1, lvl, typ, "iso", "sym", "short", "кванторы, вырожденные группы", body, "с. 99, гл. 7, § 1")


def qf_card(lvl, sec=1, typ="D"):
    a, b = qf_rand(2), qf_rand(2)
    while not (Q.groups(a) or Q.groups(b)):
        a, b = qf_rand(2), qf_rand(2)
    body = (f"## Условие\n\n{TT} Запишите бескванторную форму (D7 § 1 гл. 7) формулы ${ftex(a, b)}$.\n\n## Ответ\n\n"
            f"${ftex(Q.qfree(a), Q.qfree(b))}$\n\n## Решение\n\nD7 (с. 99): исключаются все кванторные группы.")
    return card(7, sec, lvl, typ, "iso", "sym", "short", "кванторы, бескванторная форма", body, "с. 99, гл. 7, § 1")


def wf7(lvl, typ="R"):
    its = [("(a \\leftarrow b)", "элементарное высказывание, если $a$ — субъект, $b$ — одноместный предикат (D1)"),
           ("(\\forall a)(a \\leftarrow b)", "высказывание (D2, п. 3)"), ("(\\exists b)(a \\leftarrow b)", "высказывание: $b$ — термин (предикат) (D2, п. 3)"),
           ("(\\forall a)", "кванторная группа (D3), не высказывание"), ("(\\forall x)(a \\leftarrow b)", "не высказывание: $x$ — высказывание, "
            "а кванторная группа образуется с термином (D3)"), ("\\sim(\\exists a)\\sim(a \\leftarrow b)", "высказывание (D2, пп. 2–3)")]
    pick = rnd.sample(its, 4)
    body = (f"## Условие\n\n{TT} Что представляет собой каждое выражение по § 1 гл. 7 (с. 98)?\n\n" +
            "\n".join(f"{L[i]}) ${e}$" for i, (e, _) in enumerate(pick)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {d}" for i, (_, d) in enumerate(pick)) + "\n\n## Решение\n\nD1–D3 (с. 98).")
    return card(7, 1, lvl, typ, "iso", "sym", "short", "кванторы, определения", body, "с. 98, гл. 7, § 1")


AQ = {"A1": "(\\forall a)x \\vdash x", "A2": "x \\vdash (\\exists a)x", "A3": "(\\forall a)x(\\exists a)y \\vdash (\\exists a)(xy)",
      "A4": "(\\forall a)(x \\vee y) \\vdash (\\forall a)x \\vee (\\exists a)y", "A5": "(\\exists a)x \\vdash (\\forall a)x, где $a$ не входит свободно в $x$",
      "A6": "(\\forall a)x \\vdash \\sim(\\exists a)\\sim x", "A7": "\\sim(\\exists a)\\sim x \\vdash (\\forall a)x"}


def aq_inst(n, X, Y, a):
    return {"A1": (ALL(a, X), X), "A2": (X, EX(a, X)), "A3": (C(ALL(a, X), EX(a, Y)), EX(a, C(X, Y))),
            "A4": (ALL(a, W(X, Y)), W(ALL(a, X), EX(a, Y))), "A5": (EX(a, X), ALL(a, X)), "A6": (ALL(a, X), N(EX(a, N(X)))),
            "A7": (N(EX(a, N(X))), ALL(a, X))}[n]


def aq_rec(lvl):
    names = rnd.sample([n for n in AQ if n != "A5"], 4)
    its = []
    for n in names:
        X, Y = EL(*rnd.sample("abcd", 2)), EL(*rnd.sample("abcd", 2))
        its.append((n, aq_inst(n, X, Y, rnd.choice("ab"))))
    body = (f"## Условие\n\n{TT} Каким аксиомным схемам $S^s_{{cq}}$ (с. 99) соответствуют формулы?\n\n" +
            "\n".join(f"{L[i]}) ${ftex(*f)}$" for i, (_, f) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {n}" for i, (n, _) in enumerate(its)) + "\n\n## Решение\n\n" + "; ".join(f"{n}: ${AQ[n]}$" for n in names) + ".")
    return card(7, 2, lvl, "R" if lvl == 1 else "C", "iso", "sym", "short", "кванторы, аксиомы", body, "с. 99, гл. 7, § 2", "S^s_cq")


def a5_card(lvl, typ="C"):
    its = []
    for _ in range(4):
        X = qf_rand(1)
        a = rnd.choice("ab")
        its.append((a, X))
    body = (f"## Условие\n\n{TT} Является ли формула примером схемы A5 $S^s_{{cq}}$ ($(\\exists a)x \\vdash (\\forall a)x$, где $a$ не входит "
            "свободно в $x$)?\n\n" + "\n".join(f"{L[i]}) ${ftex(EX(a, X), ALL(a, X))}$" for i, (a, X) in enumerate(its)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[i]}) " + ("да" if not Q.free_occ(a, X) else f"нет: ${a}$ входит свободно")
                                           for i, (a, X) in enumerate(its)) + "\n\n## Решение\n\nС. 99; D5 (с. 99).")
    return card(7, 2, lvl, typ, "iso", "sym", "short", "кванторы, A5", body, "с. 99, гл. 7, § 2", "S^s_cq")


def rq_card(lvl):
    X, Y = EL(*rnd.sample("abcd", 2)), EL(*rnd.sample("abcd", 2))
    base = rnd.choice([(C(X, Y), X, "$S^s$"), (C(X, Y), C(Y, X), "$S^s$"), (X, W(X, Y), None)])
    a = rnd.choice("ab")
    r = rnd.choice(["R1", "R2"])
    if base[2] is None:
        base = (C(X, Y), Y, "$S^s$")
    p, c = base[0], base[1]
    out = (ALL(a, p), ALL(a, c)) if r == "R1" else (EX(a, p), EX(a, c))
    body = (f"## Условие\n\n{TT} В $S^s$ доказуема ${ftex(p, c)}$. Что даёт правило {r} системы $S^s_{{cq}}$ с термином ${a}$ (с. 100)?\n\n"
            f"## Ответ\n\n${ftex(*out)}$\n\n## Решение\n\nR1: если $x \\vdash y$, то $(\\forall a)x \\vdash (\\forall a)y$; R2: если $x \\vdash y$, то "
            "$(\\exists a)x \\vdash (\\exists a)y$.")
    return card(7, 2, lvl, "D", "iso", "sym", "short", "кванторы, правила", body, "с. 100, гл. 7, § 2", "S^s_cq")


DQ = [("(\\forall a)x \\vdash (\\exists a)x", ["$(\\forall a)x \\vdash x$ [A1]", "$x \\vdash (\\exists a)x$ [A2]", "$(\\forall a)x \\vdash (\\exists a)x$ [R1 $S^s$: 1, 2]"]),
      ("(\\forall a)(xy) \\vdash (\\forall a)x", ["$xy \\vdash x$ [$S^s$]", "$(\\forall a)(xy) \\vdash (\\forall a)x$ [R1: 1]"]),
      ("(\\exists a)(xy) \\vdash (\\exists a)y", ["$xy \\vdash y$ [$S^s$]", "$(\\exists a)(xy) \\vdash (\\exists a)y$ [R2: 1]"]),
      ("(\\forall a)x(\\exists a)y \\vdash (\\exists a)(yx)", ["$(\\forall a)x(\\exists a)y \\vdash (\\exists a)(xy)$ [A3]", "$xy \\vdash yx$ [$S^s$]",
                                                              "$(\\exists a)(xy) \\vdash (\\exists a)(yx)$ [R2: 2]", "$(\\forall a)x(\\exists a)y \\vdash (\\exists a)(yx)$ [R1 $S^s$: 1, 3]"]),
      ("(\\forall a)(\\forall b)x \\vdash x", ["$(\\forall a)(\\forall b)x \\vdash (\\forall b)x$ [A1]", "$(\\forall b)x \\vdash x$ [A1]",
                                               "$(\\forall a)(\\forall b)x \\vdash x$ [R1 $S^s$: 1, 2]"]),
      ("x \\vdash (\\exists a)(\\exists b)x", ["$x \\vdash (\\exists b)x$ [A2]", "$(\\exists b)x \\vdash (\\exists a)(\\exists b)x$ [A2]",
                                               "$x \\vdash (\\exists a)(\\exists b)x$ [R1 $S^s$: 1, 2]"]),
      ("\\sim(\\exists a)\\sim x \\vdash (\\exists a)x", ["$\\sim(\\exists a)\\sim x \\vdash (\\forall a)x$ [A7]", "$(\\forall a)x \\vdash x$ [A1]",
                                                         "$x \\vdash (\\exists a)x$ [A2]", "$\\sim(\\exists a)\\sim x \\vdash x$ [R1 $S^s$: 1, 2]",
                                                         "$\\sim(\\exists a)\\sim x \\vdash (\\exists a)x$ [R1 $S^s$: 4, 3]"])]


def dq_card(lvl, typ="D", hide=False):
    goal, steps = rnd.choice(DQ)
    if hide:
        k = rnd.randrange(len(steps))
        shown = "\n".join(f"{i + 1}. " + (re.sub(r"\[.*\]$", "[…]", s) if i == k else s) for i, s in enumerate(steps))
        body = (f"## Условие\n\n{TT} Восстановите пропущенное основание в выводе ${goal}$ в $S^s_{{cq}}$ (R1 $S^s$ — транзитивность общей "
                f"теории дедукции).\n\n{shown}\n\n## Ответ\n\nШаг {k + 1}: {re.search(r'\[(.*)\]$', steps[k]).group(1)}\n\n## Решение\n\n" +
                "\n".join(f"{i + 1}. {s}" for i, s in enumerate(steps)))
        return card(7, 2, lvl, "D", "complete", "sym", "short", "кванторы, вывод", body, "с. 99–100, гл. 7, § 2", "S^s_cq")
    body = (f"## Условие\n\n{TT} Выведите в $S^s_{{cq}}$ формулу ${goal}$.\n\n## Ответ\n\nВывод из {len(steps)} шагов (см. решение).\n\n"
            "## Решение\n\n" + "\n".join(f"{i + 1}. {s}" for i, s in enumerate(steps)))
    return card(7, 2, lvl, typ, "iso", "sym", "proof", "кванторы, вывод", body, "с. 99–100, гл. 7, § 2", "S^s_cq")


def unprov7(lvl, typ="C", sec=2):
    its = []
    for kind in rnd.sample(["new", "qf", "ax", "ax"], 4):
        if kind == "new":
            p = rnd.choice([(ALL("a", EL("a", "b")), EL("c", "b")), (EL("c", "b"), EX("a", EL("a", "b")))])
            its.append((p, "нет: в заключение входит термин, отсутствующий в посылке (MT2 § 3)"))
        elif kind == "qf":
            X, Y = EL("a", "b"), EL("a", "c")
            p = rnd.choice([(ALL("a", W(X, Y)), ALL("a", X)), (EX("a", X), C(X, Y)), (ALL("a", X), N(X))])
            its.append((p, "нет: бескванторная форма $" + ftex(Q.qfree(p[0]), Q.qfree(p[1])) + "$ недоказуема в $S^s$ (MT3 § 3)"))
            assert not Q.strong(Q.qfree(p[0]), Q.qfree(p[1]))
        else:
            n = rnd.choice(["A1", "A2", "A3", "A4", "A6", "A7"])
            p = aq_inst(n, EL("a", "b"), EL("a", "c"), "a")
            its.append((p, f"да: схема {n}"))
    body = (f"## Условие\n\n{TT} Доказуемы ли формулы в $S^s_{{cq}}$? Обоснуйте схемой или метатеоремой § 3.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(*p)}$" for i, (p, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) {w.split(':')[0]}" for i, (_, w) in enumerate(its)) + "\n\n## Решение\n\n" +
            "\n".join(f"{L[i]}) {w}." for i, (_, w) in enumerate(its)))
    return card(7, sec, lvl, typ, "open", "sym", "short", "кванторы, доказуемость", body, "с. 99–100, гл. 7, § 2–3", "S^s_cq")


def q_e(lvl, sec=2):
    v_ = rnd.choice([("$(\\exists a)(a \\leftarrow b) \\vdash (\\forall a)(a \\leftarrow b)$ — пример A5", "в A5 $a$ не должен входить свободно в $x$, "
                      "а здесь $a$ входит свободно в $(a \\leftarrow b)$ (с. 99)"),
                     ("$(\\forall a)(a \\leftarrow b) \\vdash (c \\leftarrow b)$ — пример A1: из общего — частное", "A1 — $(\\forall a)x \\vdash x$: "
                      "заключение совпадает с $x$; подстановка $c$ вместо $a$ не предусмотрена, а формула недоказуема по MT2 § 3 (с. 100)"),
                     ("$(\\forall a)(x \\vee y) \\vdash (\\forall a)x \\vee (\\forall a)y$ — пример A4", "A4 — $(\\forall a)(x \\vee y) \\vdash (\\forall a)x \\vee (\\exists a)y$ "
                      "(с. 99)"),
                     ("$(\\exists a)x(\\exists a)y \\vdash (\\exists a)(xy)$ — пример A3", "A3 — $(\\forall a)x(\\exists a)y \\vdash (\\exists a)(xy)$; с двумя "
                      "кванторами существования формула неверна (с. 99)")])
    body = f"## Условие\n\n{TT} Студент: {v_[0]}. Найдите ошибку.\n\n## Ответ\n\nНеверно: {v_[1]}.\n\n## Решение\n\nГл. 7, § 2–3."
    return permute(card(7, sec, lvl, "E", "open", "sym", "short", "кванторы, диагностика", body, "с. 99–100, гл. 7, § 2–3", "S^s_cq"), "abcd")


QFA = [("A1", "x \\vdash x"), ("A2", "x \\vdash x"), ("A3", "xy \\vdash xy"), ("A4", "x \\vee y \\vdash x \\vee y"), ("A5", "x \\vdash x"),
       ("A6", "x \\vdash \\sim\\sim x"), ("A7", "\\sim\\sim x \\vdash x")]


def qfa_card(lvl, typ="D"):
    its = rnd.sample(QFA, 4)
    body = (f"## Условие\n\n{TT} Запишите бескванторные формы аксиомных схем $S^s_{{cq}}$ и объясните, почему отсюда следует "
            "непротиворечивость (§ 4 гл. 7).\n\n" + "\n".join(f"{L[i]}) {n}. ${AQ[n].split(',')[0]}$" for i, (n, _) in enumerate(its)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[i]}) ${f}$" for i, (_, f) in enumerate(its)) +
            "\n\n## Решение\n\nС. 100–101: бескванторные формы аксиом — теоремы $S^s$, а правила вывода из бескванторных формул "
            "$x \\vdash y$ дают только сами эти формулы; значит, бескванторные формы доказуемых формул доказуемы в $S^s$ (тавтологии).")
    return card(7, 4, lvl, typ, "iso", "sym", "short", "кванторы, непротиворечивость", body, "с. 100–101, гл. 7, § 4", "S^s_cq")


def mt1_7(lvl, typ="C"):
    its = []
    for kind in rnd.sample(["ok", "ok", "new", "new"], 4):
        if kind == "ok":
            n = rnd.choice(["A1", "A2", "A3", "A6", "A7"])
            its.append((aq_inst(n, EL("a", "b"), EL("a", "c"), "a"), True))
        else:
            its.append(((rnd.choice([ALL("a", EL("a", "b")), EL("a", "b")]), rnd.choice([EL("a", "c"), EX("a", EL("a", "c"))])), False))
    els = lambda f: sorted({k.replace("←", " \\leftarrow ") for k in Q.atoms(f)})
    body = (f"## Условие\n\n{TT} Удовлетворяют ли формулы условию непарадоксальности MT1 § 3 гл. 7: в заключение не входят элементарные "
            "высказывания (в смысле теории кванторов), отсутствующие в посылке?\n\n" +
            "\n".join(f"{L[i]}) ${ftex(*p)}$" for i, (p, _) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if ok else "нет") for i, (_, ok) in enumerate(its)) + "\n\n## Решение\n\n" +
            "\n".join(f"{L[i]}) посылка: " + ", ".join(f"$({e})$" for e in els(p[0])) + "; заключение: " +
                      ", ".join(f"$({e})$" for e in els(p[1])) + "." for i, (p, _) in enumerate(its)) +
            "\n\nС. 100: если отбросить кванторные группы и отрицания и исключить повторения, в аксиомах посылка и заключение "
            "содержат одни и те же высказывания; правила сохраняют это свойство.")
    return card(7, 3, lvl, typ, "iso", "sym", "short", "кванторы, непарадоксальность", body, "с. 100, гл. 7, § 3", "S^s_cq")


def mt3_7(lvl, typ="C"):
    a, b = qf_rand(2), qf_rand(2)
    while not Q.groups(a):
        a, b = qf_rand(2), qf_rand(2)
    qa, qb = Q.qfree(a), Q.qfree(b)
    ok = Q.strong(qa, qb)
    body = (f"## Условие\n\n{TT} Что можно сказать по MT3 § 3 гл. 7 о доказуемости в $S^s_{{cq}}$ формулы ${ftex(a, b)}$?\n\n## Ответ\n\n" +
            (f"Бескванторная форма ${ftex(qa, qb)}$ недоказуема в $S^s$, поэтому формула недоказуема в $S^s_{{cq}}$." if not ok else
             f"Бескванторная форма ${ftex(qa, qb)}$ доказуема в $S^s$; MT3 даёт лишь необходимое условие — вопрос остаётся открытым.") +
            "\n\n## Решение\n\nMT3 (с. 100): если $x \\vdash y$ доказуема в $S^s_{cq}$, то её бескванторная форма доказуема в $S^s$. "
            "Элементарные высказывания $(a \\leftarrow b)$ рассматриваются как элементарные высказывания $S^s$.")
    return card(7, 3, lvl, typ, "open", "sym", "short", "кванторы, MT3", body, "с. 100, гл. 7, § 3", "S^s_cq")


def indep7(lvl, typ="D"):
    v_ = rnd.choice([("A1", "$(\\forall a)(a \\leftarrow b) \\vdash (a \\leftarrow b)$", "термин $a$ входит в заключение свободно, а в посылку — нет; "
                      "формула имеет значение 0"),
                     ("A2", "$(a \\leftarrow b) \\vdash (\\exists a)(a \\leftarrow b)$", "термин $a$ входит в посылку свободно, а в заключение — нет; "
                      "формула имеет значение 0")])
    body = (f"## Условие\n\n{TT} По исключающему семантическому правилу для {v_[0]} (§ 5 гл. 7, с. 101) найдите значение формулы {v_[1]}.\n\n"
            f"## Ответ\n\n0: {v_[2]}.\n\n## Решение\n\nС. 101: исключающее правило применяется первым, затем общее (прочие формулы "
            "равнозначны своим бескванторным формам).")
    return card(7, 5, lvl, typ, "iso", "sym", "short", "кванторы, независимость", body, "с. 101, гл. 7, § 5", "S^s_cq")


# ================= сборка =================
def build(ch, sec, levels, diag, makers):
    out, nd = [], 0
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            if lvl >= 8:
                continue
            d = nd < diag and lvl >= 2 and (i + lvl) % 2 == 0
            c = fresh(lambda: makers(lvl, d, i))
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def m602(lvl, d, i):
    if d:
        return ifvs_e(lvl)
    if lvl == 7:
        return bad_good_card(7, "S", nat=True).replace("chapter: 6\nsection: 3", "chapter: 6\nsection: 2")
    return ifvs_card(lvl, "C")


def m603(lvl, d, i):
    if d:
        return bad_e(lvl, nat=i % 2 == 0)
    if lvl == 1:
        return rule_card(1).replace("chapter: 6\nsection: 4", "chapter: 6\nsection: 3") if i else imp_taut_card(1).replace("type: D", "type: R")
    if lvl == 2:
        return imp_taut_card(2)
    if lvl == 7:
        return cmp_card(7) if i % 2 else bad_good_card(7, "S", nat=True)
    return bad_good_card(lvl, "C", nat=(i % 2 == 1))


def m604(lvl, d, i):
    if d:
        return interp_e(lvl)
    if lvl == 1:
        return rule_card(1)
    if lvl <= 3:
        return sit_card(lvl) if i % 2 == 0 else rule_card(lvl).replace("type: R", "type: C")
    if lvl == 7:
        return cmp_card(7).replace("chapter: 6\nsection: 3", "chapter: 6\nsection: 4")
    return ex4_card(lvl)


def m605(lvl, d, i):
    if d:
        return an_e(lvl)
    if lvl == 1:
        return an_rec(1)
    return an_taut(lvl, "S" if lvl == 7 else "C")


def m606(lvl, d, i):
    if d:
        return if_e(lvl)
    if lvl == 1:
        return ax_rec(1)
    if lvl == 2:
        return ax_sub(2)
    if lvl == 3:
        return [ax_rec, ax_sub, t_complete][i % 3](3)
    if lvl == 4:
        return deriv_card(4, hide=2) if i % 2 == 0 else t_complete(4)
    if lvl == 5:
        return deriv_card(5) if i % 2 == 0 else mt_if_card(5)
    if lvl == 6:
        return mt_if_card(6)
    return bad_good_card(7, "S").replace("chapter: 6\nsection: 3", "chapter: 6\nsection: 6")


def m607(lvl, d, i):
    if d:
        return if_e(lvl, 7)
    if lvl == 1:
        return ax_rec(1, "S^w_{if}", True)
    if lvl <= 3:
        return ax_sub(lvl, True)
    if lvl == 4:
        return w_t1(4)
    if lvl == 7:
        return mt_if_card(7, "S", "w")
    return mt_if_card(lvl, "C", "w")


def m608(lvl, d, i):
    if d:
        return mt7_e(lvl) if i % 2 == 0 else if_e(lvl, 8).replace('system: "S^s_if"', 'system: "S^5_if"')
    if lvl == 1:
        return t8_rec(1)
    if lvl == 2:
        return r1_card(2) if i % 2 else t8_rec(2).replace("type: R", "type: D")
    if lvl == 3:
        return [r1_card, mt7_card, mt34_card][i % 3](3)
    if lvl == 4:
        return [mt34_card, mt7_card, s5if_card][i % 3](4)
    if lvl == 7:
        return s5if_card(7, 8, "S")
    return s5if_card(lvl)


def m609(lvl, d, i):
    if d:
        return mt7_e(lvl, 9).replace('system: "S^5_if"', 'system: "S^5*_if"').replace("S^5_{if}$ — ведь", "S^{5*}_{if}$ — ведь")
    if lvl == 1:
        return s9_rec(1)
    if lvl == 2:
        return s9_ax(2) if i == 0 else s9_rec(2)
    if lvl in (3, 4):
        return s9_rec(lvl) if i % 2 else s5if_card(lvl, 9)
    if lvl == 7:
        return s5if_card(7, 9, "S")
    return s5if_card(lvl, 9)


def m610(lvl, d, i):
    if d:
        return par_e(lvl)
    if lvl in (1, 2):
        return par_card(lvl, "R" if lvl == 1 else "C")
    if lvl == 3:
        return par_fix(3)
    return par_card(lvl, "S" if lvl == 7 else "C")


def m611(lvl, d, i):
    if d:
        return full_e(lvl)
    if lvl in (6, 7) and i == 0:
        return full_q(lvl)
    return basis_card(lvl, "S" if lvl == 7 else "C")


def m701(lvl, d, i):
    if d:
        return q_e(lvl, 1).replace('system: "S^s_cq"\n', "")
    if lvl == 1:
        return wf7(1)
    if lvl == 2:
        return [wf7, free_card, deg_card7][i % 3](2)
    if lvl == 3:
        return [free_card, deg_card7, qf_card][i % 3](3)
    return [free_card, qf_card, deg_card7][i % 3](lvl)


def m702(lvl, d, i):
    if d:
        return q_e(lvl)
    if lvl == 1:
        return aq_rec(1)
    if lvl == 2:
        return aq_rec(2) if i % 2 else rq_card(2)
    if lvl == 3:
        return [a5_card, rq_card, aq_rec][i % 3](3)
    if lvl == 4:
        return dq_card(4, hide=True) if i % 2 == 0 else a5_card(4)
    if lvl == 5:
        return dq_card(5) if i % 2 == 0 else unprov7(5)
    if lvl == 6:
        return unprov7(6)
    return qfa_card(7, "S").replace("section: 4", "section: 2")


def m703(lvl, d, i):
    if d:
        return q_e(lvl, 3)
    if lvl in (3, 4):
        return mt1_7(lvl)
    if lvl == 7:
        return mt3_7(7, "S")
    return mt3_7(lvl) if i % 2 else unprov7(lvl, "C", 3)


def m704(lvl, d, i):
    if d:
        return q_e(lvl, 4)
    if lvl <= 4:
        return qfa_card(lvl)
    if lvl == 7:
        return qf_card(7, 4, "S")
    return mt3_7(lvl).replace("section: 3", "section: 4")


def m705(lvl, d, i):
    return indep7(lvl) if lvl != 3 else qfa_card(3, "C").replace("section: 4", "section: 5")


def mixed(sec, levels, diag, src, kinds):
    out, nd = [], 0
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            if lvl >= 8:
                continue
            d = nd < diag and lvl in (3, 4, 5, 6) and i % 2 == 0
            k = kinds[(i + lvl) % len(kinds)]

            def mk():
                if k == "coord":
                    return G16.err_card(6, lvl) if d else G16.push_card(3, lvl)
                if k == "if":
                    return interp_e(lvl) if d else (sit_card(lvl) if lvl <= 3 else ex4_card(lvl))
                if k == "n":
                    return G.n_cards(None)[min(lvl, 5) % 5] if False else an_taut(lvl)
                cfg = G.mk(17, sec, k, ["c", "w"][i % 2], G.SYSTEX[k], None, "смешанный", "смешанный набор", G.SY.MT[k],
                           G.SY.MT[k], [], 0)
                return G.make(cfg, lvl, d, i, None)
            c = fresh(mk)
            for st in ("iso", "open", "transfer", "vary", "complete"):
                c = c.replace(f"step: {st}\n", "step: mixed\n")
            c = re.sub(r'source: ".*"', f'source: "{src}"', c, count=1)
            c = re.sub(r"chapter: \d+\nsection: \d+", f"chapter: 17\nsection: {sec}", c, count=1)
            c = re.sub(r'system: ".*"\n', "", c, count=1)
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def main():
    cards = []
    cards += build(6, 2, [0, 0, 1, 0, 1, 1, 2], 1, m602)
    cards += build(6, 3, [2, 2, 3, 2, 3, 5, 6], 8, m603)
    cards += build(6, 4, [2, 5, 9, 3, 3, 5, 3], 8, m604)
    cards += build(6, 5, [1, 1, 1, 0, 1, 2, 2], 3, m605)
    cards += build(6, 6, [1, 3, 4, 5, 8, 6, 3], 8, m606)
    cards += build(6, 7, [1, 2, 2, 2, 4, 3, 2], 4, m607)
    cards += build(6, 8, [2, 6, 8, 9, 16, 13, 6], 16, m608)
    cards += build(6, 9, [1, 3, 4, 5, 8, 6, 3], 8, m609)
    cards += build(6, 10, [1, 1, 1, 0, 1, 2, 2], 3, m610)
    cards += build(6, 11, [0, 0, 1, 3, 2, 3, 2], 5, m611)
    cards += build(7, 1, [3, 4, 4, 2, 1, 1, 1], 4, m701)
    cards += build(7, 2, [1, 4, 5, 6, 11, 8, 4], 10, m702)
    cards += build(7, 3, [0, 0, 1, 2, 1, 2, 1], 2, m703)
    cards += build(7, 4, [0, 1, 1, 2, 2, 2, 2], 4, m704)
    cards += build(7, 5, [0, 1, 1, 1, 0, 0, 0], 0, m705)
    cards += mixed(6, [0, 0, 0, 0, 0, 0, 2], 0, "гл. 1–5", ["s", "w", "m", "c", "q"])
    cards += mixed(7, [0, 4, 6, 2, 8, 10, 6], 10, "гл. 1–5; раздел 16", ["s", "w", "coord", "m", "c", "coord"])
    cards += mixed(8, [0, 4, 7, 1, 0, 0, 0], 3, "гл. 1–6", ["if", "s", "if", "w"])
    (ROOT / "drafts" / "41-50-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(cards))


if __name__ == "__main__":
    main()
