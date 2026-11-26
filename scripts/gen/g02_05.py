#!/usr/bin/env python3
"""Серии для занятий 19–30: гл. 2, § 4–5; гл. 3; гл. 4; гл. 5, § 1–5; смешанные наборы 17.02–17.04.
Ответы вычисляются scripts/logic/systems.py (критерии гл. 5, § 2, с. 72–73), выводы книги переписаны со страниц.
Пишет drafts/19-30-gen.md.
"""
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import systems as SY  # noqa: E402
from s1 import C, D, N, V, atoms  # noqa: E402
from s1w import W, tex  # noqa: E402

rnd = random.Random(1970_72)
L = "абвгдежз"
x, y, z, u = (V(n) for n in "xyzu")
SEEN = set()
CONV_C = "Буквы $x, y, z, u$ — элементарные высказывания; «$:$» — сильная дизъюнкция («одно и только одно из»)."
CONV_W = "Буквы $x, y, z, u$ — элементарные высказывания; «$\\vee$» — соединительная дизъюнкция («по крайней мере одно из»)."
SYSTEX = {"s": "$S^s$", "w": "$S^w$", "m": "$S^m$", "c": "$S^c$", "q": "$S^6$"}


def ftex(a, b):
    return f"{tex(a)} \\vdash {tex(b)}"


def card(ch, sec, lvl, typ, step, form, ans, tags, body, src, system=None):
    sysl = f'system: "{system}"\n' if system else ""
    return (f"---\nchapter: {ch}\nsection: {sec}\nlevel: {lvl}\ntype: {typ}\nstep: {step}\ncondition: def\nform: {form}\n"
            f"answer: {ans}\nsource: \"{src}\"\n{sysl}generated: true\ntags: [{tags}]\n---\n\n{body}\n")


def rnd_f(names, depth, lang):
    dis = "wdis" if lang == "w" else "dis"
    if depth == 0 or rnd.random() < 0.3:
        v = V(rnd.choice(names))
        return N(v) if rnd.random() < 0.35 else v
    k = rnd.choice(["neg", "conj", "conj", dis, dis])
    if k == "neg":
        s = rnd_f(names, depth - 1, lang)
        return N(s) if s[0] != "neg" else s
    a, b = rnd_f(names, depth - 1, lang), rnd_f(names, depth - 1, lang)
    return rnd_f(names, depth, lang) if a == b else (k, (a, b))


def pair(lang, ok=lambda a, b: True, na="xy", nb="xyz", d=2):
    for _ in range(3000):
        a, b = rnd_f(na, d, lang), rnd_f(nb, d, lang)
        if repr((a, b)) not in SEEN and ok(a, b):
            SEEN.add(repr((a, b)))
            return a, b
    raise RuntimeError


def want(k, kind):
    """kind: 'yes' — доказуема; 'cond' — тавтология без условия; 'taut' — условие есть, но не тавтология."""
    if k == "q" and kind == "cond":
        kind = "yes"
    return {"yes": lambda a, b: SY.provable(k, a, b),
            "cond": lambda a, b: SY.taut(a, b) and not SY.cond(k, a, b),
            "taut": lambda a, b: SY.cond(k, a, b) and not SY.taut(a, b)}[kind]


def conv(lang):
    return CONV_W if lang == "w" else CONV_C


# ---------- фабрики карточек для систем с критерием ----------
def c_cond(cfg, lvl):
    k, lang = cfg["key"], cfg["lang"]
    if k == "q":
        return c_decide(cfg, lvl, 4)
    its = [pair(lang, na="xyz", nb="xyz") for _ in range(5)]
    body = (f"## Условие\n\n{conv(lang)} Условие системы {cfg['name']} на элементарные высказывания: {SY.COND[k]}. "
            "Для каких формул оно выполнено? (Тавтологичность здесь не проверяйте.)\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if SY.cond(k, a, b) else "нет") for i, (a, b) in enumerate(its)) +
            "\n\n## Решение\n\n" + "\n".join(f"{L[i]}) в посылке " + ", ".join(f"${t}$" for t in sorted(atoms(a))) +
                                          "; в заключении " + ", ".join(f"${t}$" for t in sorted(atoms(b))) + "."
                                          for i, (a, b) in enumerate(its)) + f"\n\n{cfg['src_cond']}.")
    return card(cfg["ch"], cfg["sec"], lvl, "D", "iso", "sym", "short", cfg["tags"], body, cfg["src"], cfg["sys"])


OTHER = {"s": "w", "w": "s", "m": "s", "c": "s", "q": "s"}


def e_cond(cfg, lvl):
    k, lang = cfg["key"], cfg["lang"]
    o = OTHER[k]
    a, b = pair(lang, lambda a, b: SY.taut(a, b) and SY.cond(o, a, b) != SY.cond(k, a, b), na="xyz", nb="xyz")
    claim = "доказуема" if SY.cond(o, a, b) else "недоказуема"
    right = "доказуема" if SY.provable(k, a, b) else "недоказуема"
    body = (f"## Условие\n\n{conv(lang)} Студент проверил, что ${ftex(a, b)}$ — тавтология, и решил, что в системе "
            f"{cfg['name']} она {claim}, проверив условие «{SY.COND[o]}». Найдите ошибку.\n\n## Ответ\n\nСтудент применил условие "
            f"системы {SYSTEX[o]}. В {cfg['name']} условие: {SY.COND[k]}; формула {right}.\n\n## Решение\n\n"
            f"{cfg['src_cond']}. Элементарные высказывания посылки: " + ", ".join(f"${t}$" for t in sorted(atoms(a))) +
            "; заключения: " + ", ".join(f"${t}$" for t in sorted(atoms(b))) + ".")
    return card(cfg["ch"], cfg["sec"], lvl, "E", "iso", "sym", "short", cfg["tags"] + ", диагностика", body, cfg["src"],
                cfg["sys"])


def c_decide(cfg, lvl, n=4, step="iso"):
    k, lang = cfg["key"], cfg["lang"]
    kinds = ["yes", "yes", "cond", "taut", "yes", "cond"][:n]
    rnd.shuffle(kinds)
    its = [pair(lang, want(k, kd)) for kd in kinds]
    body = (f"## Условие\n\n{conv(lang)} Какие формулы доказуемы в {cfg['name']}? Критерий: формула доказуема тогда и "
            f"только тогда, когда она тавтология и {SY.COND[k]} ({cfg['src_crit']}).\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if SY.provable(k, a, b) else "нет") for i, (a, b) in enumerate(its)) +
            "\n\n## Решение\n\n" + "\n".join(f"{L[i]}) {SY.reason(k, a, b, tex)}." for i, (a, b) in enumerate(its)))
    return card(cfg["ch"], cfg["sec"], lvl, "C", step, "sym", "short", cfg["tags"], body, cfg["src"], cfg["sys"])


def e_taut(cfg, lvl):
    k, lang = cfg["key"], cfg["lang"]
    a, b = pair(lang, want(k, "taut"))
    body = (f"## Условие\n\n{conv(lang)} Студент: «Для ${ftex(a, b)}$ выполнено условие: {SY.COND[k]}. Значит, формула доказуема в "
            f"{cfg['name']}». Найдите ошибку.\n\n## Ответ\n\nУсловие на элементарные высказывания необходимо, но не "
            f"достаточно: формула должна быть тавтологией, а она не тавтология.\n\n## Решение\n\n"
            f"{SY.reason(k, a, b, tex).capitalize()}. Критерий — {cfg['src_crit']}.")
    return card(cfg["ch"], cfg["sec"], lvl, "E", "iso", "sym", "short", cfg["tags"] + ", диагностика", body, cfg["src"],
                cfg["sys"])


def c_one(cfg, lvl, typ="C"):
    k, lang = cfg["key"], cfg["lang"]
    a, b = pair(lang, want(k, rnd.choice(["yes", "cond", "taut"])), d=3)
    v = "доказуема" if SY.provable(k, a, b) else "недоказуема"
    body = (f"## Условие\n\n{conv(lang)} Доказуема ли в {cfg['name']} формула ${ftex(a, b)}$? Обоснуйте по критерию "
            f"({cfg['src_crit']}).\n\n## Ответ\n\n{v}\n\n## Решение\n\n{SY.reason(k, a, b, tex).capitalize()}.")
    return card(cfg["ch"], cfg["sec"], lvl, typ, "open", "sym", "short", cfg["tags"], body, cfg["src"], cfg["sys"])


def e_fake(cfg, lvl):
    k, lang = cfg["key"], cfg["lang"]
    wt = rnd.random() < 0.5 and k != "q"
    a, b = pair(lang, lambda a, b: not SY.provable(k, a, b) and SY.taut(a, b) == wt, d=2)
    body = (f"## Условие\n\n{conv(lang)} Студент утверждает, что ${ftex(a, b)}$ — теорема {cfg['name']}. Верно ли?\n\n"
            f"## Ответ\n\nНеверно: формула недоказуема.\n\n## Решение\n\n{SY.reason(k, a, b, tex).capitalize()} "
            f"({cfg['src_crit']}).")
    return card(cfg["ch"], cfg["sec"], lvl, "E", "open", "sym", "short", cfg["tags"] + ", диагностика", body, cfg["src"],
                cfg["sys"])


def table_text(a, b):
    return "; ".join(f"{SYSTEX[k]} — " + ("да" if SY.provable(k, a, b) else "нет") for k in "swmcq")


def c_multi(cfg, lvl, typ="C"):
    lang = cfg["lang"]
    a, b = pair(lang, lambda a, b: SY.taut(a, b) and len({SY.provable(k, a, b) for k in "swmc"}) == 2, nb="xyz")
    body = (f"## Условие\n\n{conv(lang)} В каких системах доказуема формула ${ftex(a, b)}$: {', '.join(SYSTEX[k] for k in 'swmcq')}? "
            "Критерии — гл. 5, § 2, MT1–MT4, MT6 (с. 72–73).\n\n## Ответ\n\n" + table_text(a, b) +
            "\n\n## Решение\n\nФормула — тавтология. Элементарные высказывания посылки: " +
            ", ".join(f"${t}$" for t in sorted(atoms(a))) + "; заключения: " +
            ", ".join(f"${t}$" for t in sorted(atoms(b))) + ". Условия: " +
            "; ".join(f"{SYSTEX[k]} — {SY.COND[k]}" for k in "swmc") + ".")
    return card(cfg["ch"], cfg["sec"], lvl, typ, "transfer", "sym", "short", cfg["tags"] + ", системы", body,
                "с. 72–73, гл. 5, § 2", cfg["sys"])


def e_multi(cfg, lvl):
    lang = cfg["lang"]
    a, b = pair(lang, lambda a, b: SY.taut(a, b) and SY.provable("w", a, b) and not SY.provable("m", a, b), nb="xyz")
    body = (f"## Условие\n\n{conv(lang)} Студент: «${ftex(a, b)}$ — тавтология, поэтому она доказуема во всех системах "
            f"общей теории дедукции». Найдите ошибку.\n\n## Ответ\n\nСистемы различаются условиями на элементарные "
            f"высказывания. Здесь: {table_text(a, b)}.\n\n## Решение\n\nГл. 5, § 2, MT1–MT4, MT6 (с. 72–73). Без "
            "условий доказуемы все тавтологии только в $S^6$.")
    return card(cfg["ch"], cfg["sec"], lvl, "E", "open", "sym", "short", cfg["tags"] + ", диагностика", body,
                "с. 72–73, гл. 5, § 2", cfg["sys"])


# ---------- обычный язык ----------
PH = {"x": ("идёт дождь", "дождь не идёт"), "y": ("дует ветер", "ветер не дует"), "z": ("холодно", "не холодно"),
      "u": ("светит солнце", "солнце не светит")}


def nl(f):
    if f[0] == "v":
        return PH[f[1]][0]
    if f[0] == "neg":
        return PH[f[1][1]][1]
    parts = [nl(a) for a in f[1]]
    if f[0] == "conj":
        return " и ".join(parts)
    if f[0] == "wdis":
        return " или ".join(parts) + " (или то и другое)"
    return "либо " + ", либо ".join(parts) + " (одно и только одно)"


def lit(f):
    return f[0] == "v" or (f[0] == "neg" and f[1][0] == "v")


def nl_pair(lang, ok):
    def g():
        dis = "wdis" if lang == "w" else "dis"
        def side(names):
            n = rnd.choice([1, 2, 2])
            ls = rnd.sample(names, n)
            ls = [N(V(t)) if rnd.random() < 0.3 else V(t) for t in ls]
            return ls[0] if n == 1 else (rnd.choice(["conj", dis]), tuple(ls))
        return side(list("xyz")), side(list("xyzu"))
    for _ in range(3000):
        a, b = g()
        if repr((a, b)) not in SEEN and ok(a, b):
            SEEN.add(repr((a, b)))
            return a, b
    return pair(lang, ok, na="xyz", nb="xyzu", d=1)


def c_nl(cfg, lvl, typ="C"):
    k, lang = cfg["key"], cfg["lang"]
    a, b = nl_pair(lang, want(k, rnd.choice(["yes", "yes", "cond", "taut"])))
    v = "да" if SY.provable(k, a, b) else "нет"
    body = (f"## Условие\n\nЗапишите рассуждение формулой и выясните, является ли оно следованием в смысле {cfg['name']}: "
            f"«{nl(a).capitalize()}; следовательно, {nl(b)}». Обозначения: $x$ — «идёт дождь», $y$ — «дует ветер», "
            "$z$ — «холодно», $u$ — «светит солнце».\n\n## Ответ\n\n" + f"${ftex(a, b)}$; {v}" +
            f"\n\n## Решение\n\n{SY.reason(k, a, b, tex).capitalize()} ({cfg['src_crit']}).")
    return card(cfg["ch"], cfg["sec"], lvl, typ, "vary", "nat", "short", cfg["tags"] + ", обычный язык", body, cfg["src"],
                cfg["sys"])


def c_classic(cfg, lvl):
    k, lang = cfg["key"], cfg["lang"]
    a, b = pair(lang, lambda a, b: SY.taut(a, b) and not SY.cond(k, a, b) if rnd.random() < 0.6 else SY.provable(k, a, b),
                nb="xyz")
    p = SY.provable(k, a, b)
    body = (f"## Условие\n\n{conv(lang)} Доказуема ли $({tex(a)}) \\supset ({tex(b)})$ в классическом пропозициональном "
            f"исчислении? Доказуема ли ${ftex(a, b)}$ в {cfg['name']}? Сошлитесь на метатеорему гл. 5, § 2.\n\n## Ответ\n\n"
            f"Классически — да; в {cfg['name']} — {'да' if p else 'нет'}.\n\n## Решение\n\n{SY.MT[k]} (с. 72–73): "
            f"формула следования доказуема в {cfg['name']} тогда и только тогда, когда импликация «посылка $\\supset$ "
            f"заключение» доказуема классически и {SY.COND[k]}. Импликация доказуема: формула следования — тавтология. "
            + ("Условие выполнено." if p else "Условие не выполнено: " + SY.reason(k, a, b, tex).split(": ", 1)[1] + "."))
    return card(cfg["ch"], cfg["sec"], lvl, "S", "transfer", "sym", "short", cfg["tags"] + ", классическая логика", body,
                "с. 72–73, гл. 5, § 2", cfg["sys"])


# ---------- выводы книги (переписаны со страниц) ----------
PROOFS = {
    "S1*T1": ("с. 46, гл. 2, § 5", "$S_1^*$", "w",
              [("x \\vdash x(y \\vee \\sim y)", "T1 в $S_1^*$; $y$ входит в $x$")],
              [("\\sim x \\vee \\sim yy \\vdash \\sim x", "A*11"), ("\\sim x \\vdash \\sim x \\vee \\sim yy", "R*4"),
               ("\\sim\\sim x \\vdash \\sim(\\sim x \\vee \\sim yy)", "1, 2, R1"),
               ("x \\vdash x(y \\vee \\sim y)", "3, A9, A10, R1, R2")]),
    "S2A8": ("с. 54, гл. 3, § 5", "$S_2$", "w", [("xz \\vee yz \\vdash (x \\vee y)z", "A8 в $S_2$")],
             [("x(x \\vee y) \\vdash x", "A3"), ("x \\vdash x", "A1, A2, R1"), ("x \\vdash x \\vee y", "A12"),
              ("x \\vdash x(x \\vee y)", "2, 3, R2"), ("\\sim(x(x \\vee y)) \\vdash \\sim x", "1, 4, R1"),
              ("\\sim x \\vee \\sim x\\sim y \\vdash \\sim x", "1, 4, A9, A10"), ("x \\vdash x \\vee xy", "A12"),
              ("x \\vee xy \\vdash x", "6"), ("xz \\vee yz \\vdash xz \\vee yz \\vee z", "A12"),
              ("xz \\vee yz \\vdash z", "7–9, R1"), ("xz(x \\vee y) \\vee yz(x \\vee y) \\vdash x \\vee y", "10"),
              ("xz(x \\vee y) \\vdash xz", "A3"), ("xz \\vdash xz(x \\vee y)", "A12, A3, R1, 2, R2"),
              ("yz \\vdash yz(x \\vee y)", "13, A4"), ("yz(x \\vee y) \\vdash yz", "A3"),
              ("xz \\vee yz \\vdash x \\vee y", "11–15, R1"), ("xz \\vee yz \\vdash (x \\vee y)z", "10, 16, R2")]),
    "S3T1": ("с. 59, гл. 4, § 1", "$S^3$", "c", [("(x : y)z \\vdash xz : yz", "T1 в $S^3$")],
             [("(x : y)z \\vdash y : xz", "A14, T8 I2, R2"), ("(x : y)z \\vdash (x : y)z", "T2 I2"),
              ("(x : y)z \\vdash (y : xz)z(x : y)z", "1, 2, R2, T3 I2, T4 I2, R3"),
              ("(x : y)z \\vdash (y : xz)z", "3, A3, R1"), ("(x : y)z \\vdash xz : yz", "4, A14, T8 I2, R1")]),
    "S3T2": ("с. 59–60, гл. 4, § 1", "$S^3$", "c", [("xz : y \\vdash (xz : y)(x : \\sim x)", "T2 в $S^3$")],
             [("xz : y \\vdash xz\\sim y : \\sim(xz)y", "T17 I2"),
              ("xz : y \\vdash xz\\sim y : \\sim xzy : x\\sim zy : \\sim x\\sim zy", "1, A7, A13, T10 I2, R3, A12, R1"),
              ("xz : y \\vdash (xz\\sim y : \\sim xzy : x\\sim zy : \\sim x\\sim zy)(x : \\sim x)",
               "2, T18 I2, T19 I2, R3, A13, R1"),
              ("xz : y \\vdash (xz : y)(x : \\sim x)", "3, A11, T17 I2, R3, R1")]),
    "S3A8": ("с. 61, гл. 4, § 1", "$S_3$", "w", [("(x \\vee y)z \\vdash xz \\vee yz", "в $S_3$ с ограничением на A3")],
             [("(x \\vee y)z \\vdash (x \\vee y)z", "—"), ("(x \\vee y)z \\vdash xz \\vee y", "A7"),
              ("(x \\vee y)z \\vdash (x \\vee y)z(xz \\vee y)", "R2, 1, 2"),
              ("(x \\vee y)z(xz \\vee y) \\vdash (xz \\vee y)z", "—"), ("(xz \\vee y)z \\vdash xz \\vee yz", "A7, A4"),
              ("(x \\vee y)z \\vdash xz \\vee yz", "R1, 3, 4, 5"), ("xz \\vee yz \\vdash (x \\vee y)z", "A8")]),
    "S6MT3": ("с. 71, гл. 4, § 4", "$S^{*6}$", "w", [("x \\dashv\\vdash x(y \\vee \\sim y)", "доказательство MT3")],
              [("x(y \\vee \\sim y) \\vdash x", "A3"), ("x \\vdash zy \\vee x", "A12, R1, $a \\vee b \\vdash b \\vee a$"),
               ("zy \\vee x \\vdash (zy \\vee x)(y \\vee \\sim y)", "A11"), ("zy \\vee x \\vdash y \\vee \\sim y", "A3, R1"),
               ("x \\vdash y \\vee \\sim y", "2, 3, 4, R1"), ("x \\vdash x", "A1, A2, R1"),
               ("x \\vdash x(y \\vee \\sim y)", "5, 6, R2"), ("x \\dashv\\vdash x(y \\vee \\sim y)", "1, 7")]),
}


def c_proof(cfg, lvl, key, hide_n=2):
    src, sysn, _, head, steps = PROOFS[key]
    cand = [i for i, (_, b) in enumerate(steps) if b != "—"]
    hide = sorted(rnd.sample(cand, min(hide_n, len(cand))))
    shown = "\n".join(f"{i + 1}. ${f}$ [{'…' if i in hide else b}]" for i, (f, b) in enumerate(steps))
    body = (f"## Условие\n\nДоказательство в {sysn} ({head[0][1]}; {src}). Восстановите пропущенные основания.\n\n{shown}\n\n"
            "## Ответ\n\n" + "; ".join(f"{i + 1} — {steps[i][1]}" for i in hide) + f"\n\n## Решение\n\n{src}. "
            "Номера в скобках — ссылки на предыдущие строки; «I2» — теоремные схемы § 2 гл. 1.")
    return card(cfg["ch"], cfg["sec"], lvl, "D", "complete", "sym", "short", cfg["tags"] + ", вывод", body, src, cfg["sys"])


def e_proof(cfg, lvl, key):
    src, sysn, _, head, steps = PROOFS[key]
    cand = [i for i, (_, b) in enumerate(steps) if b in ("A3", "A12", "A11", "A7", "A8", "A*11", "R*4", "T17 I2", "T2 I2")]
    i = rnd.choice(cand)
    alt = {"A3": "A4", "A12": "A3", "A11": "A12", "A7": "A8", "A8": "A7", "A*11": "A11", "R*4": "R1",
           "T17 I2": "T18 I2", "T2 I2": "T1 I2"}[steps[i][1]]
    shown = "\n".join(f"{j + 1}. ${f}$ [{alt if j == i else b}]" for j, (f, b) in enumerate(steps))
    body = (f"## Условие\n\nВ доказательстве в {sysn} ({src}) одно основание указано неверно. Найдите его.\n\n{shown}\n\n"
            f"## Ответ\n\nШаг {i + 1}: верно — {steps[i][1]}.\n\n## Решение\n\n{src}.")
    return card(cfg["ch"], cfg["sec"], lvl, "E", "complete", "sym", "short", cfg["tags"] + ", вывод, диагностика", body,
                src, cfg["sys"])


# ---------- особые системы ----------
def s21_card(cfg, lvl, typ="C"):
    its = []
    for want_ in rnd.sample([True, True, False, False], 4):
        its.append(pair("w", lambda a, b: SY.taut(a, b) and SY.s21(a, b) == want_, d=2))
    body = (f"## Условие\n\n{CONV_W} Доказуемы ли формулы в $S_2^1$? По MT1, MT2 (с. 56–57): $x \\vdash y$ доказуема тогда и "
            "только тогда, когда для каждого члена $x^i$ дизъюнктивной нормальной формы $x$ найдётся член $y^j$ "
            "дизъюнктивной нормальной формы $y$, все конъюнктивные составляющие которого входят в $x^i$.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if SY.s21(a, b) else "нет") for i, (a, b) in enumerate(its)) +
            "\n\n## Решение\n\n" + "\n".join(f"{L[i]}) ДНФ посылки: ${SY.dnf_tex(SY.dnf(a), tex)}$; ДНФ заключения: "
                                          f"${SY.dnf_tex(SY.dnf(b), tex)}$." for i, (a, b) in enumerate(its)) +
            "\n\nВсе формулы — тавтологии; доказуемость в $S_2^1$ решает условие на составляющие.")
    return card(cfg["ch"], cfg["sec"], lvl, typ, "iso", "sym", "short", cfg["tags"], body, "с. 55–57, гл. 3, § 6", "S_2^1")


def s21_dnf(cfg, lvl):
    f = None
    while f is None or repr(f) in SEEN or len(SY.dnf(f)) < 2:
        f = rnd_f("xy", 2, "w")
        f = N(f) if f[0] != "neg" and rnd.random() < 0.5 else f
    SEEN.add(repr(f))
    body = (f"## Условие\n\n{CONV_W} Приведите ${tex(f)}$ к дизъюнктивной нормальной форме (с. 56): внесите отрицания внутрь "
            "по A9, A10, снимите двойные отрицания, раскройте конъюнкции дизъюнкций.\n\n## Ответ\n\n" +
            f"${SY.dnf_tex(SY.dnf(f), tex)}$ (порядок членов и составляющих не важен)\n\n## Решение\n\nС. 56: каждый член — "
            "конъюнкция элементарных высказываний и их отрицаний.")
    return card(cfg["ch"], cfg["sec"], lvl, "D", "iso", "sym", "short", cfg["tags"] + ", ДНФ", body, "с. 56, гл. 3, § 6",
                "S_2^1")


def s21_e(cfg, lvl):
    a, b = pair("w", lambda a, b: SY.taut(a, b) and not SY.s21(a, b) and SY.provable("w", a, b), d=2)
    body = (f"## Условие\n\n{CONV_W} Студент: «${ftex(a, b)}$ — тавтология с общими элементарными высказываниями, значит, "
            "она доказуема и в $S^w$, и в $S_2^1$». Найдите ошибку.\n\n## Ответ\n\nВ $S^w$ доказуема, в $S_2^1$ — нет: у "
            "$S_2^1$ другой критерий (MT1, MT2, с. 56–57).\n\n## Решение\n\nДНФ посылки: "
            f"${SY.dnf_tex(SY.dnf(a), tex)}$; заключения: ${SY.dnf_tex(SY.dnf(b), tex)}$. Найдётся член посылки, для которого "
            "ни один член заключения не состоит из его составляющих. $S_2^1$ неполна в смысле полноты $S^w$ (с. 55).")
    return card(cfg["ch"], cfg["sec"], lvl, "E", "open", "sym", "short", cfg["tags"] + ", диагностика", body,
                "с. 55–57, гл. 3, § 6", "S_2^1")


def deg_card(cfg, lvl, typ="C", n=5):
    its = []
    for w_ in rnd.sample([True, True, True, False, False], n):
        f = None
        while f is None or repr(f) in SEEN or SY.is_taut(f) != w_:
            f = rnd_f("xy", 3, rnd.choice(["c", "w"]))
        SEEN.add(repr(f))
        its.append(f)
    body = ("## Условие\n\n" + CONV_W.replace(".", "; «$:$» — сильная дизъюнкция.", 1) +
            " Какие формулы вырожденного следования доказуемы в $S^5$ (MT1, MT4, с. 67–69)?\n\n" +
            "\n".join(f"{L[i]}) $\\vdash {tex(f)}$" for i, f in enumerate(its)) + "\n\n## Ответ\n\n" +
            "; ".join(f"{L[i]}) " + ("да" if SY.is_taut(f) else "нет") for i, f in enumerate(its)) +
            "\n\n## Решение\n\n$\\vdash x$ доказуема в $S^5$ тогда и только тогда, когда $x$ — тавтология (MT1, MT4).\n" +
            "\n".join(f"{L[i]}) " + ("тавтология." if SY.is_taut(f) else
                                     "при " + SY.env_text(next(e for e in SY.rows(f) if not SY.value(f, e))) +
                                     " — значение 0.") for i, f in enumerate(its)))
    return card(cfg["ch"], cfg["sec"], lvl, typ, "iso", "sym", "short", cfg["tags"], body, "с. 67–69, гл. 4, § 3", "S^5")


def deg_e(cfg, lvl):
    f = None
    while f is None or repr(f) in SEEN or not SY.is_taut(f) or len(atoms(f)) < 2:
        f = rnd_f("xy", 3, "w")
    SEEN.add(repr(f))
    body = (f"## Условие\n\n{CONV_W} Студент: «$\\vdash {tex(f)}$ недоказуема в $S^5$: формула вырожденного следования не "
            "имеет посылки, поэтому условие непарадоксальности нарушено». Найдите ошибку.\n\n## Ответ\n\nДля $\\vdash x$ "
            "условия на элементарные высказывания нет: $\\vdash x$ доказуема, если $x$ — тавтология (MT4, с. 69); это "
            "тавтология.\n\n## Решение\n\nD1, D2, MT1, MT4 (с. 67–69).")
    return card(cfg["ch"], cfg["sec"], lvl, "E", "open", "sym", "short", cfg["tags"] + ", диагностика", body,
                "с. 67–69, гл. 4, § 3", "S^5")


def rd_card(cfg, lvl):
    a, b = pair("w", lambda a, b: SY.taut(a, b) and not SY.cond("s", a, b) and SY.is_taut(a), na="x", nb="xy", d=2)
    body = (f"## Условие\n\n{CONV_W} В $S^5$ доказуема $\\vdash {tex(a)}$. Можно ли по $R^d1$ (если $x \\vdash y$ и $\\vdash x$, "
            f"то $\\vdash y$) получить $\\vdash {tex(b)}$, используя формулу ${ftex(a, b)}$? Доказуема ли $\\vdash {tex(b)}$?"
            "\n\n## Ответ\n\n" + ("$\\vdash$" + f"${tex(b)}$ доказуема (тавтология), но не через ${ftex(a, b)}$: эта формула "
                                 "недоказуема в $S^s$ — в заключение входит $y$.").replace("$\\vdash$$", "$\\vdash ") +
            "\n\n## Решение\n\n$R^d1$ (с. 67) требует доказуемости $x \\vdash y$; в $S^5$ формулы следования доказуемы по "
            "правилам $S^s$. $\\vdash y$ доказуема по MT4, так как $y$ — тавтология.")
    if not SY.is_taut(b):
        return None
    return card(cfg["ch"], cfg["sec"], lvl, "C", "open", "sym", "short", cfg["tags"], body, "с. 67–69, гл. 4, § 3", "S^5")


NN = lambda n: ("nn", n)
QQ = lambda n: ("qq", n)


def ntex(f):
    k = f[0]
    if k == "v":
        return f"{f[1]}"
    if k == "nn":
        return f"\\urcorner {f[1]}"
    if k == "qq":
        return f"?{f[1]}"
    if k == "neg":
        a = f[1]
        return f"\\sim {ntex(a)}" if a[0] in ("v", "nn", "qq", "neg") else f"\\sim({ntex(a)})"
    if k == "conj":
        return "".join(f"({ntex(a)})" if a[0] in ("conj", "wdis") else ntex(a) for a in f[1])
    return " \\vee ".join(f"({ntex(a)})" if a[0] == "wdis" else ntex(a) for a in f[1])


NCONV = ("Буква $x$ — высказывание с главным оператором $\\leftarrow$ (например, $a \\leftarrow b$); $\\urcorner x$ и $?x$ — "
         "по дополнению к определению высказывания (гл. 5, § 5, с. 76).")


def n_cards(cfg):
    out = []
    an = [("A^n1", N(V("x")), W(NN("x"), QQ("x"))), ("A^n2", W(NN("x"), QQ("x")), N(V("x"))),
          ("A^n3", N(NN("x")), W(V("x"), QQ("x"))), ("A^n4", W(V("x"), QQ("x")), N(NN("x"))),
          ("A^n5", N(QQ("x")), W(V("x"), NN("x"))), ("A^n6", W(V("x"), NN("x")), N(QQ("x")))]
    its = rnd.sample(an, 4)
    out.append(card(5, 5, 1, "R", "iso", "sym", "short", "неклассический случай",
                    f"## Условие\n\n{NCONV} Каким дополнительным аксиомным схемам $S_n^i$ (с. 76) соответствуют формулы?\n\n" +
                    "\n".join(f"{L[i]}) ${ntex(a)} \\vdash {ntex(b)}$" for i, (_, a, b) in enumerate(its)) + "\n\n## Ответ\n\n" +
                    "; ".join(f"{L[i]}) ${n}$" for i, (n, _, _) in enumerate(its)) + "\n\n## Решение\n\nС. 76.",
                    "с. 76, гл. 5, § 5", "S_n"))
    out.append(card(5, 5, 2, "D", "iso", "sym", "short", "неклассический случай",
                    "## Условие\n\nЗапишите $\\urcorner x$ и $?x$ для высказываний: а) $a \\leftarrow b$; б) $(\\forall a)\\,x$.\n\n"
                    "## Ответ\n\nа) $a \\urcorner\\!\\leftarrow b$ и $a? \\leftarrow b$; б) $(\\urcorner\\forall a)\\,x$ и $(?\\forall a)\\,x$.\n\n"
                    "## Решение\n\nДополнение к определению высказывания (с. 76): операторы ставятся перед главным оператором.",
                    "с. 76, гл. 5, § 5", "S_n"))
    out.append(card(5, 5, 2, "E", "iso", "sym", "short", "неклассический случай, диагностика",
                    "## Условие\n\nСтудент: «$\\urcorner(xy)$ — высказывание $S_n^i$: внутреннее отрицание перед конъюнкцией». "
                    "Найдите ошибку.\n\n## Ответ\n\n$\\urcorner$ и ? ставятся только перед главными операторами "
                    "$\\leftarrow$, $\\forall$, $\\exists$, $\\rightarrow$, а не перед $\\cdot$, $:$, $\\vee$, $\\sim$.\n\n## Решение\n\n"
                    "Гл. 5, § 5 (с. 75–76).", "с. 75–76, гл. 5, § 5", "S_n"))
    cands = [("T2", V("x"), N(NN("x")), True), ("T3", V("x"), N(QQ("x")), True), ("T5", NN("x"), N(V("x")), True),
             ("—", N(NN("x")), V("x"), False), ("—", N(V("x")), NN("x"), False), ("T8", QQ("x"), N(V("x")), True),
             ("—", N(QQ("x")), V("x"), False)]
    for _ in range(2):
        its = rnd.sample(cands, 4)
        out.append(card(5, 5, 3, "C", "iso", "sym", "short", "неклассический случай",
                        f"## Условие\n\n{NCONV} Главная интерпретация (с. 76): если одно из $x$ и $\\urcorner x$ имеет значение 1, "
                        "другое — 0; если одно имеет значение 0, значение другого от него не зависит; $?x$ равнозначно "
                        "$\\sim x\\sim\\urcorner x$. Какие формулы — тавтологии?\n\n" +
                        "\n".join(f"{L[i]}) ${ntex(a)} \\vdash {ntex(b)}$" for i, (_, a, b, _) in enumerate(its)) +
                        "\n\n## Ответ\n\n" + "; ".join(f"{L[i]}) " + ("да" if SY.ntaut(a, b) else "нет")
                                                       for i, (_, a, b, _) in enumerate(its)) +
                        "\n\n## Решение\n\nИз трёх высказываний $x$, $\\urcorner x$, $?x$ истинно ровно одно. Перебираем три "
                        "случая.", "с. 76–77, гл. 5, § 5", "S_n"))
        assert all(SY.ntaut(a, b) == w_ for (_, a, b, w_) in its)
    out.append(card(5, 5, 3, "E", "iso", "sym", "short", "неклассический случай, диагностика",
                    f"## Условие\n\n{NCONV} Студент: «$\\sim\\urcorner x \\vdash x$ — тавтология: отрицание внутреннего отрицания "
                    "даёт утверждение». Найдите ошибку.\n\n## Ответ\n\nНе тавтология: при истинном $?x$ высказывание "
                    "$\\sim\\urcorner x$ истинно, а $x$ ложно (MT3, с. 76).\n\n## Решение\n\nС. 76: формулы $\\sim\\urcorner x \\vdash x$ "
                    "и $\\vdash x \\vee \\urcorner x$ недоказуемы в $S_n^i$.", "с. 76, гл. 5, § 5", "S_n"))
    out.append(card(5, 5, 4, "D", "complete", "sym", "short", "неклассический случай",
                    f"## Условие\n\n{NCONV} Восстановите пропуски в теоремных схемах $S_n^i$ (с. 77):\n\n- T1. $x \\dashv\\vdash$ …\n"
                    "- T4. $\\urcorner x \\dashv\\vdash$ …\n- T7. $?x \\dashv\\vdash$ …\n- T14. $\\vdash$ …\n\n## Ответ\n\n"
                    "T1: $\\sim\\urcorner x\\sim ?x$; T4: $\\sim x\\sim ?x$; T7: $\\sim x\\sim\\urcorner x$; T14: "
                    "$x \\vee \\urcorner x \\vee ?x$.\n\n## Решение\n\nС. 77. Все — тавтологии при главной интерпретации "
                    "(ровно одно из $x$, $\\urcorner x$, $?x$ истинно).", "с. 77, гл. 5, § 5", "S_n"))
    assert SY.ntaut(V("x"), C(N(NN("x")), N(QQ("x")))) and SY.ntaut(W(V("x"), NN("x"), QQ("x")))
    return out


# ---------- конфигурации разделов ----------
def mk(ch, sec, key, lang, name, sysn, tags, src, src_crit, src_cond, levels, diag, proofs=(), special=None):
    return dict(ch=ch, sec=sec, key=key, lang=lang, name=name, sys=sysn, tags=tags, src=src, src_crit=src_crit,
                src_cond=src_cond, levels=levels, diag=diag, proofs=list(proofs), special=special)


CFG = [
    mk(2, 4, "s", "w", "$S_1$", "S_1", "S1w, эквивалентность", "с. 45, гл. 2, § 4", "гл. 2, § 2, MT5; § 4, с. 45",
       "Гл. 2, § 1–2", [0, 0, 0, 0, 0, 1, 1, 0, 0, 0], 1),
    mk(2, 5, "s", "w", "$S^s$", "S^s", "сильное следование", "с. 45–48, гл. 2, § 5", "гл. 5, § 2, MT1, с. 72",
       "Гл. 2, § 5; гл. 5, § 2", [2, 2, 4, 2, 4, 7, 9, 0, 0, 0], 10, proofs=["S1*T1"]),
    mk(3, 1, "w", "c", "$S^2$", "S^2", "S2, ослабленное следование", "с. 49, гл. 3, § 1", "гл. 3, § 2–3, MT1, MT4, с. 49–52",
       "Гл. 3, § 1–2, с. 49", [0, 1, 2, 2, 3, 3, 1, 0, 0, 0], 3),
    mk(3, 2, "w", "c", "$S^2$", "S^2", "S2, непарадоксальность", "с. 49–50, гл. 3, § 2", "гл. 3, § 2–3, MT1, MT4, с. 49–52",
       "Гл. 3, § 2, MT1, с. 49", [0, 1, 1, 2, 2, 2, 2, 0, 0, 0], 4),
    mk(3, 3, "w", "c", "$S^2$", "S^2", "S2, полнота", "с. 50–52, гл. 3, § 3", "гл. 3, § 3, MT4, с. 52",
       "Гл. 3, § 3, с. 51–52", [0, 0, 1, 2, 1, 2, 1, 0, 0, 0], 3),
    mk(3, 4, "w", "w", "$S_2$", "S_2", "S2w, ослабленное следование", "с. 52–53, гл. 3, § 4", "гл. 3, § 3–4; гл. 5, § 2, MT3",
       "Гл. 3, § 4", [1, 3, 4, 5, 8, 6, 3, 0, 0, 0], 8, proofs=["S2A8"]),
    mk(3, 5, "w", "w", "$S^w$", "S^w", "Sw, ослабленное следование", "с. 53–54, гл. 3, § 5", "гл. 5, § 2, MT3, с. 73",
       "Гл. 3, § 5; гл. 5, § 2", [1, 3, 4, 5, 8, 6, 3, 0, 0, 0], 8, proofs=["S2A8"]),
    mk(3, 6, "w", "w", "$S_2^1$", "S_2^1", "S21, системы, сходные с Sw", "с. 54–58, гл. 3, § 6", "с. 56–57",
       "Гл. 3, § 6", [2, 5, 6, 8, 13, 11, 5, 0, 0, 0], 13, special="s21"),
    mk(4, 1, "m", "c", "$S^m$", "S^3", "S3, максимальное следование", "с. 59–62, гл. 4, § 1", "гл. 4, § 1, MT1, MT5; гл. 5, § 2, MT2",
       "Гл. 4, § 1, с. 59", [1, 3, 4, 5, 8, 6, 3, 0, 0, 0], 8, proofs=["S3T1", "S3T2", "S3A8"]),
    mk(4, 2, "c", "c", "$S^c$", "S^4", "S4, конверсное следование", "с. 62–67, гл. 4, § 2", "гл. 4, § 2, MT1, MT5; гл. 5, § 2, MT4",
       "Гл. 4, § 2, с. 63", [2, 5, 6, 8, 13, 11, 5, 0, 0, 0], 13),
    mk(4, 3, "s", "w", "$S^5$", "S^5", "S5, вырожденное следование", "с. 67–70, гл. 4, § 3", "с. 67–69", "Гл. 4, § 3",
       [1, 3, 4, 5, 8, 6, 3, 0, 0, 0], 8, special="deg"),
    mk(4, 4, "q", "w", "$S^6$", "S^6", "S6, квазиследование", "с. 70–71, гл. 4, § 4", "гл. 4, § 4, MT1, MT2, с. 70",
       "Гл. 4, § 4", [1, 2, 3, 3, 5, 4, 2, 0, 0, 0], 5, proofs=["S6MT3"]),
    mk(5, 1, "s", "c", "$S^s$", "S^s", "общая теория дедукции", "с. 72–73, гл. 5, § 1–2", "гл. 5, § 2, MT1",
       "Гл. 5, § 2", [1, 2, 2, 2, 4, 3, 2, 0, 0, 0], 4),
    mk(5, 2, "w", "c", "$S^w$", "S^w", "классическая логика", "с. 72–73, гл. 5, § 2", "гл. 5, § 2, MT3",
       "Гл. 5, § 2", [1, 1, 2, 1, 2, 3, 5, 0, 0, 0], 5),
    mk(5, 3, "s", "c", "$S^s$", "S^s", "парадоксы следования", "с. 74, гл. 5, § 3", "гл. 5, § 2, MT1",
       "Гл. 5, § 2–3", [1, 1, 1, 0, 1, 2, 2, 0, 0, 0], 3),
    mk(5, 4, "s", "c", "$S^s$", "S^s", "интуиционистская логика", "с. 75, гл. 5, § 4", "гл. 5, § 2, MT1",
       "Гл. 5, § 2", [1, 1, 1, 0, 1, 1, 2, 0, 0, 0], 2),
]


def fill(cfg):
    out = []
    lv = cfg["levels"]
    # распределение диагностики по ступеням 2–6
    dslots = []
    for lvl in (2, 3, 4, 5, 6, 5, 6, 3, 4, 2, 6, 5, 4):
        if len(dslots) < cfg["diag"] and sum(1 for s in dslots if s == lvl) < max(1, lv[lvl - 1] // 2) and lv[lvl - 1] > 0:
            dslots.append(lvl)
    sp = cfg["special"]
    for lvl in range(1, 8):
        n = lv[lvl - 1]
        nd = min(dslots.count(lvl), n)
        for i in range(n):
            diag = i < nd
            c = None
            while c is None:
                c = make(cfg, lvl, diag, i, sp)
            out.append(c)
    return out


def make(cfg, lvl, diag, i, sp):
    if sp == "s21":
        if lvl == 1:
            return s21_dnf(cfg, 1).replace("level: 1\ntype: D", "level: 1\ntype: R")
        if diag:
            return s21_e(cfg, lvl)
        if lvl in (2, 3):
            return s21_dnf(cfg, lvl)
        if lvl == 7:
            return c_multi(cfg, 7, "S") if i % 2 else s21_card(cfg, 7, "S")
        return s21_card(cfg, lvl) if i % 3 else c_cond(cfg, lvl) if lvl < 5 else s21_card(cfg, lvl)
    if sp == "deg":
        if diag:
            return deg_e(cfg, lvl) if i % 2 == 0 else e_fake(cfg, lvl)
        if lvl == 1:
            return deg_card(cfg, 1, "R", 4)
        if lvl == 4 and i == 0:
            return deg_steps(cfg)
        if lvl in (5, 6) and i % 3 == 0:
            return rd_card(cfg, lvl)
        if lvl == 7:
            return c_classic(cfg, 7)
        return deg_card(cfg, lvl) if i % 2 == 0 else c_decide(cfg, lvl)
    if diag:
        if lvl == 2:
            return e_cond(cfg, lvl)
        if lvl == 3:
            return e_taut(cfg, lvl)
        if lvl == 4:
            return e_proof(cfg, lvl, rnd.choice(cfg["proofs"])) if cfg["proofs"] and i % 2 == 0 else e_cond(cfg, lvl)
        if lvl == 5:
            return e_fake(cfg, lvl)
        return e_multi(cfg, lvl) if i % 2 else e_fake(cfg, lvl)
    if lvl == 1:
        return c_cond(cfg, 1).replace("level: 1\ntype: D", "level: 1\ntype: R")
    if lvl == 2:
        return c_cond(cfg, 2)
    if lvl == 3:
        return c_decide(cfg, 3)
    if lvl == 4:
        if cfg["proofs"] and i % 2 == 0:
            return c_proof(cfg, 4, cfg["proofs"][i // 2 % len(cfg["proofs"])])
        return c_decide(cfg, 4, 5, "complete") if i % 3 else c_nl(cfg, 4, "D")
    if lvl == 5:
        return c_nl(cfg, 5) if i % 2 else c_one(cfg, 5)
    if lvl == 6:
        return c_multi(cfg, 6) if i % 2 else c_nl(cfg, 6)
    return c_classic(cfg, 7) if i % 2 == 0 else c_multi(cfg, 7, "S")


def deg_steps(cfg):
    p = V("p")
    st = [(p, p), (p, C(p, W(p, N(p)))), (p, W(C(p, p), C(N(p), p))), (p, W(p, C(N(p), p))),
          (W(p, C(N(p), p)), W(C(p, p), C(N(p), p))), (W(C(p, p), C(N(p), p)), C(W(p, N(p)), p)),
          (C(W(p, N(p)), p), p), (W(p, C(N(p), p)), p)]
    assert all(SY.provable("s", a, b) for a, b in st)
    body = ("## Условие\n\nБуква $p$ — элементарное высказывание. В доказательстве MT2 § 3 гл. 4 (с. 67) приведены формулы "
            "без оснований:\n\n" + "\n".join(f"{i + 1}. ${ftex(a, b)}$" for i, (a, b) in enumerate(st)) +
            "\n\nПроверьте, что каждая из них — сильная тавтология (значит, доказуема в $S^s$), и скажите, что доказано.\n\n"
            "## Ответ\n\nВсе восемь — сильные тавтологии; доказано $p \\dashv\\vdash p \\vee \\sim pp$ (строки 4 и 8).\n\n"
            "## Решение\n\nКаждая — тавтология, и в заключение входит только $p$. По полноте $S^s$ (гл. 2, § 2, MT5) все "
            "доказуемы. Каноническая форма $p$ — $p \\vee \\sim pp$ (с. 67).")
    return card(cfg["ch"], cfg["sec"], 4, "D", "complete", "sym", "short", cfg["tags"], body, "с. 67, гл. 4, § 3", "S^5")


def mixed(sec, levels, diag, keys, lang_mix=("c", "w")):
    out = []
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            if lvl > 7:
                continue
            k = keys[(i + lvl) % len(keys)]
            lang = lang_mix[i % len(lang_mix)]
            cfg = mk(17, sec, k, lang, SYSTEX[k] if k != "s" else "$S^1$", None, "смешанный",
                     "смешанный набор", SY.MT[k], SY.MT[k], [], 0)
            d = len([c for c in out if "type: E" in c]) < diag and lvl in (3, 4, 5, 6) and i % 3 == 0
            c = None
            while c is None:
                c = make(cfg, lvl, d, i, None)
            c = c.replace("step: iso", "step: mixed").replace("step: open", "step: mixed").replace(
                "step: transfer", "step: mixed").replace("step: vary", "step: mixed").replace("step: complete", "step: mixed")
            c = c.replace('source: "с. 72–73, гл. 5, § 2"', 'source: "' + {2: "гл. 1, § 4–7", 3: "гл. 1–2", 4: "гл. 1–3"}[sec] + '"')
            out.append(c)
    return out


def main():
    cards = []
    for cfg in CFG:
        cards += fill(cfg)
    cards += n_cards(None)
    cards += mixed(2, [0, 0, 1, 3, 11, 13, 8, 0, 0, 0], 11, ["s"])
    cards += mixed(3, [0, 3, 4, 1, 5, 6, 4, 0, 0, 0], 6, ["s"])
    cards += mixed(4, [0, 3, 3, 0, 0, 0, 0, 0, 0, 0], 1, ["s", "w"])
    (ROOT / "drafts" / "19-30-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(cards))


if __name__ == "__main__":
    main()
