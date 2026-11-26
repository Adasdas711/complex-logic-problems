#!/usr/bin/env python3
"""Серии для занятий 61–70: гл. 8, § 5–7; гл. 9 (теория терминов); гл. 10, § 1–8 (логика классов);
смешанные 17.09 (окончание) и 17.10 (начало). Пишет drafts/61-70-gen.md.
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

spec = importlib.util.spec_from_file_location("g07_08", ROOT / "scripts" / "gen" / "g07_08.py")
G7 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G7)
G7.rnd.seed(6170)
G7.G6.rnd.seed(6171)
G7.G6.G.rnd.seed(6172)
rnd = random.Random(6173)
card, fresh, items, answers, build, relabel = G7.card, G7.fresh, G7.items, G7.answers, G7.build, G7.relabel
USED = G7.USED
L = G7.L



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

def permute2(strs, letters="abc"):
    p = dict(zip(letters, rnd.sample(letters, len(letters))))

    def rm(m):
        return tex_map(m.group(0), p)
    return [re.sub(r"\$[^$]+\$", rm, s) for s in strs]


COUNTERS = {}


def nxt(key):
    COUNTERS[key] = COUNTERS.get(key, -1) + 1
    return COUNTERS[key]


def E(sec_ch, sec, lvl, pre, claim, why, src, tags, system=None, form="sym"):
    return card(sec_ch, sec, lvl, "E", "open", f"{pre} Студент: {claim}. Найдите ошибку.", f"Неверно: {why}.",
                f"{src[0].upper() + src[1:]}.", src, tags, form=form, system=system)


def pick_e(pool, ch, sec, pre, src, tags, system=None):
    def f(lvl):
        s, w = rnd.choice(pool)
        return E(ch, sec, lvl, pre, s, w, src, tags, system)
    return f


# ================================================================ гл. 8, § 5–7
PP = G7.PP
D85 = [("Предикаты $b$ и $c$ дедуктивно связаны", "доказуема хотя бы одна из формул $(a \\leftarrow b) \\vdash (a \\leftarrow c)$ и $(a \\leftarrow c) \\vdash (a \\leftarrow b)$", "D1"),
       ("Предикат $b$ дедуктивно включается в $c$", "доказуема $(a \\leftarrow c) \\vdash (a \\leftarrow b)$", "D2"),
       ("Предикаты $b$ и $c$ дедуктивно эквивалентны", "доказуемы обе формулы $(a \\leftarrow b) \\vdash (a \\leftarrow c)$ и $(a \\leftarrow c) \\vdash (a \\leftarrow b)$", "D3"),
       ("Предикат $b$ дедуктивно сильнее $c$", "доказуема $(a \\leftarrow b) \\vdash (a \\leftarrow c)$ и недоказуема $(a \\leftarrow c) \\vdash (a \\leftarrow b)$", "D4")]
PRED = [("«квадрат»", "«прямоугольник»"), ("«делится на 6»", "«делится на 3»"), ("«равносторонний треугольник»", "«равнобедренный треугольник»"),
        ("«ель»", "«хвойное дерево»"), ("«простое число больше 2»", "«нечётное число»"), ("«сосна»", "«дерево»"), ("«ромб»", "«параллелограмм»")]


def c805(lvl):
    b, c = rnd.choice(PRED)
    q = rnd.choice(["сильнее", "включается", "эквивалентны", "связаны"])
    cond = (f"Пусть доказуема $(a \\leftarrow b) \\vdash (a \\leftarrow c)$ и недоказуема $(a \\leftarrow c) \\vdash (a \\leftarrow b)$, где $b$ — {b}, $c$ — {c}. "
            "Какие из отношений D1–D4 § 5 гл. 8 (с. 135) имеют место между $b$ и $c$? Для каждого укажите, в каком порядке.")
    ans = "$b$ и $c$ дедуктивно связаны (D1); $c$ дедуктивно включается в $b$ (D2); $b$ дедуктивно сильнее $c$ (D4); не эквивалентны (D3)."
    return card(8, 5, lvl, "C", "iso", cond, ans, "D1–D4, с. 135.", "с. 135, гл. 8, § 5", "предикация, дедуктивные связи", form="nat")


def c805b(lvl):
    its = rnd.sample(D85, 3)
    rnd.shuffle(its)
    return card(8, 5, lvl, "C", "iso", "Сформулируйте условия доказуемости, при которых (§ 5 гл. 8, с. 135):\n\n" + items([s for s, _, _ in its]),
                answers([f"{w} ({n})" for _, w, n in its]), "С. 135.", "с. 135, гл. 8, § 5", "предикация, дедуктивные связи")


def c805c(lvl):
    b, c = rnd.choice(PRED)
    return card(8, 5, lvl, "S" if lvl == 7 else "C", "transfer", f"Предикат $b$ — {b}, $c$ — {c}; $b$ дедуктивно сильнее $c$. Какие формулы надо "
                "доказать, чтобы установить, что $b$ дедуктивно категорически сильнее $c$ (D5 § 5 гл. 8): а) в неклассическом случае; б) в классическом?",
                "а) $(a \\leftarrow b) \\vdash (a \\leftarrow c)$, $(a \\urcorner\\!\\leftarrow c) \\vdash (a \\urcorner\\!\\leftarrow b)$, $(a? \\leftarrow c) \\vdash \\sim(a \\leftarrow b)$; "
                "б) $(a \\leftarrow b) \\vdash (a \\leftarrow c)$ и $\\sim(a \\leftarrow c) \\vdash \\sim(a \\leftarrow b)$.", "D5, с. 135.", "с. 135, гл. 8, § 5",
                "предикация, дедуктивные связи", form="nat")


E805 = [("«если $b$ дедуктивно включается в $c$, то доказуема $(a \\leftarrow b) \\vdash (a \\leftarrow c)$»", "по D2 (с. 135) $b$ включается в $c$, если "
         "доказуема $(a \\leftarrow c) \\vdash (a \\leftarrow b)$"),
        ("«дедуктивно связанные предикаты всегда дедуктивно эквивалентны»", "для связи (D1) достаточно одной из двух формул, для эквивалентности (D3) "
         "нужны обе (с. 135)"),
        ("«в неклассическом случае для D5 достаточно $(a \\leftarrow b) \\vdash (a \\leftarrow c)$ и $\\sim(a \\leftarrow c) \\vdash \\sim(a \\leftarrow b)$»",
         "этого достаточно только в классическом случае; в неклассическом нужны $(a \\urcorner\\!\\leftarrow c) \\vdash (a \\urcorner\\!\\leftarrow b)$ и "
         "$(a? \\leftarrow c) \\vdash \\sim(a \\leftarrow b)$ (с. 135)"),
        ("«если $b$ дедуктивно сильнее $c$, то недоказуема $(a \\leftarrow b) \\vdash (a \\leftarrow c)$»", "по D4 (с. 135) она доказуема, а недоказуема обратная")]


def m805(lvl, d, i):
    if d:
        s, w = rnd.choice(E805)
        return E(8, 5, lvl, PP, s, w, "с. 135, гл. 8, § 5", "предикация, дедуктивные связи, диагностика")
    if lvl == 7:
        return c805c(7)
    return [c805, c805b][i % 2](lvl) if lvl != 6 else c805c(6)


T86 = [("\\sim(\\forall a)\\sim(a \\leftarrow b) \\vdash (\\urcorner\\forall a)\\sim(a \\leftarrow b) \\vee (?\\forall a)\\sim(a \\leftarrow b)", "T1"),
       ("(\\forall a)(a \\leftarrow b) \\vdash (\\urcorner\\exists a)(a \\urcorner\\!\\leftarrow b)(\\urcorner\\exists a)(a? \\leftarrow b)", "T3"),
       ("(\\urcorner\\forall a)(a \\leftarrow b) \\vdash (\\exists a)(a \\urcorner\\!\\leftarrow b) \\vee (\\exists a)(a? \\leftarrow b)", "T4"),
       ("(\\urcorner\\forall a)(a \\urcorner\\!\\leftarrow b) \\vdash (\\exists a)(a \\leftarrow b) \\vee (\\exists a)(a? \\leftarrow b)", "T5"),
       ("(\\urcorner\\exists a)(a \\leftarrow b) \\vdash (\\forall a)(a \\urcorner\\!\\leftarrow b) \\vee (\\exists a)(a? \\leftarrow b)", "T6")]


def m806(lvl, d, i):
    if d:
        pool = [("«в $S^s_{nq}$ доказуема $\\sim(\\forall a)\\sim x \\dashv\\vdash (\\exists a)x$, как в классическом случае»", "по § 6 гл. 8 (с. 135) "
                 "такие формулы в $S^s_{nq}$ недоказуемы"),
                ("«T3 § 6 гл. 8 доказуема уже в $S^s_{nq}$ без теории предикации»", "T1–T6 имеют силу в теории кванторов, расширенной за счёт "
                 "дополнения § 1 (теории предикации) (с. 136)"),
                ("«T4: $(\\urcorner\\forall a)(a \\leftarrow b) \\vdash (\\exists a)(a \\urcorner\\!\\leftarrow b)$»", "в заключении T4 — дизъюнкция "
                 "$(\\exists a)(a \\urcorner\\!\\leftarrow b) \\vee (\\exists a)(a? \\leftarrow b)$ (с. 136)")]
        s, w = rnd.choice(pool)
        return E(8, 6, lvl, PP, s, w, "с. 135–136, гл. 8, § 6", "предикация и кванторы, диагностика")
    if lvl in (2, 3, 4):
        its = rnd.sample(T86, 3)
        return card(8, 6, lvl, "R" if lvl == 2 else "C", "iso", f"{PP} Укажите номера теоремных схем § 6 гл. 8 (с. 136):\n\n" + items([f"${s}$" for s, _ in its]),
                    answers([n for _, n in its]), "С. 136.", "с. 136, гл. 8, § 6", "предикация и кванторы")
    if lvl == 5:
        RD = {"T3": "Если все $a$ имеют $b$, то нет таких $a$, которые не имеют $b$, и нет таких $a$, которые неопределённо имеют $b$",
              "T4": "Если не все $a$ имеют $b$ (внутреннее отрицание), то некоторые $a$ не имеют $b$ или некоторые $a$ неопределённо имеют $b$",
              "T5": "Если не все $a$ не имеют $b$, то некоторые $a$ имеют $b$ или некоторые $a$ неопределённо имеют $b$",
              "T6": "Если нет таких $a$, которые имеют $b$, то все $a$ не имеют $b$ или некоторые $a$ неопределённо имеют $b$"}
        n = ["T3", "T4", "T5", "T6"][i % 4]
        s = dict((nn, ss) for ss, nn in T86)[n]
        return card(8, 6, 5, "C", "iso", f"{PP} Прочитайте теоремную схему {n} § 6 гл. 8 (с. 136) на обычном языке, пользуясь чтениями кванторов "
                    f"$(\\urcorner\\forall a)$ — «не все $a$», $(\\urcorner\\exists a)$ — «нет таких $a$»: ${s}$.", RD[n] + ".",
                    "Чтения операторов — Введение, § 3, 5; схема — с. 136.", "с. 136, гл. 8, § 6", "предикация и кванторы", form="nat", answ="text")
    pool = [("$\\sim(\\forall a)\\sim(a \\leftarrow b) \\vdash (\\exists a)(a \\leftarrow b)$", "нет / да", "в $S^s_{nq}$ недоказуема (с. 135; MT3 § 15 гл. 7); в $S^s_{cq}$ — T37"),
            ("$(\\forall a)(a \\leftarrow b) \\vdash (\\urcorner\\exists a)(a \\urcorner\\!\\leftarrow b)$", "да / —", "следует из T3 § 6 гл. 8 по $S^s$; в $S^s_{cq}$ нет оператора $\\urcorner$"),
            ("$\\sim(\\exists a)\\sim(a \\leftarrow b) \\vdash (\\forall a)(a \\leftarrow b)$", "нет / да", "в $S^s_{nq}$ недоказуема (с. 135, 126); в $S^s_{cq}$ — A7"),
            ("$(\\forall a)(a \\leftarrow b) \\vdash \\sim(\\exists a)\\sim(a \\leftarrow b)$", "да / да", "в обоих случаях: A6 (A¹6 и T-схемы для $S^s_{nq}$ через $\\sim$) — "
             "бескванторная форма $x \\vdash \\sim\\sim x$")]
    pool = pool[:3]
    its = rnd.sample(pool, 2)
    return card(8, 6, lvl, "S" if lvl == 7 else "C", "transfer", f"{PP} Доказуемы ли формулы в неклассической теории кванторов, расширенной теорией "
                "предикации, и в $S^s_{cq}$?\n\n" + items([s for s, _, _ in its]), answers([a for _, a, _ in its]),
                "\n".join(f"{L[k]}) {w}." for k, (_, _, w) in enumerate(its)), "с. 135–136, гл. 8, § 6", "предикация и кванторы")


Q87 = [("Почему, по § 7 гл. 8, логику нельзя построить как одну систему по образцу $S^s$, $S^s_{cq}$?", "Построение логики — процесс, протекающий в "
        "различных планах («измерениях»); построить её в одной «плоскости» невозможно (с. 136)."),
       ("В каком смысле логические системы, по § 7 гл. 8, остаются незамкнутыми?", "Определённые в них операторы остаются неопределёнными "
        "относительно комбинаций с другими возможными операторами, отсутствующими в этих системах (с. 136)."),
       ("За счёт чего может быть расширена теория предикации (§ 7 гл. 8)?", "За счёт учёта строения субъектов и предикатов (с. 136; это делается "
        "в гл. 9)."),
       ("Какое обстоятельство, по § 7 гл. 8, оправдывает название «комплексная логика»?", "Построение логики протекает в различных планах, логика "
        "не строится как одна система, а системы остаются незамкнутыми (с. 136).")]


def m807(lvl, d, i):
    if d:
        pool = [("«$S^s_p$ полностью определяет свойства оператора $\\leftarrow$, так что новые системы ничего о нём не добавят»", "по § 7 (с. 136) "
                 "системы незамкнуты: $\\leftarrow$ не определён в комбинациях с кванторами — это добавляет § 6 (T1–T6)"),
                ("«комплексная логика — это одна большая система, объединяющая $S^s$, $S^s_{cq}$, $S^s_p$»", "по § 7 (с. 136) построить логику как одну "
                 "систему (в одной «плоскости») невозможно")]
        s, w = rnd.choice(pool)
        return E(8, 7, lvl, PP, s, w, "с. 136, гл. 8, § 7", "предикация, расширения, диагностика")
    if lvl in (2, 3):
        q, a = rnd.choice(Q87)
        return card(8, 7, lvl, "R" if lvl == 2 else "C", "iso", q, a, "С. 136.", "с. 136, гл. 8, § 7", "предикация, расширения", form="meta", answ="text")
    pool = [("оператор $\\leftarrow$ ($S^s_p$) и кванторы ($S^s_{nq}$)", "T1–T6 § 6 гл. 8 (с. 136): соединение теорий даёт новые теоремы, недоказуемые в каждой отдельно"),
            ("оператор условности ($S^s_{if}$) и кванторы ($S^s_{cq}$)", "аксиомные схемы § 21 гл. 7 (с. 131)"),
            ("кванторы и термины вида $(a^1, \\ldots, a^n)$", "схемы A*I § 20 гл. 7 (с. 130–131)"),
            ("кванторы и кванторные группы вида $((K^1a) \\cdot (K^2b))$", "схемы A*II § 20 гл. 7 (с. 131)"),
            ("внутреннее отрицание $\\urcorner$ и кванторы", "система $S^s_{nq}$, § 12 гл. 7 (с. 122–123)"),
            ("оператор $\\leftarrow$ и строение субъектов и предикатов", "гл. 9 (теория терминов), например AIII § 3 (с. 142–143)")]
    k = {4: 1, 5: 2, 6: 2, 7: 3}[lvl]
    its = rnd.sample(pool, k)
    return card(8, 7, lvl, "S" if lvl == 7 else "C", "transfer", "Проиллюстрируйте тезис § 7 гл. 8 о незамкнутости логических систем на примере "
                + " и ".join(s for s, _ in its) + ": где в книге определяются их комбинации?", answers([w for _, w in its]) if k > 1 else its[0][1],
                "С. 136; отсылки к соответствующим параграфам.", "с. 136, гл. 8, § 7", "предикация, расширения", form="meta", answ="text")


# ================================================================ гл. 9, § 1: термины
TERMS = [("$(a \\cdot b)$, где $a$, $b$ — предикаты", "предикат (D1, п. 2)"), ("$(a \\cdot b)$, где $a$, $b$ — субъекты", "субъект (D2, п. 2)"),
         ("$(a, b)$, где $a$, $b$ — субъекты", "субъект (D2, п. 2); как предикат не определён"), ("$\\downarrow x$, где $x$ — высказывание", "субъект (D2, п. 5)"),
         ("$x \\downarrow$, где $x$ — высказывание", "предикат (D1, п. 5)"), ("$a \\downarrow x$, где $a$ — предикат", "предикат (D1, п. 4)"),
         ("$a \\downarrow x$, где $a$ — субъект", "субъект (D2, п. 4)"), ("$[a]$, где $a$ — предикат", "субъект (D2, п. 6)"),
         ("$\\tilde a$, где $a$ — предикат", "предикат (D1, п. 3)"), ("$\\sim a$, где $a$ — субъект", "субъект (D2, п. 3)"),
         ("$(\\vee (a, b))$, где $a$, $b$ — предикаты", "предикат (D1, п. 2)"), ("$(\\cdot(a^1, a^2, a^3))$, где $a^i$ — субъекты", "субъект (D2, п. 2)"),
         ("$sc$", "универсальный субъект («объект»), простой субъект"), ("$pc$", "универсальный предикат («признак»)"),
         ("$\\rightharpoonup$", "двухместный простой предикат включения (п. 1 D1)")]


def c901(lvl, typ="R"):
    its = rnd.sample(TERMS, 4)
    return card(9, 1, lvl, typ, "iso", "Что представляет собой каждое выражение по определениям § 1 гл. 9 (с. 137–138)?\n\n" + items([s for s, _ in its]),
                answers([w for _, w in its]), "D1 (предикат), D2 (субъект), D3: субъекты и предикаты (и только они) суть термины.",
                "с. 137–138, гл. 9, § 1", "термины, определения")


READ = [("$a \\rightharpoonup b$, $a$ — «геометрическая фигура», $b$ — «треугольник»", "«Треугольник есть геометрическая фигура»: каждый треугольник может быть назван и геометрической фигурой"),
        ("$a \\rightharpoonup b$, $a$ — «ромб», $b$ — «равносторонний четырёхугольник»", "«Равносторонний четырёхугольник есть ромб»"),
        ("$a \\rightharpoonup b$, $a$ — «млекопитающее», $b$ — «кит»", "«Кит есть млекопитающее»"),
        ("$a \\rightleftharpoons b$, $a$ — «ромб», $b$ — «равносторонний четырёхугольник»", "«Ромб есть равносторонний четырёхугольник, и равносторонний четырёхугольник есть ромб» (D4)"),
        ("$a \\rightharpoonup b$, $a$ — «число», $b$ — «чётное число»", "«Чётное число есть число»"),
        ("$(ab)$, $a$ — «писатель», $b$ — «художник»", "предмет, который может быть назван и писателем, и художником (писатель — художник)"),
        ("$\\sim a$, $a$ — «стол»", "«не-стол»: не являющийся столом, не называемый столом"),
        ("$\\tilde a$, $a$ — «знание»", "«незнание» — противоположный предмет")]


def c901r(lvl, typ="C"):
    its = rnd.sample(READ, 3)
    return card(9, 1, lvl, typ, "iso", "Прочитайте выражения по § 1 гл. 9 (с. 138–139):\n\n" + items([s for s, _ in its]), answers([w for _, w in its]),
                "С. 138–139: $a \\rightharpoonup b$ читается «$b$ есть $a$».", "с. 138–139, гл. 9, § 1", "термины, чтение", form="nat")


NATINC = [("«Всякий квадрат есть прямоугольник»", "a \\rightharpoonup b", "$a$ — «прямоугольник», $b$ — «квадрат»"),
          ("«Всякая ель есть дерево»", "a \\rightharpoonup b", "$a$ — «дерево», $b$ — «ель»"),
          ("«Ромб и равносторонний четырёхугольник — одно и то же по значению»", "a \\rightleftharpoons b", "$a$ — «ромб», $b$ — «равносторонний четырёхугольник»"),
          ("«Всякий кит есть млекопитающее»", "a \\rightharpoonup b", "$a$ — «млекопитающее», $b$ — «кит»")]


def c901w(lvl, typ="C"):
    s, f, leg = rnd.choice(NATINC)
    return card(9, 1, lvl, typ, "iso", f"Запишите в символике § 1 гл. 9 высказывание {s} (как высказывание о включении терминов по значению).",
                f"${f}$, где {leg}", "С. 139: $a \\rightharpoonup b$ — «$b$ есть $a$»; $a \\rightleftharpoons b$ — сокращение для $(a \\rightharpoonup b)(b \\rightharpoonup a)$.",
                "с. 139, гл. 9, § 1", "термины, включение", form="nat")


E901 = [("«$a \\rightharpoonup b$ читается “$a$ есть $b$”»", "по с. 139 $a \\rightharpoonup b$ читается «$b$ есть $a$»: каждый предмет, обозначаемый $b$, может быть обозначен и $a$"),
        ("«$(\\cdot(a, b))$ и $(ab)$ — один и тот же термин»", "по с. 138–139 это термины разного типа: $(ab)$ обозначает предмет, называемый и $a$, и $b$; "
         "$(\\cdot(a, b))$ имеет смысл лишь как часть высказывания («каждый из»)"),
        ("«$\\sim a$ и $\\tilde a$ — одно и то же: “не-знание” и “незнание”»", "по с. 138 $\\sim a$ — «не являющийся $a$», $\\tilde a$ — противоположный предмет"),
        ("«$(a^1, \\ldots, a^n)$ есть и субъект, и предикат»", "по D2, п. 2 это субъект; в D1 такой предикат не вводится (с. 137–138)"),
        ("«$[a]$ — предикат, если $a$ — предикат»", "по D2, п. 6 $[a]$ есть субъект (с. 138)"),
        ("«Определения D1, D2 описывают все возможные субъекты и предикаты»", "по с. 138 они не исчерпывают всех возможных терминов")]


def m901(lvl, d, i):
    if d:
        s, w = rnd.choice(E901)
        return E(9, 1, lvl, "Буквы $a, b$ — термины; $x$ — высказывание.", s, w, "с. 137–139, гл. 9, § 1", "термины, диагностика")
    if lvl == 1:
        return c901(1)
    if lvl == 2:
        return [c901, c901r, c901w][i % 3](2, "C")
    if lvl == 3:
        return [c901r, c901w, c901][i % 3](3, "C")
    if lvl in (4, 5, 6):
        return c901w(lvl) if i % 2 else c901r(lvl)
    return card(9, 1, 7, "S", "transfer", "Сравните предложения «Писатель и художник создаёт духовные ценности» и «Писатель-художник создаёт духовные "
                "ценности». Какие термины (§ 1 гл. 9) в них употреблены?", "В первом — $(\\cdot(a, b))$ («каждый из»): и писатель, и художник создаёт "
                "ценности; во втором — $(ab)$: предмет, являющийся и писателем, и художником.", "С. 138.", "с. 138, гл. 9, § 1", "термины", form="nat")


# ================================================================ гл. 9, § 2: S¹_t
def ttex(f):
    k = f[0]
    if k == "v":
        return f[1]
    if k == "neg":
        g = f[1]
        return "\\sim " + (ttex(g) if g[0] in ("v", "neg") else f"({ttex(g)})")
    if k == "conj":
        return "".join(ttex(a) if a[0] in ("v", "neg") else f"({ttex(a)})" for a in f[1])
    if k == "wdis":
        return " \\vee ".join(ttex(a) for a in f[1])
    raise ValueError(k)


def inc(a, b):
    pa = ttex(a) if a[0] in ("v", "neg", "conj") else f"({ttex(a)})"
    pb = ttex(b) if b[0] in ("v", "neg", "conj") else f"({ttex(b)})"
    return f"{pa} \\rightharpoonup {pb}"


def prov_inc(a, b):
    """MT1–MT3 § 2 гл. 9: ⊢(a ⇀ b) доказуема ⇔ b ⊃ a тавтология и есть общий термин."""
    return Q.is_taut(Q.IMP(b, a)) and bool(Q.atoms(a) & Q.atoms(b))


def rterm(depth=2, letters="abc"):
    if depth == 0 or rnd.random() < 0.3:
        return V(rnd.choice(letters))
    k = rnd.choice(["neg", "conj", "wdis", "conj"])
    if k == "neg":
        return N(rterm(depth - 1, letters))
    x1, x2 = rterm(depth - 1, letters), rterm(depth - 1, letters)
    while x1 == x2:
        x2 = rterm(depth - 1, letters)
    return (k, (x1, x2))


def inc_card(lvl, typ="C"):
    its = []
    for want in rnd.sample([True, True, False, False], 4):
        for _ in range(500):
            a, b = rterm(2), rterm(2)
            if Q.is_taut(a) or Q.is_taut(N(a)) or Q.is_taut(b) or Q.is_taut(N(b)):
                continue
            if prov_inc(a, b) == want and a != b and repr((a, b)) not in USED:
                USED.add(repr((a, b)))
                its.append((a, b))
                break
    cond = ("Буквы $a, b, c$ — простые термины. Доказуемы ли в $S^1_t$ (§ 2 гл. 9) формулы? Пользуйтесь MT1–MT3 (с. 140–141): $a \\rightharpoonup b$ "
            "равнозначна $b \\supset a$, если $a$ и $b$ рассматривать как высказывания.\n\n" + items([f"$\\vdash ({inc(a, b)})$" for a, b in its]))
    sol = []
    for a, b in its:
        t = Q.is_taut(Q.IMP(b, a))
        com = bool(Q.atoms(a) & Q.atoms(b))
        sol.append(("$" + ttex(b) + " \\supset " + ttex(a) + "$ — " + ("тавтология" if t else "не тавтология") +
                    ("" if not t else ("; общий термин есть — доказуема (MT3)" if com else "; общего термина нет — недоказуема (MT1)"))) +
                   ("" if t else " — недоказуема (MT2)"))
    return card(9, 2, lvl, typ, "iso", cond, answers(["да" if prov_inc(a, b) else "нет" for a, b in its]),
                "\n".join(f"{L[k]}) {s}." for k, s in enumerate(sol)), "с. 140–141, гл. 9, § 2", "термины, S1t", system="S^1_t")


AI9 = {1: "\\vdash \\sim\\sim a \\rightleftharpoons a", 2: "\\vdash a \\rightharpoonup ab", 3: "\\vdash ab \\rightharpoonup ba",
       5: "\\vdash \\sim(ab) \\rightleftharpoons (\\sim a \\vee \\sim b)", 6: "\\vdash (a \\rightharpoonup b) \\to (\\sim b \\rightharpoonup \\sim a)",
       7: "\\vdash (a \\rightharpoonup b)(b \\rightharpoonup c) \\to (a \\rightharpoonup c)", 8: "\\vdash (a \\rightharpoonup c)(b \\rightharpoonup c) \\to (ab \\rightharpoonup c)",
       9: "\\vdash (a \\rightharpoonup b) \\to \\sim(\\sim a \\rightharpoonup b)", 10: "\\vdash (\\tilde{\\tilde a} \\rightleftharpoons a)",
       11: "\\vdash (\\widetilde{ab} \\rightleftharpoons (\\tilde a \\vee \\tilde b))", 12: "\\vdash (\\sim a \\rightharpoonup \\tilde a)"}
T9 = {1: "\\vdash (a \\vee b) \\rightharpoonup a", 2: "\\vdash a \\rightharpoonup a", 3: "\\vdash aa \\rightharpoonup a", 4: "\\vdash (ad \\rightharpoonup c) \\to (a \\rightharpoonup c)",
      5: "\\vdash (a \\rightharpoonup b)(a \\rightharpoonup c) \\to (a \\rightharpoonup (b \\vee c))", 6: "\\vdash (a \\rightharpoonup (b \\vee c)) \\to (a \\rightharpoonup bc)",
      7: "\\vdash (a \\vee b) \\rightharpoonup (b \\vee a)", 8: "\\vdash (a \\rightharpoonup b)(c \\rightharpoonup d) \\to ((a \\vee c) \\rightharpoonup (b \\vee d))",
      9: "\\vdash a \\rightharpoonup (a \\vee \\sim bb)"}


def ai_rec(lvl, typ="R"):
    ks = rnd.sample(sorted(AI9), 4)
    return card(9, 2, lvl, typ, "iso", "Буквы $a, b, c$ — термины. Каким аксиомным схемам AI системы $S^1_t$ (с. 139–140) соответствуют формулы?\n\n" +
                items([f"${AI9[k]}$" for k in ks]), answers([f"AI.{k}" for k in ks]), "С. 139–140.", "с. 139–140, гл. 9, § 2", "термины, S1t", system="S^1_t")


def t9_rec(lvl, typ="C"):
    ks = rnd.sample(sorted(T9), 3)
    return card(9, 2, lvl, typ, "iso", "Буквы $a, b, c, d$ — термины. Укажите номера теоремных схем $S^1_t$ (с. 140):\n\n" + items([f"${T9[k]}$" for k in ks]),
                answers([f"T{k}" for k in ks]), "С. 140.", "с. 140, гл. 9, § 2", "термины, S1t", system="S^1_t")


def t9_check(lvl, typ="C"):
    pure = {1: (W(V("a"), V("b")), V("a")), 2: (V("a"), V("a")), 3: (C(V("a"), V("a")), V("a")), 7: (W(V("a"), V("b")), W(V("b"), V("a"))),
            9: (V("a"), W(V("a"), C(N(V("b")), V("b"))))}
    ks = rnd.sample(sorted(pure), 2)
    return card(9, 2, lvl, typ, "iso", "Проверьте по MT2 и MT3 § 2 гл. 9, что теоремные схемы $S^1_t$ доказуемы:\n\n" + items([f"T{k}. ${T9[k]}$" for k in ks]),
                answers([f"$" + ttex(pure[k][1]) + " \\supset " + ttex(pure[k][0]) + "$ — тавтология, общий термин есть" for k in ks]),
                "MT3 (с. 141): тавтология $\\vdash (a \\rightharpoonup b)$ с общим термином доказуема. Для T9 заметим: $\\sim bb$ — противоречие.",
                "с. 140–141, гл. 9, § 2", "термины, S1t", system="S^1_t")


E902 = [("«$\\vdash (a \\vee \\sim a) \\rightharpoonup b$ доказуема: $b \\supset a \\vee \\sim a$ — тавтология»", "по MT1 (с. 140) в доказуемой "
         "$\\vdash (a \\rightharpoonup b)$ должен быть общий термин; у $a \\vee \\sim a$ и $b$ его нет"),
        ("«$\\vdash a \\rightharpoonup (a \\vee b)$ доказуема: $a$ входит в обе части»", "$(a \\vee b) \\supset a$ не тавтология, а по MT2 (с. 141) "
         "доказуемы только тавтологии; доказуема обратная — T1 $\\vdash (a \\vee b) \\rightharpoonup a$"),
        ("«$\\vdash ab \\rightharpoonup a$ — это AI.2»", "AI.2 — $\\vdash a \\rightharpoonup ab$ (с. 139); $ab \\supset a$, а не $a \\supset ab$"),
        ("«$a \\rightharpoonup b$ равнозначна $a \\supset b$»", "по с. 141 $a \\rightharpoonup b$ равнозначна $b \\supset a$"),
        ("«AI.6: $\\vdash (a \\rightharpoonup b) \\to (\\sim a \\rightharpoonup \\sim b)$»", "AI.6 — $\\vdash (a \\rightharpoonup b) \\to (\\sim b \\rightharpoonup \\sim a)$ (с. 140)")]


def m902(lvl, d, i):
    if d:
        s, w = rnd.choice(E902)
        return E(9, 2, lvl, "Буквы $a, b$ — термины.", s, w, "с. 139–141, гл. 9, § 2", "термины, S1t, диагностика", system="S^1_t")
    if lvl == 1:
        return ai_rec(1)
    if lvl == 2:
        return ai_rec(2, "C") if i % 2 else t9_rec(2)
    if lvl == 3:
        return [t9_rec, t9_check, ai_rec][i % 3](3, "C") if i % 3 != 2 else ai_rec(3, "C")
    if lvl == 4:
        return t9_check(4, "D") if i % 2 == 0 else inc_card(4)
    if lvl == 7:
        return inc_card(7, "S")
    return inc_card(lvl)


# ================================================================ гл. 9, § 3: S²_t
AIII9 = {1: "(a \\leftarrow (\\cdot(b, c))) \\dashv\\vdash (a \\leftarrow b)(a \\leftarrow c)", 2: "((\\cdot(a, b)) \\leftarrow c) \\dashv\\vdash (a \\leftarrow c)(b \\leftarrow c)",
         3: "(a \\leftarrow (\\vee(b, c))) \\dashv\\vdash (a \\leftarrow b) \\vee (a \\leftarrow c)", 4: "((\\vee(a, b)) \\leftarrow c) \\dashv\\vdash (a \\leftarrow c) \\vee (b \\leftarrow c)",
         6: "(\\forall a)(a \\leftarrow c)(\\forall b)(b \\leftarrow c) \\vdash (\\forall(ab))((ab) \\leftarrow c)",
         8: "(\\exists(ab))((ab) \\leftarrow c) \\vdash (\\exists a)(a \\leftarrow c)(\\exists b)(b \\leftarrow c)",
         10: "(\\exists a)(a \\leftarrow c) \\vee (\\exists b)(b \\leftarrow c) \\dashv\\vdash (\\exists(a \\vee b))((a \\vee b) \\leftarrow c)",
         12: "(\\forall a)(a \\leftarrow c) \\vee (\\forall b)(b \\leftarrow c) \\vdash (\\forall(a \\vee b))((a \\vee b) \\leftarrow c)",
         14: "(\\forall a)(a \\leftarrow c)(\\exists b)(b \\leftarrow c) \\vdash (\\exists(ab))((ab) \\leftarrow c)"}
AI93 = {3: "(a \\rightharpoonup b)(c \\leftarrow b) \\vdash (c \\leftarrow a)", 4: "(a \\rightharpoonup b)(c \\urcorner\\!\\leftarrow a) \\vdash (c \\urcorner\\!\\leftarrow b)",
        5: "(a \\rightharpoonup b)(c? \\leftarrow a) \\vdash \\sim(c \\leftarrow b)"}
T93 = {1: "\\vdash (a \\leftarrow (bc)) \\to (a \\leftarrow b)(a \\leftarrow c)", 2: "\\vdash (a \\urcorner\\!\\leftarrow b) \\vee (a \\urcorner\\!\\leftarrow c) \\to (a \\urcorner\\!\\leftarrow bc)",
       3: "\\vdash (a \\leftarrow b) \\vee (a \\leftarrow c) \\to (a \\leftarrow (b \\vee c))", 4: "\\vdash (a \\urcorner\\!\\leftarrow (b \\vee c)) \\to (a \\urcorner\\!\\leftarrow b)(a \\urcorner\\!\\leftarrow c)",
       5: "\\vdash \\sim(a \\leftarrow b) \\to \\sim(a \\leftarrow bc)", 6: "\\vdash \\sim(a \\leftarrow (b \\vee c)) \\to \\sim(a \\leftarrow b)",
       7: "\\vdash \\sim(a \\leftarrow (\\widetilde{bb}))", 8: "(a \\leftarrow b) \\vdash \\sim(a \\leftarrow \\tilde b)", 9: "(a \\leftarrow \\tilde b) \\vdash \\sim(a \\leftarrow b)",
       10: "(a \\leftarrow \\tilde b) \\vdash (a \\leftarrow \\sim b)", 11: "\\vdash \\sim((a \\leftarrow b)(a \\leftarrow \\tilde b))"}
AIV9 = {1: "\\vdash (a \\downarrow x) \\downarrow y \\rightleftharpoons (a \\downarrow y) \\downarrow x", 2: "\\vdash x \\to (a \\rightharpoonup a \\downarrow x)",
        3: "\\vdash (a \\downarrow x \\rightharpoonup a)", 6: "\\vdash (x \\to (a \\leftarrow (x \\downarrow)))", 7: "\\vdash (a \\leftarrow (x \\downarrow)) \\to x",
        8: "\\vdash (a \\downarrow x) \\leftarrow (x \\downarrow)"}
NAT3 = [("геометрическая фигура", "треугольник", "этот чертёж"), ("млекопитающее", "кит", "это животное"), ("дерево", "ель", "это растение"),
        ("число", "чётное число", "выражение «2 + 2»"), ("металл", "железо", "этот образец")]


def ai3_nat(lvl, typ="C"):
    a, b, c = rnd.choice(NAT3)
    n = rnd.choice([3, 4])
    if n == 3:
        cond = (f"Пусть $a$ — «{a}», $b$ — «{b}», $c$ — «{c}», и $a \\rightharpoonup b$ («{b} есть {a}»). Что следует по AI.3 § 3 гл. 9 из высказывания "
                f"«{c[0].upper() + c[1:]} имеет признак “{b}”»?")
        ans = f"«{c[0].upper() + c[1:]} имеет признак “{a}”»: $(a \\rightharpoonup b)(c \\leftarrow b) \\vdash (c \\leftarrow a)$."
    else:
        cond = (f"Пусть $a$ — «{a}», $b$ — «{b}», $c$ — «{c}», и $a \\rightharpoonup b$. Что следует по AI.4 § 3 гл. 9 из того, что {c} не имеет признака "
                f"«{a}» ($c \\urcorner\\!\\leftarrow a$)?")
        ans = f"{c[0].upper() + c[1:]} не имеет признака «{b}»: $(a \\rightharpoonup b)(c \\urcorner\\!\\leftarrow a) \\vdash (c \\urcorner\\!\\leftarrow b)$."
    return card(9, 3, lvl, typ, "iso", cond, ans, "С. 142.", "с. 142, гл. 9, § 3", "термины, S2t", form="nat", system="S^2_t")


def ai3_e(lvl):
    a, b, c = rnd.choice(NAT3)
    return card(9, 3, lvl, "E", "open", f"Пусть $a$ — «{a}», $b$ — «{b}». Студент: «{c[0].upper() + c[1:]} имеет признак “{a}”; {b} есть {a}; значит, по AI.3 § 3 "
                f"гл. 9 {c} имеет признак “{b}”». Найдите ошибку.", f"Неверно: AI.3 — $(a \\rightharpoonup b)(c \\leftarrow b) \\vdash (c \\leftarrow a)$: от «{b}» "
                f"к «{a}», а не обратно; $(a \\rightharpoonup b)(c \\leftarrow a) \\vdash (c \\leftarrow b)$ в системе не принимается.", "С. 142.",
                "с. 142, гл. 9, § 3", "термины, S2t, диагностика", form="nat", system="S^2_t")


def rec93(lvl, typ="C"):
    pools = [("AIII", AIII9), ("AI", AI93), ("AIV", AIV9)]
    name, D = rnd.choice(pools)
    ks = rnd.sample(sorted(D), 3)
    return card(9, 3, lvl, typ, "iso", f"Буквы $a, b, c$ — термины; $x, y$ — высказывания. Каким аксиомным схемам {name} системы $S^2_t$ (с. 142–144) "
                "соответствуют формулы?\n\n" + items([f"${D[k]}$" for k in ks]), answers([f"{name}.{k}" for k in ks]), "С. 142–144.",
                "с. 142–144, гл. 9, § 3", "термины, S2t", system="S^2_t")


def t93_rec(lvl, typ="C"):
    ks = rnd.sample(sorted(T93), 3)
    return card(9, 3, lvl, typ, "iso", "Буквы $a, b, c$ — термины. Укажите номера следствий $S^2_t$ (с. 142–143):\n\n" + items([f"${T93[k]}$" for k in ks]),
                answers([f"T{k}" for k in ks]), "С. 142–143.", "с. 142–143, гл. 9, § 3", "термины, S2t", system="S^2_t")


ALPH = [("\\urcorner", "a \\urcorner\\!\\downarrow b", "a \\downarrow (a \\urcorner\\!\\leftarrow b)"), ("?", "a? \\downarrow b", "a \\downarrow (a? \\leftarrow b)"),
        ("", "a \\downarrow b", "a \\downarrow (a \\leftarrow b)"), ("\\sim", "a\\sim \\downarrow b", "a \\downarrow (a \\sim \\leftarrow b)")]


def d1_card(lvl, typ="D"):
    pool = [("a \\urcorner\\!\\downarrow b", "a \\downarrow (a \\urcorner\\!\\leftarrow b)"), ("a? \\downarrow b", "a \\downarrow (a? \\leftarrow b)"),
            ("b \\urcorner\\!\\downarrow a", "b \\downarrow (a \\urcorner\\!\\leftarrow b)"), ("b? \\downarrow a", "b \\downarrow (a? \\leftarrow b)"),
            ("sc? \\downarrow b", "sc \\downarrow (sc? \\leftarrow b)"), ("pc \\urcorner\\!\\downarrow a", "pc \\downarrow (a \\urcorner\\!\\leftarrow pc)")]
    its = rnd.sample(pool, 2)
    return card(9, 3, lvl, typ, "iso", "Раскройте сокращения D1 § 3 гл. 9 (с. 144): $a\\alpha \\downarrow b$ есть $a \\downarrow (a\\,\\alpha \\leftarrow b)$, "
                "$b\\alpha \\downarrow a$ есть $b \\downarrow (a\\,\\alpha \\leftarrow b)$.\n\n" + items([f"${s}$" for s, _ in its]), answers([f"${w}$" for _, w in its]),
                "С. 144, D1.", "с. 144, гл. 9, § 3", "термины, S2t", system="S^2_t")


def tilde_card(lvl, typ="D"):
    pool = [("(c \\leftarrow \\tilde d)", "(c \\urcorner\\!\\leftarrow d)"), ("(c \\urcorner\\!\\leftarrow \\tilde d)", "(c \\leftarrow d)"), ("(c? \\leftarrow \\tilde d)", "(c? \\leftarrow d)"),
            ("(c \\leftarrow (\\cdot(d, e)))", "(c \\leftarrow d)(c \\leftarrow e)"), ("((\\vee(c, d)) \\leftarrow e)", "(c \\leftarrow e) \\vee (d \\leftarrow e)"),
            ("((\\cdot(c, d)) \\leftarrow e)", "(c \\leftarrow e)(d \\leftarrow e)"), ("(c \\leftarrow (\\vee(d, e)))", "(c \\leftarrow d) \\vee (c \\leftarrow e)")]
    its = rnd.sample(pool, 3)
    return card(9, 3, lvl, typ, "iso", "Буквы $c, d, e$ — термины. Преобразуйте высказывания по схемам AIII.1–AIII.5 § 3 гл. 9 (с. 142):\n\n" +
                items([f"${s}$" for s, _ in its]), answers([f"${w}$" for _, w in its]), "AIII.1–5, с. 142.", "с. 142, гл. 9, § 3", "термины, S2t", system="S^2_t")


E903 = [("«$\\vdash (a \\leftarrow b)(a \\leftarrow c) \\to (a \\leftarrow (bc))$ надо принять»", "по с. 143–144 её принимать нельзя: тогда пришлось бы "
         "принять $\\vdash \\sim((a \\leftarrow b)(a \\leftarrow \\sim b))$, что не соответствует смыслу $\\sim b$"),
        ("«Аналогично T8 для $\\sim b$: $(a \\leftarrow b) \\vdash \\sim(a \\leftarrow \\sim b)$»", "утверждения, аналогичные T8 и T11, для $\\sim b$ неприемлемы: "
         "предмет может иметь признак $b$ и другой признак, не обозначаемый $b$ (с. 143)"),
        ("«AIII.5: $(a \\leftarrow \\tilde b) \\dashv\\vdash \\sim(a \\leftarrow b)$»", "AIII.5 — $(a \\leftarrow \\tilde b) \\dashv\\vdash (a \\urcorner\\!\\leftarrow b)$ (с. 142)"),
        ("«AIV.3 $\\vdash (a \\downarrow x \\rightharpoonup a)$ верна без ограничений»", "по с. 144 — если $a$ не входит свободно в $x$ или $\\vdash x$ доказуема"),
        ("«T10: $(a \\leftarrow \\sim b) \\vdash (a \\leftarrow \\tilde b)$»", "T10 — $(a \\leftarrow \\tilde b) \\vdash (a \\leftarrow \\sim b)$ (с. 143)"),
        ("«AIII.1: $(a \\leftarrow (bc)) \\dashv\\vdash (a \\leftarrow b)(a \\leftarrow c)$»", "в AIII.1 стоит термин $(\\cdot(b, c))$, а не $(bc)$; для $(bc)$ "
         "доказуема лишь T1: $\\vdash (a \\leftarrow (bc)) \\to (a \\leftarrow b)(a \\leftarrow c)$ (с. 142)")]


def m903(lvl, d, i):
    if d:
        if i % 3 == 0:
            return ai3_e(lvl)
        s, w = rnd.choice(E903)
        return E(9, 3, lvl, "Буквы $a, b, c$ — термины; $x$ — высказывание.", s, w, "с. 142–144, гл. 9, § 3", "термины, S2t, диагностика", system="S^2_t")
    if lvl == 1:
        return rec93(1, "R")
    if lvl == 2:
        return [rec93, t93_rec, d1_card, tilde_card][i % 4](2, "C") if i % 4 < 2 else [d1_card, tilde_card][i % 2](2)
    if lvl == 3:
        return [tilde_card, d1_card, rec93, t93_rec, ai3_nat][i % 5](3)
    if lvl in (4, 5, 6):
        return [ai3_nat, tilde_card, rec93, t93_rec][i % 4](lvl, "C")
    return ai3_nat(7, "S")


# ================================================================ гл. 9, § 4–7
SYLP = [("A1", "(\\exists a)(a \\leftarrow b) \\dashv\\vdash (\\exists(sc \\downarrow b))((sc \\downarrow b) \\leftarrow (pc \\downarrow a))"),
        ("A*2", "(\\forall a)(a \\leftarrow b) \\dashv\\vdash (\\forall(sc\\sim \\downarrow b))\\sim((sc\\sim \\downarrow b) \\leftarrow (pc \\downarrow a))")]


def m904(lvl, d, i):
    if d:
        pool = [("«в схеме A2 § 4 гл. 9 α, β, γ могут совпадать»", "по с. 145 они означают наличие или отсутствие $\\urcorner$ или ?, причём все различны"),
                ("«классический случай получается заменой схемы A1»", "заменяется схема A2 — схемой A*2 (с. 145)"),
                ("«силлогистика, рассматриваемая в логике, есть силлогистика предикатов»", "по с. 146 фактически это силлогистика классов")]
        s, w = rnd.choice(pool)
        return E(9, 4, lvl, "Буквы $a, b$ — термины.", s, w, "с. 145–146, гл. 9, § 4", "силлогистика предикатов, диагностика")
    if lvl in (2, 3):
        n, f = SYLP[i % 2]
        return card(9, 4, lvl, "R" if lvl == 2 else "C", "iso", f"Какая схема силлогистики предикатов (§ 4 гл. 9, с. 145) записана: ${f}$?",
                    f"{n} ({'неклассический и классический случаи' if n == 'A1' else 'классический случай'})", "С. 145.", "с. 145, гл. 9, § 4", "силлогистика предикатов")
    if lvl in (4, 5, 6) and i % 2 == 0:
        n, f = rnd.choice(SYLP)
        bb = rnd.choice(["c", "(cd)", "\\tilde c", "(c \\vee d)", "\\sim c"])
        bw = bb if bb.startswith("(") or len(bb) == 1 else f"({bb})"
        g = f.replace("\\downarrow b", f"\\downarrow {bw}").replace("\\leftarrow b)", f"\\leftarrow {bw})")
        return card(9, 4, lvl, "D", "iso", f"Буквы $a, b, c, d$ — термины. Подставьте в схему {n} § 4 гл. 9 (${f}$) вместо $b$ термин ${bb}$.",
                    f"${g}$", "С. 145.", "с. 145, гл. 9, § 4", "силлогистика предикатов")
    WORDS = [("студент", "сдал экзамен"), ("птица", "умеет летать"), ("металл", "проводит ток"), ("число", "делится на 2"), ("дерево", "сбрасывает листья")]
    aw, bw_ = rnd.choice(WORDS)
    pool = [("(\\exists a)(a \\leftarrow b)", f"«Некоторые предметы “{aw}” имеют признак “{bw_}”» равнозначно «некоторые предметы, имеющие признак “{bw_}”, "
             f"имеют признак “быть {aw}”»", "A1"),
            ("(\\forall a)(a \\leftarrow b)", f"«Все предметы “{aw}” имеют признак “{bw_}”» равнозначно «ни один предмет, не имеющий признака “{bw_}”, "
             f"не имеет признака “быть {aw}”» (классический случай)", "A*2")]
    pool_old = [("(\\exists a)(a \\leftarrow b)", "«Некоторые $a$ имеют $b$» равнозначно «некоторые предметы, имеющие $b$, имеют признак “быть $a$”» "
             "($(sc \\downarrow b)$ — предмет, такой, что он имеет $b$; $(pc \\downarrow a)$ — признак, такой, что им обладают $a$)", "A1"),
            ("(\\forall a)(a \\leftarrow b)", "«Все $a$ имеют $b$» равнозначно «ни один предмет, не имеющий $b$, не имеет признака $(pc \\downarrow a)$» — "
             "в классическом случае", "A*2")]
    f, r, n = rnd.choice(pool)
    return card(9, 4, lvl, "S" if lvl == 7 else "C", "transfer", f"Пусть $a$ — «{aw}», $b$ — «{bw_}». Перескажите на обычном языке, что утверждает схема {n} § 4 гл. 9 "
                f"о высказывании ${f}$, и объясните роль терминов $sc$ и $pc$.", r + ".", "С. 145; $sc$, $pc$ — с. 137.", "с. 137, 145, гл. 9, § 1, 4", "силлогистика предикатов",
                form="nat", answ="text")


Q905 = [("Что такое определения по § 5 гл. 9?", "Соглашения о том (или намерения считать), что предметы заданного вида $a^1, \\ldots, a^n$ ($n \\geq 1$) будут "
         "терминами, для которых верны заданные утверждения $x^1, \\ldots, x^m$ с предикатом $\\rightharpoonup$ (с. 146)."),
        ("Каким условиям должны удовлетворять утверждения $x^1, \\ldots, x^m$ определения (с. 146)?", "Для каждого $a^i$ должны быть верны $a^i \\rightharpoonup b^1, "
         "\\ldots, a^i \\rightharpoonup b^k$ и $b^1 \\vee \\ldots \\vee b^k \\rightharpoonup a^i$, где $b^j$ — термины, через которые определяется $a^i$."),
        ("Какой вид имеет простейший вариант определения одного термина $a$ (случай 1, с. 146)?", "1) $a \\rightharpoonup b$; 2) $b \\rightharpoonup a$."),
        ("Что такое случай 2 определений (с. 146)?", "Термины $a^1, \\ldots, a^n$ ($n \\geq 2$) определяются одновременно, и одни используются при определении других."),
        ("Каков статус утверждений $x^1, \\ldots, x^m$, если определение принято (с. 146)?", "Они принимаются как доказуемые (или истинные)."),
        ("Что нельзя подставлять на место переменных $a^1, \\ldots, a^n$ в определении с переменными (с. 147)?", "Термин $b$ и все термины, которые содержат $b$ "
         "или определяются с использованием $b$."),
        ("Какой вид имеют рекурсивные определения (с. 146)?", "1. $a \\rightharpoonup b^1, \\ldots, a \\rightharpoonup b^r$; 2. $(a \\rightharpoonup c^1) \\cdot \\ldots \\cdot (a \\rightharpoonup c^s) \\to "
         "(a \\rightharpoonup d^1) \\cdot \\ldots \\cdot (a \\rightharpoonup d^t)$; 3. $b^1 \\vee \\ldots \\vee b^r \\vee d^1 \\vee \\ldots \\vee d^t \\rightharpoonup a$."),
        ("Какой принцип позволяет получать следствия из определений (с. 147)?", "Если определение принято, утверждения $x^1, \\ldots, x^m$ принимаются как "
         "доказуемые; например, из определения «$a \\rightleftharpoons b \\downarrow c$» принимается $\\vdash (a \\rightleftharpoons b \\downarrow c)$, и из него выводятся следствия.")]
STEPS = [("$\\vdash (a \\rightleftharpoons b \\downarrow c)$", "согласно определению"), ("$\\vdash ((b \\downarrow c) \\leftarrow c)$", "согласно $S^2_t$"),
         ("$\\vdash (\\forall(b \\downarrow c))((b \\downarrow c) \\leftarrow c)$", "согласно $S^5_{cq}$"),
         ("$\\vdash (a \\rightleftharpoons b \\downarrow c)(\\forall(b \\downarrow c))((b \\downarrow c) \\leftarrow c) \\to (\\forall a)(a \\leftarrow c)$", "согласно $S^2_t$"),
         ("$\\vdash (\\forall a)(a \\leftarrow c)$", "согласно 1, 2 и $S^i_{if}$")]


def m905(lvl, d, i):
    if d:
        pool = [("«в определении с переменной на место $a^i$ можно подставить и определяемый термин $b$»", "это запрещено правилом с. 147: $a^1, \\ldots, a^n$ "
                 "должны быть терминами независимо от определения $b$"),
                ("«для определения $a$ через $b^1, \\ldots, b^k$ достаточно $a \\rightharpoonup b^1, \\ldots, a \\rightharpoonup b^k$»", "нужно ещё "
                 "$b^1 \\vee \\ldots \\vee b^k \\rightharpoonup a$ (с. 146)")]
        s, w = rnd.choice(pool)
        return E(9, 5, lvl, "Буквы $a, b$ — термины.", s, w, "с. 146–147, гл. 9, § 5", "определения, диагностика")
    if lvl in (1, 2, 3):
        q, a = Q905[nxt("q905") % len(Q905)]
        return card(9, 5, lvl, "R" if lvl == 1 else "C", "iso", q, a, "Гл. 9, § 5.", "с. 146–147, гл. 9, § 5", "определения", form="meta", answ="text")
    k = rnd.randrange(5)
    shown = "\n".join(f"{n + 1}) {s} — " + ("…" if n == k else w) for n, (s, w) in enumerate(STEPS))
    return card(9, 5, lvl, "D", "complete", f"Принято определение «предмет $a$ будет термином таким, что $a \\rightleftharpoons b \\downarrow c$». Восстановите "
                f"пропущенное обоснование в выводе следствия (с. 147):\n\n{shown}", f"Шаг {k + 1}: {STEPS[k][1]}.",
                "\n".join(f"{n + 1}) {s} — {w}" for n, (s, w) in enumerate(STEPS)), "с. 147, гл. 9, § 5", "определения")


LI = [("(a \\leftarrow b) \\vdash (\\alpha a \\urcorner\\!\\leftarrow c)", "1"), ("(a \\urcorner\\!\\leftarrow b) \\vdash (\\alpha a \\leftarrow c)", "2"),
      ("(a? \\leftarrow b) \\vdash (\\alpha a? \\leftarrow c)", "3"), ("(a \\leftarrow c) \\vdash (\\alpha a \\urcorner\\!\\leftarrow b)", "4"),
      ("(a \\urcorner\\!\\leftarrow c) \\vdash (\\alpha a \\leftarrow b)", "5"), ("(a? \\leftarrow c) \\vdash (\\alpha a? \\leftarrow b)", "6")]
LIC = [("(a \\leftarrow b) \\vdash \\sim(\\alpha a \\leftarrow c)", "1"), ("\\sim(a \\leftarrow b) \\vdash (\\alpha a \\leftarrow c)", "2"),
       ("(a \\leftarrow c) \\vdash \\sim(\\alpha a \\leftarrow b)", "3"), ("\\sim(a \\leftarrow c) \\vdash (\\alpha a \\leftarrow b)", "4")]


def m906(lvl, d, i):
    if d:
        pool = [("«в D1 § 6 гл. 9 $\\alpha a$ означает $a$ или $\\sim a$»", "$\\alpha a$ означает $a$, $\\sim a$ или $\\tilde a$ (с. 148)"),
                ("«конъюнкция и слабая дизъюнкция взаимозаменимы, потому что $xy \\dashv\\vdash x \\vee y$»", "по с. 148 имеют силу $xy \\vdash x \\vee y$, "
                 "$\\sim(x \\vee y) \\vdash \\sim(xy)$, $\\sim(x \\vee y) \\vdash \\sim x\\sim y$, $x \\vee y \\dashv\\vdash \\sim(\\sim x \\vee \\sim y)$ и т. п.; $x \\vee y \\vdash xy$ не доказуема")]
        s, w = rnd.choice(pool)
        return E(9, 6, lvl, "Буквы $a, b, c$ — термины.", s, w, "с. 147–148, гл. 9, § 6", "взаимозаменимые предикаты, диагностика")
    if lvl in (2, 3, 4):
        if i % 2 == 0:
            its = rnd.sample(LI, 3)
            return card(9, 6, lvl, "C", "iso", "Каким номерам списка D1 § 6 гл. 9 (неклассический случай, с. 147–148) соответствуют формулы?\n\n" +
                        items([f"${s}$" for s, _ in its]), answers([n for _, n in its]), "С. 147–148.", "с. 147–148, гл. 9, § 6", "взаимозаменимые предикаты")
        its = rnd.sample(LIC, 2)
        return card(9, 6, lvl, "C", "iso", "Каким номерам списка D1 § 6 гл. 9 для классического случая (с. 148) соответствуют формулы?\n\n" +
                    items([f"${s}$" for s, _ in its]), answers([n for _, n in its]), "С. 148.", "с. 148, гл. 9, § 6", "взаимозаменимые предикаты")
    al = rnd.choice(["a", "\\sim a", "\\tilde a"])
    k = rnd.randrange(6)
    s = LI[k][0].replace("\\alpha a", al)
    return card(9, 6, lvl, "S" if lvl == 7 else "D", "iso", f"Предикаты $b$ и $c$ логически взаимозаменимы (D1 § 6 гл. 9). Запишите формулу {k + 1} списка "
                f"неклассического случая при $\\alpha a = {al}$" + (" и сравните с соответствующей формулой классического случая." if lvl == 7 else "."),
                f"${s}$" + (f"; в классическом случае — " + {0: "$(a \\leftarrow b) \\vdash \\sim(" + al + " \\leftarrow c)$", 3: "$(a \\leftarrow c) \\vdash \\sim(" + al + " \\leftarrow b)$"}.get(k, "аналога с $?$ и $\\urcorner$ нет: используются $\\sim$")
                if lvl == 7 else ""), "С. 147–148.", "с. 147–148, гл. 9, § 6", "взаимозаменимые предикаты")


LOGT = [("термины существования", True), ("термины модальностей", True), ("термины классов", True), ("термины отношений", True),
        ("«треугольник»", False), ("«железо»", False), ("«стол»", False), ("«писатель»", False)]


def m907(lvl, d, i):
    if d:
        pool = [("«логика исследует только логические операторы»", "по § 7 (с. 148) она исследует также особого вида термины — логические"),
                ("«правила оперирования терминами существования сводятся к правилам для логических операторов»", "по с. 148 они не сводимы к ним")]
        s, w = rnd.choice(pool)
        return E(9, 7, lvl, "", s, w, "с. 148, гл. 9, § 7", "логические термины, диагностика")
    if lvl in (1, 2, 3):
        its = rnd.sample(LOGT, 4)
        return card(9, 7, lvl, "R" if lvl == 1 else "C", "iso", "Какие из терминов (или видов терминов) § 7 гл. 9 называет логическими?\n\n" + items([s for s, _ in its]),
                    answers(["логический" if t else "нет" for _, t in its]), "С. 148: установление свойств этих терминов — дело логики, а не конкретной науки.",
                    "с. 148, гл. 9, § 7", "логические термины", form="nat")
    if lvl == 6:
        return card(9, 7, 6, "C", "transfer", "Приведите пример логического термина (§ 7 гл. 9), свойства которого книга устанавливает в следующей главе, и "
                    "назовите правила для него.", "Термин класса $Ka$ (гл. 10): предикаты $\\in$, $\\subset$ и аксиомные схемы A1–A7 $S^1_k$ (с. 149–150).",
                    "С. 148–150.", "с. 148–150, гл. 9–10", "логические термины", form="meta", answ="text")
    return card(9, 7, lvl, "C", "iso", "Почему, по § 7 гл. 9, термины существования, модальностей, классов и отношений называются логическими?",
                "Установление их свойств есть дело логики, а не какой-либо иной конкретной науки (с. 148).", "С. 148.", "с. 148, гл. 9, § 7", "логические термины",
                form="meta", answ="text")


# ================================================================ гл. 10: классы
KK = "Буквы $a, b, c$ — термины; $Ka$ — класс $a$."


def m1001(lvl, d, i):
    if d:
        pool = [("«$Ka$ — предикат: “быть классом $a$”»", "по D1 § 1 гл. 10 (с. 149) термин класса есть субъект"),
                ("«$a \\in Kb$ — это сокращение для $(a \\leftarrow Kb)$»", "это сокращение для $(a, Kb) \\leftarrow (\\in)$; $\\in$ — двухместный простой предикат (с. 149)")]
        s, w = rnd.choice(pool)
        return E(10, 1, lvl, KK, s, w, "с. 149, гл. 10, § 1", "классы, диагностика")
    pool = [("$\\in$", "двухместный предикат включения индивида в класс"), ("$\\subset$", "двухместный предикат включения класса в класс"),
            ("$K$", "классообразующий оператор"), ("$Ka$", "термин класса («класс $a$»), субъект"), ("$a \\in Kb$", "сокращение для $(a, Kb) \\leftarrow (\\in)$"),
            ("$Ka \\subset Kb$", "сокращение для $(Ka, Kb) \\leftarrow (\\subset)$")]
    its = rnd.sample(pool, 3)
    if lvl >= 4:
        nat = [("«Сократ — человек» (индивид в классе)", "$a \\in Kb$, $a$ — «Сократ», $b$ — «человек»"),
               ("«Класс квадратов входит в класс прямоугольников»", "$Ka \\subset Kb$, $a$ — «квадрат», $b$ — «прямоугольник»"),
               ("«Число 7 принадлежит классу простых чисел»", "$a \\in Kb$, $a$ — «7», $b$ — «простое число»")]
        s, w = rnd.choice(nat)
        return card(10, 1, lvl, "C", "iso", f"Запишите в символике § 1 гл. 10 высказывание {s}.", w, "С. 149.", "с. 149, гл. 10, § 1", "классы", form="nat")
    return card(10, 1, lvl, "R" if lvl == 1 else "C", "iso", f"{KK} Что обозначает каждое выражение в логике классов (§ 1 гл. 10, с. 149)?\n\n" + items([s for s, _ in its]),
                answers([w for _, w in its]), "С. 149.", "с. 149, гл. 10, § 1", "классы")


AK1 = {"A1": "(\\exists a)(a \\in Kb) \\vdash (\\exists b)(b \\in Ka)", "A2": "\\sim(a \\in Kb) \\vdash (a \\in K\\sim b)", "A3": "(a \\in K\\sim b) \\vdash \\sim(a \\in Kb)",
       "A4": "(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (a \\in Kc)", "A5": "\\vdash (a \\in K(a \\vee b))", "A6": "(\\forall a)(a \\in Kb) \\vdash (Ka \\subset Kb)",
       "A7": "(Ka \\subset Kb) \\vdash (\\forall a)(a \\in Kb)"}
TK1 = {"T1": "(\\forall a)(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (\\forall a)(a \\in Kc)", "T2": "(\\exists a)(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (\\exists a)(a \\in Kc)",
       "T3": "(\\forall a)(a \\in Kb) \\vdash (\\forall\\sim b)\\sim(\\sim b \\in Ka)", "T4": "(\\forall\\sim b)\\sim(\\sim b \\in Ka) \\vdash (\\forall a)(a \\in Kb)",
       "T5": "\\vdash ab \\in Ka", "T6": "\\vdash Ka \\subset K(a \\vee b)", "T7": "\\vdash K(ab) \\subset Ka"}
RK = [("R1", "замена термина $\\sim\\sim a$ термином $a$ и наоборот"), ("R2", "замена термина $ab$ термином $ba$"), ("R3", "замена термина $a$ термином $aa$ и наоборот"),
      ("R4", "перегруппировка $a^1 \\cdot \\ldots \\cdot a^ia^{i+1} \\cdot \\ldots \\cdot a^n$ ↔ $a^1 \\cdot \\ldots \\cdot a^i(a^{i+1} \\cdot \\ldots \\cdot a^n)$"),
      ("R5", "замена термина $\\sim(ab)$ термином $\\sim a \\vee \\sim b$ и наоборот")]


def apply_r(t):
    """Один шаг правил R1–R5 § 2 гл. 10 к термину (верхний уровень). Возвращает список (правило, новый термин)."""
    out = []
    k = t[0]
    if k == "neg" and t[1][0] == "neg":
        out.append(("R1", t[1][1]))
    if k == "conj" and len(t[1]) == 2:
        out.append(("R2", C(t[1][1], t[1][0])))
        if t[1][0] == t[1][1]:
            out.append(("R3", t[1][0]))
    if k == "neg" and t[1][0] == "conj" and len(t[1][1]) == 2:
        out.append(("R5", W(N(t[1][1][0]), N(t[1][1][1]))))
    if k == "wdis" and len(t[1]) == 2 and all(x[0] == "neg" for x in t[1]):
        out.append(("R5", N(C(t[1][0][1], t[1][1][1]))))
    return out


def kcls(t):
    return f"K{ttex(t)}" if t[0] == "v" else f"K({ttex(t)})"


def rk_card(lvl, typ="C"):
    pool = [N(N(V("b"))), C(V("b"), V("c")), C(V("b"), V("b")), N(C(V("b"), V("c"))), W(N(V("b")), N(V("c"))), N(N(C(V("b"), V("c")))),
            C(N(V("b")), V("c")), N(C(V("c"), N(V("b"))))]
    its = []
    for t in rnd.sample(pool, 3):
        r, t2 = rnd.choice(apply_r(t))
        its.append((t, t2, r))
    return card(10, 2, lvl, typ, "iso", "Буквы $a, b, c$ — термины. Каким правилом замены терминов $S^1_k$ (R1–R5, с. 150) получено второе высказывание из первого?\n\n" +
                items([f"$a \\in {kcls(t)}$ → $a \\in {kcls(t2)}$" for t, t2, _ in its]),
                answers([r for _, _, r in its]), "С. 150: " + "; ".join(f"{n} — {w}" for n, w in RK) + ".", "с. 150, гл. 10, § 2", "классы, правила замены",
                system="S^1_k")


def chain_rk(lvl, typ="D"):
    start = rnd.choice([N(N(C(V("b"), V("c")))), N(C(V("c"), V("b"))), C(N(N(V("b"))), V("c")), N(N(N(C(V("b"), V("c")))))])
    target = {repr(N(N(C(V("b"), V("c"))))): (C(V("c"), V("b")), ["R1", "R2"]), repr(N(C(V("c"), V("b")))): (W(N(V("b")), N(V("c"))), ["R2 (внутри $\\sim$)", "R5"]),
              repr(C(N(N(V("b"))), V("c"))): (C(V("c"), V("b")), ["R1 (внутри)", "R2"]), repr(N(N(N(C(V("b"), V("c")))))): (W(N(V("b")), N(V("c"))), ["R1", "R5"])}[repr(start)]
    return card(10, 2, lvl, typ, "iso", f"Буквы $a, b, c$ — термины. Покажите, как правилами R1–R5 $S^1_k$ (с. 150) из $a \\in {kcls(start)}$ получить "
                f"$a \\in {kcls(target[0])}$.", "Правила: " + ", затем ".join(target[1]) + ".", "Правила замены дают равнозначные высказывания "
                "(п. 6 интерпретации, с. 151). С. 150.", "с. 150–151, гл. 10, § 2", "классы, правила замены", system="S^1_k")


def ak_rec(lvl, typ="R"):
    D_ = dict(AK1, **TK1)
    ks = rnd.sample(sorted(D_), 4)
    return card(10, 2, lvl, typ, "iso", f"{KK} Укажите аксиомные (A) или теоремные (T) схемы $S^1_k$ (с. 150):\n\n" + items([f"${D_[k]}$" for k in ks]),
                answers(ks), "С. 150.", "с. 150, гл. 10, § 2", "классы, S1k", system="S^1_k")


def sub_ak(lvl, typ="D"):
    n = rnd.choice(["A2", "A3", "A4", "A6", "A7"])
    s = AK1[n]
    # Связанной квантором букве — только простой термин; остальным — любые различные.
    bound = set(re.findall(r"\\(?:forall|exists) ([abc])", s))
    for _ in range(200):
        A_, B_, C_ = rnd.sample(["d", "e", "\\sim d", "de", "(d \\vee e)"], 3)
        if all(t in ("d", "e") for v, t in zip("abc", (A_, B_, C_)) if v in bound):
            break
    toks = re.findall(r"\\[A-Za-z]+|.", s)
    mp = {"a": A_, "b": B_, "c": C_}
    out = ""
    for i, tok in enumerate(toks):
        v = mp.get(tok)
        if v is None:
            out += tok
            continue
        prev = toks[i - 1] if i else ""
        if prev in ("K", "\\sim") and v not in ("d", "e") and not v.startswith("(") and not v.startswith("\\sim"):
            v = f"({v})"
        elif prev == "\\sim" and v.startswith("\\sim"):
            v = " " + v
        out += v
    return card(10, 2, lvl, typ, "iso", f"Термины $d$, $e$ — простые. Подставьте в схему {n} системы $S^1_k$ (${s}$) вместо $a$ — ${A_}$, вместо $b$ — ${B_}$" +
                (f", вместо $c$ — ${C_}$" if "c" in re.sub(r"\\[a-z]+", "", s) else "") + " (кванторы связывают подставленные термины).", f"${out}$",
                "С. 150; в схемах буквы — метапеременные для терминов.", "с. 150, гл. 10, § 2", "классы, S1k", system="S^1_k")


def kval(facts):
    """Пропагация значений по правилам интерпретации 1–3 (с. 150–151). facts: {(x, y): v}, x∈Ky."""
    neg = lambda t: t[1:] if t.startswith("~") else "~" + t
    F = dict(facts)
    for _ in range(6):
        new = dict(F)
        for (x_, y_), v_ in F.items():
            if v_ == 1:
                new.setdefault((x_, neg(y_)), 0)
                new.setdefault((neg(y_), neg(x_)), 1)
            else:
                new.setdefault((x_, neg(y_)), 1)
                new.setdefault((y_, x_), 0)
        for (x_, y_), v1 in F.items():
            for (y2, z_), v2 in F.items():
                if y2 == y_ and v1 == 1 and x_ != z_:
                    new.setdefault((x_, z_), v2)
        F = new
    return F


def kt(x_, y_):
    t = lambda s: ("\\sim " + s[1:]) if s.startswith("~") else s
    return f"{t(x_)} \\in K{'' if not y_.startswith('~') else ''}{t(y_) if not y_.startswith('~') else '\\sim ' + y_[1:]}"


def kval_card(lvl, typ="C"):
    letters = rnd.sample(["a", "b", "c", "d", "e"], 4)
    for _ in range(300):
        n = 2 if lvl <= 4 else 3
        chain = letters[:n + 1]
        vals = [1] * (n - 1) + [rnd.choice([0, 1])]
        facts = {(chain[j], chain[j + 1]): vals[j] for j in range(n)}
        F = kval(facts)
        tgt = (chain[0], chain[-1])
        if tgt in F:
            break
    extra = rnd.choice([(chain[0], "~" + chain[1]), ("~" + chain[1], "~" + chain[0])])
    ask = [tgt, extra] if extra in F else [tgt]
    cond = (f"Буквы $a, b, c, d, e$ — термины; $Ka$ — класс $a$. По интерпретации § 2 гл. 10 (с. 150–151) дано: " + ", ".join(f"${kt(*k)}$ имеет значение {v}" for k, v in facts.items()) +
            ". Какие значения следуют для " + " и ".join(f"${kt(*k)}$" for k in ask) + "?")
    return card(10, 2, lvl, typ, "iso", cond, "; ".join(f"${kt(*k)}$ — {F[k]}" for k in ask),
                "П. 1: если $a \\in Kb = 1$, то $a \\in K\\sim b = 0$ и $\\sim b \\in K\\sim a = 1$; п. 2: если $a \\in Kb = 0$, то $a \\in K\\sim b = 1$, "
                "$b \\in Ka = 0$; п. 3: из $a \\in Kb = 1$ и $b \\in Kc = 1$ — $a \\in Kc = 1$; из $a \\in Kb = 1$ и $b \\in Kc = 0$ — $a \\in Kc = 0$. "
                "Значение для $" + kt(*tgt) + "$ получается по п. 3 последовательно по цепочке.", "с. 150–151, гл. 10, § 2", "классы, интерпретация", system="S^1_k")


def t1_deriv(lvl, hide=False):
    st = [("$(\\forall b)(b \\in Kc) \\vdash (\\forall a)(\\forall b)(b \\in Kc)$", "T17 § 6 гл. 7: $a$ не входит свободно"),
          ("$(\\forall a)(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (\\forall a)(a \\in Kb)(\\forall a)(\\forall b)(b \\in Kc)$", "$S^s$: 1"),
          ("$(\\forall a)(a \\in Kb)(\\forall a)(\\forall b)(b \\in Kc) \\vdash (\\forall a)((a \\in Kb)(\\forall b)(b \\in Kc))$", "T19 § 6 гл. 7"),
          ("$(\\forall a)((a \\in Kb)(\\forall b)(b \\in Kc)) \\vdash (\\forall a)(a \\in Kc)$", "R1 гл. 7 из A4"),
          ("$(\\forall a)(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (\\forall a)(a \\in Kc)$", "$S^s$: 2, 3, 4")]
    if hide:
        k = rnd.randrange(len(st))
        return card(10, 2, lvl, "D", "complete", f"{KK} Восстановите пропущенное основание в выводе T1 $S^1_k$ из A4:\n\n" +
                    "\n".join(f"{n + 1}. {s} [{'…' if n == k else w}]" for n, (s, w) in enumerate(st)), f"Шаг {k + 1}: {st[k][1]}.",
                    "\n".join(f"{n + 1}. {s} [{w}]" for n, (s, w) in enumerate(st)), "с. 104, 150, гл. 7, § 6; гл. 10, § 2", "классы, вывод", system="S^1_k")
    return card(10, 2, lvl, "D", "iso", f"{KK} Выведите T1 $S^1_k$ — $(\\forall a)(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (\\forall a)(a \\in Kc)$ — из A4 средствами "
                "$S^s_{cq}$.", "Вывод из 5 шагов (см. решение).", "\n".join(f"{n + 1}. {s} [{w}]" for n, (s, w) in enumerate(st)),
                "с. 104, 150, гл. 7, § 6; гл. 10, § 2", "классы, вывод", answ="proof", system="S^1_k")


E1002 = [("«по A2 $S^1_k$ из $\\sim(a \\in Kb)$ следует $(\\sim a \\in Kb)$»", "A2 — $\\sim(a \\in Kb) \\vdash (a \\in K\\sim b)$: отрицание переходит на класс (с. 150)"),
         ("«если $a \\in Kb$ имеет значение 0 и $b \\in Kc$ — 1, то $a \\in Kc$ имеет значение 0»", "по п. 3 (с. 151) при $a \\in Kb = 0$ значение $a \\in Kc$ "
          "остаётся неопределённым, какое бы значение ни приписали $b \\in Kc$"),
         ("«по п. 1 интерпретации из $a \\in Kb = 1$ следует $\\sim a \\in K\\sim b = 1$»", "по п. 1 (с. 150) значения $\\sim a \\in Kb$ и $\\sim a \\in K\\sim b$ "
          "не зависят от $a \\in Kb$; значение 1 получает $\\sim b \\in K\\sim a$"),
         ("«по п. 2 из $a \\in Kb = 0$ следует $b \\in Ka = 1$»", "по п. 2 (с. 151) $b \\in Ka$ приписывается значение 0"),
         ("«R5 позволяет заменять $\\sim(ab)$ на $\\sim a\\sim b$»", "R5 — замена $\\sim(ab)$ на $\\sim a \\vee \\sim b$ и наоборот (с. 150)"),
         ("«A6 $S^1_k$: $(Ka \\subset Kb) \\vdash (\\forall a)(a \\in Kb)$»", "это A7; A6 — обратная: $(\\forall a)(a \\in Kb) \\vdash (Ka \\subset Kb)$ (с. 150)"),
         ("«T5 $\\vdash ab \\in Ka$ означает, что класс $ab$ включается в класс $a$»", "T5 говорит о включении индивида $ab$ в класс $a$ ($\\in$); "
          "включение классов — T7 $\\vdash K(ab) \\subset Ka$ (с. 150)"),
         ("«правила замены R1–R5 нужны при любом построении $S^1_k$»", "по с. 150 — если $S^1_k$ строится независимо от теории терминов")]


def kval_e(lvl):
    l3 = rnd.sample(["a", "b", "c", "d", "e"], 3)
    x_, y_, z_ = l3
    v = rnd.choice([(1, 0, "1"), (0, 1, "0"), (0, 0, "0"), (1, 1, "0")])
    claim = f"${x_} \\in K{y_}$ имеет значение {v[0]}, ${y_} \\in K{z_}$ — {v[1]}; значит, ${x_} \\in K{z_}$ имеет значение {v[2]}"
    if v[0] == 1:
        right = f"по п. 3 (с. 151) ${x_} \\in K{z_}$ имеет значение {v[1]}"
    else:
        right = f"по п. 3 (с. 151) при ${x_} \\in K{y_} = 0$ значение ${x_} \\in K{z_}$ остаётся неопределённым, какое бы значение ни приписали ${y_} \\in K{z_}$"
    if v[0] == 1 and str(v[1]) == v[2]:
        v = (1, 1, "0")
        claim = f"${x_} \\in K{y_}$ имеет значение 1, ${y_} \\in K{z_}$ — 1; значит, ${x_} \\in K{z_}$ имеет значение 0"
        right = f"по п. 3 (с. 151) ${x_} \\in K{z_}$ имеет значение 1"
    return E(10, 2, lvl, "Буквы $a, b, c, d, e$ — термины; $Ka$ — класс $a$.", "«" + claim + "»", right, "с. 150–151, гл. 10, § 2", "классы, интерпретация, диагностика", system="S^1_k")


def m1002(lvl, d, i):
    if d:
        if i % 2 == 0:
            return kval_e(lvl)
        s, w = rnd.choice(E1002)
        s, w = permute2([s, w])
        return E(10, 2, lvl, KK, s, w, "с. 150–151, гл. 10, § 2", "классы, S1k, диагностика", system="S^1_k")
    if lvl == 1:
        return ak_rec(1)
    if lvl == 2:
        return [ak_rec, rk_card][i % 2](2, "C")
    if lvl == 3:
        return [rk_card, sub_ak, ak_rec, kval_card][i % 4](3) if i % 4 != 2 else ak_rec(3, "C")
    if lvl == 4:
        return [chain_rk, t1_deriv, kval_card, sub_ak][i % 4](4) if i % 4 != 1 else t1_deriv(4, hide=True)
    if lvl == 5:
        if i == 1:
            return t1_deriv(5)
        return [kval_card, sub_ak, chain_rk][i % 3](5) if i % 3 != 2 or i < 9 else t1_deriv(5, hide=True)
    if lvl == 6:
        return kval_card(6) if i % 2 == 0 else sub_ak(6, "C")
    return kval_card(7, "S")


# ---- 10.03 S²_k
def subst_x(x, a, b):
    """y — замена a на b везде в x (высказывания вида u ∈ Kw с ~)."""
    toks = re.findall(r"\\[A-Za-z]+|.", x)
    return "".join(b if t == a else t for t in toks)


XS = ["(a \\in Kc)", "\\sim(a \\in Kc)", "(c \\in Ka)", "(a \\in Kc)(a \\in Kd)", "(a \\in Kc) \\vee (d \\in Ka)", "(a \\in K\\sim c)", "(\\forall c)(c \\in Ka)",
      "(\\exists c)(a \\in Kc)"]


def a14_card(lvl, typ="D"):
    x = rnd.choice(XS)
    which = rnd.choice(["A14", "A24"])
    if which == "A14":
        y = subst_x(x, "a", "b")
        cond = f"{KK} Запишите пример схемы $A^14$ $S^2_k$ ($(\\forall a)x(b \\in Ka) \\vdash y$, $y$ — из $x$ заменой $a$ на $b$, с. 151) при $x = {x}$."
        ans = f"$(\\forall a)({x})(b \\in Ka) \\vdash {y}$" if " " in x and not x.startswith("(") or ")(" in x or "\\vee" in x else f"$(\\forall a){x}(b \\in Ka) \\vdash {y}$"
    else:
        xb = subst_x(x, "a", "b")
        y = subst_x(xb, "b", "a")
        cond = f"{KK} Запишите пример схемы $A^24$ $S^2_k$ ($x(b \\in Ka) \\vdash (\\exists a)y$, $y$ — из $x$ заменой $b$ на $a$, с. 151) при $x = {xb}$."
        wrap = f"({y})" if (")(" in y or "\\vee" in y) else y
        ans = f"${xb if not ('\\vee' in xb) else '(' + xb + ')'}(b \\in Ka) \\vdash (\\exists a){wrap}$"
    return card(10, 3, lvl, typ, "iso", cond, ans, "С. 151.", "с. 151, гл. 10, § 3", "классы, S2k", system="S^2_k")


def a4_from(lvl, typ="D"):
    return card(10, 3, lvl, typ, "iso", f"{KK} Покажите, что A4 $S^1_k$ — $(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (a \\in Kc)$ — получается в $S^2_k$ из $A^14$ "
                "(с. 151).", "$A^14$ с переменной $b$ вместо $a$ и индивидом $a$ вместо $b$, $x = (b \\in Kc)$: $(\\forall b)(b \\in Kc)(a \\in Kb) \\vdash (a \\in Kc)$; "
                "перестановка конъюнктов посылки по $S^s$.", "С. 151: «A4 получается в $S^2_k$ как следствие из $A^14$».", "с. 151, гл. 10, § 3", "классы, S2k",
                answ="proof", system="S^2_k")


def bkc_card(lvl, typ="D"):
    return card(10, 3, lvl, typ, "iso", f"{KK} Выведите в $S^2_k$ формулу $(b \\in Kc)(b \\in Ka) \\vdash (\\exists a)(a \\in Kc)$ (с. 151).",
                "Это пример $A^24$ при $x = (b \\in Kc)$: $y$ получается заменой $b$ на $a$ — $(a \\in Kc)$.", "С. 151.", "с. 151, гл. 10, § 3", "классы, S2k",
                answ="proof", system="S^2_k")


def a14_check(lvl, typ="C"):
    its = []
    for _ in range(3):
        x = rnd.choice(XS)
        good = rnd.random() < 0.5
        y = subst_x(x, "a", "b") if good else rnd.choice([x, subst_x(x, "c", "b"), subst_x(x, "a", "c")])
        if y == subst_x(x, "a", "b"):
            good = True
        its.append((x, y, good))
    return card(10, 3, lvl, typ, "open", f"{KK} Являются ли формулы примерами схемы $A^14$ $S^2_k$ ($(\\forall a)x(b \\in Ka) \\vdash y$, $y$ — из $x$ заменой $a$ на $b$)?\n\n" +
                items([f"$(\\forall a)" + (f"({x})" if (")(" in x or "\\vee" in x) else x) + f"(b \\in Ka) \\vdash {y}$" for x, y, _ in its]),
                answers(["да" if g else "нет" for _, _, g in its]), "\n".join(f"{L[k]}) из $x$ заменой $a$ на $b$ получается ${subst_x(x, 'a', 'b')}$." for k, (x, _, _) in enumerate(its)) +
                " С. 151.", "с. 151, гл. 10, § 3", "классы, S2k", system="S^2_k")


E1003 = [("«в $A^14$ $y$ образуется из $x$ заменой $b$ на $a$»", "в $A^14$ $a$ заменяется на $b$; замена $b$ на $a$ — в $A^24$ (с. 151)"),
         ("«$S^2_k$ получается добавлением $A^14$ и $A^24$ к схемам $S^1_k$»", "они принимаются вместо A4 (с. 151)"),
         ("«в $S^2_k$ A4 недоказуема, потому что её нет среди аксиом»", "A4 получается в $S^2_k$ как следствие из $A^14$ (с. 151)"),
         ("«$A^24$: $x(b \\in Ka) \\vdash (\\forall a)y$»", "в $A^24$ заключение $(\\exists a)y$ (с. 151)"),
         ("«в $A^14$ $(b \\in Ka)$ означает, что класс $b$ включается в класс $a$»", "это включение индивида $b$ в класс $Ka$; включение классов "
          "записывается $Kb \\subset Ka$ (с. 149)"),
         ("«$A^14$ отличается от A1 $S^s_{cq}$ только записью»", "в $A^14$ есть дополнительный член посылки $(b \\in Ka)$: частное получается лишь для "
          "индивида $b$, принадлежащего классу $Ka$ (с. 151)")]


def m1003(lvl, d, i):
    if d:
        if i % 2 == 0:
            x = rnd.choice(XS)
            bad = subst_x(x, "a", "c")
            return card(10, 3, lvl, "E", "open", f"{KK} Студент записал пример $A^14$: $(\\forall a)" + (f"({x})" if (")(" in x or "\\vee" in x) else x) +
                        f"(b \\in Ka) \\vdash {x}$. Найдите ошибку.", f"Неверно: $y$ должно получаться из $x$ заменой $a$ на $b$ везде: ${subst_x(x, 'a', 'b')}$ (с. 151).",
                        "С. 151.", "с. 151, гл. 10, § 3", "классы, S2k, диагностика", system="S^2_k")
        s, w = rnd.choice(E1003)
        return E(10, 3, lvl, KK, s, w, "с. 151, гл. 10, § 3", "классы, S2k, диагностика", system="S^2_k")
    if lvl == 1:
        return card(10, 3, 1, "R", "iso", f"{KK} Чем $S^2_k$ отличается от $S^1_k$ (§ 3 гл. 10)?", "Вместо A4 принимаются схемы $A^14$ и $A^24$ (с. 151).",
                    "С. 151.", "с. 151, гл. 10, § 3", "классы, S2k", system="S^2_k")
    if lvl in (2, 3):
        return a14_card(lvl) if i % 3 else (a4_from(lvl) if lvl == 3 else a14_card(lvl))
    if lvl == 4:
        return [a14_card, bkc_card, a14_check][i % 3](4) if i % 3 != 2 else a14_check(4)
    if lvl == 7:
        return a14_check(7, "S")
    return a14_check(lvl) if i % 2 == 0 else a14_card(lvl, "C")


# ---- 10.04 силлогистика классов
ASK = {"A1": "x \\vdash \\sim\\sim x", "A2": "\\sim\\sim x \\vdash x", "A3": "xy \\vdash x", "A4": "xy \\vdash yx", "A5": "(\\forall a)x \\vdash x",
       "A6": "x \\vdash (\\exists a)x", "A7": "(\\forall a)x \\vdash \\sim(\\exists a)\\sim x", "A8": "\\sim(\\exists a)\\sim x \\vdash (\\forall a)x",
       "A9": "(\\forall a)(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (\\forall a)(a \\in Kc)", "A10": "(\\exists a)(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (\\exists a)(a \\in Kc)",
       "A11": "(\\forall a)(a \\in Kb) \\vdash (\\forall\\sim b)\\sim(\\sim b \\in Ka)", "A12": "(\\forall\\sim b)\\sim(\\sim b \\in Ka) \\vdash (\\forall a)(a \\in Kb)",
       "A13": "(\\exists a)(a \\in Kb) \\vdash (\\exists b)(b \\in Ka)"}
# коды посылок и заключений (с. 153)
CODES = {}
for v_, q_ in [("a", "c"), ("b", "c"), ("c", "a"), ("c", "b")]:
    pass
FORMS = {"1a": ("\\forall", "a", "a", "c", 0), "1b": ("\\exists", "a", "a", "c", 0), "1c": ("\\forall", "a", "a", "c", 1), "1d": ("\\exists", "a", "a", "c", 1),
         "2a": ("\\forall", "c", "c", "a", 0), "2b": ("\\exists", "c", "c", "a", 0), "2c": ("\\forall", "c", "c", "a", 1), "2d": ("\\exists", "c", "c", "a", 1),
         "3a": ("\\forall", "b", "b", "c", 0), "3b": ("\\exists", "b", "b", "c", 0), "3c": ("\\forall", "b", "b", "c", 1), "3d": ("\\exists", "b", "b", "c", 1),
         "4a": ("\\forall", "c", "c", "b", 0), "4b": ("\\exists", "c", "c", "b", 0), "4c": ("\\forall", "c", "c", "b", 1), "4d": ("\\exists", "c", "c", "b", 1),
         "5a": ("\\forall", "a", "a", "b", 0), "5b": ("\\forall", "a", "a", "b", 1), "5c": ("\\exists", "a", "a", "b", 0), "5d": ("\\exists", "a", "a", "b", 1)}


def ftex(code):
    q, v_, s, k, n = FORMS[code]
    return f"({q} {v_})" + ("\\sim" if n else "") + f"({s} \\in K{k})"


MODI = {1: "(\\forall c)(c \\in Kb)(\\forall a)(a \\in Kc) \\vdash (\\forall a)(a \\in Kb)", 2: "(\\forall c)\\sim(c \\in Kb)(\\forall a)(a \\in Kc) \\vdash (\\forall a)\\sim(a \\in Kb)",
        3: "(\\forall c)(c \\in Kb)(\\exists a)(a \\in Kc) \\vdash (\\exists a)(a \\in Kb)", 4: "(\\forall c)\\sim(c \\in Kb)(\\exists a)(a \\in Kc) \\vdash (\\exists a)\\sim(a \\in Kb)",
        5: "(\\forall b)\\sim(b \\in Kc)(\\forall a)(a \\in Kc) \\vdash (\\forall a)\\sim(a \\in Kb)", 6: "(\\forall b)(b \\in Kc)(\\forall a)\\sim(a \\in Kc) \\vdash (\\forall a)\\sim(a \\in Kb)",
        7: "(\\forall b)\\sim(b \\in Kc)(\\exists a)(a \\in Kc) \\vdash (\\exists a)\\sim(a \\in Kb)", 8: "(\\forall b)(b \\in Kc)(\\exists a)\\sim(a \\in Kc) \\vdash (\\exists a)\\sim(a \\in Kb)",
        9: "(\\forall c)(c \\in Kb)(\\forall c)(c \\in Ka) \\vdash (\\exists a)(a \\in Kb)", 10: "(\\forall c)\\sim(c \\in Kb)(\\forall c)(c \\in Ka) \\vdash (\\exists a)\\sim(a \\in Kb)",
        11: "(\\exists c)(c \\in Kb)(\\forall c)(c \\in Ka) \\vdash (\\exists a)(a \\in Kb)", 12: "(\\forall c)(c \\in Kb)(\\exists c)(c \\in Ka) \\vdash (\\exists a)(a \\in Kb)",
        13: "(\\exists c)\\sim(c \\in Kb)(\\forall c)(c \\in Ka) \\vdash (\\exists a)\\sim(a \\in Kb)", 14: "(\\forall c)\\sim(c \\in Kb)(\\exists c)(c \\in Ka) \\vdash (\\exists a)\\sim(a \\in Kb)",
        15: "(\\forall b)(b \\in Kc)(\\forall c)(c \\in Ka) \\vdash (\\exists a)(a \\in Kb)", 16: "(\\forall b)(b \\in Kc)(\\forall c)\\sim(c \\in Ka) \\vdash (\\forall a)\\sim(a \\in Kb)",
        17: "(\\exists b)(b \\in Kc)(\\forall c)(c \\in Ka) \\vdash (\\exists a)(a \\in Kb)", 18: "(\\forall b)\\sim(b \\in Kc)(\\forall c)(c \\in Ka) \\vdash (\\exists a)\\sim(a \\in Kb)",
        19: "(\\forall b)\\sim(b \\in Kc)(\\exists c)(c \\in Ka) \\vdash (\\exists a)\\sim(a \\in Kb)"}
MBASE = {1: "R2, A9, R1, A4, R5", 2: "A9, L1, L2, R2–R5", 3: "A4, A10, R1, R2, R5", 4: "A7, A8, L1, T3, R2, R4, R5", 5: "A7, A8, L2, T1, R2, R4, R5",
         6: "A1, A2, L1, T5, R1, R4, R5", 7: "T4, L5, R4, R5", 8: "A1, A2, A7, A8, T7, L1, R2, R4, R5", 10: "A7, A8, T9, L1, R2, R4, R5",
         11: "A10, A13, R2, R4, R5", 12: "A13, T3, R4, R5", 13: "A7, A8, T11, L1, R2, R4, R5", 14: "A7, A8, T12, L1, R2, R4, R5",
         15: "A6, A9, A13, A5, R1, R2, R4, R5", 16: "R4, R5, T6, L5", 17: "R4, R5, T11, A13", 18: "R4, R5, T10, L5", 19: "R4, R5, T14, L5"}
NAMES = {1: "Barbara", 2: "Celarent", 3: "Darii", 4: "Ferio", 5: "Cesare", 6: "Camestres"}
CODE_OF = {}
for code, (q, v_, s, k, n) in FORMS.items():
    CODE_OF[ftex(code)] = code


def modus_codes(m):
    p, c = MODI[m].split(" \\vdash ")
    parts = re.findall(r"\((?:\\forall|\\exists) [abc]\)(?:\\sim)?\([abc] \\in K[abc]\)", p)
    return [CODE_OF[x] for x in parts], CODE_OF[c]


for m in MODI:
    pc, cc = modus_codes(m)
    assert len(pc) == 2 and cc.startswith("5"), m


def code_card(lvl, typ="C"):
    ms = rnd.sample(sorted(MODI), 2)
    ans = []
    for m in ms:
        pc, cc = modus_codes(m)
        ans.append(f"${pc[0]} \\cdot {pc[1]} \\vdash {cc}$")
    return card(10, 4, lvl, typ, "iso", f"{KK} Запишите кодами посылок и заключения (1a–4d, 5a–5d, с. 153) простые категорические силлогизмы:\n\n" +
                items([f"${MODI[m]}$" for m in ms]), answers(ans), "Таблица видов посылок и заключений на с. 153.", "с. 153–155, гл. 10, § 4",
                "силлогистика классов", system="S^s_k")


def form_card(lvl, typ="R"):
    cs = rnd.sample(sorted(FORMS), 4)
    return card(10, 4, lvl, typ, "iso", f"{KK} Запишите формулы, обозначенные в доказательстве MT1 § 4 гл. 10 (с. 153) кодами: " + ", ".join(cs) + ".",
                answers([f"${ftex(c)}$" for c in cs]), "С. 153.", "с. 153, гл. 10, § 4", "силлогистика классов", system="S^s_k")


def modus_rec(lvl, typ="C"):
    ms = rnd.sample(sorted(MODI), 3)
    return card(10, 4, lvl, typ, "iso", f"{KK} Укажите номера модусов (T1–T19, с. 155–156):\n\n" + items([f"${MODI[m]}$" for m in ms]),
                answers([f"T{m}" + (f" ({NAMES[m]})" if m in NAMES else "") for m in ms]), "С. 155–156; T1–T6 — Barbara, Celarent, Darii, Ferio, Cesare, "
                "Camestres.", "с. 155–156, гл. 10, § 4", "силлогистика классов", system="S^s_k")


def base_card(lvl, typ="D"):
    ms = rnd.sample(sorted(MBASE), 2)
    return card(10, 4, lvl, typ, "complete", f"{KK} Восстановите основания (по списку книги, с. 155–156) модусов:\n\n" +
                items([f"T{m}. ${MODI[m]}$" for m in ms]), answers([f"[{MBASE[m]}]" for m in ms]), "С. 155–156.", "с. 155–156, гл. 10, § 4",
                "силлогистика классов", system="S^s_k")


ZERO = [("1a", "3a", "5b"), ("1a", "4a", "5d"), ("2a", "3a", "5a")]


def r_star(lvl, typ="C"):
    p1, p2, c = rnd.choice(ZERO)
    opts = []
    if c in ("5b", "5d"):
        opts.append((p1, p2, {"5b": "5a", "5d": "5c"}[c], "R*1"))
    for j, p in enumerate((p1, p2)):
        if p[1] in "ac":
            q = p[0] + {"a": "b", "c": "d"}[p[1]]
            opts.append(((q, p2, c) if j == 0 else (p1, q, c)) + ("R*2",))
    o = rnd.choice(opts)
    return card(10, 4, lvl, typ, "iso", f"{KK} По с. 154 формула ${p1} \\cdot {p2} \\vdash {c}$ может принять значение 0. Какую формулу, которая тоже может принять "
                f"значение 0, даёт правило {o[3]} (с. 153–154)? Запишите её кодами и формулой.", f"${o[0]} \\cdot {o[1]} \\vdash {o[2]}$: ${ftex(o[0])}{ftex(o[1])} \\vdash {ftex(o[2])}$",
                "R*1: заключение 5b, 5d → 5a, 5c; R*2: член посылки вида $ia$ или $ic$ → $ib$ или $id$ (с. 153–154).", "с. 153–154, гл. 10, § 4",
                "силлогистика классов", system="S^s_k")


def r_star_multi(lvl, typ="C"):
    p1, p2, c = rnd.choice(ZERO)
    res = set()
    frontier = [(p1, p2, c)]
    while frontier:
        a1, a2, cc = frontier.pop()
        if (a1, a2, cc) in res:
            continue
        res.add((a1, a2, cc))
        if cc in ("5b", "5d"):
            frontier.append((a1, a2, {"5b": "5a", "5d": "5c"}[cc]))
        for j, pp in enumerate((a1, a2)):
            if pp[1] in "ac":
                q = pp[0] + {"a": "b", "c": "d"}[pp[1]]
                frontier.append((q, a2, cc) if j == 0 else (a1, q, cc))
    res.discard((p1, p2, c))
    lst = sorted(res)
    return card(10, 4, lvl, typ, "open", f"{KK} Формула ${p1} \\cdot {p2} \\vdash {c}$ может принять значение 0 (с. 154). Найдите все простые категорические "
                "силлогизмы, которые по правилам R*1 и R*2 (с. 153–154), применённым сколько угодно раз, тоже могут принять значение 0.",
                ", ".join(f"${a} \\cdot b' \\vdash {cc}$".replace("b'", b2) for a, b2, cc in lst), f"Всего {len(lst)}. Каждое применение R*1 меняет 5b на 5a "
                "(5d на 5c), R*2 — $ia$ на $ib$, $ic$ на $id$ в одном члене посылки.", "с. 153–154, гл. 10, § 4", "силлогистика классов", system="S^s_k")


def ask_rec(lvl, typ="R"):
    ks = rnd.sample(sorted(ASK), 4)
    return card(10, 4, lvl, typ, "iso", f"{KK} Каким аксиомным схемам $S^s_k$ (с. 152) соответствуют формулы?\n\n" + items([f"${ASK[k]}$" for k in ks]),
                answers(ks), "С. 152.", "с. 152, гл. 10, § 4", "силлогистика классов", system="S^s_k")


def d1_syl(lvl, typ="C"):
    its = []
    good_ = rnd.choice(sorted(MODI))
    its.append((MODI[good_], "да"))
    its.append(("(\\forall a)(a \\in Kc)(\\forall a)(a \\in Kc) \\vdash (\\forall a)(a \\in Kc)", "нет: высказывания посылки должны быть различны"))
    its.append(("(\\forall a)(a \\in Kc)(\\forall c)(c \\in Kb)(\\forall b)(b \\in Kd) \\vdash (\\forall a)(a \\in Kd)", "нет: в посылке три члена (это категорический силлогизм по D2)"))
    rnd.shuffle(its)
    return card(10, 4, lvl, typ, "iso", f"{KK} Являются ли формулы простыми категорическими силлогизмами (D1 § 4 гл. 10, с. 152)?\n\n" + items([f"${s}$" for s, _ in its]),
                answers([w.split(":")[0] for _, w in its]), "\n".join(f"{L[k]}) {w}." for k, (_, w) in enumerate(its)) + " D1 (с. 152), D2 (с. 156).",
                "с. 152, 156, гл. 10, § 4", "силлогистика классов", system="S^s_k")


E1004 = [("«простых категорических силлогизмов 256»", "их 512; рассматривать достаточно 256, так как остальные получаются по A4 (с. 153)"),
         ("«$1a \\cdot 3a \\vdash 5b$ — тавтология»", "по с. 154 такие формулы могут принять значение 0"),
         ("«$2a \\cdot 3a \\vdash 5a$ — тавтология: это Barbara»", "Barbara — T1, код $1a \\cdot 4a \\vdash 5a$; формула $2a \\cdot 3a \\vdash 5a$ может принять значение 0 (с. 154)"),
         ("«$1a \\cdot 4a \\vdash 5d$ — тавтология»", "по с. 154 она может принять значение 0"),
         ("«R*1: если $x \\vdash y$ с заключением 5a имеет значение 0, то и с заключением 5b»", "R*1 идёт от 5b к 5a и от 5d к 5c (с. 153)"),
         ("«R*2: член посылки вида $ib$ можно заменить на $ia$ с сохранением значения 0»", "R*2 — от $ia$ к $ib$ и от $ic$ к $id$ (с. 153–154)"),
         ("«все простые категорические силлогизмы, кроме 19 модусов, доказуемы, но не тавтологии»", "по с. 156 в силу непротиворечивости $S^s_k$ остальные "
          "простые категорические силлогизмы недоказуемы"),
         ("«T5 — это Celarent»", "Celarent — T2; T5 — Cesare (с. 156)")]


def zero_closure():
    res = set()
    for start in ZERO:
        frontier = [start]
        while frontier:
            a1, a2, cc = frontier.pop()
            if (a1, a2, cc) in res:
                continue
            res.add((a1, a2, cc))
            if cc in ("5b", "5d"):
                frontier.append((a1, a2, {"5b": "5a", "5d": "5c"}[cc]))
            for j, pp in enumerate((a1, a2)):
                if pp[1] in "ac":
                    q = pp[0] + {"a": "b", "c": "d"}[pp[1]]
                    frontier.append((q, a2, cc) if j == 0 else (a1, q, cc))
    return res


ZC = set(ZERO)
MCODE = {m: modus_codes(m) for m in MODI}


def zsrc(f):
    for s in ZERO:
        if s == f:
            return f"с. 154: формула ${s[0]} \\cdot {s[1]} \\vdash {s[2]}$ может принять значение 0"
    return ""


def zero_closure_from(start):
    res, frontier = set(), [start]
    while frontier:
        a1, a2, cc = frontier.pop()
        if (a1, a2, cc) in res:
            continue
        res.add((a1, a2, cc))
        if cc in ("5b", "5d"):
            frontier.append((a1, a2, {"5b": "5a", "5d": "5c"}[cc]))
        for j, pp in enumerate((a1, a2)):
            if pp[1] in "ac":
                q = pp[0] + {"a": "b", "c": "d"}[pp[1]]
                frontier.append((q, a2, cc) if j == 0 else (a1, q, cc))
    return res


def syl_e(lvl):
    if rnd.random() < 0.5:
        m = rnd.choice(sorted(MODI))
        return E(10, 4, lvl, KK, f"«формула ${MODI[m]}$ может принять значение 0»", f"это модус T{m}" + (f" ({NAMES[m]})" if m in NAMES else "") +
                 " — тавтология, доказуемая в $S^s_k$ (с. 155–156)", "с. 154–156, гл. 10, § 4", "силлогистика классов, диагностика", system="S^s_k")
    f = rnd.choice(sorted(ZC))
    return E(10, 4, lvl, KK, f"«${f[0]} \\cdot {f[1]} \\vdash {f[2]}$ — тавтология»", "формула может принять значение 0: " + zsrc(f),
             "с. 153–154, гл. 10, § 4", "силлогистика классов, диагностика", system="S^s_k")


def syl_status(lvl, typ="C"):
    pool = [("m", m) for m in MODI] + [("z", f) for f in sorted(ZC)]
    its = rnd.sample(pool, 3)
    def show(it):
        if it[0] == "m":
            pc, cc = MCODE[it[1]]
            return f"${pc[0]} \\cdot {pc[1]} \\vdash {cc}$"
        return f"${it[1][0]} \\cdot {it[1][1]} \\vdash {it[1][2]}$"
    return card(10, 4, lvl, typ, "open", f"{KK} Запишите формулы по кодам (с. 153) и выясните, какие из них — модусы T1–T19, а какие могут принять значение 0 "
                "(по с. 154–156):\n\n" + items([show(x) for x in its]),
                answers([f"модус T{x[1]}" if x[0] == "m" else "может принять 0" for x in its]),
                "\n".join(f"{L[k]}) " + (f"${MODI[x[1]]}$ — T{x[1]} (с. 155–156)." if x[0] == "m" else f"${ftex(x[1][0])}{ftex(x[1][1])} \\vdash {ftex(x[1][2])}$; {zsrc(x[1])}.")
                          for k, x in enumerate(its)), "с. 153–156, гл. 10, § 4", "силлогистика классов", system="S^s_k")


def m1004(lvl, d, i):
    if d:
        if i % 2 == 0:
            return syl_e(lvl)
        s, w = rnd.choice(E1004)
        return E(10, 4, lvl, KK, s, w, "с. 152–156, гл. 10, § 4", "силлогистика классов, диагностика", system="S^s_k")
    if lvl == 1:
        return [ask_rec, form_card][i % 2](1)
    if lvl == 2:
        return [ask_rec, form_card, code_card, modus_rec][i % 4](2, "C")
    if lvl == 3:
        return [code_card, modus_rec, d1_syl, form_card][i % 4](3) if i % 4 != 3 else form_card(3, "C")
    if lvl == 4:
        return [base_card, code_card, modus_rec][i % 3](4)
    if lvl == 5:
        return [syl_status, base_card, code_card, modus_rec][i % 4](5)
    if lvl == 6:
        return syl_status(6) if i % 2 == 0 else [d1_syl, code_card][i % 4 // 2](6)
    return syl_status(7, "S")


def m1005(lvl, d, i):
    if d and nxt("e1005") % 2 == 1:
        return E(10, 5, lvl, "Буква $a$ — термин, $x$ — высказывание.", "«схема $(a \\leftarrow (x \\downarrow)) \\dashv\\vdash (a \\in K(sc \\downarrow x))$ связывает силлогистику "
                 "классов с неклассической силлогистикой предикатов»", "по с. 157 связь устанавливается с классической силлогистикой предикатов",
                 "с. 157, гл. 10, § 5", "силлогистика классов и предикатов, диагностика")
    if d:
        return E(10, 5, lvl, "Буквы $a$ — термин, $x$ — высказывание.", "«связь силлогистики классов с силлогистикой предикатов: "
                 "$(a \\leftarrow x) \\dashv\\vdash (a \\in Kx)$»", "схема § 5 (с. 157): $(a \\leftarrow (x \\downarrow)) \\dashv\\vdash (a \\in K(sc \\downarrow x))$ — "
                 "предикат «такой, что $x$» и класс предметов, таких, что $x$", "с. 157, гл. 10, § 5", "силлогистика классов и предикатов, диагностика")
    X = rnd.choice(["(a \\leftarrow b)", "(a \\leftarrow b)(a \\leftarrow c)", "\\sim(a \\leftarrow c)", "(\\forall b)(b \\leftarrow c)"])
    if lvl == 1:
        return card(10, 5, 1, "R", "iso", "Какой аксиомной схемой устанавливается связь силлогистики классов и классической силлогистики предикатов (§ 5 гл. 10)?",
                    "$(a \\leftarrow (x \\downarrow)) \\dashv\\vdash (a \\in K(sc \\downarrow x))$ (с. 157).", "С. 157.", "с. 157, гл. 10, § 5", "силлогистика классов и предикатов")
    return card(10, 5, lvl, "S" if lvl == 7 else "D", "iso", f"Буквы $a, b, c$ — термины. Подставьте в схему § 5 гл. 10 ($(a \\leftarrow (x \\downarrow)) \\dashv\\vdash "
                f"(a \\in K(sc \\downarrow x))$) высказывание $x = {X}$ и прочитайте результат.", f"$(a \\leftarrow ({X} \\downarrow)) \\dashv\\vdash (a \\in K(sc \\downarrow {X}))$: "
                "«$a$ имеет признак “такой, что $x$”» равнозначно «$a$ принадлежит классу предметов, таких, что $x$».", "С. 157; $sc$ — универсальный субъект (с. 137).",
                "с. 137, 157, гл. 9–10", "силлогистика классов и предикатов")


def m1006(lvl, d, i):
    if d:
        pool = [("«A1 § 6 гл. 10 ($\\vdash a \\in Kb$) означает, что любой предмет принадлежит любому классу в реальности»", "по с. 157 это допущение о том, что "
                 "области значения всех простых субъектов совпадают"),
                ("«$(\\forall a)(a \\leftarrow b) \\vdash (c \\leftarrow b)$ доказуема уже в $S^s_{cq}$»", "в $S^s_{cq}$ она недоказуема (MT2 § 3 гл. 7: новый "
                 "термин $c$); доказуемой она становится благодаря A1 на уровне систем квазиследования (с. 157)")]
        s, w = rnd.choice(pool)
        return E(10, 6, lvl, "Буквы $a, b, c$ — термины.", s, w, "с. 157, гл. 10, § 6", "квазиклассический случай, диагностика")
    if lvl == 2:
        return card(10, 6, 2, "D", "iso", "Что следует из аксиомной схемы A1 $\\vdash a \\in Kb$ квазиклассического случая (§ 6 гл. 10)?", "T1. $\\vdash (\\forall a)(a \\in Kb)$.",
                    "С. 157.", "с. 157, гл. 10, § 6", "квазиклассический случай")
    pool = [("$(\\forall a)(a \\leftarrow b) \\vdash (c \\leftarrow b)$", "доказуема благодаря A1 на уровне систем квазиследования; в $S^s_{cq}$ — нет (MT2 § 3 гл. 7)"),
            ("$(c \\leftarrow b) \\vdash (\\exists a)(a \\leftarrow b)$", "доказуема благодаря A1 на уровне квазиследования; в $S^s_{cq}$ — нет (MT2 § 3 гл. 7)"),
            ("$\\vdash (\\forall a)(a \\leftarrow b) \\supset (c \\leftarrow b)$", "общезначима лишь при допущении совпадения областей значения субъектов; в $S^5_{cq}$ недоказуема (MT2 § 10 гл. 7)"),
            ("$(\\forall a)(a \\leftarrow b)(c \\in Ka) \\vdash (c \\leftarrow b)$", "доказуема в $S^2_k$ (с. 157)"),
            ("$(c \\leftarrow b)(c \\in Ka) \\vdash (\\exists a)(a \\leftarrow b)$", "доказуема в $S^2_k$ (с. 157)")]
    k = 2 if lvl >= 6 else 1
    its = rnd.sample(pool, k)
    return card(10, 6, lvl, "S" if lvl == 7 else "C", "transfer", "Буквы $a, b, c$ — термины. Где и благодаря чему доказуемы (или недоказуемы) формулы (§ 6 гл. 10, с. 157)?\n\n" +
                items([s for s, _ in its]), answers([w for _, w in its]), "С. 157; гл. 7, § 3, 10.", "с. 157, гл. 10, § 6", "квазиклассический случай")


def m1007(lvl, d, i):
    if d:
        pool = [("«если $a$ есть термин, то $\\vdash (\\forall Ka)(Ka \\in Kkl)$ — и для $a = kl$»", "по с. 158 это рассуждение содержит ошибки: на место $a$ "
                 "нельзя подставить $kl$ (определение с переменной)"),
                ("«$K$ и $kl$ — одно и то же»", "надо различать термин «класс» ($kl$) и классообразующий оператор $K$, который термином не является (с. 158)")]
        s, w = rnd.choice(pool)
        return E(10, 7, lvl, "Буква $a$ — термин; $kl$ — термин «класс».", s, w, "с. 158, гл. 10, § 7", "классы классов, диагностика")
    pool = [("Как определяется термин $kl$ (D1 § 7 гл. 10)?", "Пусть $kl$ будет термином таким, что если $a$ есть термин, то $\\vdash (kl \\rightharpoonup Ka)$ (с. 158)."),
            ("Какой вид можно придать D1 § 7 гл. 10 (D*1)?", "Пусть $kl$ и $Kkl$ будут терминами такими, что если $a$ есть термин, то $\\vdash (\\forall Ka)(Ka \\in Kkl)$ (с. 158)."),
            ("Что утверждает MT1 § 7 гл. 10?", "Если $a$ есть термин, не зависящий по значению от $kl$, то $kl \\rightharpoonup Ka$ (то $Ka \\in Kkl$) (с. 158)."),
            ("Какие утверждения о $kl$ не могут быть получены из D1 § 7 (с. 158)?", "«Если $a$ — термин, то $kl \\rightharpoonup Ka$» для любого $a$, включая $kl$; "
             "а также $kl \\rightharpoonup Kkl$ и $Kkl \\in Kkl$."),
            ("Какую роль играет $a$ в D1 § 7 гл. 10?", "Роль переменной; область её значения — термины, не зависящие по значению от $kl$ (с. 158)."),
            ("От чего, по с. 159, зависит судьба утверждений $kl \\rightharpoonup Kkl$ и $Kkl \\in Kkl$?", "От внешних обстоятельств: они могут быть приняты или не приняты "
             "как аксиомы в зависимости от того, нужно ли это и приведёт ли к противоречиям."),
            ("Какими логическими свойствами обладает выражение «Пусть $kl$ будет термином» (с. 158)?", "Оно превращает вещь вида $kl$, которая до этого и "
             "независимо от этого не была термином, в термин."),
            ("Какую ошибку содержит рассуждение «если $a$ есть термин, то $Ka$ есть $kl$, т. е. $\\vdash (kl \\rightharpoonup Ka)$; значит, $\\vdash (\\forall Ka)(Ka \\in Kkl)$» (с. 158)?",
             "Не различаются термин «класс» ($kl$) и классообразующий оператор $K$, не являющийся термином; кроме того, на место $a$ подставляется и $kl$.")]
    q, a = pool[nxt("q1007") % len(pool)]
    return card(10, 7, lvl, "R" if lvl == 1 else "C", "iso", q, a, "Гл. 10, § 7.", "с. 158–159, гл. 10, § 7", "классы классов", form="meta", answ="text")


def m1008(lvl, d, i):
    return card(10, 8, 1, "R", "iso", "Как в § 8 гл. 10 (с. 159) определяется нормальный класс (D1)?", "Если $a$ есть термин и при этом $\\sim(Ka \\in Ka)$, "
                "то $Ka$ называется нормальным классом ($nk$).", "С. 159: прежнее определение непригодно, так как в нём не выражено, что класс есть всегда "
                "класс чего-то.", "с. 159, гл. 10, § 8", "парадокс нормальных классов")


# ================================================================ ручные ступени 8–10
H = []


def hand(ch, sec, lvl, cond, ans, sol, src, tags, system=None):
    H.append(card(ch, sec, lvl, "I" if lvl == 10 else "M", "transfer", cond, ans, sol, src, tags, form="meta", answ="proof", system=system, gen=False))


def hand_cards():
    hand(9, 2, 8, "Восстановите доказательство MT1 § 2 гл. 9 (с. 140–141): если доказуема $\\vdash (a \\rightharpoonup b)$, то в $a$ и $b$ входит хотя бы один одинаковый термин.",
         "Аксиомы 1–5 удовлетворяют MT1. Из формул вида $\\vdash (a \\rightharpoonup ab)$ по аксиомам 7 получаются лишь $\\vdash (a \\rightharpoonup ab^1 \\ldots b^n)$, по аксиомам 6 — "
         "лишь $\\vdash (\\sim(ab^1 \\ldots b^n) \\rightharpoonup \\sim a)$; формулы по аксиомам 8 явно удовлетворяют MT1.", "С. 140–141.", "с. 140–141, гл. 9, § 2", "термины, S1t", "S^1_t")
    hand(9, 3, 8, "Восстановите рассуждение с. 143–144: почему нельзя принимать $\\vdash (a \\leftarrow b)(a \\leftarrow c) \\to (a \\leftarrow (bc))$?",
         "Тогда пришлось бы принять $\\vdash (a \\leftarrow b)(a \\leftarrow \\sim b) \\to (a \\leftarrow (\\sim bb))$, а по AII.1 и $S^5$ — $\\vdash \\sim((a \\leftarrow b)(a \\leftarrow \\sim b))$, "
         "что не соответствует смыслу $\\sim b$: предмет может иметь признак $b$ и другой признак, не обозначаемый $b$.", "С. 143–144.", "с. 143–144, гл. 9, § 3", "термины, S2t", "S^2_t")
    hand(9, 3, 9, "Докажите T11 § 3 гл. 9 $\\vdash \\sim((a \\leftarrow b)(a \\leftarrow \\tilde b))$ из AIII.5 и $S^5_p$.", "По AIII.5 $(a \\leftarrow \\tilde b) \\dashv\\vdash (a \\urcorner\\!\\leftarrow b)$; "
         "по T8 $S^5_p$ $\\vdash \\sim((a \\leftarrow b)(a \\urcorner\\!\\leftarrow b))$; замена равнозначных.", "С. 133, 142–143.", "с. 133, 142–143, гл. 8–9", "термины, S2t", "S^2_t")
    hand(9, 3, 10, "Исследуйте, какие из схем AIII.6–AIII.15 § 3 гл. 9 доказуемы по аналогии друг из друга (например, 7 из 6 с помощью теоремных схем гл. 7 и 8). "
         "Предложите минимальный набор.", "Критерии: использованы T1–T6 § 6 гл. 8 и схемы § 14 гл. 7; приведены выводы хотя бы двух схем; набор обоснован.",
         "С. 142–143.", "с. 136, 142–143, гл. 8–9", "термины, исследование", "S^2_t")
    hand(10, 2, 8, "По образцу вывода T1 $S^1_k$ из A4 выведите T2: $(\\exists a)(a \\in Kb)(\\forall b)(b \\in Kc) \\vdash (\\exists a)(a \\in Kc)$.",
         "$(\\forall b)(b \\in Kc) \\vdash (\\forall a)(\\forall b)(b \\in Kc)$ [T17 гл. 7]; по A3 гл. 7: $(\\forall a)(\\forall b)(b \\in Kc)(\\exists a)(a \\in Kb) \\vdash (\\exists a)((\\forall b)(b \\in Kc)(a \\in Kb))$; "
         "R2 гл. 7 из A4 (с перестановкой): $(\\exists a)((\\forall b)(b \\in Kc)(a \\in Kb)) \\vdash (\\exists a)(a \\in Kc)$; $S^s$.", "С. 99–104, 150.", "с. 99–104, 150, гл. 7, 10",
         "классы, вывод", "S^1_k")
    hand(10, 2, 9, "Докажите MT1 § 2 гл. 10 для схем A2, A3, A5 по интерпретации (с. 150–151).", "A2: если $a \\in Kb = 0$, по п. 2 $a \\in K\\sim b = 1$ — значит, при посылке 1 "
         "заключение 1. A3: если $a \\in K\\sim b = 1$, то по п. 1 (для $\\sim b$, с R1) $a \\in K\\sim\\sim b = 0$, то есть $a \\in Kb = 0$. A5: п. 4.", "С. 150–151.",
         "с. 150–151, гл. 10, § 2", "классы, интерпретация", "S^1_k")
    hand(10, 2, 10, "Исследуйте замечание с. 151: какие аксиомные схемы $S^1_k$ становятся зависимыми, если принять $(a \\rightharpoonup b) \\vdash (\\forall b)(b \\in Ka)$ и обратную?",
         "Критерии: показано, как A6, A7 связываются с $\\rightharpoonup$; найдены выводы хотя бы одной схемы (например, T5–T7 через AI.2 гл. 9); вывод о зависимости.",
         "С. 151.", "с. 139–141, 150–151, гл. 9–10", "классы, исследование", "S^1_k")
    hand(10, 3, 8, "Покажите, что в $S^2_k$ доказуемы T1 и T2 $S^1_k$ (с. 150).", "A4 выводится из $A^14$ (с. 151); T1 и T2 выводятся из A4 средствами $S^s_{cq}$ (см. вывод T1).",
         "С. 150–151.", "с. 150–151, гл. 10, § 2–3", "классы, S2k", "S^2_k")
    hand(10, 3, 9, "Докажите: из $A^24$ следует $(b \\in Kc)(b \\in Ka) \\vdash (\\exists a)(a \\in Kc)$, а из $A^14$ — $(\\forall a)(a \\in Kc)(b \\in Ka) \\vdash (b \\in Kc)$. "
         "Сопоставьте их со схемами A2 и A1 $S^s_{cq}$.", "Примеры схем при $x = (b \\in Kc)$ и $x = (a \\in Kc)$. Аналогия: $A^14$ — «из общего — частное» (A1), $A^24$ — "
         "«из частного — существование» (A2), но с условием принадлежности $b$ классу $Ka$.", "С. 99, 151.", "с. 99, 151, гл. 7, 10", "классы, S2k", "S^2_k")
    hand(10, 4, 8, "По образцу MT2 § 4 гл. 10 (с. 156) докажите доказуемость категорического силлогизма $(\\forall d)(d \\in Kb)(\\forall c)(c \\in Kd)(\\forall a)(a \\in Kc) \\vdash (\\forall a)(a \\in Kb)$.",
         "Случай 2: $z = (\\forall a)(a \\in Kd)$: $(\\forall c)(c \\in Kd)(\\forall a)(a \\in Kc) \\vdash (\\forall a)(a \\in Kd)$ (Barbara, T1) и $z(\\forall d)(d \\in Kb) \\vdash (\\forall a)(a \\in Kb)$ "
         "(T1) — тавтологии и доказуемы; отсюда доказуема формула.", "С. 156.", "с. 155–156, гл. 10, § 4", "силлогистика классов", "S^s_k")
    hand(10, 4, 9, "Докажите производное правило R*3 (с. 154): если $x \\dashv\\vdash y$, то $\\sim y \\dashv\\vdash \\sim x$ [R1, A1, A2, R5, R4].",
         "Из $x \\dashv\\vdash y$ по R1 в $\\sim x \\vdash \\sim x$ (R4/A-схемы) заменяем вхождение $x$ на $y$: $\\sim x \\vdash \\sim y$; аналогично $\\sim y \\vdash \\sim x$; R3 даёт пару.",
         "С. 152–154.", "с. 152–154, гл. 10, § 4", "силлогистика классов", "S^s_k")
    hand(10, 4, 10, "Проверьте утверждение с. 154 о 19 модусах для фигуры с посылками вида 1 и 4: составьте все 16 силлогизмов $1x \\cdot 4y \\vdash 5a$ и отметьте, какие "
         "из них — модусы T1–T19.", "Критерии: перечень 16 формул с кодами (с. 153); сопоставление с T1–T19 (с. 155–156); для модусов указаны основания из книги.", "С. 153–156.",
         "с. 153–156, гл. 10, § 4", "силлогистика классов", "S^s_k")
    hand(10, 5, 8, "Покажите, как схема § 5 гл. 10 позволяет перевести высказывание силлогистики предикатов $(a \\leftarrow ((b \\leftarrow c) \\downarrow))$ в язык классов.",
         "$(a \\leftarrow ((b \\leftarrow c) \\downarrow)) \\dashv\\vdash (a \\in K(sc \\downarrow (b \\leftarrow c)))$.", "С. 157.", "с. 157, гл. 10, § 5", "силлогистика классов и предикатов")
    hand(10, 5, 9, "Докажите, что по схеме § 5 гл. 10 и AIV.6–7 § 3 гл. 9 доказуема $\\vdash x \\to (a \\in K(sc \\downarrow x))$.", "AIV.6: $\\vdash (x \\to (a \\leftarrow (x \\downarrow)))$; "
         "схема § 5: $(a \\leftarrow (x \\downarrow)) \\vdash (a \\in K(sc \\downarrow x))$; по $S^i_{if}$ (транзитивность условности, R1 $S^5_{if}$) — $\\vdash x \\to (a \\in K(sc \\downarrow x))$.",
         "С. 144, 157.", "с. 144, 157, гл. 9–10", "силлогистика классов и предикатов")
    hand(10, 5, 10, "Исследуйте, можно ли с помощью схемы § 5 гл. 10 перевести модусы T1–T6 силлогистики классов в силлогистику предикатов (§ 4 гл. 9). Какие трудности "
         "отмечает книга?", "Критерии: перевод хотя бы одного модуса; обсуждение громоздкости силлогистики предикатов (с. 146).", "С. 145–146, 157.", "с. 145–146, 157, гл. 9–10",
         "силлогистика классов и предикатов")
    # 17.09: L8 3, L9 2, L10 1
    hand(17, 9, 8, "Докажите в $S^s_{cq}$: $(\\forall a)(\\forall b)x \\vdash (\\exists b)(\\exists a)x$ двумя способами — по T40 и через T14, T27.",
         "T40 [A1, A2]. Иначе: T14 $(\\forall a)(\\forall b)x \\vdash (\\forall b)(\\forall a)x$; A1, T27: $(\\forall b)(\\forall a)x \\vdash (\\exists b)(\\forall a)x$; R2 из T27: "
         "$(\\exists b)(\\forall a)x \\vdash (\\exists b)(\\exists a)x$; транзитивность.", "Гл. 7, § 6.", "гл. 1–7", "смешанный, кванторы")
    hand(17, 9, 8, "Покажите, что $(\\exists a)((a \\leftarrow b) \\vee (a \\leftarrow c)) \\vdash (\\exists a)(a \\leftarrow b) \\vee (\\exists a)(a \\leftarrow c)$ удовлетворяет условиям процедуры "
         "§ 9 гл. 7, и установите её доказуемость.", "Бескванторная форма $z \\vee v \\vdash z \\vee v$ доказуема в $S^s$; п. 1 D1: контрольная форма совпадает с формулой; "
         "тавтология (случай 5, с. 109) — доказуема (T22).", "Гл. 7, § 8–9.", "гл. 1–7", "смешанный, кванторы")
    hand(17, 9, 8, "Докажите в $S^s_{if}$ и $S^s_{cq}$ одновременно: $(x \\rightarrow y)x(\\forall a)z \\vdash yz$.", "A1 $S^s_{if}$: $(x \\rightarrow y)x \\vdash y$; A1 $S^s_{cq}$: "
         "$(\\forall a)z \\vdash z$; объединение по $S^s$.", "Гл. 6, § 6; гл. 7, § 2.", "гл. 1–7", "смешанный")
    hand(17, 9, 9, "Докажите: если $x \\vdash y$ доказуема в $S^s_{cq}$, то её бескванторная форма — сильная тавтология (ограничение $S^s$).", "MT3 § 3 гл. 7: бескванторная "
         "форма доказуема в $S^s$; доказуемые в $S^s$ формулы — сильные тавтологии (гл. 5, § 2).", "Гл. 5, 7.", "гл. 1–7", "смешанный")
    hand(17, 9, 9, "Докажите, что в $S^s_{nq}$ недоказуема $\\vdash$-независимая формула $(\\urcorner\\forall a)x \\vdash \\sim(\\forall a)x\\sim(?\\forall a)x$ не может быть ослаблена до "
         "$\\sim(\\forall a)x \\vdash (\\urcorner\\forall a)x$.", "Первая — $A^28$. Вторая — A*13, принимаемая лишь в классическом варианте (§ 17); в $S^s_{nq}$ не тавтология: "
         "при истинном $(?\\forall a)x$ посылка истинна, заключение ложно (интерпретация § 15).", "Гл. 7, § 12, 15, 17.", "гл. 1–7", "смешанный")
    hand(17, 9, 10, "Сравните способы доказательства непротиворечивости в гл. 1, 7 (§ 4, 13) и 10 (интерпретация А. М. Фединой): что у них общего и чем они отличаются?",
         "Критерии: во всех — построена оценка, при которой аксиомы истинны и правила сохраняют истинность; указаны отличия (бескванторные формы, частичная интерпретация).",
         "Гл. 1, 7, 10.", "гл. 1–7", "смешанный, исследование")


# ================================================================ сборка
def mixed09(levels, diag):
    makers = [G7.prov706, G7.taut_n, G7.decide_card, G7.step1_card, G7.mtn_card, G7.ctrl1_card, G7.qf13_rand, G7.s5cq_card, G7.case_card]
    emk = [G7.e706, G7.e708, G7.e709, G7.e707, G7.e708x, G7.G6.q_e, G7.G6.interp_e, G7.G6.mt7_e, G7.G6.an_e, G7.G6.if_e]
    out, nd = [], 0
    left = sum(levels)
    for lvl, n in enumerate(levels, 1):
        for i in range(n):
            left -= 1
            d = nd < diag and lvl >= 3 and (i % 2 == 0 or left < diag - nd)
            mk = (lambda: emk[(i + lvl) % len(emk)](lvl)) if d else (lambda: makers[(i * 3 + lvl) % len(makers)](lvl))
            c = relabel(fresh(mk), 9, "гл. 1–7")
            c = re.sub(r"level: \d+", f"level: {lvl}", c, count=1)
            if lvl == 7:
                c = c.replace("type: C\n", "type: S\n", 1)
            if "type: E" in c:
                nd += 1
            out.append(c)
    return out


def mixed10():
    out = []
    for lvl, mk in [(2, lambda: G7.ap_rec(2, "C")), (2, lambda: G7.tp5_rec(2)), (3, lambda: G7.tp_rec(3)), (3, lambda: G7.p_deriv(3))]:
        c = relabel(fresh(mk), 10, "гл. 1–8")
        out.append(re.sub(r"level: \d+", f"level: {lvl}", c, count=1))
    return out


def main():
    cards = []
    cards += build(8, 5, [0, 0, 0, 1, 3, 2, 1], 2, m805)
    cards += build(8, 6, [0, 1, 1, 2, 3, 2, 1], 2, m806)
    cards += build(8, 7, [0, 1, 1, 2, 3, 2, 1], 2, m807)
    cards += build(9, 1, [4, 6, 5, 2, 1, 2, 1], 5, m901)
    cards += build(9, 2, [1, 2, 3, 3, 5, 4, 2], 5, m902)
    cards += build(9, 3, [1, 4, 5, 6, 11, 8, 4], 10, m903)
    cards += build(9, 4, [0, 1, 1, 2, 3, 2, 1], 2, m904)
    cards += build(9, 5, [2, 3, 3, 1, 0, 1, 0], 2, m905)
    cards += build(9, 6, [0, 1, 1, 2, 3, 2, 1], 2, m906)
    cards += build(9, 7, [2, 3, 3, 1, 0, 1, 0], 2, m907)
    cards += build(10, 1, [2, 3, 3, 1, 0, 1, 0], 2, m1001)
    cards += build(10, 2, [2, 6, 8, 9, 16, 13, 6], 16, m1002)
    cards += build(10, 3, [1, 3, 4, 5, 8, 6, 3], 8, m1003)
    cards += build(10, 4, [2, 5, 6, 8, 13, 11, 5], 13, m1004)
    cards += build(10, 5, [1, 1, 1, 0, 1, 1, 2], 2, m1005)
    cards += build(10, 6, [0, 1, 1, 2, 3, 2, 1], 2, m1006)
    cards += build(10, 7, [2, 3, 3, 1, 0, 1, 0], 2, m1007)
    cards += build(10, 8, [1], 0, m1008)
    cards += mixed09([0, 0, 9, 3, 13, 16, 9], 16)
    cards += mixed10()
    hand_cards()
    cards += H
    (ROOT / "drafts" / "61-70-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(cards), "из них ручных", len(H))


if __name__ == "__main__":
    main()
