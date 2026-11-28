#!/usr/bin/env python3
"""F18: переписывание карточек раздела 18 на месте (те же id) — П3 (естественно-языковая форма),
П4 (дубли и монотонные серии), П5 (пробелы покрытия).

Берёт исходные карточки из audit/orig18.md (копия до правок), пишет заплатки
drafts/18-F18-gen.md (карточки с id). Каждое условие и ответ проверяются здесь же
(независимый разбор строк выводов, перебор числовых моделей, вычисление составов классов).
Применение: python3 audit/apply_patch.py 18 drafts/18-F18-*.md
"""
import itertools
import random
import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[3]
ORIG = ROOT / "audit/orig18.md"
OUT = ROOT / "drafts/18-F18-gen.md"
rnd = random.Random(18_1972)


# ---------------------------------------------------------------- карточки
def load_orig():
    d = {}
    for t in ORIG.read_text(encoding="utf-8").split("\n=====\n"):
        m = re.search(r"^---\n(.*?)\n---\n", t.strip("\n") + "\n", re.S)
        if not m:
            continue
        fm = yaml.safe_load(m.group(1))
        body = t.strip("\n")[m.end():]
        sec = {}
        for mm in re.finditer(r"^## (Условие|Ответ|Решение)\n(.*?)(?=^## (?:Условие|Ответ|Решение)\n|\Z)", body, re.S | re.M):
            sec[mm.group(1)] = mm.group(2).strip()
        d[fm["id"]] = dict(fm=fm, **sec)
    return d


O = load_orig()
ORDER = ["id", "chapter", "section", "level", "type", "step", "condition", "form", "answer",
         "source", "system", "case", "series", "tags"]


def card(cid, level, typ, step, cond, form, ans, src, tags, U, A, R):
    o = O[cid]["fm"]
    head = ["---", f'id: "{cid}"', "chapter: 18", f"section: {o['section']}", f"level: {level}", f"type: {typ}",
            f"step: {step}", f"condition: {cond}", f"form: {form}", f"answer: {ans}", f'source: "{src}"',
            "generated: true", "tags: [" + ", ".join(tags) + "]", "---"]
    return "\n".join(head) + f"\n\n## Условие\n\n{U.strip()}\n\n## Ответ\n\n{A.strip()}\n\n## Решение\n\n{R.strip()}\n"


# ---------------------------------------------------------------- сравнение и порядок: разбор
REL_RE = re.compile(r"([a-fA-F]) (\\urcorner > |> |= |< )(p|m|\\alpha )([a-fA-F])")


def atom(tex):
    m = REL_RE.fullmatch(tex.strip().strip("$").strip())
    if not m:
        raise ValueError(tex)
    r = {"\\urcorner > ": "n", "> ": ">", "= ": "=", "< ": "<"}[m.group(2)]
    return (m.group(1), r, m.group(4))


def atex(a, mark):
    u, r, v = a
    s = {"n": "\\urcorner > ", ">": "> ", "=": "= ", "<": "< "}[r]
    return f"${u} {s}{mark}{v}$"


LINE_RE = re.compile(r"^(\d+)\. (\$[^$]+\$|…) \[(.*?)\]\s*$")


def parse_lines(text):
    out = []
    for ln in text.splitlines():
        m = LINE_RE.match(ln.strip())
        if m:
            out.append((int(m.group(1)), m.group(2), m.group(3)))
    return out


def norm(a):
    """< сводится к > (определение <)."""
    u, r, v = a
    return (v, ">", u) if r == "<" else a


def check_step(f, refs, rule, L, prem):
    """Верна ли строка f по правилу rule из строк refs (списки атомов). Перестановка членов конъюнкции допускается."""
    if rule == "посылка":
        return f in prem
    R = [L[i] for i in refs]
    if rule == "определение $<$":
        return len(R) == 1 and norm(R[0]) == norm(f) and R[0] != f
    if rule == "определение $=$":
        if len(R) == 1:
            u, r, v = R[0]
            return r == "=" and f in ((u, "n", v), (v, "n", u))
        if len(R) == 2 and f[1] == "=":
            u, _, v = f
            return set(R) == {(u, "n", v), (v, "n", u)}
        return False
    if rule == "C2":
        return len(R) == 1 and norm(R[0])[1] == ">" and f == (norm(R[0])[2], "n", norm(R[0])[0])
    pats = {"C4": (">", ">", ">"), "C5": (">", "=", ">"), "C6": ("=", ">", ">"), "C7": ("n", "n", "n")}
    if rule in pats and len(R) == 2:
        p1, p2, pc = pats[rule]
        for x, y in (R, R[::-1]):
            x, y = norm(x), norm(y)
            if x[1] == p1 and y[1] == p2 and x[2] == y[0] and norm(f) == (x[0], pc, y[2]):
                return True
    return False


def parse_basis(b):
    b = b.strip()
    if b == "посылка":
        return [], "посылка"
    m = re.match(r"^([\d, ]+); (.+)$", b)
    if not m:
        raise ValueError(b)
    return [int(x) for x in m.group(1).replace(" ", "").split(",")], m.group(2)


def check_deriv(lines, prem, goal):
    L = {}
    bad = []
    for n, ftex, basis in lines:
        f = atom(ftex)
        refs, rule = parse_basis(basis)
        if any(r >= n for r in refs) or not check_step(f, refs, rule, L, prem):
            bad.append(n)
        L[n] = f
    assert lines and atom(lines[-1][1]) == goal
    return bad


def model_ok(vals, a):
    u, r, v = a
    x, y = vals[u], vals[v]
    return {">": x > y, "=": x == y, "<": x < y, "n": x <= y}[r]


# ---------------------------------------------------------------- контексты (словарь «буква — фраза»)
CMP_CTX = [
    dict(key="рост", names=["Анна", "Борис", "Вера", "Глеб", "Дина", "Егор"],
         intro="Рост нескольких человек измеряли одним и тем же ростомером.",
         p="рост, измеренный одним и тем же ростомером (по с. 80 буква за знаком обозначает и признак, и способ сравнения)",
         ph={">": "{u} выше, чем {v}", "=": "{u} такого же роста, как {v}", "<": "{u} ниже, чем {v}", "n": "{u} не выше, чем {v}"},
         words="«выше» — $> p$, «такого же роста» — $= p$, «ниже» — $< p$, «не выше» — $\\urcorner > p$",
         unit=("рост", "см", 160, 5)),
    dict(key="вес", names=["чемодан", "рюкзак", "сумка", "коробка", "мешок", "корзина"],
         intro="Вещи взвешивали на одних и тех же весах.",
         p="вес, установленный на одних и тех же весах (по с. 80 буква за знаком обозначает и признак, и способ сравнения)",
         ph={">": "{u} тяжелее, чем {v}", "=": "{u} весит столько же, сколько {v}", "<": "{u} легче, чем {v}", "n": "{u} не тяжелее, чем {v}"},
         words="«тяжелее» — $> p$, «весит столько же» — $= p$, «легче» — $< p$, «не тяжелее» — $\\urcorner > p$",
         unit=("вес", "кг", 8, 2)),
    dict(key="скорость", names=["катер", "паром", "яхта", "баржа", "лодка", "буксир"],
         intro="Скорости судов сравнивали по показаниям одного и того же радара (ср. пример с. 80: «$a$ движется медленнее, чем $b$»).",
         p="скорость движения, установленная по одному и тому же радару (по с. 80 буква за знаком обозначает и признак, и способ сравнения)",
         ph={">": "{u} движется быстрее, чем {v}", "=": "{u} движется так же быстро, как {v}", "<": "{u} движется медленнее, чем {v}",
             "n": "{u} движется не быстрее, чем {v}"},
         words="«быстрее» — $> p$, «так же быстро» — $= p$, «медленнее» — $< p$, «не быстрее» — $\\urcorner > p$",
         unit=("скорость", "км/ч", 10, 5)),
]
ORD_CTX = [
    dict(key="финиш", names=["Антон", "Белла", "Виктор", "Галина", "Денис", "Елена"],
         intro="Бегуны стартовали одновременно; моменты финиша засекал судья по одному секундомеру.",
         p="способ установления порядка: отсчёт моментов финиша по секундомеру судьи от общего старта",
         ph={">": "{u} финишировал(а) позже, чем {v}", "=": "{u} финишировал(а) в тот же момент, что и {v}",
             "<": "{u} финишировал(а) раньше, чем {v}", "n": "{u} финишировал(а) не позже, чем {v}"},
         words="«позже» — $> \\alpha$, «в тот же момент» — $= \\alpha$, «раньше» — $< \\alpha$, «не позже» — $\\urcorner > \\alpha$",
         unit=("момент финиша", "с после старта", 50, 1)),
    dict(key="улица", names=["аптека", "почта", "школа", "библиотека", "пекарня", "баня"],
         intro="Здания стоят вдоль одной улицы; расстояние отсчитывается по улице от въезда в посёлок.",
         p="способ установления порядка: расстояние по улице от въезда в посёлок (точка отсчёта — въезд)",
         ph={">": "{u} стоит дальше от въезда, чем {v}", "=": "{u} стоит на том же расстоянии от въезда, что и {v}",
             "<": "{u} стоит ближе к въезду, чем {v}", "n": "{u} стоит не дальше от въезда, чем {v}"},
         words="«дальше» — $> \\alpha$, «на том же расстоянии» — $= \\alpha$, «ближе» — $< \\alpha$, «не дальше» — $\\urcorner > \\alpha$",
         unit=("расстояние", "сотен метров", 1, 1)),
]


def nm_of(ctx, x):
    n = ctx["names"]
    return n[x] if isinstance(n, dict) else n["abcdef".index(x)]


def phrase(ctx, a):
    u, r, v = a
    s = ctx["ph"][r].format(u=nm_of(ctx, u), v=nm_of(ctx, v))
    return s[0].upper() + s[1:]


def dict_line(ctx, letters, mark):
    lets = ", ".join(f"${x}$ — {nm_of(ctx, x)}" for x in letters)
    sym = {"p": "$p$", "m": "$m$"}.get(mark, "$\\alpha$")
    return f"Словарь: {lets}; {sym} — {ctx['p']}. Запись: {ctx['words']}."


def split_header(U):
    """Часть условия с определениями и аксиомами (от «Определения» до конца перечня аксиом)."""
    m = re.search(r"(Определения(?: \(с\. 79\))?: .*?C7 [^.]*?\$\.)", U, re.S)
    return m.group(1)


def prem_goal(U):
    m = re.search(r"(?:Выведите|выводится ли|вывод(?:е)? формулы) (\$[^$]+\$) из посылок (.*?)(?: по аксиомам|\. Укажите|;?\s*$)", U)
    if m:
        goal = atom(m.group(1))
        prem = [atom(x) for x in re.findall(r"\$[^$]+\$", m.group(2))]
        return prem, goal
    raise ValueError(U[:200])


def letters_of(atoms):
    s = sorted({x for a in atoms for x in (a[0], a[2])})
    return s


def quote_list(ctx, atoms):
    return "; ".join(f"«{phrase(ctx, a)}»" for a in atoms)


def num_text(ctx, vals):
    nm, unit, base, step = ctx["unit"]
    return ", ".join(f"{nm_of(ctx, x)} — {base + step * vals[x]:g}" for x in sorted(vals)) + f" ({nm}, {unit})"


def conv_cmp(cid, ctx, kind):
    """kind: iso | open | err. Переписывает карточку § 18/19 в естественно-языковую форму."""
    o = O[cid]
    U, A, R = o["Условие"], o["Ответ"], o["Решение"]
    mark = "\\alpha " if "\\alpha" in U else ("m" if re.search(r"[A-F] (?:\\\\urcorner )?[>=<] m[A-F]", U) else "p")
    head = split_header(U)
    sec = o["fm"]["section"]
    src = o["fm"]["source"]
    if sec == 19:
        head = ("По с. 82 отношения $= \\alpha$ и $< \\alpha$ определяются через $> \\alpha$ так же, как отношения сравнения, "
                "а для $> \\alpha$ принимаются аксиомы, аналогичные C1–C7 (вместо признака $p$ — способ упорядочивания $\\alpha$; "
                "что считать $> \\alpha$, а что $< \\alpha$, не предрешено — важно лишь, что если одно есть $> \\alpha$, то другое есть $< \\alpha$). "
                + head)
    if kind in ("iso", "open"):
        prem, goal = prem_goal(U)
    lets_all = None
    if kind == "iso":
        lines = parse_lines(R)
        assert check_deriv(lines, prem, goal) == [], cid
        lets = letters_of(prem + [goal])
        Un = (f"{ctx['intro']} {dict_line(ctx, lets, mark.strip())} {head} Известно: {quote_list(ctx, prem)}. "
              f"Формализуйте эти высказывания и выведите из них высказывание «{phrase(ctx, goal)}». "
              "Укажите основание каждой строки (номера строк и аксиому или определение); перестановка членов конъюнкции и удаление члена конъюнкции подразумеваются.")
        An = (f"Посылки: {'; '.join(atex(a, mark) for a in prem)}; заключение {atex(goal, mark)}. "
              f"Вывод в {len(lines)} строк (см. решение): «{phrase(ctx, goal)}» следует из данных.")
        Rn = ("Формализация по словарю: " + "; ".join(f"«{phrase(ctx, a)}» — {atex(a, mark)}" for a in prem + [goal]) + ".\n\n" + R)
        return card(cid, o["fm"]["level"], "F", "vary", "def", "nat", "proof", src, tags_of(o, "формализация"), Un, An, Rn)
    if kind == "open":
        lets = letters_of(prem + [goal])
        derivable = A.startswith("Выводится")
        if derivable:
            lines = parse_lines(R)
            assert check_deriv(lines, prem, goal) == [], cid
            Rn = ("Формализация по словарю: " + "; ".join(f"«{phrase(ctx, a)}» — {atex(a, mark)}" for a in prem + [goal]) + ".\n\n" + R)
            An = f"Следует: {atex(goal, mark)} выводится из посылок — вывод в {len(lines)} строк (см. решение)."
        else:
            vals = {k: int(v) for k, v in re.findall(r"\$([a-f]) = (\d+)\$", A)}
            assert all(model_ok(vals, a) for a in prem) and not model_ok(vals, goal), cid
            # ни одна модель не делает вывод возможным — проверяем ещё, что цель не в замыкании (перебор моделей 0..3 не нужен: модель уже опровергает)
            nums = num_text(ctx, vals)
            An = (f"Не следует: при значениях {nums} все посылки верны, а «{phrase(ctx, goal)}» неверно; "
                  f"значит, {atex(goal, mark)} не выводится из посылок по C2, C4–C7 и определениям.")
            nm = ctx["unit"][0]
            Rn = ("Формализация по словарю: " + "; ".join(f"«{phrase(ctx, a)}» — {atex(a, mark)}" for a in prem + [goal]) + ".\n\n"
                  f"1. Сопоставим каждому предмету число — {nm}: {nums}; знак $>$ читаем как «больше», $=$ — «равно», $\\urcorner >$ — «не больше», $<$ — «меньше».\n"
                  "2. При таком чтении верна каждая аксиома C2, C4–C7 и оба определения: например, если $u > v$ и $v > w$, то $u > w$ (C4); "
                  "если $u > v$, то $v$ не больше $u$ (C2); $u = v$ тогда и только тогда, когда ни одно не больше другого. "
                  "Значит, всякая строка вывода из верных посылок тоже верна.\n"
                  f"3. Все посылки при этих значениях верны: {'; '.join(atex(a, mark) for a in prem)}.\n"
                  f"4. Заключение {atex(goal, mark)} при этих значениях неверно. Будь оно выводимо, оно было бы верно (п. 2). Вывода нет.\n\n"
                  f"Источник: {src}.")
        Un = (f"{ctx['intro']} {dict_line(ctx, lets, mark.strip())} {head} Из сообщений {quote_list(ctx, prem)} "
              f"кто-то заключает: «{phrase(ctx, goal)}». Формализуйте рассуждение и исследуйте, следует ли заключение из сообщений по аксиомам C2, C4–C7 и определениям: "
              f"если следует — постройте вывод с основанием каждой строки, если нет — подберите значения признака ({ctx['unit'][0]}, {ctx['unit'][1]}), "
              "при которых все сообщения верны, а заключение неверно, и объясните, почему этого достаточно.")
        return card(cid, o["fm"]["level"], "F", "open", "def", "nat", "proof", src, tags_of(o, "формализация", "открытый исход"), Un, An, Rn)
    raise ValueError(kind)


def tags_of(o, *extra):
    t = [x for x in o["fm"].get("tags", []) if x not in ("вывод",)]
    for e in extra:
        if e not in t:
            t.append(e)
    return t


RULES_CMP = ["C2", "C4", "C5", "C6", "C7", "определение $=$", "определение $<$"]


def make_two_errors(lines, prem, goal, seed):
    """Две ошибки в основаниях: в одной строке — неверная ссылка на строку, в другой — неверное правило.
    Каждая ошибочная строка не выводится по указанному основанию ни при каком порядке ссылок."""
    r = random.Random(seed)
    L = {n: atom(f) for n, f, _ in lines}
    cand = [k for k, (n, f, b) in enumerate(lines) if b != "посылка"]
    for _ in range(500):
        i, j = sorted(r.sample(cand, 2))
        if abs(i - j) < 2:
            continue
        new = list(lines)
        # ошибка 1: ссылка
        n, f, b = lines[i]
        refs, rule = parse_basis(b)
        k = r.randrange(len(refs))
        alts = [m for m in L if m < n and m not in refs]
        if not alts:
            continue
        refs2 = list(refs)
        refs2[k] = r.choice(alts)
        b1 = f"{', '.join(map(str, refs2))}; {rule}"
        # ошибка 2: правило
        n2, f2, bb = lines[j]
        refs_j, rule_j = parse_basis(bb)
        opts = [x for x in RULES_CMP if x != rule_j]
        rule2 = r.choice(opts)
        b2 = f"{', '.join(map(str, refs_j))}; {rule2}"
        new[i] = (n, f, b1)
        new[j] = (n2, f2, b2)
        Lw = {}
        badset = []
        for nn, ff, bs in new:
            rr, ru = parse_basis(bs)
            if not check_step(atom(ff), rr, ru, Lw, prem):
                badset.append(nn)
            Lw[nn] = atom(ff)
        if sorted(badset) == sorted([n, n2]):
            return new, (i, b, b1), (j, bb, b2)
    raise RuntimeError("не удалось")


def conv_err(cid, ctx):
    o = O[cid]
    U, R = o["Условие"], o["Решение"]
    mark = "\\alpha " if "\\alpha" in U else ("m" if re.search(r"[A-F] (?:\\\\urcorner )?[>=<] m[A-F]", U) else "p")
    src = o["fm"]["source"]
    # исправленный (верный) вывод — во второй половине решения
    good = parse_lines(R.split("Исправленный вывод:")[1])
    prem = [atom(f) for n, f, b in good if b == "посылка"]
    goal = atom(good[-1][1])
    assert check_deriv(good, prem, goal) == [], cid
    new, e1, e2 = make_two_errors(good, prem, goal, cid)
    head = split_header(U)
    if o["fm"]["section"] == 19:
        head = ("По с. 82 отношения $= \\alpha$ и $< \\alpha$ определяются через $> \\alpha$ так же, как отношения сравнения, "
                "а для $> \\alpha$ принимаются аксиомы, аналогичные C1–C7 (вместо признака $p$ — способ упорядочивания $\\alpha$). " + head)
    lets = letters_of(prem + [goal])
    body = "\n".join(f"{n}. {f} [{b}]" for n, f, b in new)
    Un = (f"{ctx['intro']} {dict_line(ctx, lets, mark.strip())} {head} Из сообщений {quote_list(ctx, prem)} студент заключил: «{phrase(ctx, goal)}» — "
          "и записал вывод. Перестановка членов конъюнкции и удаление члена конъюнкции подразумеваются. "
          "Ровно два основания в выводе указаны неверно. Найдите обе ошибки, назовите нарушенное правило и исправьте основания.\n\n" + body)
    def expl(e):
        i, right, wrong = e
        n, f, _ = good[i]
        return n, f, right, wrong
    rows = sorted([expl(e1), expl(e2)])
    An = "; ".join(f"строка {n}: указано [{w}], верно [{r}]" for n, f, r, w in rows) + "."
    Lm = {n: atom(f) for n, f, _ in good}
    def why(n, f, r, w):
        rr, ru = parse_basis(w)
        what = ", ".join(f"строка {k} — {atex(Lm[k], mark)}" for k in rr)
        return (f"Строка {n} ({f}): по основанию [{w}] её получить нельзя ({what}; под схему «{ru}» "
                f"эти строки не подходят ни в каком порядке). Верное основание — [{r}].")
    Rn = ("\n".join(why(*x) for x in rows) + "\n\nИсправленный вывод:\n\n" + "\n".join(f"{n}. {f} [{b}]" for n, f, b in good)
          + f"\n\nОстальные строки проверены: каждая получается по указанному основанию (с. 79{', 82' if o['fm']['section'] == 19 else ''}).\n\nИсточник: {src}.")
    return card(cid, o["fm"]["level"], "E", "vary", "def", "nat", "text", src, tags_of(o, "диагностика", "естественный язык"), Un, An, Rn)


def sec18_19():
    out = []
    c = CMP_CTX
    iso18 = ["18.18-014", "18.18-016", "18.18-018", "18.18-020", "18.18-022", "18.18-024", "18.18-026"]
    for k, cid in enumerate(iso18):
        out.append(conv_cmp(cid, c[k % 3], "iso"))
    open18 = ["18.18-046", "18.18-048", "18.18-050", "18.18-052", "18.18-055"]
    for k, cid in enumerate(open18):
        out.append(conv_cmp(cid, c[(k + 1) % 3], "open"))
    err18 = ["18.18-039", "18.18-041", "18.18-043", "18.18-045"]
    for k, cid in enumerate(err18):
        out.append(conv_err(cid, c[(k + 2) % 3]))
    iso19 = ["18.19-014", "18.19-016", "18.19-018", "18.19-020", "18.19-022", "18.19-024"]
    for k, cid in enumerate(iso19):
        out.append(conv_cmp(cid, ORD_CTX[k % 2], "iso"))
    open19 = ["18.19-039", "18.19-040", "18.19-042", "18.19-044"]
    for k, cid in enumerate(open19):
        out.append(conv_cmp(cid, ORD_CTX[(k + 1) % 2], "open"))
    err19 = ["18.19-033", "18.19-036"]
    for k, cid in enumerate(err19):
        out.append(conv_err(cid, ORD_CTX[k % 2]))
    return out


# ---------------------------------------------------------------- § 6 классы: обычный язык
PEOPLE = ["Ольга", "Пётр", "Ирина", "Семён", "Тамара", "Юрий", "Лидия"]
CLASS_SETS = [
    [("A", "играет в шахматы", "шахматистов"), ("B", "поёт в хоре", "хористов"), ("C", "занимается плаванием", "пловцов")],
    [("A", "говорит по-французски", "говорящих по-французски"), ("B", "водит автомобиль", "водителей"), ("C", "играет на гитаре", "гитаристов")],
    [("A", "живёт в общежитии", "живущих в общежитии"), ("B", "получает стипендию", "стипендиатов"), ("C", "занимается в научном кружке", "кружковцев")],
]


def t_tex(t, top=True):
    if isinstance(t, str):
        return t
    op, x, y = t
    s = f"{t_tex(x, False)} \\{'cap' if op == '&' else 'cup'} {t_tex(y, False)}"
    return s if top else f"({s})"


def t_set(t, mem):
    if isinstance(t, str):
        return set(mem[t])
    op, x, y = t
    a, b = t_set(x, mem), t_set(y, mem)
    return a & b if op == "&" else a | b


def t_inner(t, verb):
    if isinstance(t, str):
        return verb[t]
    op, x, y = t
    assert isinstance(x, str) and isinstance(y, str)
    return f"и {verb[x]}, и {verb[y]}" if op == "&" else f"{verb[x]} или {verb[y]}"


def t_phrase(t, verb):
    if isinstance(t, str) or all(isinstance(z, str) for z in t[1:]):
        return f"те, кто {t_inner(t, verb)}"
    op, x, y = t
    if op == "&":
        return f"те, кто {t_inner(x, verb)}, и при этом {t_inner(y, verb)}"
    return f"те, кто {t_inner(x, verb)}, а также те, кто {t_inner(y, verb)}"


def t_steps(t, mem, names):
    out = []
    def rec(u):
        if isinstance(u, str):
            return
        rec(u[1]); rec(u[2])
        rule = "входят в оба (правило для $\\cap$)" if u[0] == "&" else "входят хотя бы в один (правило для $\\cup$)"
        out.append(f"${t_tex(u)}$: {rule} — {ppl(t_set(u, mem), names)}")
    rec(t)
    return "; ".join(out)


def ppl(s, names):
    return "никто (класс пуст)" if not s else ", ".join(names[i] for i in sorted(s))


def rand_mem(r, n=7):
    while True:
        mem = {k: sorted(r.sample(range(n), r.randint(2, 4))) for k in "ABC"}
        if len({tuple(v) for v in mem.values()}) == 3:
            return mem


def rand_tree(r, depth):
    L = ["A", "B", "C"]
    if depth == 1:
        x, y = r.sample(L, 2)
        return (r.choice("&|"), x, y)
    x, y, z = r.sample(L, 3)
    a = (r.choice("&|"), x, y)
    if r.random() < 0.55:
        b = z
    else:
        w = r.choice([x, y])
        b = (r.choice("&|"), *r.sample([z, w], 2))
    return (r.choice("&|"), a, b) if r.random() < 0.6 else (r.choice("&|"), b, a) if isinstance(b, tuple) else (r.choice("&|"), a, b)


def class_header(cs, mem, names, lets="ABC"):
    verb = {k: v for k, v, _ in cs}
    parts = [f"${k}$ — класс тех, кто {v}: в него включаются {', '.join(names[i] for i in mem[k])} и только они" for k, v, _ in cs if k in lets]
    return verb, ("Индивидная переменная $d$ пробегает семерых студентов одной группы: " + ", ".join(f"$e_{i + 1}$ — {n}" for i, n in enumerate(names)) + ". Словарь и данные: "
                  + "; ".join(parts) + ". Правила с. 62: $(d \\in A) \\wedge (d \\in B) \\dashv\\vdash (d \\in A \\cap B)$; "
                  "$(d \\in A) \\vee (d \\in B) \\dashv\\vdash (d \\in A \\cup B)$.")


def sec06_terms(cid, level, ntrees, depth, seed):
    r = random.Random(seed)
    cs = CLASS_SETS[seed % 3]
    for _ in range(1000):
        mem = rand_mem(r)
        trees = []
        while len(trees) < ntrees:
            t = rand_tree(r, depth if len(trees) else 2) if depth == 2 else rand_tree(r, 1)
            if t not in trees and t_tex(t) not in [t_tex(z) for z in trees]:
                trees.append(t)
        sets = [frozenset(t_set(t, mem)) for t in trees]
        if len(set(sets)) == len(sets) and frozenset() in sets or (len(set(sets)) == len(sets) and r.random() < 0.3):
            break
    verb, hdr = class_header(cs, mem, PEOPLE)
    items = "\n".join(f"{'абвгд'[i]}) «{t_phrase(t, verb).capitalize()}»" for i, t in enumerate(trees))
    U = (hdr + " Для каждого описания класса запишите термин класса в символах с. 62 (через $A$, $B$, $C$, $\\cap$, $\\cup$, со скобками) "
         "и найдите всех, кто в него включается; для каждой составной части укажите правило.\n\n" + items)
    A = "; ".join(f"{'абвгд'[i]}) ${t_tex(t)}$ — {ppl(t_set(t, mem), PEOPLE)}" for i, t in enumerate(trees)) + "."
    R = "По правилам с. 62 «включается и в $P$, и в $Q$» ($\\wedge$) выражается термином $P \\cap Q$, «включается в $P$ или в $Q$» ($\\vee$) — термином $P \\cup Q$.\n\n" + "\n\n".join(f"{'абвгд'[i]}) «{t_phrase(t, verb).capitalize()}»: термин ${t_tex(t)}$. "
                    + t_steps(t, mem, PEOPLE) + "." for i, t in enumerate(trees)) + "\n\nПравила — с. 62, гл. 2, § 6."
    return card(cid, level, "F", "vary", "def", "nat", "short", "с. 62, гл. 2, § 6", ["классы", "операции над классами", "формализация"], U, A, R)


def sec06_member(cid, seed):
    """Ступень 2: высказывания о включении в $A \\cap B$, $A \\cup B$ на обычном языке."""
    r = random.Random(seed)
    cs = CLASS_SETS[seed % 3][:2]
    mem = rand_mem(r)
    verb = {k: v for k, v, _ in cs}
    items, ans, sol = [], [], []
    ops = ["&", "|", "&", "|"]
    r.shuffle(ops)
    used = set()
    for i, op in enumerate(ops):
        while True:
            e = r.randrange(7)
            if (e, op) not in used:
                used.add((e, op)); break
        t = (op, "A", "B")
        val = e in t_set(t, mem)
        items.append(f"{'абвг'[i]}) «{PEOPLE[e]} включается в класс тех, кто {t_inner(t, verb)}»")
        ans.append(f"{'абвг'[i]}) $e_{e + 1} \\in {t_tex(t)}$ — {'истинно' if val else 'ложно'}")
        inA, inB = e in mem["A"], e in mem["B"]
        rule = ("$(d \\in A) \\wedge (d \\in B) \\dashv\\vdash (d \\in A \\cap B)$" if op == "&" else "$(d \\in A) \\vee (d \\in B) \\dashv\\vdash (d \\in A \\cup B)$")
        sol.append(f"{'абвг'[i]}) «и …, и …» — $\\cap$, «или» — $\\cup$: $e_{e + 1} \\in {t_tex(t)}$; {rule} (с. 62); {PEOPLE[e]} {'включается' if inA else 'не включается'} в $A$, "
                   f"{'включается' if inB else 'не включается'} в $B$ — высказывание {'истинно' if val else 'ложно'}.")
    _, hdr = class_header(cs, mem, PEOPLE, "AB")
    U = hdr + " Запишите каждое высказывание в символах с. 62 и установите по правилам для $\\cap$ и $\\cup$, истинно оно или ложно.\n\n" + "\n".join(items)
    return card(cid, 2, "T", "iso", "def", "nat", "short", "с. 62, гл. 2, § 6", ["классы", "операции над классами", "перевод"], U, "; ".join(ans) + ".", "\n".join(sol))


def sec06_preds(cid, seed):
    """Ступень 3: подкласс, пересечение, эквивалентность, пустота — на обычном языке (с. 63)."""
    r = random.Random(seed)
    cs = CLASS_SETS[seed % 3]
    while True:
        mem = rand_mem(r)
        if any(set(mem[x]) < set(mem[y]) for x in "ABC" for y in "ABC" if x != y):
            break
    verb = {k: v for k, v, _ in cs}
    gen = {k: g for k, _, g in cs}
    pairs = [(x, y) for x in "ABC" for y in "ABC" if x != y]
    r.shuffle(pairs)
    sub = next(p for p in pairs if set(mem[p[0]]) < set(mem[p[1]]))
    nsub = next(p for p in pairs if not set(mem[p[0]]) <= set(mem[p[1]]) and p != sub)
    inter = r.choice([p for p in pairs if p[0] < p[1]])
    tq = (r.choice("&|"), *r.sample("ABC", 2))
    items = [
        (f"«Каждый, кто {verb[sub[0]]}, {verb[sub[1]]}»", f"${sub[0]} \\subset {sub[1]}$", True,
         f"все включаемые в ${sub[0]}$ ({ppl(mem[sub[0]], PEOPLE)}) включаются в ${sub[1]}$ — по с. 63 $(\\forall d)((d \\in {sub[0]}) \\to (d \\in {sub[1]}))$, т. е. ${sub[0]} \\subset {sub[1]}$"),
        (f"«Класс {gen[nsub[0]]} — подкласс класса {gen[nsub[1]]}»", f"${nsub[0]} \\subset {nsub[1]}$", False,
         f"{PEOPLE[min(set(mem[nsub[0]]) - set(mem[nsub[1]]))]} включается в ${nsub[0]}$, но не в ${nsub[1]}$ — условие $(\\forall d)((d \\in {nsub[0]}) \\to (d \\in {nsub[1]}))$ нарушено (с. 63)"),
    ]
    common = set(mem[inter[0]]) & set(mem[inter[1]])
    items.append((f"«Классы {gen[inter[0]]} и {gen[inter[1]]} пересекаются»", f"$(\\exists d)((d \\in {inter[0]}) \\wedge (d \\in {inter[1]}))$", bool(common),
                  (f"{ppl(common, PEOPLE)} — в обоих классах" if common else "ни один студент не включается в оба класса") + " (определение пересечения, с. 63)"))
    s = t_set(tq, mem)
    items.append((f"«Класс тех, кто {t_inner(tq, verb)}, пуст»", f"$(\\forall d) {{\\sim}}(d \\in {t_tex(tq)})$", not s,
                  f"в ${t_tex(tq)}$ включаются: {ppl(s, PEOPLE)} (правило для $\\{'cap' if tq[0] == '&' else 'cup'}$, с. 62; определение пустого класса, с. 63)"))
    _, hdr = class_header(cs, mem, PEOPLE)
    defs = ("Определения с. 63: $A \\subset B$ — сокращение для $(\\forall d)((d \\in A) \\to (d \\in B))$; $A$ и $B$ пересекаются, если $(\\exists d)((d \\in A) \\wedge (d \\in B))$, "
            "и не пересекаются, если $(\\forall d){\\sim}((d \\in A) \\wedge (d \\in B))$; $A$ пуст, если $(\\forall d){\\sim}(d \\in A)$, и непуст, если $(\\exists d)(d \\in A)$.")
    U = (hdr + " " + defs + " Запишите каждое высказывание в символах § 6 и установите, истинно оно или ложно, обосновав по определениям.\n\n"
         + "\n".join(f"{'абвг'[i]}) {t}" for i, (t, _, _, _) in enumerate(items)))
    A = "; ".join(f"{'абвг'[i]}) {f} — {'истинно' if v else 'ложно'}" for i, (_, f, v, _) in enumerate(items)) + "."
    R = "\n".join(f"{'абвг'[i]}) {t} — {f}: {w}; {'истинно' if v else 'ложно'}." for i, (t, f, v, w) in enumerate(items))
    return card(cid, 3, "T", "iso", "def", "nat", "short", "с. 62–63, гл. 2, § 6", ["классы", "предикаты классов", "перевод"], U, A, R)


def sec06():
    out = []
    for k, cid in enumerate(["18.06-006", "18.06-007", "18.06-009", "18.06-010"]):
        out.append(sec06_member(cid, 600 + k))
    for k, cid in enumerate(["18.06-013", "18.06-015", "18.06-017"]):
        out.append(sec06_preds(cid, 610 + k))
    for k, cid in enumerate(["18.06-027", "18.06-029", "18.06-031", "18.06-033", "18.06-035", "18.06-037"]):
        out.append(sec06_terms(cid, 4, 4, 2, 620 + k))
    return out


# ---------------------------------------------------------------- § 5 степени истинности и § 16 вероятность: обычный язык
def tx(v):
    s = f"{v:.2f}".rstrip("0").rstrip(".")
    return s.replace(".", ",")


def tm(v):
    return tx(v).replace(",", "{,}")


V_STMTS = [
    [("x", "длина стола равна 2 м"), ("y", "масса гири равна 5 кг"), ("z", "температура воды равна 20 °C"), ("w", "скорость поезда равна 80 км/ч")],
    [("x", "высота башни равна 60 м"), ("y", "вес мешка равен 50 кг"), ("z", "расстояние до станции равно 3 км"), ("w", "площадь участка равна 6 соток")],
]
P_STMTS = [
    [("x", "завтра будет дождь"), ("y", "поезд опоздает"), ("z", "матч состоится"), ("w", "рейс задержат")],
    [("x", "урожай будет высоким"), ("y", "цена на зерно вырастет"), ("z", "река разольётся"), ("w", "дорогу закроют")],
]


def f_tex(t, top=True):
    if isinstance(t, str):
        return t
    if t[0] == "~":
        return f"{{\\sim}}{f_tex(t[1], False)}"
    s = f"{f_tex(t[1], False)} \\{'wedge' if t[0] == '&' else 'vee'} {f_tex(t[2], False)}"
    return s if top else f"({s})"


def f_inner(t, ph):
    if isinstance(t, str):
        return ph[t]
    op, x, y = t
    return f"{ph[x]} и {ph[y]}" if op == "&" else f"{ph[x]} или {ph[y]}"


def f_phrase(t, ph):
    if isinstance(t, str) or all(isinstance(z, str) for z in t[1:]):
        s = f_inner(t, ph)
    else:
        op, x, y = t
        s = f"{f_inner(x, ph)}, и при этом {f_inner(y, ph)}" if op == "&" else f"{f_inner(x, ph)}, или же {f_inner(y, ph)}"
    return s[0].upper() + s[1:]


def rand_ftree(r, lets, depth):
    if depth == 1:
        x, y = r.sample(lets, 2)
        return (r.choice("&|"), x, y)
    x, y, z = r.sample(lets, 3)
    a = (r.choice("&|"), x, y)
    b = z if r.random() < 0.5 else (r.choice("&|"), z, r.choice([w for w in lets if w != z]))
    return (r.choice("&|"), a, b) if r.random() < 0.5 else (r.choice("&|"), b, a)


def v_val(t, v):
    if isinstance(t, str):
        return v[t]
    a, b = v_val(t[1], v), v_val(t[2], v)
    return min(a, b) if t[0] == "&" else max(a, b)


def v_steps(t, v):
    out = []
    def rec(u):
        if isinstance(u, str):
            return
        rec(u[1]); rec(u[2])
        f = "min" if u[0] == "&" else "max"
        out.append(f"$v({f_tex(u)}) = {f}({tm(v_val(u[1], v))}, {tm(v_val(u[2], v))}) = {tm(v_val(u, v))}$")
    rec(t)
    return "; ".join(out)


V_HEAD = ("По с. 59–60 высказывания вида $P_\\alpha(a)$ («вес $a$ равен 10 кг») измеряются с большей или меньшей точностью; "
          "здесь уместно говорить о степенях истинности. Логических способов их измерения нет, но если они как-то измерены, "
          "имеют место правила: $\\vdash v(x \\wedge y) = min(v(x), v(y))$; $\\vdash v(x \\vee y) = max(v(x), v(y))$; "
          "$(x \\vdash y) \\wedge (v(x) = \\alpha) \\vdash (v(y) \\leqslant \\alpha)$.")


def sec05_card(cid, level, n, depth, seed):
    r = random.Random(seed)
    S = V_STMTS[seed % 2]
    lets = [k for k, _ in S][: (3 if depth == 1 else 4)]
    ph = dict(S)
    v = {k: r.choice([0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]) for k in lets}
    trees = []
    while len(trees) < n:
        t = rand_ftree(r, lets, depth)
        if t not in trees:
            trees.append(t)
    dic = "; ".join(f"${k}$ — «{ph[k]}», $v({k}) = {tm(v[k])}$" for k in lets)
    items = "\n".join(f"{'абвг'[i]}) «{f_phrase(t, ph)}»" for i, t in enumerate(trees))
    U = (V_HEAD + f" Словарь и данные измерений: {dic}. Запишите каждое высказывание формулой (союз «и» — $\\wedge$, «или» — $\\vee$, со скобками) "
         "и найдите его степень истинности, указав для каждой подформулы правило.\n\n" + items)
    A = "; ".join(f"{'абвг'[i]}) ${f_tex(t)}$, $v = {tm(v_val(t, v))}$" for i, t in enumerate(trees)) + "."
    R = "\n\n".join(f"{'абвг'[i]}) ${f_tex(t)}$: " + v_steps(t, v) + "." for i, t in enumerate(trees)) + \
        "\n\nПравила: степень истинности конъюнкции — наименьшая из степеней членов, дизъюнкции — наибольшая (с. 60, гл. 2, § 5)."
    return card(cid, level, "F", "vary", "def", "nat", "short", "с. 59–60, гл. 2, § 5", ["степени истинности", "формализация"], U, A, R)


def sec05_inverse(cid, seed, variant=0):
    """Ступень 3: найти степень члена по степени дизъюнкции/конъюнкции; обнаружить, когда данных не хватает."""
    r = random.Random(seed)
    S = V_STMTS[seed % 2]
    ph = dict(S)
    a, b = 0.2 + 0.1 * r.randrange(3), 0.6 + 0.1 * r.randrange(4)
    cap = lambda s: s[0].upper() + s[1:]
    if variant == 0:
        U = (V_HEAD + f" Словарь: $x$ — «{ph['x']}», $y$ — «{ph['y']}», $z$ — «{ph['z']}». "
             f"Измерено: степень истинности высказывания «{f_phrase(('|', 'x', 'y'), ph)}» равна {tx(b)}, высказывания «{cap(ph['x'])}» — {tx(a)}; "
             f"высказывание «{f_phrase(('&', 'y', 'z'), ph)}» имеет степень истинности {tx(a)}. "
             "Формализуйте данные и установите, что можно утверждать о $v(y)$ и о $v(z)$; если значение однозначно не определяется, укажите, какие ограничения на него дают правила.")
        A = (f"$v(x \\vee y) = {tm(b)}$, $v(x) = {tm(a)}$, $v(y \\wedge z) = {tm(a)}$. Отсюда $v(y) = {tm(b)}$; "
             f"$v(z) = {tm(a)}$ (так как $min({tm(b)}, v(z)) = {tm(a)}$).")
        R = (f"1. $v(x \\vee y) = max(v(x), v(y))$ (с. 60): $max({tm(a)}, v(y)) = {tm(b)}$; так как ${tm(a)} < {tm(b)}$, наибольшим должен быть $v(y)$: $v(y) = {tm(b)}$.\n"
             f"2. $v(y \\wedge z) = min(v(y), v(z))$ (с. 60): $min({tm(b)}, v(z)) = {tm(a)}$; так как ${tm(b)} > {tm(a)}$, наименьшим должен быть $v(z)$: $v(z) = {tm(a)}$.\n"
             "Оба значения определены однозначно.")
    else:
        U = (V_HEAD + f" Словарь: $x$ — «{ph['x']}», $y$ — «{ph['y']}», $z$ — «{ph['z']}». "
             f"Измерено: степень истинности высказывания «{f_phrase(('&', 'x', 'y'), ph)}» равна {tx(a)}, высказывания «{cap(ph['x'])}» — тоже {tx(a)}. "
             f"Из высказывания «{f_phrase(('&', 'x', 'y'), ph)}» выведено высказывание $z$ («{ph['z']}»). "
             "Формализуйте данные и установите, что можно утверждать о $v(y)$ и о $v(z)$; если значение однозначно не определяется, укажите, какие ограничения на него дают правила.")
        A = (f"$v(x \\wedge y) = {tm(a)}$, $v(x) = {tm(a)}$, $x \\wedge y \\vdash z$. Значение $v(y)$ однозначно не определяется: $v(y) \\geqslant {tm(a)}$; "
             f"$v(z) \\leqslant {tm(a)}$.")
        R = (f"1. $v(x \\wedge y) = min(v(x), v(y))$ (с. 60): $min({tm(a)}, v(y)) = {tm(a)}$ — это верно при любом $v(y) \\geqslant {tm(a)}$ "
             f"(тогда наименьшее — $v(x) = {tm(a)}$), и неверно при $v(y) < {tm(a)}$ (тогда наименьшее было бы $v(y)$). Значит, $v(y) \\geqslant {tm(a)}$, точнее правила не определяют.\n"
             f"2. По правилу $(x \\vdash y) \\wedge (v(x) = \\alpha) \\vdash (v(y) \\leqslant \\alpha)$ (с. 60) для посылки $x \\wedge y$ и заключения $z$: "
             f"$v(z) \\leqslant v(x \\wedge y) = {tm(a)}$ — степень истинности заключения не превышает степени истинности посылки.")
    return card(cid, 3, "F", "vary", "alt" if variant else "def", "nat", "short", "с. 59–60, гл. 2, § 5", ["степени истинности", "формализация"], U, A, R)


P_HEAD = ("По с. 75–76 «вероятность $sx$ равна $\\beta$» — языковая трансформация высказываний $M\\alpha(sx)$ («$sx$ возможно со степенью $\\beta$»); "
          "записывается $p(x) = \\beta$. Правила с. 76: $\\vdash 0 \\leqslant p(x) \\leqslant 1$; $\\vdash (p(x) = 0) \\leftrightarrow \\urcorner M(sx)$; "
          "$\\vdash (p(x) > 0) \\leftrightarrow M(sx)$; $\\vdash p(x \\wedge y) \\leqslant min(p(x), p(y))$; $\\vdash p(x \\vee y) \\geqslant max(p(x), p(y))$; "
          "$\\vdash p({\\sim}x) = 1 - p(x)$.")


def p_iv(t, p):
    if isinstance(t, str):
        return (p[t], p[t])
    if t[0] == "~":
        lo, hi = p_iv(t[1], p)
        return (round(1 - hi, 4), round(1 - lo, 4))
    a, b = p_iv(t[1], p), p_iv(t[2], p)
    if t[0] == "&":
        return (0, min(a[1], b[1]))
    return (max(a[0], b[0]), 1)


def p_txt(t, p):
    lo, hi = p_iv(t, p)
    if lo == hi:
        return f"$p({f_tex(t)}) = {tm(lo)}$"
    return f"${tm(lo)} \\leqslant p({f_tex(t)}) \\leqslant {tm(hi)}$"


def p_steps(t, p):
    out = []
    def rec(u):
        if isinstance(u, str):
            return
        if u[0] == "~":
            rec(u[1]); out.append(p_txt(u, p) + " [по $p({\\sim}x) = 1 - p(x)$]"); return
        rec(u[1]); rec(u[2])
        out.append(p_txt(u, p) + (" [по $p(x \\wedge y) \\leqslant min$ и $p \\geqslant 0$]" if u[0] == "&" else " [по $p(x \\vee y) \\geqslant max$ и $p \\leqslant 1$]"))
    rec(t)
    return "; ".join(out)


def sec16_card(cid, level, seed):
    r = random.Random(seed)
    S = P_STMTS[seed % 2]
    ph = dict(S)
    lets = [k for k, _ in S]
    p = {k: r.choice([0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]) for k in lets}
    trees = [("~", r.choice(lets))]
    while len(trees) < 4:
        t = rand_ftree(r, lets, 1 if len(trees) == 1 else 2)
        if t not in trees:
            trees.append(t)
    def ph_of(t):
        if t[0] == "~":
            return f"Неверно, что {ph[t[1]]}"
        return f_phrase(t, ph)
    dic = "; ".join(f"${k}$ — «{ph[k]}», $p({k}) = {tm(p[k])}$" for k in lets)
    items = "\n".join(f"{'абвг'[i]}) «{ph_of(t)}»" for i, t in enumerate(trees))
    U = (P_HEAD + f" Словарь и данные: {dic}. Запишите вероятность каждого из следующих состояний формулой (союз «и» — $\\wedge$, «или» — $\\vee$, «неверно, что» — ${{\\sim}}$) "
         "и найдите оценку, которую дают правила с. 76, применённые по строению формулы (снизу вверх), с обоснованием каждого шага; укажите, возможно ли состояние, когда это следует из оценки.\n\n" + items)
    def poss(t):
        lo, hi = p_iv(t, p)
        if lo > 0:
            return f"; так как $p > 0$ — $M(s({f_tex(t)}))$"
        if hi == 0:
            return f"; так как $p = 0$ — $\\urcorner M(s({f_tex(t)}))$"
        return "; возможность из оценки не следует"
    A = "; ".join(f"{'абвг'[i]}) {p_txt(t, p)}{poss(t)}" for i, t in enumerate(trees)) + "."
    R = "\n\n".join(f"{'абвг'[i]}) «{ph_of(t)}» — $p({f_tex(t)})$: " + p_steps(t, p) + poss(t) + " (с. 76)." for i, t in enumerate(trees)) + \
        "\n\nДля отрицания границы меняются местами: $1 -$ верхняя граница даёт нижнюю. Правила — с. 76, гл. 2, § 16."
    return card(cid, level, "F", "vary", "def", "nat", "short", "с. 75–76, гл. 2, § 16", ["вероятность", "формализация"], U, A, R)


def sec05_16():
    out = []
    for k, cid in enumerate(["18.05-004", "18.05-007"]):
        out.append(sec05_card(cid, 2 + k, 2, 1, 500 + k))
    out.append(sec05_inverse("18.05-005", 505))
    out.append(sec05_inverse("18.05-008", 508, 1))
    for k, cid in enumerate(["18.05-014", "18.05-016", "18.05-018", "18.05-020", "18.05-022"]):
        out.append(sec05_card(cid, 4, 3, 2, 510 + k))
    for k, cid in enumerate(["18.16-007", "18.16-014", "18.16-016", "18.16-018", "18.16-020", "18.16-022", "18.16-024", "18.16-026"]):
        out.append(sec16_card(cid, 3 if cid == "18.16-007" else 4, 1600 + k))
    return out


# ---------------------------------------------------------------- § 20 «между», § 23 соседство, § 24 соприкосновение: обычный язык
MAP = dict(a="Сосновка", b1="Озёрск", b2="Каменка", b3="Борки")
MAPH = {"1": "{u} восточнее, чем {v}", "2": "{u} севернее, чем {v}"}
MAP_INTRO = ("Посёлок Сосновка ($a$) и города Озёрск ($b^1$), Каменка ($b^2$), Борки ($b^3$) отмечены на карте. "
             "Способы установления порядка: $\\alpha^1$ — с запада на восток («восточнее» записывается как $> \\alpha^1$), "
             "$\\alpha^2$ — с юга на север («севернее» — $> \\alpha^2$). ")
BETW_DEF = ("По § 20 (с. 82) $a$ находится между $b^1, …, b^n$ относительно $\\alpha^1, …, \\alpha^m$, если и только если для любой пары $b^i$ и $b^k$ "
            "найдётся такой $\\alpha^j$, что $(a > \\alpha^j b^i) \\wedge (b^k > \\alpha^j a)$ или $(b^i > \\alpha^j a) \\wedge (a > \\alpha^j b^k)$.")


def bname(t):
    return MAP["a"] if t == "a" else MAP["b" + t[-1]]


USED20 = set()


def sec20_card(cid, seed, fresh=False):
    o = O[cid]
    U, A0 = o["Условие"], o["Ответ"]
    facts = re.findall(r"\$(a|b\^\d) > \\alpha\^(\d) (a|b\^\d)\$", U.split("Известно:")[1])
    assert len(facts) == 6, cid
    if fresh:
        r = random.Random(seed)
        while True:
            facts = [((b, j, "a") if r.random() < 0.5 else ("a", j, b)) for j in "12" for b in ("b^1", "b^2", "b^3")]
            key = frozenset(facts)
            if all(len(key - k) >= 2 for k in USED20):
                USED20.add(key); break
        A0 = None
    rel = {(u, j, v) for u, j, v in facts}
    def side(b, j):
        if (b, j, "a") in rel:
            return ">"
        if ("a", j, b) in rel:
            return "<"
        return None
    bs = ["b^1", "b^2", "b^3"]
    res, ok_all = [], True
    for i, k in itertools.combinations(range(3), 2):
        bi, bk = bs[i], bs[k]
        js = [j for j in "12" if side(bi, j) and side(bk, j) and side(bi, j) != side(bk, j)]
        if js:
            j = js[0]
            res.append((bi, bk, j))
        else:
            res.append((bi, bk, None)); ok_all = False
    if A0 is not None:
        assert ("Находится" in A0) == ok_all or ("Не находится" in A0) != ok_all, cid
    sent = "; ".join("«" + MAPH[j].format(u=bname(u), v=bname(v)) + "»" for u, j, v in facts)
    Un = (MAP_INTRO + BETW_DEF + f" Известно: {sent}. Формализуйте сведения и установите, находится ли Сосновка между Озёрском, Каменкой и Борками "
          "относительно $\\alpha^1, \\alpha^2$; для каждой пары городов укажите подходящий способ или докажите, что его нет.")
    def pair_txt(bi, bk, j):
        ni, nk = bname(bi), bname(bk)
        if j is None:
            return f"для пары {ni}, {nk} способа нет: относительно каждого из $\\alpha^1$, $\\alpha^2$ Сосновка лежит с обоими по одну сторону (или сведений нет)"
        if side(bi, j) == ">":
            return f"для пары {ni}, {nk} подходит $\\alpha^{j}$: $({bi} > \\alpha^{j} a) \\wedge (a > \\alpha^{j} {bk})$"
        return f"для пары {ni}, {nk} подходит $\\alpha^{j}$: $(a > \\alpha^{j} {bi}) \\wedge ({bk} > \\alpha^{j} a)$"
    An = ("Находится" if ok_all else "Не находится") + ": " + "; ".join(pair_txt(*x) for x in res) + "."
    Rn = ("Формализация: " + "; ".join(f"«{MAPH[j].format(u=bname(u), v=bname(v))}» — ${u} > \\alpha^{j} {v}$" for u, j, v in facts) + ".\n\n"
          + "\n".join(f"{n + 1}. {pair_txt(*x)}." for n, x in enumerate(res))
          + f"\n{len(res) + 1}. " + ("Для каждой пары способ нашёлся — по определению § 20 Сосновка находится между тремя городами относительно $\\alpha^1, \\alpha^2$ (с. 82)."
                                    if ok_all else "Хотя бы для одной пары способа нет — Сосновка не находится между ними (с. 82)."))
    return card(cid, 5, "F", "vary", "def", "nat", "short", o["fm"]["source"], ["между", "порядок", "формализация"], Un, An, Rn)


def sec20_err(cid, kind):
    if kind == 1:
        U = (MAP_INTRO + "По § 20 (с. 82) $a$ находится между $b$ и $c$ относительно $\\alpha$, если и только если $(a > \\alpha b) \\wedge (c > \\alpha a)$ или $(b > \\alpha a) \\wedge (a > \\alpha c)$. "
             "Известно: «Сосновка восточнее, чем Озёрск», «Сосновка восточнее, чем Каменка». Студент: «Значит, Сосновка находится между Озёрском и Каменкой относительно $\\alpha^1$: "
             "она связана отношением $> \\alpha^1$ с обоими». Найдите ошибку и назовите нарушенное определение.")
        A = ("Ошибка в применении определения «между» (§ 20, с. 82): даны $a > \\alpha^1 b^1$ и $a > \\alpha^1 b^2$ — Сосновка превосходит по порядку оба города; "
             "определение требует, чтобы один из двух превосходил $a$, а $a$ превосходил другой. Из данных «между» не следует.")
        R = ("1. Формализация: $a > \\alpha^1 b^1$, $a > \\alpha^1 b^2$.\n2. Для «$a$ между $b^1$ и $b^2$» нужно $(a > \\alpha^1 b^1) \\wedge (b^2 > \\alpha^1 a)$ или $(b^1 > \\alpha^1 a) \\wedge (a > \\alpha^1 b^2)$ (с. 82).\n"
             "3. По аксиоме C2 (аналог для $> \\alpha$, с. 82) из $a > \\alpha^1 b^2$ следует $b^2 \\urcorner > \\alpha^1 a$, а из $a > \\alpha^1 b^1$ — $b^1 \\urcorner > \\alpha^1 a$: оба нужных вторых члена ложны.\n"
             "4. Сосновка восточнее обоих городов, т. е. лежит по одну сторону от них; «между» не выполняется. Нарушено определение § 20.")
        return card(cid, 3, "E", "vary", "def", "nat", "text", "с. 82, гл. 2, § 20", ["между", "диагностика"], U, A, R)
    if kind == 2:
        U = (MAP_INTRO + "По § 20 (с. 82) $a$ находится между $b$ и $c$ относительно способа $\\alpha$, если и только если $(a > \\alpha b) \\wedge (c > \\alpha a)$ или $(b > \\alpha a) \\wedge (a > \\alpha c)$; "
             "в общем случае для пары $b^i$, $b^k$ нужен такой $\\alpha^j$, что $(a > \\alpha^j b^i) \\wedge (b^k > \\alpha^j a)$ или $(b^i > \\alpha^j a) \\wedge (a > \\alpha^j b^k)$. "
             "Известно: «Сосновка восточнее, чем Озёрск», «Каменка севернее, чем Сосновка»; других сведений нет. Студент: «Сосновка находится между Озёрском и Каменкой "
             "относительно $\\alpha^1, \\alpha^2$: Озёрск уступает ей по одному способу, а Каменка превосходит её по другому». Найдите ошибку и назовите нарушенное определение.")
        A = ("Нарушено определение § 20 (с. 82): оба члена конъюнкции должны относиться к одному и тому же способу $\\alpha^j$. Здесь $a > \\alpha^1 b^1$, но $b^2 > \\alpha^2 a$ — "
             "способы разные; ни для $\\alpha^1$, ни для $\\alpha^2$ данных на обе половины нет, так что «между» не установлено.")
        R = ("1. Формализация: $a > \\alpha^1 b^1$; $b^2 > \\alpha^2 a$.\n2. Для пары $b^1$, $b^2$ нужен один $\\alpha^j$ с $(a > \\alpha^j b^1) \\wedge (b^2 > \\alpha^j a)$ или $(b^1 > \\alpha^j a) \\wedge (a > \\alpha^j b^2)$.\n"
             "3. При $j = 1$ нет сведений о $b^2$ относительно $\\alpha^1$; при $j = 2$ — о $b^1$ относительно $\\alpha^2$. Студент составил конъюнкцию из членов с разными способами — так определение не позволяет.\n"
             "4. Вывод «Сосновка между городами» не обоснован (с. 82).")
        return card(cid, 4, "E", "vary", "under", "nat", "text", "с. 82, гл. 2, § 20", ["между", "диагностика"], U, A, R)
    U = (MAP_INTRO + BETW_DEF + " Известно: «Озёрск восточнее, чем Сосновка», «Сосновка восточнее, чем Каменка», «Борки севернее, чем Сосновка», «Сосновка севернее, чем Озёрск», "
         "«Сосновка севернее, чем Каменка», «Сосновка восточнее, чем Борки». Студент: «Сосновка не находится между тремя городами: ни по $\\alpha^1$, ни по $\\alpha^2$ "
         "она не лежит между всеми парами сразу». Проверьте рассуждение по определению, найдите ошибку и установите, находится ли Сосновка между городами.")
    facts = [("b1", "1", "a"), ("a", "1", "b2"), ("b3", "2", "a"), ("a", "2", "b1"), ("a", "2", "b2"), ("a", "1", "b3")]
    rel = set(facts)
    def ok(bi, bk):
        for j in "12":
            if ((bi, j, "a") in rel and ("a", j, bk) in rel) or (("a", j, bi) in rel and (bk, j, "a") in rel):
                return j
    pairs = {(x, y): ok(x, y) for x, y in itertools.combinations(["b1", "b2", "b3"], 2)}
    assert pairs == {("b1", "b2"): "1", ("b1", "b3"): "1", ("b2", "b3"): "2"}, pairs
    A = ("Ошибка: определение § 20 (с. 82) не требует одного способа для всех пар — для каждой пары достаточно своего $\\alpha^j$. "
         "Пара Озёрск, Каменка — $\\alpha^1$: $(b^1 > \\alpha^1 a) \\wedge (a > \\alpha^1 b^2)$; пара Озёрск, Борки — $\\alpha^1$: $(b^1 > \\alpha^1 a) \\wedge (a > \\alpha^1 b^3)$ (подходит и $\\alpha^2$: $(a > \\alpha^2 b^1) \\wedge (b^3 > \\alpha^2 a)$); "
         "пара Каменка, Борки — $\\alpha^2$: $(a > \\alpha^2 b^2) \\wedge (b^3 > \\alpha^2 a)$. Сосновка находится между тремя городами.")
    R = ("1. Формализация: $b^1 > \\alpha^1 a$; $a > \\alpha^1 b^2$; $b^3 > \\alpha^2 a$; $a > \\alpha^2 b^1$; $a > \\alpha^2 b^2$; $a > \\alpha^1 b^3$.\n"
         "2. В определении квантор «найдётся такой $\\alpha^j$» стоит внутри «для любой пары»: способ подбирается для каждой пары отдельно. Студент переставил кванторы — потребовал один способ для всех пар.\n"
         "3. Проверка пар — см. ответ; для каждой пары способ найден, значит, Сосновка находится между Озёрском, Каменкой и Борками относительно $\\alpha^1, \\alpha^2$ (с. 82).")
    return card(cid, 5, "E", "vary", "def", "nat", "text", "с. 82, гл. 2, § 20", ["между", "диагностика"], U, A, R)


ROW_NAMES = dict(a="«Лесная»", b="«Озёрная»", c="«Садовая»", d="«Речная»", e="«Парковая»", f="«Заводская»")
ROW_INTRO = ("Станции одной линии метро обозначены буквами: " + ", ".join(f"${k}$ — станция {v}" for k, v in ROW_NAMES.items())
             + "; $\\alpha$ — порядок по расстоянию от депо вдоль линии («дальше от депо» записывается как $> \\alpha$). Станции образуют ряд $A$ относительно $\\alpha$; "
             "для $> \\alpha$ принимаются аксиомы, аналогичные C1–C7 (с. 82), в частности C4: $(a > \\alpha b) \\wedge (b > \\alpha c) \\vdash (a > \\alpha c)$. "
             "По с. 85 элементы ряда соседние, если и только если ни один элемент $A$ не находится между ними; по § 20 (с. 82) $u$ находится между $v$ и $w$, "
             "если и только если $(u > \\alpha v) \\wedge (w > \\alpha u)$ или $(v > \\alpha u) \\wedge (u > \\alpha w)$. ")


def rname(x):
    return "станция " + ROW_NAMES[x]


def row_data(r, extra=1):
    order = r.sample(list("abcdef"), 6)
    facts = [(order[i + 1], order[i]) for i in range(5)]
    for _ in range(extra):
        i, j = sorted(r.sample(range(6), 2))
        if j - i > 1 and (order[j], order[i]) not in facts:
            facts.append((order[j], order[i]))
    r.shuffle(facts)
    # проверка: порядок восстанавливается однозначно по замыканию C4
    clo = set(facts)
    changed = True
    while changed:
        changed = False
        for (x, y) in list(clo):
            for (y2, z) in list(clo):
                if y == y2 and (x, z) not in clo:
                    clo.add((x, z)); changed = True
    assert all(((order[j], order[i]) in clo) for i in range(6) for j in range(i + 1, 6))
    return order, facts


def row_fact_txt(facts):
    return "; ".join(f"«{rname(x)[0].upper() + rname(x)[1:]} дальше от депо, чем {rname(y)}»" for x, y in facts)


def sec23_card(cid, seed):
    r = random.Random(seed)
    order, facts = row_data(r)
    pos = {x: i for i, x in enumerate(order)}
    pairs = []
    adj = [(order[i], order[i + 1]) for i in range(5)]
    p1 = r.choice(adj); pairs.append(p1[::-1] if r.random() < 0.5 else p1)
    while len(pairs) < 3:
        x, y = r.sample(order, 2)
        if (x, y) not in pairs and (y, x) not in pairs and abs(pos[x] - pos[y]) > 1:
            pairs.append((x, y))
    r.shuffle(pairs)
    def verdict(x, y):
        i, j = sorted((pos[x], pos[y]))
        if j - i == 1:
            return True, f"между {rname(x)} и {rname(y)} в цепочке нет станций: любая другая либо ближе к депо, чем обе, либо дальше обеих (п. 1), ни одно условие § 20 не выполнено — соседние"
        m = order[i + 1]
        return False, (f"{rname(m)} находится между ними: ${m} > \\alpha {order[i]}$ и ${order[j]} > \\alpha {m}$ (п. 1; § 20) — не соседние")
    U = (ROW_INTRO + "Известно: " + row_fact_txt(facts) + " (других сведений о порядке нет). Формализуйте сведения, установите порядок станций от депо и для каждой пары "
         "выясните, соседние ли это элементы ряда; ответ обоснуйте выводом по C4 и определениям.\n\n"
         + "\n".join(f"{'абв'[k]}) {rname(x)} и {rname(y)}" for k, (x, y) in enumerate(pairs)))
    A = (f"Порядок от депо: {', '.join(ROW_NAMES[x] for x in order)}; " + "; ".join(f"{'абв'[k]}) {'соседние' if verdict(x, y)[0] else 'не соседние'}" for k, (x, y) in enumerate(pairs)) + ".")
    chain = ", ".join(f"${order[i + 1]} > \\alpha {order[i]}$" for i in range(5))
    R = ("Формализация: " + "; ".join(f"${x} > \\alpha {y}$" for x, y in facts) + ".\n\n"
         f"1. Среди данных есть цепочка {chain}. По C4, применённой несколько раз, каждая станция дальше в цепочке превосходит по порядку каждую ближе к её началу: "
         f"порядок от депо — {', '.join(f'${x}$' for x in order)}.\n"
         + "\n".join(f"{'абв'[k]}) {verdict(x, y)[1]}." for k, (x, y) in enumerate(pairs)) + "\n\nИсточник: с. 82, 85, гл. 2, § 20, 23.")
    return card(cid, 5, "F", "vary", "over" if len(facts) > 5 else "def", "nat", "short", "с. 82, 85, гл. 2, § 20, 23", ["ряды", "порядок", "формализация"], U, A, R)


def sec23_err(cid, seed):
    r = random.Random(seed)
    order, facts = row_data(r)
    pos = {x: i for i, x in enumerate(order)}
    claims = []
    allp = [(x, y) for x, y in itertools.combinations("abcdef", 2)]
    r.shuffle(allp)
    adj = [p for p in allp if abs(pos[p[0]] - pos[p[1]]) == 1][:2]
    non = [p for p in allp if abs(pos[p[0]] - pos[p[1]]) > 1][:3]
    pl = adj + non
    r.shuffle(pl)
    wrong = set(r.sample(range(5), 2))
    items, sol = [], []
    for k, (x, y) in enumerate(pl):
        truth = abs(pos[x] - pos[y]) == 1
        said = truth if k not in wrong else not truth
        items.append(f"{'абвгд'[k]}) {rname(x)} и {rname(y)} — {'соседние' if said else 'не соседние'}")
        i, j = sorted((pos[x], pos[y]))
        why = ("между ними нет станции ряда" if truth else f"между ними находится {rname(order[i + 1])}: ${order[i + 1]} > \\alpha {order[i]}$, ${order[j]} > \\alpha {order[i + 1]}$")
        sol.append(f"{'абвгд'[k]}) {why} — {'соседние' if truth else 'не соседние'}; утверждение {'ошибочно' if k in wrong else 'верно'}.")
    bad = sorted(wrong)
    U = (ROW_INTRO + "Известно: " + row_fact_txt(facts) + ". Студент утверждает:\n\n" + "\n".join(items)
         + "\n\nРовно два утверждения ошибочны. Найдите их, назовите нарушенное определение и исправьте.")
    def fix(k):
        x, y = pl[k]
        truth = abs(pos[x] - pos[y]) == 1
        return f"{'абвгд'[k]}) на самом деле {'соседние' if truth else 'не соседние'}"
    A = "; ".join(fix(k) for k in bad) + " — нарушено определение соседних элементов ряда (с. 85) вместе с определением «между» (§ 20, с. 82). Остальные пункты верны (см. решение)."
    R = (f"Порядок от депо по C4: {', '.join(f'${x}$' for x in order)} (цепочка " + ", ".join(f"${order[i + 1]} > \\alpha {order[i]}$" for i in range(5)) + ").\n"
         + "\n".join(sol) + "\n\nИсточник: с. 82, 85, гл. 2, § 20, 23.")
    return card(cid, 5, "E", "vary", "def", "nat", "text", "с. 82, 85, гл. 2, § 20, 23", ["ряды", "порядок", "диагностика"], U, A, R)


SHELF = dict(a="энциклопедия", b="атлас", c="задачник", d="справочник", e="альбом", f="сборник")
SHELF_INTRO = ("Книги стоят на полке слева направо и образуют ряд $A$ относительно $\\alpha$ — порядка слева направо («правее» записывается как $> \\alpha$). "
               "Словарь: " + ", ".join(f"${k}$ — {v}" for k, v in SHELF.items()) + ". Для $> \\alpha$ принимаются аксиомы, аналогичные C1–C7 (с. 82), в частности "
               "C4: $(a > \\alpha b) \\wedge (b > \\alpha c) \\vdash (a > \\alpha c)$. По § 20 (с. 82) $u$ находится между $v$ и $w$, если и только если "
               "$(u > \\alpha v) \\wedge (w > \\alpha u)$ или $(v > \\alpha u) \\wedge (u > \\alpha w)$. По § 24 (с. 86–87) $u \\parallel \\alpha v$ («соприкасаются»), "
               "если и только если $(u > \\alpha v) \\vee (v > \\alpha u)$ и никакой индивид подразумеваемого класса невозможно поместить между ними; подразумеваемый класс — книги, "
               "в том числе книги этого ряда. ")


def sec24_card(cid, seed):
    r = random.Random(seed)
    order, facts = row_data(r, 0)
    pos = {x: i for i, x in enumerate(order)}
    gaps = set(r.sample(range(5), 2))
    gaptxt = ", ".join(f"между книгами «{SHELF[order[g]]}» и «{SHELF[order[g + 1]]}»" for g in sorted(gaps))
    pairs = []
    adj = [(order[i], order[i + 1]) for i in range(5)]
    pairs.append(next(adj[g] for g in sorted(gaps)))
    pairs.append(next(adj[i] for i in range(5) if i not in gaps))
    while len(pairs) < 4:
        x, y = r.sample(order, 2)
        if (x, y) not in pairs and (y, x) not in pairs and abs(pos[x] - pos[y]) > 1:
            pairs.append((x, y))
    r.shuffle(pairs)
    def verdict(x, y):
        i, j = sorted((pos[x], pos[y]))
        if j - i > 1:
            return False, f"между ними стоит книга «{SHELF[order[i + 1]]}» — индивид подразумеваемого класса (${order[i + 1]} > \\alpha {order[i]}$, ${order[j]} > \\alpha {order[i + 1]}$), значит, поместить индивид между ними можно — не соприкасаются"
        if i in gaps:
            return False, "соседние, но по условию между ними можно поставить книгу — не соприкасаются"
        return True, "соседние, и между соседними книгами поставить книгу можно только в указанных местах, а здесь нельзя — соприкасаются"
    def fact_txt(x, y):
        return f"«{SHELF[x][0].upper() + SHELF[x][1:]} стоит правее, чем {SHELF[y]}»"
    U = (SHELF_INTRO + "Известно: " + "; ".join(fact_txt(x, y) for x, y in facts) + ". Из пар соседних книг поставить ещё одну книгу можно лишь " + gaptxt
         + "; между остальными соседними — нельзя. Формализуйте сведения, установите порядок книг и для каждой пары определите по § 24, соприкасаются ли книги, с обоснованием.\n\n"
         + "\n".join(f"{'абвг'[k]}) {SHELF[x]} и {SHELF[y]}" for k, (x, y) in enumerate(pairs)))
    A = (f"Порядок слева направо: {', '.join(SHELF[x] for x in order)}; " + "; ".join(f"{'абвг'[k]}) {'соприкасаются' if verdict(x, y)[0] else 'не соприкасаются'}" for k, (x, y) in enumerate(pairs)) + ".")
    R = ("Формализация: " + "; ".join(f"${x} > \\alpha {y}$" for x, y in facts) + ".\n\n"
         f"1. Данные образуют цепочку; по C4 порядок слева направо — {', '.join(f'${x}$' for x in order)}.\n"
         + "\n".join(f"{'абвг'[k]}) {verdict(x, y)[1]}." for k, (x, y) in enumerate(pairs))
         + "\n\nПо с. 86 вопрос, можно ли поместить индивид между двумя, решается практически (договорённость, возможности); здесь он решён условием. Источник: с. 82, 86–87, гл. 2, § 24.")
    return card(cid, 5, "F", "vary", "def", "nat", "short", "с. 82, 86–87, гл. 2, § 24", ["соприкосновение", "формализация"], U, A, R)


def sec20_24():
    out = []
    for k, cid in enumerate(["18.20-005", "18.20-007", "18.20-009", "18.20-011"]):
        out.append(sec20_card(cid, k, fresh=True))
    out.append(sec20_err("18.20-006", 1))
    out.append(sec20_err("18.20-008", 2))
    out.append(sec20_err("18.20-010", 3))
    for k, cid in enumerate(["18.23-014", "18.23-016", "18.23-018", "18.23-020"]):
        out.append(sec23_card(cid, 2300 + k))
    for k, cid in enumerate(["18.23-015", "18.23-017", "18.23-019", "18.23-021"]):
        out.append(sec23_err(cid, 2310 + k))
    for k, cid in enumerate(["18.24-008", "18.24-009", "18.24-010", "18.24-011", "18.24-012"]):
        out.append(sec24_card(cid, 2400 + k))
    return out


# ---------------------------------------------------------------- § 31, § 37: снижение доли E (те же данные — задание на установление)
def sec31_noerr(cid):
    o = O[cid]
    U, R = o["Условие"], o["Решение"]
    head, rest = U.split("Студент утверждает:")
    items = re.findall(r"^([а-д])\) элементы скопления (.*?) (?:не )?образуют структуру относительно (\$B = .*?\$)\s*$", rest, re.M)
    assert len(items) == 5, cid
    verdict = dict(re.findall(r"^([а-д])\) .*— (образуют|не образуют)\.\s*$", R, re.M))
    assert len(verdict) == 5, cid
    Un = (head.strip() + " Для каждого скопления установите по определению с. 97, образуют ли его элементы структуру относительно указанного класса способов $B$; "
          "для каждого элемента назовите партнёра и способ (с выводом по аналогу C4, если отношение не дано прямо) или докажите, что партнёра нет.\n\n"
          + "\n".join(f"{k}) скопление {sc}; {b}" for k, sc, b in items))
    An = "; ".join(f"{k}) {verdict[k]}" for k, _, _ in items) + "."
    Rn = R
    return card(cid, 5, "C", "vary", "def", "sym", "short", o["fm"]["source"], ["структура"], Un, An, Rn)


ORD_PAIRS = [("позже этого", "раньше этого"), ("через час после этого", "за час до этого"), ("правее этого", "левее этого"),
             ("выше этого", "ниже этого"), ("дальше от входа, чем это", "ближе к входу, чем это"), ("севернее этого", "южнее этого")]
ORD_EVENTS = [("сверкнула молния", "загремел гром"), ("включили насос", "вода поднялась в бак"), ("пришла телеграмма", "уехал гость"),
              ("прозвенел звонок", "начался урок"), ("открыли шлюз", "уровень воды упал"), ("остыл металл", "раскололась форма")]
ORD_PLACES = [("висит картина", "висят часы"), ("стоит словарь", "стоит атлас"), ("стоит почта", "стоит школа"), ("лежит ковёр", "стоит кресло")]
K_HEAD = ("Буквы $x, y$ — высказывания; $R^1$, $R^2$ — отношения порядка. По с. 106 для упорядоченных конъюнкций и дизъюнкций не принимаются правила коммутации "
          "$x \\wedge (Rx)y \\vdash y \\wedge (Ry)x$, $x \\vee (Rx)y \\vdash y \\vee (Ry)x$; верны лишь (K1) $(x \\wedge (R^1x)y) \\wedge ((aR^1b) \\to (bR^2a)) \\vdash (y \\wedge (R^2y)x)$ "
          "и (K2) $(x \\vee (R^1x)y) \\wedge ((aR^1b) \\to (bR^2a)) \\vdash (y \\vee (R^2y)x)$. Для условных высказываний (с. 106): "
          "(У2) $(x \\to (R^1x)y) \\wedge ((aR^1b) \\to (bR^2a)) \\vdash ({\\sim}y \\to (R^2{\\sim}y){\\sim}x)$.")


def sec37_build(cid, seed):
    r = random.Random(seed)
    items, ans, sol = [], [], []
    forms = ["&", "|", ">", r.choice("&|>")]
    r.shuffle(forms)
    used = set()
    for k, f in enumerate(forms):
        while True:
            if f == "&" and r.random() < 0.5:
                (x, y), (r1, r2) = r.choice(ORD_PLACES), r.choice(ORD_PAIRS[2:])
            else:
                (x, y), (r1, r2) = r.choice(ORD_EVENTS), r.choice(ORD_PAIRS[:2])
            if (x, f) not in used:
                used.add((x, f)); break
        if f == "&":
            s, t, rule, sym = f"«{x}, и {r1} — {y}»", f"«{y}, и {r2} — {x}»", "K1", "$x \\wedge (R^1x)y$ ⟶ $y \\wedge (R^2y)x$"
        elif f == "|":
            s, t, rule, sym = f"«{x}, или {r1} — {y}»", f"«{y}, или {r2} — {x}»", "K2", "$x \\vee (R^1x)y$ ⟶ $y \\vee (R^2y)x$"
        else:
            s, t, rule, sym = (f"«если {x}, то {r1} — {y}»", f"«если неверно, что {y}, то {r2} — неверно, что {x}»", "У2",
                               "$x \\to (R^1x)y$ ⟶ ${\\sim}y \\to (R^2{\\sim}y){\\sim}x$")
        items.append(f"{'абвг'[k]}) {s}")
        ans.append(f"{'абвг'[k]}) {t} — по {rule}")
        sol.append(f"{'абвг'[k]}) $x$ — «{x}», $y$ — «{y}», $R^1$ — «{r1}»; {sym} по {rule} (с. 106) при дополнительной посылке $(aR^1b) \\to (bR^2a)$, "
                   f"где $R^2$ — «{r2}» (если $a$ находится к $b$ в отношении «{r1}», то $b$ к $a$ — в отношении «{r2}»); простая перестановка без замены $R^1$ на $R^2$ была бы непринимаемой коммутацией.")
    U = (K_HEAD + " Для каждого высказывания постройте высказывание, в котором на первом месте стоит второй член, назовите применённое правило и выпишите нужную дополнительную посылку "
         "$(aR^1b) \\to (bR^2a)$, указав $R^1$ и $R^2$.\n\n" + "\n".join(items))
    A = "; ".join(ans) + "; в каждом случае нужна посылка $(aR^1b) \\to (bR^2a)$ для указанной пары отношений."
    R = "\n".join(sol) + "\n\nИсточник: с. 106, гл. 2, § 37–38."
    return card(cid, 5, "D", "vary", "def", "nat", "build", "с. 106, гл. 2, § 37–38", ["упорядоченные конъюнкции", "построение"], U, A, R)


def sec31_37():
    return [sec31_noerr("18.31-048"), sec31_noerr("18.31-049"), sec37_build("18.37-028", 3728), sec37_build("18.37-029", 3729),
            sec24_card("18.24-016", 2405), sec24_card("18.24-017", 2406)]



# ---------------------------------------------------------------- дополнительные переводы на обычный язык (дополнение выводов, § 35, § 31)
POW_CTX = dict(key="мощность", names=dict(A="класс первокурсников", B="класс второкурсников", C="класс аспирантов", D="класс лаборантов",
                                          E="класс преподавателей", F="класс библиотекарей"),
               intro="Сравниваются по мощности (числу элементов, с. 63) классы сотрудников и учащихся одного факультета.",
               p="признак «мощность» (число элементов класса, с. 63); предикаты $> m$, $= m$ понимаются как сравнение по этому признаку (с. 79, 104)",
               ph={">": "{u} превосходит по мощности {v}", "=": "{u} и {v} равномощны", "<": "{u} менее многочислен, чем {v}",
                   "n": "{u} не превосходит по мощности {v}"},
               words="«превосходит по мощности» — $> m$, «равномощны» — $= m$, «менее многочислен» — $< m$, «не превосходит по мощности» — $\\urcorner > m$",
               unit=("число элементов", "человек", 10, 5))


def conv_complete(cid, ctx):
    o = O[cid]
    U, A, R = o["Условие"], o["Ответ"], o["Решение"]
    mark = "\\alpha " if "\\alpha" in U else "p"
    head = split_header(U)
    if o["fm"]["section"] == 19:
        head = ("По с. 82 отношения $= \\alpha$ и $< \\alpha$ определяются через $> \\alpha$ так же, как отношения сравнения, "
                "а для $> \\alpha$ принимаются аксиомы, аналогичные C1–C7 (вместо признака $p$ — способ упорядочивания $\\alpha$). " + head)
    goal = atom(re.search(r"В выводе формулы (\$[^$]+\$)", U).group(1))
    shown = U[U.index("\n1. "):].strip()
    full = parse_lines(R)
    prem = [atom(f) for n, f, b in full if b == "посылка"]
    assert check_deriv(full, prem, goal) == [], cid
    lets = letters_of(prem + [goal])
    Un = (f"{ctx['intro']} {dict_line(ctx, lets, mark.strip())} {head} Из сообщений {quote_list(ctx, prem)} выведено высказывание «{phrase(ctx, goal)}». "
          "Ниже — символическая запись вывода, в которой пропущены формулы некоторых строк и основания некоторых шагов («…»). "
          "Проверьте формализацию посылок по словарю и восстановите пропуски; перестановка членов конъюнкции и удаление члена конъюнкции подразумеваются.\n\n" + shown)
    Rn = "Формализация по словарю: " + "; ".join(f"«{phrase(ctx, a)}» — {atex(a, mark)}" for a in prem + [goal]) + ".\n\n" + R
    return card(cid, o["fm"]["level"], "D", "complete", "def", "nat", "build", o["fm"]["source"], tags_of(o, "формализация"), Un, A, Rn)


HOUSES = dict(a="почта", b="школа", c="аптека", d="клуб", e="баня", f="мельница")


def conv31_nat(cid):
    o = O[cid]
    U, A, R = o["Условие"], o["Ответ"], o["Решение"]
    known = U.split("Известно:")[1].split("других отношений")[0]
    facts = re.findall(r"\$([a-f]) > \\alpha\^(\d) ([a-f])\$", known)
    items = re.findall(r"^([а-г])\) скопление (.*?), \$B = \\\{(.*?)\\\}\$\s*$", U, re.M)
    assert facts and len(items) == 4, cid
    # независимый пересчёт: замыкание по аналогу C4 для каждого способа и определение с. 97
    rel = {j: {(u, v) for u, jj, v in facts if jj == j} for j in "12"}
    for j in "12":
        ch = True
        while ch:
            ch = False
            for (x, y) in list(rel[j]):
                for (y2, z) in list(rel[j]):
                    if y == y2 and (x, z) not in rel[j]:
                        rel[j].add((x, z)); ch = True
    ans = dict(re.findall(r"([а-г])\) (образуют|не образуют)", A))
    for k, sc, B in items:
        els = re.findall(r"[a-f]", sc)
        ways = re.findall(r"\\alpha\^(\d)", B)
        ok = all(any((u, v) in rel[j] or (v, u) in rel[j] for v in els if v != u for j in ways) for u in els)
        assert ("образуют" if ok else "не образуют") == ans[k], (cid, k)
    ph = {"1": "{u} стоит восточнее, чем {v}", "2": "{u} стоит севернее, чем {v}"}
    cap = lambda t: t[0].upper() + t[1:]
    sent = "; ".join("«" + cap(ph[j].format(u=HOUSES[u], v=HOUSES[v])) + "»" for u, j, v in facts)
    Un = ("Здания посёлка обозначены буквами: " + ", ".join(f"${k}$ — {v}" for k, v in HOUSES.items())
          + ". Способы установления порядка: $\\alpha^1$ — с запада на восток («восточнее» — $> \\alpha^1$), $\\alpha^2$ — с юга на север («севернее» — $> \\alpha^2$). "
          "По с. 97 элементы скопления $A$ образуют структуру относительно класса способов $B$, если и только если для любого элемента $u$ скопления найдётся другой элемент $v$ "
          "и способ $\\alpha$ из $B$, что $u > \\alpha v$ или $v > \\alpha u$. Для каждого способа принимается аналог аксиомы C4 (с. 82): $(u > \\alpha v) \\wedge (v > \\alpha w) \\vdash (u > \\alpha w)$. "
          f"Известно: {sent}; других сведений о взаимном расположении нет, кроме выводимых по аналогу C4. Формализуйте сведения и для каждого скопления зданий и класса способов $B$ "
          "установите, образуют ли его элементы структуру относительно $B$, и обоснуйте.\n\n"
          + "\n".join(f"{k}) {', '.join(HOUSES[x] for x in re.findall(r'[a-f]', sc))}; $B = \\{{{B}\\}}$" for k, sc, B in items))
    Rn = "Формализация: " + "; ".join(f"«{cap(ph[j].format(u=HOUSES[u], v=HOUSES[v]))}» — ${u} > \\alpha^{j} {v}$" for u, j, v in facts) + ".\n\n" + R
    return card(cid, o["fm"]["level"], "F", "vary", o["fm"].get("condition", "def"), "nat", "short", o["fm"]["source"], ["структура", "формализация"], Un, A, Rn)


def sec_more():
    out = []
    for k, cid in enumerate(["18.18-028", "18.18-030", "18.18-032", "18.18-034"]):
        out.append(conv_complete(cid, CMP_CTX[k % 3]))
    for k, cid in enumerate(["18.19-025", "18.19-027", "18.19-029"]):
        out.append(conv_complete(cid, ORD_CTX[k % 2]))
    for cid in ["18.35-021", "18.35-028"]:
        out.append(conv_cmp(cid, POW_CTX, "iso"))
    for cid in ["18.31-027", "18.31-029", "18.31-031", "18.31-033", "18.31-035", "18.31-037"]:
        out.append(conv31_nat(cid))
    for k, cid in enumerate(["18.23-022", "18.23-024", "18.23-026", "18.23-028"]):
        out.append(sec23_card(cid, 2320 + k))
    for k, cid in enumerate(["18.20-013", "18.20-015", "18.20-017"]):
        out.append(sec20_card(cid, 20 + k, fresh=True))
    return out


SECTIONS = [sec18_19, sec06, sec05_16, sec20_24, sec31_37, sec_more]


def main():
    allc = []
    for f in SECTIONS:
        allc += f()
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text("\n=====\n\n".join(allc), encoding="utf-8")
    print(f"{OUT}: {len(allc)} карточек")


if __name__ == "__main__":
    main()
