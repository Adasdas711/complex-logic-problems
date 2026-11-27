#!/usr/bin/env python3
"""Трудные задачи раздела 18 («Логическая физика», 1972, гл. 2): длинные выводы, дополнение длинных выводов,
диагностика с двумя ошибками, «выведите или докажите, что нельзя», длинные серии с обоснованием значениями.

Все выводы строит и проверяет машина lf_engine; значения считаются программой по правилам книги.
Пишет drafts/18-hard.md (generated: true); перенос — scripts/split_cards.py.

Запуск: python3 src/scripts/gen/g18_hard.py
"""
import itertools
import random
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import lf_engine as E  # noqa: E402
from g18 import tx, tm, items, ans_items  # noqa: E402

rnd = random.Random(19721127)
USED = set()
OUT = []


def card(sec, lvl, typ, step, cond, form, ans, src, tags, U, A, R, case=None):
    key = U.strip()
    if key in USED:
        raise ValueError("повтор условия")
    USED.add(key)
    head = ["---", "chapter: 18", f"section: {sec}", f"level: {lvl}", f"type: {typ}", f"step: {step}",
            f"condition: {cond}", f"form: {form}", f"answer: {ans}", f'source: "{src}"']
    if case:
        head.append(f"case: {case}")
    head += ["generated: true", "tags: [" + ", ".join(tags) + "]", "---"]
    if not re.search(r"[сС]\. \d|§", R):
        R = R.rstrip() + f"\n\nИсточник: {src}."
    its = re.findall(r"^([а-з])\) ", U, re.M)
    a_its = set(re.findall(r"(?:^|[;\s(])([а-з])\)", A))
    if its and a_its and len(a_its) != len(its) and "см." not in A:
        A = A.rstrip().rstrip(".") + ". Остальные пункты верны (см. решение)."
    OUT.append("\n".join(head) + f"\n\n## Условие\n\n{U.strip()}\n\n## Ответ\n\n{A.strip()}\n\n## Решение\n\n{R.strip()}\n")


def fresh(make, tries=200):
    """Повторять make(), пока условие не новое."""
    for _ in range(tries):
        r = make()
        if r and r[0].strip() not in USED:
            return r
    return None


# ====================================================================== сравнение, порядок, мощность

def cmp_rules(extra=False):
    R = [
        ("C2", 1, lambda p: ("n>", p[0][2], p[0][1]) if p[0][0] == ">" else None),
        ("C4", 2, lambda p: (">", p[0][1], p[1][2]) if p[0][0] == ">" and p[1][0] == ">" and p[0][2] == p[1][1] and p[0][1] != p[1][2] else None),
        ("C5", 2, lambda p: (">", p[0][1], p[1][2]) if p[0][0] == ">" and p[1][0] == "=" and p[0][2] == p[1][1] and p[0][1] != p[1][2] else None),
        ("C6", 2, lambda p: (">", p[0][1], p[1][2]) if p[0][0] == "=" and p[1][0] == ">" and p[0][2] == p[1][1] and p[0][1] != p[1][2] else None),
        ("C7", 2, lambda p: ("n>", p[0][1], p[1][2]) if p[0][0] == "n>" and p[1][0] == "n>" and p[0][2] == p[1][1] and p[0][1] != p[1][2] else None),
        ("D=", 2, lambda p: ("=", p[0][1], p[0][2]) if p[0][0] == "n>" and p[1] == ("n>", p[0][2], p[0][1]) and p[0][1] != p[0][2] else None),
        ("D=1", 1, lambda p: ("n>", p[0][1], p[0][2]) if p[0][0] == "=" else None),
        ("D=2", 1, lambda p: ("n>", p[0][2], p[0][1]) if p[0][0] == "=" else None),
        ("D<", 1, lambda p: (">", p[0][2], p[0][1]) if p[0][0] == "<" else None),
        ("D<'", 1, lambda p: ("<", p[0][2], p[0][1]) if p[0][0] == ">" else None),
    ]
    if extra:
        R += [
            ("1", 1, lambda p: ("n>", p[0][1], p[0][2]) if p[0][0] == "sub" else None),
            ("3", 1, lambda p: ("n>", p[0][1], p[0][2]) if p[0][0] == "cor" else None),
            ("9", 1, lambda p: ("=", p[0][1], p[0][2]) if p[0][0] == "bij" else None),
            ("D<≡>1", 1, lambda p: ("cor", p[0][1], p[0][2]) if p[0][0] == "bij" else None),
            ("D<≡>2", 1, lambda p: ("cor", p[0][2], p[0][1]) if p[0][0] == "bij" else None),
            ("2", 2, lambda p: (">", p[0][1], p[1][1]) if p[0][0] == "ne" and p[1][0] == "em" else None),
        ]
    return R


class Cmp:
    """Обозначения: kind = 'p' (сравнение, § 18), 'a' (порядок, § 19), 'm' (мощность, § 35)."""

    def __init__(self, kind):
        self.kind = kind
        self.s = {"p": "p", "a": "\\alpha ", "m": "m"}[kind]

    def f(self, x):
        k = x[0]
        a, b = x[1], x[2] if len(x) > 2 else None
        s = self.s
        if k == ">":
            return f"{a} > {s}{b}"
        if k == "n>":
            return f"{a} \\urcorner > {s}{b}"
        if k == "=":
            return f"{a} = {s}{b}"
        if k == "<":
            return f"{a} < {s}{b}"
        if k == "sub":
            return f"{a} \\subset {b}"
        if k == "cor":
            return f"{a} \\langle\\equiv {b}"
        if k == "bij":
            return f"{a} \\langle\\equiv\\rangle {b}"
        if k == "ne":
            return f"(\\exists d)(d \\in {a})"
        if k == "em":
            return f"(\\forall d){{\\sim}}(d \\in {a})"
        raise ValueError(k)

    def why(self, name, refs):
        r = ", ".join(map(str, refs))
        names = {
            "C2": "C2", "C4": "C4", "C5": "C5", "C6": "C6", "C7": "C7",
            "D=": "определение $=$", "D=1": "определение $=$", "D=2": "определение $=$",
            "D<": "определение $<$", "D<'": "определение $<$",
            "1": "утверждение 1", "3": "утверждение 3", "9": "следствие 9", "2": "утверждение 2",
            "D<≡>1": "определение $\\langle\\equiv\\rangle$", "D<≡>2": "определение $\\langle\\equiv\\rangle$",
        }
        if name == "посылка":
            return "посылка"
        return f"{r}; {names[name]}" if refs else names[name]

    def show(self, lines, hide_f=(), hide_w=()):
        out = []
        for i, (f, name, refs) in enumerate(lines, 1):
            ff = "…" if i in hide_f else f"${self.f(f)}$"
            ww = "…" if i in hide_w else self.why(name, refs)
            out.append(f"{i}. {ff} [{ww}]")
        return "\n".join(out)


def ref_text(kind):
    """Справка в условии: определения и аксиомы (с. 79; для порядка — с. 82; для мощности — с. 104)."""
    s = {"p": "p", "a": "\\alpha ", "m": "m"}[kind]
    base = (f"Определения (с. 79): $(a = {s}b) \\equiv Df.(a \\urcorner > {s}b) \\wedge (b \\urcorner > {s}a)$; "
            f"$(a < {s}b) \\equiv Df.(b > {s}a)$. Аксиомы: C2 $(a > {s}b) \\vdash (b \\urcorner > {s}a)$; "
            f"C4 $(a > {s}b) \\wedge (b > {s}c) \\vdash (a > {s}c)$; C5 $(a > {s}b) \\wedge (b = {s}c) \\vdash (a > {s}c)$; "
            f"C6 $(a = {s}b) \\wedge (b > {s}c) \\vdash (a > {s}c)$; C7 $(a \\urcorner > {s}b) \\wedge (b \\urcorner > {s}c) \\vdash (a \\urcorner > {s}c)$.")
    if kind == "a":
        base = ("По с. 82 отношения $= \\alpha$ и $< \\alpha$ определяются через $> \\alpha$ так же, как отношения сравнения, "
                "а для $> \\alpha$ принимаются аксиомы, аналогичные C1–C7 (вместо признака $p$ — способ упорядочивания $\\alpha$). "
                + base.replace("Определения (с. 79)", "Определения"))
    if kind == "m":
        base = ("Предикаты сравнения классов по мощности $> m$, $= m$ понимаются как сравнение по признаку «мощность» (с. 79, 104). "
                + base + " Утверждения с. 104: 1. $\\vdash (A \\subset B) \\to (A \\urcorner > mB)$; "
                "2. $\\vdash (\\exists d)(d \\in A) \\wedge (\\forall d){\\sim}(d \\in B) \\to (A > mB)$; "
                "3. $\\vdash (A \\langle\\equiv B) \\to (A \\urcorner > mB)$; 9. $\\vdash (A \\langle\\equiv\\rangle B) \\to (A = mB)$; "
                "$(A \\langle\\equiv\\rangle B) \\equiv Df.(A \\langle\\equiv B) \\wedge (B \\langle\\equiv A)$.")
    return base


def num_model(prem, target, terms):
    """Числа для терминов: посылки верны, цель неверна (> — «больше», = — «равно», ¬> — «не больше»)."""
    def val(x, v):
        k = x[0]
        if k == ">":
            return v[x[1]] > v[x[2]]
        if k == "n>":
            return v[x[1]] <= v[x[2]]
        if k == "=":
            return v[x[1]] == v[x[2]]
        if k == "<":
            return v[x[1]] < v[x[2]]
        if k in ("sub", "cor"):
            return v[x[1]] <= v[x[2]]
        if k == "bij":
            return v[x[1]] == v[x[2]]
        if k == "ne":
            return v[x[1]] >= 1
        if k == "em":
            return v[x[1]] == 0
        return None
    for vals in itertools.product(range(len(terms)), repeat=len(terms)):
        v = dict(zip(terms, vals))
        if all(val(p, v) for p in prem) and (target is None or not val(target, v)):
            return v
    return None


def cmp_problem(kind, nterms=(5, 6), lo=8, hi=12, extra=False):
    terms = list("abcdef")[:rnd.choice(nterms)] if kind != "m" else list("ABCDEF")[:rnd.choice(nterms)]
    rules = cmp_rules(extra)
    for _ in range(400):
        prem = set()
        n = rnd.choice([4, 5])
        while len(prem) < n:
            a, b = rnd.sample(terms, 2)
            kinds = [">", ">", "<", "=", "n>"] + (["sub", "cor", "bij"] if extra else [])
            k = rnd.choice(kinds)
            prem.add((k, a, b))
        if extra and rnd.random() < 0.4:
            a, b = rnd.sample(terms, 2)
            prem |= {("ne", a), ("em", b)}
        prem = sorted(prem)
        if num_model(prem, None, terms) is None:
            continue
        how = E.closure(prem, rules, limit=300)
        cands = []
        for f in how:
            if f[0] not in (">", "n>", "=", "<") or how[f][0] == "посылка":
                continue
            L = E.proof(f, how)
            used = {x[0] for x in L if x[1] == "посылка"}
            if lo <= len(L) <= hi and len(used) == len(prem):
                cands.append((f, L))
        if cands:
            f, L = rnd.choice(cands)
            assert not E.check(L, rules, prem)
            return terms, prem, f, L, rules, how
    return None


def cmp_header(kind, terms):
    T = ", ".join(terms)
    if kind == "p":
        return f"Буквы ${T}$ — термины; $p$ — признак (и способ сравнения)."
    if kind == "a":
        return f"Буквы ${T}$ — термины; $\\alpha$ — способ установления порядка."
    return f"Буквы ${T}$ — термины классов; $d$ — индивидная переменная."


SRC = {"p": ("с. 79, гл. 2, § 18", 18, ["сравнение", "вывод"]),
       "a": ("с. 79, 82, гл. 2, § 18–19", 19, ["порядок", "вывод"]),
       "m": ("с. 79, 104, гл. 2, § 35", 35, ["мощность", "вывод"])}


def cmp_long(kind, extra=False):
    def make():
        r = cmp_problem(kind, extra=extra)
        if not r:
            return None
        terms, prem, f, L, rules, how = r
        C = Cmp(kind)
        P = "; ".join(f"${C.f(p)}$" for p in prem)
        U = (f"{cmp_header(kind, terms)} {ref_text(kind)} Выведите ${C.f(f)}$ из посылок {P}. "
             "Укажите основание каждой строки (номера строк и аксиому или определение); перестановка членов конъюнкции "
             "и удаление члена конъюнкции подразумеваются.")
        A = f"Вывод в {len(L)} строк, последняя — ${C.f(f)}$ (см. решение)."
        R = C.show(L)
        return U, A, R, len(L)
    r = fresh(make)
    if r:
        src, sec, tags = SRC[kind]
        card(sec, 5, "D", "iso", "def", "sym", "proof", src, tags, r[0], r[1], r[2])


def cmp_complete(kind, extra=False):
    def make():
        r = cmp_problem(kind, extra=extra, lo=9, hi=12)
        if not r:
            return None
        terms, prem, f, L, rules, how = r
        C = Cmp(kind)
        inner = [i for i, x in enumerate(L, 1) if x[1] != "посылка" and i != len(L)]
        if len(inner) < 4:
            return None
        hide_f = set(rnd.sample(inner, 2))
        rest = [i for i, x in enumerate(L, 1) if x[1] != "посылка" and i not in hide_f]
        hide_w = set(rnd.sample(rest, min(3, len(rest))))
        U = (f"{cmp_header(kind, terms)} {ref_text(kind)} В выводе формулы ${C.f(f)}$ пропущены формулы некоторых строк "
             f"и основания некоторых шагов («…»). Восстановите их.\n\n{C.show(L, hide_f, hide_w)}")
        parts = []
        for i in sorted(hide_f | hide_w):
            x = L[i - 1]
            s = f"{i} — " + (f"${C.f(x[0])}$" if i in hide_f else "")
            if i in hide_w:
                s += (" " if i in hide_f else "") + f"[{C.why(x[1], x[2])}]"
            parts.append(s)
        A = "; ".join(parts)
        R = ("Формулу пропущенной строки восстанавливаем по строкам, которые на неё ссылаются, и по её собственному основанию. "
             "Полный вывод:\n\n" + C.show(L))
        return U, A, R
    r = fresh(make)
    if r:
        src, sec, tags = SRC[kind]
        card(sec, 5, "D", "complete", "def", "sym", "build", src, tags + ["дополнение"], *r)


def cmp_two_errors(kind, extra=False):
    rules = cmp_rules(extra)
    names = [n for n, _, _ in rules if n != "посылка"]

    def make():
        r = cmp_problem(kind, extra=extra, lo=9, hi=12)
        if not r:
            return None
        terms, prem, f, L, rules_, how = r
        C = Cmp(kind)
        inner = [i for i, x in enumerate(L, 1) if x[1] != "посылка"]
        if len(inner) < 4:
            return None
        bad = sorted(rnd.sample(inner, 2))
        L2 = list(L)
        for i in bad:
            fx, name, refs = L2[i - 1]
            # неверное основание: та же формула, другое правило (той же арности) или другие строки
            alts = []
            for n2, ar, _ in rules:
                if n2 != name and ar == len(refs) and C.why(n2, refs) != C.why(name, refs):
                    alts.append((fx, n2, refs))
            if len(refs) == 2:
                alts.append((fx, name, (refs[1], refs[0])))
            if len(refs) >= 1:
                for j in range(1, i):
                    if j not in refs:
                        alts.append((fx, name, tuple(sorted(set(refs[:-1] + (j,))))) if len(refs) == 2 else (fx, name, (j,)))
            rnd.shuffle(alts)
            for a in alts:
                L3 = list(L2)
                L3[i - 1] = a
                if i in E.check(L3, rules, prem) and C.why(a[1], a[2]) != C.why(name, refs):
                    L2 = L3
                    break
            else:
                return None
        if sorted(E.check(L2, rules, prem)) != bad:
            return None
        U = (f"{cmp_header(kind, terms)} {ref_text(kind)} В выводе формулы ${C.f(f)}$ из посылок ровно два основания указаны "
             f"неверно. Найдите обе ошибки, назовите, какое правило нарушено, и исправьте основания.\n\n{C.show(L2)}")
        A = "; ".join(f"строка {i}: указано [{C.why(L2[i-1][1], L2[i-1][2])}], верно [{C.why(L[i-1][1], L[i-1][2])}]" for i in bad)
        expl = []
        for i in bad:
            fx, n2, refs2 = L2[i - 1]
            got = dict((n, fn) for n, _, fn in rules)[n2]
            prem_f = tuple(L2[r - 1][0] for r in refs2)
            res = got(prem_f) if len(prem_f) == dict((n, a) for n, a, _ in rules)[n2] else None
            if res is None:
                why = f"строки {', '.join(map(str, refs2))} не подходят под {C.why(n2, ()).strip()}"
            else:
                why = f"по [{C.why(n2, refs2)}] получилось бы ${C.f(res)}$, а не ${C.f(fx)}$"
            expl.append(f"Строка {i}: {why}. Верное основание — [{C.why(L[i-1][1], L[i-1][2])}].")
        R = "\n".join(expl) + "\n\nИсправленный вывод:\n\n" + C.show(L)
        return U, A, R
    r = fresh(make)
    if r:
        src, sec, tags = SRC[kind]
        card(sec, 6, "E", "vary", "def", "sym", "text", src, tags + ["диагностика"], *r)


def cmp_open(kind):
    """Выведите или докажите, что из C1–C7 и определений это не выводится."""
    def make():
        r = cmp_problem(kind, lo=6, hi=10)
        if not r:
            return None
        terms, prem, f, L, rules, how = r
        C = Cmp(kind)
        derivable = rnd.random() < 0.5
        if derivable:
            goal, model = f, None
        else:
            cands = []
            for a, b in itertools.permutations(terms, 2):
                for k in (">", "n>", "=", "<"):
                    g = (k, a, b)
                    if g not in how:
                        m = num_model(prem, g, terms)
                        if m:
                            cands.append((g, m))
            if not cands:
                return None
            goal, model = rnd.choice(cands)
        P = "; ".join(f"${C.f(p)}$" for p in prem)
        U = (f"{cmp_header(kind, terms)} {ref_text(kind)} Исследуйте, выводится ли ${C.f(goal)}$ из посылок {P} по аксиомам "
             "C2, C4–C7 и определениям; если выводится — постройте вывод, если нет — докажите, что вывода нет. "
             "(Для опровержения можно сопоставить терминам числа: $>$ — «больше», $=$ — «равно», $\\urcorner >$ — «не больше», "
             "$<$ — «меньше».)")
        if derivable:
            A = f"Выводится (вывод в {len(L)} строк — см. решение)."
            R = C.show(L)
        else:
            vs = ", ".join(f"${t} = {model[t]}$" for t in terms)
            A = f"Не выводится: при числах {vs} посылки верны, а ${C.f(goal)}$ неверно."
            R = (f"1. Сопоставим числа: {vs}; знак $>$ читаем как «больше», $=$ — «равно», $\\urcorner >$ — «не больше», $<$ — «меньше».\n"
                 "2. При таком чтении верна каждая аксиома C2, C4–C7 и оба определения: например, если $u > v$ и $v > w$, то $u > w$ "
                 "(C4); если $u > v$, то $v$ не больше $u$ (C2); $u = v$ тогда и только тогда, когда ни одно не больше другого. "
                 "Значит, всякая строка вывода из верных посылок тоже верна.\n"
                 f"3. Все посылки при этих числах верны: " + "; ".join(f"${C.f(p)}$" for p in prem) + ".\n"
                 f"4. Цель ${C.f(goal)}$ при этих числах неверна. Будь она выводима, она была бы верна (п. 2). Вывода нет.")
        return U, A, R, derivable
    r = fresh(make)
    if r:
        src, sec, tags = SRC[kind]
        card(sec, 6, "C", "open", "def", "sym", "proof", src, tags + ["открытый исход"], *r[:3])


# ====================================================================== main

def main():
    for fn, kind, n, ex in [(cmp_long, "p", 13, False), (cmp_complete, "p", 9, False), (cmp_two_errors, "p", 10, False),
                            (cmp_open, "p", 10, False), (cmp_long, "a", 11, False), (cmp_complete, "a", 7, False),
                            (cmp_two_errors, "a", 7, False), (cmp_open, "a", 7, False), (cmp_long, "m", 10, True),
                            (cmp_complete, "m", 8, True), (cmp_two_errors, "m", 8, True)]:
        for _ in range(n):
            fn(kind, ex) if fn is not cmp_open else fn(kind)
    import g18_hard2 as H2
    H2.run(card, fresh, rnd)
    import g18_hard3 as H3
    H3.run(card, fresh, rnd)
    sys.path.insert(0, str(HERE))
    from g18_open import process_card
    cards = [process_card(c) for c in OUT]
    path = ROOT / "drafts" / "18-hard.md"
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n=====\n\n".join(cards), encoding="utf-8")
    print(f"Карточек: {len(cards)} → {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
