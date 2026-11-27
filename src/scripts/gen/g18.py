#!/usr/bin/env python3
"""Серии раздела 18 («Логическая физика», 1972, гл. 2, с. 54–110), ступени 1–3.

§ 5 степени истинности, § 6 классы, § 9 существование, § 11 возможность, § 16 вероятность,
§ 18 сравнение (аксиомы C1–C7), § 23–26 ряды, § 31 структуры, § 35 соответствие классов.
Ответы вычисляются по определениям книги; условия проходят через g18_open (без «тестовой» формы). Пишет drafts/18-gen.md; все карточки generated: true.
"""
import itertools
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
rnd = random.Random(1972)
USED = set()


def tx(v):
    """Число для текста: 0,3."""
    return f"{v:.2f}".rstrip("0").rstrip(".").replace(".", ",") if v != int(v) else str(int(v))


def tm(v):
    """Число для формулы: 0{,}3."""
    return tx(v).replace(",", "{,}")


def card(sec, lvl, typ, step, cond, form, ans, src, tags, U, A, R, case=None):
    key = U.strip()
    if key in USED:
        raise ValueError(f"повтор условия: {key[:80]}")
    USED.add(key)
    head = ["---", "chapter: 18", f"section: {sec}", f"level: {lvl}", f"type: {typ}", f"step: {step}",
            f"condition: {cond}", f"form: {form}", f"answer: {ans}", f'source: "{src}"']
    if case:
        head.append(f"case: {case}")
    head += ["generated: true", "tags: [" + ", ".join(tags) + "]", "---"]
    return "\n".join(head) + f"\n\n## Условие\n\n{U.strip()}\n\n## Ответ\n\n{A.strip()}\n\n## Решение\n\n{R.strip()}\n"


def items(lst):
    return "\n".join(f"{'абвгдеж'[i]}) {s}" for i, s in enumerate(lst))


def ans_items(lst):
    return "; ".join(f"{'абвгдеж'[i]}) {s}" for i, s in enumerate(lst)) + "."


def steps(lst):
    return "\n".join(f"{i + 1}. {s}" for i, s in enumerate(lst))


VALS = [0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]
V5 = "Буквы $x, y, z, w$ — высказывания; $v(x)$ — степень истинности $x$ (с. 60)."


# ================================================================ § 5 степени истинности
def g05():
    out = []
    S = "с. 60, гл. 2, § 5"
    a, b = rnd.sample(VALS, 2)
    out.append(card(5, 2, "C", "iso", "def", "sym", "short", S, ["степени истинности"],
        f"{V5} Известно: $v(x) = {tm(a)}$, $v(y) = {tm(b)}$. Найдите $v(x \\wedge y)$.",
        f"$v(x \\wedge y) = {tm(min(a, b))}$.",
        f"По правилу $\\vdash v(x \\wedge y) = min(v(x), v(y))$ (с. 60): $v(x \\wedge y) = min({tm(a)}, {tm(b)}) = {tm(min(a, b))}$."))
    a, c = sorted(rnd.sample(VALS[:-1], 2))
    out.append(card(5, 2, "C", "vary", "def", "sym", "short", S, ["степени истинности", "обращение"],
        f"{V5} Известно: $v(x \\vee y) = {tm(c)}$, $v(x) = {tm(a)}$. Найдите $v(y)$.",
        f"$v(y) = {tm(c)}$.",
        f"По правилу $\\vdash v(x \\vee y) = max(v(x), v(y))$ (с. 60): $max({tm(a)}, v(y)) = {tm(c)}$. "
        f"Так как ${tm(a)} < {tm(c)}$, наибольшим может быть только $v(y)$, значит, $v(y) = {tm(c)}$."))
    a, b = rnd.sample(VALS, 2)
    out.append(card(5, 2, "E", "iso", "def", "sym", "short", S, ["степени истинности", "диагностика"],
        f"{V5} Известно: $v(x) = {tm(a)}$, $v(y) = {tm(b)}$. Студент: «$v(x \\wedge y) = {tm(max(a, b))}$: конъюнкция "
        f"истинна настолько, насколько истинен её самый надёжный член». Найдите ошибку.",
        f"Нарушено правило $\\vdash v(x \\wedge y) = min(v(x), v(y))$ (с. 60): $v(x \\wedge y) = {tm(min(a, b))}$; максимум берётся для дизъюнкции.",
        f"С. 60: «степень истинности конъюнкции равна наименьшей из степеней истинности её членов», а наибольшая — у дизъюнкции. "
        f"Студент применил к $\\wedge$ правило для $\\vee$. Верно: $min({tm(a)}, {tm(b)}) = {tm(min(a, b))}$."))
    # ступень 3
    for form_ in ("conjdis", "dis2"):
        if form_ == "conjdis":
            x, y, z = rnd.sample(VALS, 3)
            f1, r1 = "(x \\wedge y) \\vee z", max(min(x, y), z)
            f2, r2 = "x \\wedge (y \\vee z)", min(x, max(y, z))
            out.append(card(5, 3, "C", "iso", "def", "sym", "short", S, ["степени истинности"],
                f"{V5} Известно: $v(x) = {tm(x)}$, $v(y) = {tm(y)}$, $v(z) = {tm(z)}$. Найдите $v({f1})$ и $v({f2})$.",
                f"$v({f1}) = {tm(r1)}$; $v({f2}) = {tm(r2)}$.",
                steps([f"$v(x \\wedge y) = min({tm(x)}, {tm(y)}) = {tm(min(x, y))}$ [правило для $\\wedge$, с. 60].",
                       f"$v({f1}) = max({tm(min(x, y))}, {tm(z)}) = {tm(r1)}$ [правило для $\\vee$, с. 60].",
                       f"$v(y \\vee z) = max({tm(y)}, {tm(z)}) = {tm(max(y, z))}$ [правило для $\\vee$].",
                       f"$v({f2}) = min({tm(x)}, {tm(max(y, z))}) = {tm(r2)}$ [правило для $\\wedge$]."])))
        else:
            x, y, z, w = rnd.sample(VALS, 4)
            f1, r1 = "(x \\vee y) \\wedge (z \\vee w)", min(max(x, y), max(z, w))
            out.append(card(5, 3, "C", "iso", "def", "sym", "short", S, ["степени истинности"],
                f"{V5} Известно: $v(x) = {tm(x)}$, $v(y) = {tm(y)}$, $v(z) = {tm(z)}$, $v(w) = {tm(w)}$. Найдите $v({f1})$.",
                f"$v({f1}) = {tm(r1)}$.",
                steps([f"$v(x \\vee y) = max({tm(x)}, {tm(y)}) = {tm(max(x, y))}$ [с. 60].",
                       f"$v(z \\vee w) = max({tm(z)}, {tm(w)}) = {tm(max(z, w))}$ [с. 60].",
                       f"$v({f1}) = min({tm(max(x, y))}, {tm(max(z, w))}) = {tm(r1)}$ [правило для $\\wedge$, с. 60]."])))
    x, z = 0.6, 0.9
    out.append(card(5, 3, "E", "iso", "def", "sym", "short", S, ["степени истинности", "диагностика"],
        f"{V5} Из посылок $x$ и $z$ выведено $y$, т. е. $x \\wedge z \\vdash y$. Известно: $v(x) = {tm(x)}$, $v(z) = {tm(z)}$. "
        f"Студент: «заключение подкреплено сразу двумя посылками, поэтому $v(y) = 0{{,}}7$». Найдите ошибку.",
        "Нарушено правило $(x \\vdash y) \\wedge (v(x) = \\alpha) \\vdash (v(y) \\leqslant \\alpha)$ (с. 60): $v(y) \\leqslant 0{,}6$.",
        steps([f"Посылка вывода — конъюнкция $x \\wedge z$: $v(x \\wedge z) = min({tm(x)}, {tm(z)}) = {tm(x)}$ [с. 60].",
               "По правилу $(x \\vdash y) \\wedge (v(x) = \\alpha) \\vdash (v(y) \\leqslant \\alpha)$ (с. 60) степень истинности заключения не превышает степени истинности посылок: $v(y) \\leqslant 0{,}6$.",
               "Значение $0{,}7$ этому противоречит: число посылок степень истинности заключения не повышает."])))
    return out


# ================================================================ § 6 классы
U6 = "Индивидная переменная $a$ пробегает индивиды $e_1, …, e_6$; $A$, $B$ — термины классов."


def els(s):
    return ", ".join(f"$e_{i}$" for i in sorted(s)) if s else "ни один индивид"


def cls_text(name, s):
    return f"в {name} включаются {els(s)}" + (" и только они" if s else "")


def g06():
    out = []
    S = "с. 63, гл. 2, § 6"
    full = set(range(1, 7))
    # ступень 1: предикаты одного класса
    cases = [set(rnd.sample(sorted(full), 3)), set(), full, set(rnd.sample(sorted(full), 5))]
    for i, A in enumerate(cases):
        res = []
        res.append("непустой" if A else "пустой")
        res.append("универсальный" if A == full else "неуниверсальный")
        expl = []
        if A:
            e = min(A)
            expl.append(f"$e_{e} \\in A$, значит $(\\exists a)(a \\in A)$ — $A$ непустой; пустым он не является [с. 63].")
        else:
            expl.append("ни один индивид не включается в $A$: $(\\forall a){\\sim}(a \\in A)$ — $A$ пустой [с. 63].")
        if A == full:
            expl.append("каждый из $e_1, …, e_6$ включается в $A$: $(\\forall a)(a \\in A)$ — $A$ универсальный [с. 63].")
        else:
            e = min(full - A)
            expl.append(f"${{\\sim}}(e_{e} \\in A)$, значит $(\\exists a){{\\sim}}(a \\in A)$ — $A$ неуниверсальный [с. 63].")
        out.append(card(6, 1, "R", "iso", "def", "sym", "short", S, ["классы", "предикаты классов"],
            f"{U6} Известно: {cls_text('$A$', A)}. Какие из предикатов «пустой», «непустой», «универсальный», «неуниверсальный» (с. 63) "
            f"истинны для $A$?{'' if i else ''}",
            f"$A$ — {res[0]} и {res[1]}.",
            steps(expl)))
    A = {2}
    out.append(card(6, 1, "E", "iso", "def", "sym", "short", S, ["классы", "диагностика"],
        f"{U6} Известно: {cls_text('$A$', A)}. Студент: «$A$ неуниверсален, следовательно, $A$ пуст». Найдите ошибку.",
        "Неуниверсальный — $(\\exists a){\\sim}(a \\in A)$, пустой — $(\\forall a){\\sim}(a \\in A)$ (с. 63); $A$ неуниверсален, но непуст ($e_2 \\in A$).",
        "Определения с. 63: класс пуст, если $(\\forall a){\\sim}(a \\in A)$, неуниверсален, если $(\\exists a){\\sim}(a \\in A)$. "
        "Здесь ${\\sim}(e_1 \\in A)$, поэтому $A$ неуниверсален; но $e_2 \\in A$, т. е. $(\\exists a)(a \\in A)$ — $A$ непустой. "
        "Студент подменил отрицание универсальности отрицанием непустоты."))
    # ступень 2: включение в пересечение, объединение, двойное дополнение
    for k in range(6):
        while True:
            A = set(rnd.sample(sorted(full), rnd.choice([2, 3, 4])))
            B = set(rnd.sample(sorted(full), rnd.choice([2, 3, 4])))
            if A & B and A - B and B - A and full - (A | B):
                break
        e1 = rnd.choice(sorted(A & B)) if k % 2 == 0 else rnd.choice(sorted(A - B))
        e2 = rnd.choice(sorted(B - A)) if k % 3 else rnd.choice(sorted(full - (A | B)))
        e3 = rnd.choice(sorted(full))
        e4 = rnd.choice(sorted((full - (A | B)) - {e2}) or sorted(full - (A | B))) if k % 2 == 0 else rnd.choice(sorted(A & B))
        qs = [(f"$e_{e1} \\in A \\cap B$", e1 in A and e1 in B, "cap", e1),
              (f"$e_{e2} \\in A \\cup B$", e2 in A or e2 in B, "cup", e2),
              (f"$e_{e3} \\in \\bar{{\\bar{{A}}}}$", e3 in A, "bar", e3),
              (f"$e_{e4} \\in A \\cup B$" if k % 2 == 0 else f"$e_{e4} \\in B \\cap A$", (e4 in A or e4 in B) if k % 2 == 0 else (e4 in A and e4 in B),
               "cup" if k % 2 == 0 else "cap", e4)]
        sol = []
        for j, (q, val, kind, e) in enumerate(qs):
            ina, inb = ("\\in" if e in A else "\\notin"), ("\\in" if e in B else "\\notin")
            if kind == "cap":
                sol.append(f"{'абвг'[j]}) $(a \\in A) \\wedge (a \\in B) \\dashv\\vdash (a \\in A \\cap B)$ (с. 62); $e_{e} {ina} A$, $e_{e} {inb} B$ — {'включается' if val else 'не включается'}.")
            elif kind == "cup":
                sol.append(f"{'абвг'[j]}) $(a \\in A) \\vee (a \\in B) \\dashv\\vdash (a \\in A \\cup B)$ (с. 62); $e_{e} {ina} A$, $e_{e} {inb} B$ — {'включается' if val else 'не включается'}.")
            else:
                sol.append(f"{'абвг'[j]}) $(a \\in B) \\dashv\\vdash (a \\in \\bar{{\\bar{{B}}}})$ (с. 62) для класса $A$; $e_{e} {ina} A$ — {'включается' if val else 'не включается'}.")
        out.append(card(6, 2, "C", "iso", "def", "sym", "short", "с. 62, гл. 2, § 6", ["классы", "операции над классами"],
            f"{U6} Известно: {cls_text('$A$', A)}; {cls_text('$B$', B)}. Верно ли:\n\n" + items([q[0] for q in qs]),
            ans_items(["да" if q[1] else "нет" for q in qs]),
            "\n".join(sol)))
    A, B = {1, 2, 4}, {4, 5}
    out.append(card(6, 2, "E", "iso", "def", "sym", "short", "с. 62, гл. 2, § 6", ["классы", "диагностика"],
        f"{U6} Известно: {cls_text('$A$', A)}; {cls_text('$B$', B)}. Студент: «$e_2 \\in A \\cup B$, следовательно, $e_2 \\in A \\cap B$». Найдите ошибку.",
        "Перепутаны правила для $\\cup$ и $\\cap$ (с. 62): $e_2 \\in A \\cup B$ верно, но $e_2 \\in A \\cap B$ требует $(e_2 \\in A) \\wedge (e_2 \\in B)$, а $e_2 \\notin B$.",
        "С. 62: $(a \\in A) \\vee (a \\in B) \\dashv\\vdash (a \\in A \\cup B)$, $(a \\in A) \\wedge (a \\in B) \\dashv\\vdash (a \\in A \\cap B)$. "
        "Из дизъюнкции конъюнкция не следует: $e_2$ включается только в $A$."))
    # ступень 3: отношения двух классов
    for k in range(5):
        while True:
            A = set(rnd.sample(sorted(full), rnd.choice([2, 3])))
            mode = k % 5
            if mode == 0:
                B = A | set(rnd.sample(sorted(full - A), 2))
            elif mode == 1:
                B = set(A)
            elif mode == 2:
                B = set(rnd.sample(sorted(full - A), 2))
            elif mode == 3:
                B = set(rnd.sample(sorted(A), 1)) | set(rnd.sample(sorted(full - A), 2))
            else:
                B = set(rnd.sample(sorted(A), len(A) - 1))
            if B and (B, A) not in [(1, 1)]:
                break
        sub, sup = A <= B, B <= A
        inter = bool(A & B)
        eq = sub and sup
        sol = []
        if sub:
            sol.append(f"Каждый индивид из $A$ ({els(A)}) включается в $B$: $(\\forall a)((a \\in A) \\to (a \\in B))$, т. е. $A \\subset B$ [с. 62–63].")
        else:
            e = min(A - B)
            sol.append(f"$e_{e} \\in A$, но $e_{e} \\notin B$ — условие $(\\forall a)((a \\in A) \\to (a \\in B))$ нарушено: $A \\subset B$ неверно [с. 62–63].")
        if sup:
            sol.append(f"Каждый индивид из $B$ ({els(B)}) включается в $A$: $B \\subset A$ [с. 63].")
        else:
            e = min(B - A)
            sol.append(f"$e_{e} \\in B$, но $e_{e} \\notin A$: $B \\subset A$ неверно [с. 63].")
        if inter:
            e = min(A & B)
            sol.append(f"$e_{e} \\in A$ и $e_{e} \\in B$: $(\\exists a)((a \\in A) \\wedge (a \\in B))$ — классы пересекаются [с. 63].")
        else:
            sol.append("Ни один индивид не включается в оба класса: $(\\forall a){\\sim}((a \\in A) \\wedge (a \\in B))$ — классы не пересекаются [с. 63].")
        sol.append(("$(A \\subset B) \\wedge (B \\subset A)$ — классы эквивалентны [с. 63]." if eq else
                    "Хотя бы одно из включений неверно, поэтому классы не эквивалентны [определение эквивалентности, с. 63]."))
        out.append(card(6, 3, "C", "iso", "def", "sym", "short", S, ["классы", "отношения классов"],
            f"{U6} Известно: {cls_text('$A$', A)}; {cls_text('$B$', B)}. Выясните, верно ли:\n\n" +
            items(["$A \\subset B$", "$B \\subset A$", "$A$ и $B$ пересекаются", "$A$ и $B$ эквивалентны"]),
            ans_items(["да" if sub else "нет", "да" if sup else "нет", "да" if inter else "нет", "да" if eq else "нет"]),
            steps(sol)))
    A, B = {1, 3}, {1, 3, 5}
    out.append(card(6, 3, "E", "iso", "def", "sym", "short", S, ["классы", "диагностика"],
        f"{U6} Известно: {cls_text('$A$', A)}; {cls_text('$B$', B)}. Студент: «$A \\subset B$, оба класса непусты и пересекаются, "
        "значит, $A$ и $B$ эквивалентны». Найдите ошибку.",
        "Эквивалентность — $(A \\subset B) \\wedge (B \\subset A)$ (с. 63); $B \\subset A$ неверно: $e_5 \\in B$, $e_5 \\notin A$.",
        steps(["$A \\subset B$ верно: $e_1, e_3$ включаются в $B$ [с. 62].",
               "Определение с. 63: $A$ и $B$ эквивалентны, если и только если $(A \\subset B) \\wedge (B \\subset A)$, или $(\\forall a)((a \\in A) \\leftrightarrow (a \\in B))$.",
               "$e_5 \\in B$, но $e_5 \\notin A$, значит, $B \\subset A$ неверно; непустота и пересечение эквивалентности не дают."])))
    return out


# ================================================================ § 9 существование
ST = {"E": "существует", "N": "не существует", "Q": "неопределённо, существует ли"}
STF = {"E": "E", "N": "\\urcorner E", "Q": "?E"}


def enka_status(sts):
    if all(s == "E" for s in sts):
        return "E"
    if any(s == "N" for s in sts):
        return "N"
    return "Q"


def g09():
    out = []
    S = "с. 66–67, гл. 2, § 9"
    pool = []
    for n in (3, 4):
        for sts in itertools.product("ENQ", repeat=n):
            pool.append(sts)
    rnd.shuffle(pool)
    want = ["E", "N", "Q"]
    for w in want:
        sts = next(s for s in pool if enka_status(s) == w and len(set(s)) >= (1 if w == "E" else 2))
        pool.remove(sts)
        n = len(sts)
        lst = "; ".join(f"$a^{i + 1}$ — {ST[s]}" for i, s in enumerate(sts))
        enk = "a^1, …, a^" + str(n)
        res = enka_status(sts)
        if res == "E":
            sol = f"Все члены существуют: $E(a^1) \\wedge … \\wedge E(a^{n})$. По п. 4 (с. 67) $E({enk})$."
        elif res == "N":
            j = sts.index("N") + 1
            sol = (f"$\\urcorner E(a^{j})$, поэтому истинна дизъюнкция $\\urcorner E(a^1) \\vee … \\vee \\urcorner E(a^{n})$; "
                   f"по п. 5 (с. 67) $\\urcorner E({enk})$.")
        else:
            j = sts.index("Q") + 1
            sol = (f"$?E(a^{j})$, т. е. ${{\\sim}}E(a^{j}) \\wedge {{\\sim}}\\urcorner E(a^{j})$ (п. 3, с. 67). Поэтому неверна конъюнкция "
                   f"$E(a^1) \\wedge … \\wedge E(a^{n})$ и по п. 4 ${{\\sim}}E({enk})$. Ни один член не имеет $\\urcorner E$, дизъюнкция "
                   f"$\\urcorner E(a^1) \\vee … \\vee \\urcorner E(a^{n})$ неверна, по п. 5 ${{\\sim}}\\urcorner E({enk})$. По п. 6 $?E({enk})$.")
        out.append(card(9, 2, "C", "iso", "def", "sym", "short", S, ["существование", "энки"],
            f"Буквы $a^1, …, a^{n}$ — индивидуальные термины. Известно: {lst}. Что истинно: $E({enk})$, $\\urcorner E({enk})$ или $?E({enk})$?",
            f"${STF[res]}({enk})$.", sol))
    for w in ("N", "Q"):
        while True:
            sts = tuple(rnd.choice("NQ") for _ in range(3))
            if enka_status(sts) == w and (w == "N" and len(set(sts)) == 1 or w == "Q"):
                break
        lst = "; ".join(f"$I_{i + 1}$ — {ST[s]}" for i, s in enumerate(sts))
        if w == "N":
            sol = ("Индивид, который есть $a$ и существует, отсутствует; все такие индивиды не существуют: "
                   "$(\\forall I)((I \\rightharpoonup a) \\to \\urcorner E(I))$. По определению (с. 66) $\\urcorner E(a)$.")
        else:
            j = sts.index("Q") + 1
            sol = steps(["Ни один из индивидов $I_1, I_2, I_3$ не существует, поэтому $(\\exists I)((I \\rightharpoonup a) \\wedge E(I))$ неверно и ${\\sim}E(a)$ [определение $E$, с. 66].",
                         f"$?E(I_{j})$, значит, ${{\\sim}}\\urcorner E(I_{j})$; условие $(\\forall I)((I \\rightharpoonup a) \\to \\urcorner E(I))$ неверно и ${{\\sim}}\\urcorner E(a)$ [определение $\\urcorner E$, с. 66].",
                         "$?E(a) \\equiv Df.{\\sim}E(a) \\wedge {\\sim}\\urcorner E(a)$ (с. 66): истинно $?E(a)$."])
        out.append(card(9, 2, "C", "iso", "def", "sym", "short", "с. 66, гл. 2, § 9", ["существование", "общие термины"],
            f"Буква $a$ — общий термин-субъект; $I_1, I_2, I_3$ — все индивиды, которые суть $a$ ($I_i \\rightharpoonup a$). Известно: {lst}. "
            "Что истинно: $E(a)$, $\\urcorner E(a)$ или $?E(a)$?",
            f"${STF[w]}(a)$.", sol))
    out.append(card(9, 2, "E", "iso", "def", "nat", "short", "с. 66–67, гл. 2, § 9", ["существование", "энки", "диагностика"],
        "Энка образована тремя индивидами: кораблём «Арго», кораблём «Бигль» и кораблём «Наутилус» капитана Немо (вымышленным). "
        "Студент: «энка существует, ведь в ней есть по крайней мере один существующий корабль». Найдите ошибку.",
        "Нарушено определение п. 4 (с. 66–67): $E(a^1, …, a^n) \\dashv\\vdash E(a^1) \\wedge … \\wedge E(a^n)$; один несуществующий член даёт $\\urcorner E$ энки (п. 5).",
        "С. 66: «энка предметов существует, если и только если существует каждый предмет, входящий в неё»; и не существует, если не существует "
        "хотя бы один из входящих в неё предметов (п. 5, с. 67). «Наутилус» вымышлен, поэтому $\\urcorner E$ энки. Студент применил к энке "
        "условие существования родового термина (хотя бы один индивид, с. 66)."))
    out.append(card(9, 2, "E", "iso", "def", "nat", "short", "с. 66, гл. 2, § 9", ["существование", "общие термины", "диагностика"],
        "Студент: «Динозавр, по имени известный каждому школьнику, — индивид, который не существует. Значит, по определению предиката $E$ "
        "для общих субъектов верно: собака не существует, если хотя бы одна собака не существует». Найдите ошибку.",
        "Нарушено определение $\\urcorner E(a) \\equiv Df.(\\forall I)((I \\rightharpoonup a) \\to \\urcorner E(I))$ (с. 66): нужно, чтобы не существовали все индивиды, которые суть $a$.",
        "С. 66: «$a$ не существует, если и только если все индивиды, которые суть $a$, не существуют». Несуществование одного индивида "
        "даёт лишь ${\\sim}$ для формулы с квантором общности по $E(I)$, а не $\\urcorner E(a)$; при существовании хотя бы одной собаки "
        "по определению $E(a) \\equiv Df.(\\exists I)((I \\rightharpoonup a) \\wedge E(I))$ истинно $E(a)$."))
    # ступень 3: состояния
    S3 = "с. 67, гл. 2, § 9"
    for k in range(2):
        tvx, tvy = [(True, False), (False, True), (True, True), (False, False)][rnd.randrange(4) if k else 0]
        forms = [("x \\wedge y", tvx and tvy), ("x \\vee y", tvx or tvy), ("x \\wedge {\\sim}y", tvx and not tvy),
                 ("{\\sim}x \\vee y", (not tvx) or tvy)]
        if k:
            forms = [("x \\vee {\\sim}x", True), ("{\\sim}x \\wedge y", (not tvx) and tvy), ("x \\wedge {\\sim}x", False), ("{\\sim}(x \\wedge y)", not (tvx and tvy))]
        tv = lambda b: "истинно" if b else "ложно"
        sol = []
        for j, (f, val) in enumerate(forms):
            if val:
                sol.append(f"{'абвг'[j]}) ${f}$ истинно, по аксиоме 7 ($E(sx) \\dashv\\vdash x$, с. 67) $E(s({f}))$.")
            else:
                sol.append(f"{'абвг'[j]}) истинно ${{\\sim}}({f})$, по аксиоме 8 ($\\urcorner E(sx) \\dashv\\vdash {{\\sim}}x$, с. 67) $\\urcorner E(s({f}))$.")
        out.append(card(9, 3, "C", "iso", "def", "sym", "short", S3, ["существование", "состояния"],
            f"Буквы $x, y$ — высказывания; истинны {'$x$' if tvx else '${\\sim}x$'} и {'$y$' if tvy else '${\\sim}y$'}. "
            "Для каждого состояния установите, что истинно: $E$ или $\\urcorner E$.\n\n" + items([f"$s({f})$" for f, _ in forms]),
            ans_items([f"$E$" if v else "$\\urcorner E$" for _, v in forms]),
            "\n".join(sol)))
    sts = ["E", "E", "N"]
    rnd.shuffle(sts)
    out.append(card(9, 3, "C", "iso", "def", "sym", "short", "с. 68, гл. 2, § 9", ["существование", "скопления"],
        "Термин скопления $a$ построен так, что в $a$ включаются только предметы $b^1, b^2, b^3$. Известно: " +
        "; ".join(f"$b^{i + 1}$ — {ST[s]}" for i, s in enumerate(sts)) + ". Существует ли скопление $a$?",
        "Нет: ${\\sim}E(a)$.",
        steps(["Для такого скопления $E(a) \\equiv Df.E(b^1) \\wedge E(b^2) \\wedge E(b^3)$ (с. 68).",
               f"$\\urcorner E(b^{sts.index('N') + 1})$, а из $\\urcorner E$ следует ${{\\sim}}E$, так что конъюнкция неверна.",
               "Значит, ${\\sim}E(a)$: скопление не существует."])))
    sts = ["N", "Q", "E", "N"]
    rnd.shuffle(sts)
    out.append(card(9, 3, "C", "iso", "def", "sym", "short", "с. 68, гл. 2, § 9", ["существование", "скопления"],
        "Скопление $a$ — индивидуальный термин; не определено, какие именно и сколько предметов в него включаются. Известно, что индивиды "
        "$I_1, …, I_4$ — все кандидаты на включение в $a$ и что они включаются в $a$ ($I_i \\in a$); " +
        "; ".join(f"$I_{i + 1}$ — {ST[s]}" for i, s in enumerate(sts)) + ". Что истинно: $E(a)$, $\\urcorner E(a)$ или $?E(a)$?",
        "$E(a)$.",
        steps(["Для индивидуального термина скопления $E(a) \\dashv\\vdash (\\exists I)E(I \\downarrow (I \\in a))$ (с. 68).",
               f"$I_{sts.index('E') + 1} \\in a$ и существует; значит, существует индивид, входящий в $a$.",
               "Следовательно, $E(a)$; несуществование других индивидов этого не меняет."])))
    out.append(card(9, 3, "E", "iso", "def", "nat", "short", "с. 62, 67–68, гл. 2, § 9", ["существование", "классы", "диагностика"],
        "Студент: «Термин “класс единорогов” образован, но единороги не существуют. Значит, $\\urcorner E(K\\text{единорог})$: класс единорогов не существует». "
        "Найдите ошибку.",
        "Нарушено правило для первичных классов (с. 67–68): $E(Ka)$, если и только если $a$ — термин-субъект; существование класса не зависит от существования индивидов (с. 62).",
        steps(["«Единорог» — термин-субъект, поэтому «класс единорогов» — первичный класс $Ka$ (с. 60–61).",
               "Для первичных классов: 1) $E(Ka)$, если и только если $a$ есть термин-субъект (с. 67); значит, $E(K\\text{единорог})$.",
               "С. 62: построив выражение «класс богов», мы образовали класс, и он существует независимо от того, существуют боги или нет. Класс единорогов пуст, но существует."])))
    return out


# ================================================================ § 11 возможность
def g11():
    out = []
    S = "с. 70–71, гл. 2, § 11"
    D = "Буквы $x, y, z$ — высказывания; $sx, sy, sz$ — родовые термины состояний; принимаются аксиомы для $M$ с операторами $\\vee$ и $\\wedge$ (с. 70–71)."
    out.append(card(11, 2, "D", "iso", "def", "sym", "short", S, ["возможность"],
        f"{D} Известно: $M(sx)$, $\\urcorner M(sy)$. Что следует для $s(x \\vee y)$?",
        "$M(s(x \\vee y))$.",
        "По аксиоме $M(s(x \\vee y)) \\dashv\\vdash M(sx) \\vee M(sy)$ (с. 70): дизъюнкция истинна, так как $M(sx)$; значит, $M(s(x \\vee y))$."))
    out.append(card(11, 2, "D", "iso", "def", "sym", "short", S, ["возможность"],
        f"{D} Известно: $\\urcorner M(sy)$; о $sx$ ничего не известно. Что следует для $s(x \\wedge y)$?",
        "$\\urcorner M(s(x \\wedge y))$.",
        "По аксиоме $\\urcorner M(s(x \\wedge y)) \\dashv\\vdash \\urcorner M(sx) \\vee \\urcorner M(sy)$ (с. 70) достаточно одного члена: $\\urcorner M(sy)$ даёт $\\urcorner M(s(x \\wedge y))$."))
    out.append(card(11, 2, "E", "iso", "def", "nat", "short", S, ["возможность", "диагностика"],
        "Студент: «Возможно, что завтра в полдень Иван будет в Москве; возможно, что завтра в полдень Иван будет во Владивостоке. "
        "Следовательно, возможно, что завтра в полдень Иван будет и в Москве, и во Владивостоке». Найдите ошибку.",
        "Применено неприемлемое утверждение $M(sx) \\wedge M(sy) \\vdash M(s(x \\wedge y))$ (с. 70): при $x \\to {\\sim}y$ верно $\\urcorner M(s(x \\wedge y))$.",
        "С. 70: утверждение $M(sx) \\wedge M(sy) \\vdash M(s(x \\wedge y))$ неприемлемо в общем виде, так как если $x \\to {\\sim}y$, то будет "
        "$\\urcorner M(s(x \\wedge y))$. Здесь пребывание в Москве в данный момент обязывает признать, что Иван не во Владивостоке. "
        "Допустима лишь схема с ограничением $M(s(x \\wedge y)) \\dashv\\vdash M(sx) \\wedge M(sy) \\wedge {\\sim}(x \\to {\\sim}y)$ (с. 71)."))
    # ступень 3
    out.append(card(11, 3, "D", "iso", "def", "sym", "short", S, ["возможность"],
        f"{D} Известно: $M(sx)$, $M(sz)$, ${{\\sim}}((x \\vee y) \\to {{\\sim}}z)$. Возможно ли состояние $s((x \\vee y) \\wedge z)$?",
        "Да: $M(s((x \\vee y) \\wedge z))$.",
        steps(["$M(sx)$ даёт $M(sx) \\vee M(sy)$, по аксиоме для $\\vee$ (с. 70) $M(s(x \\vee y))$.",
               "Схема с ограничением (с. 71): $M(s(u \\wedge z)) \\dashv\\vdash M(su) \\wedge M(sz) \\wedge {\\sim}(u \\to {\\sim}z)$, где $u$ — $x \\vee y$.",
               "Все три члена даны или получены: $M(s(x \\vee y))$, $M(sz)$, ${\\sim}((x \\vee y) \\to {\\sim}z)$.",
               "Следовательно, $M(s((x \\vee y) \\wedge z))$."])))
    sts = ["M", "M", "N"]
    rnd.shuffle(sts)
    j = sts.index("N") + 1
    out.append(card(11, 3, "D", "iso", "def", "sym", "short", "с. 71, 66–67, гл. 2, § 11", ["возможность", "энки"],
        "Буквы $a^1, a^2, a^3$ — индивидуальные термины. Известно: " +
        "; ".join(f"{'$M' if s == 'M' else '$\\urcorner M'}(a^{i + 1})$" for i, s in enumerate(sts)) +
        ". Что истинно: $M(a^1, a^2, a^3)$ или $\\urcorner M(a^1, a^2, a^3)$?",
        "$\\urcorner M(a^1, a^2, a^3)$.",
        steps(["Для энок $M$ определяется аналогично $E$: в определениях $E$ везде заменить $E$ на $M$ (с. 71).",
               "Аналог п. 5 (с. 67): $\\urcorner M(a^1, a^2, a^3) \\dashv\\vdash \\urcorner M(a^1) \\vee \\urcorner M(a^2) \\vee \\urcorner M(a^3)$.",
               f"Дизъюнкция истинна, так как $\\urcorner M(a^{j})$; значит, $\\urcorner M(a^1, a^2, a^3)$."])))
    out.append(card(11, 3, "E", "iso", "def", "nat", "short", "с. 71, гл. 2, § 11", ["возможность", "классы", "диагностика"],
        "Термин «класс натуральных чисел, которые одновременно чётны и нечётны» построен так, что из определения следует "
        "$(a \\in A) \\wedge {\\sim}(a \\in A)$. Студент: «Такой класс не существует, но всё же возможен: невозможного класса нет». Найдите ошибку.",
        "Для классов $M(a) \\equiv Df.E(a)$, $\\urcorner M(a) \\equiv Df.\\urcorner E(a)$ (с. 71): несуществующий класс невозможен.",
        steps(["Если из определения термина класса следует $(a \\in A) \\wedge {\\sim}(a \\in A)$, то $A$ не существует: $\\urcorner E(A)$ (с. 62).",
               "Для абстрактных предметов и классов термины $E$ и $M$ не различаются: $M(a) \\equiv Df.E(a)$, $\\urcorner M(a) \\equiv Df.\\urcorner E(a)$ (с. 71).",
               "Значит, $\\urcorner M(A)$; утверждение студента «не существует, но возможен» для класса противоречит определению."])))
    return out


# ================================================================ § 16 вероятность
def g16():
    out = []
    S = "с. 76, гл. 2, § 16"
    D = "Буквы $x, y$ — высказывания; $p(x)$ — вероятность $sx$ (с. 76)."
    a = rnd.choice([0.15, 0.35, 0.45, 0.65])
    out.append(card(16, 2, "C", "iso", "def", "sym", "short", S, ["вероятность"],
        f"{D} Известно: $p(x) = {tm(a)}$. Найдите $p({{\\sim}}x)$ и установите, возможно ли $sx$.",
        f"$p({{\\sim}}x) = {tm(round(1 - a, 2))}$; $M(sx)$.",
        steps([f"$\\vdash p({{\\sim}}x) = 1 - p(x)$ (с. 76): $p({{\\sim}}x) = 1 - {tm(a)} = {tm(round(1 - a, 2))}$.",
               f"$\\vdash (p(x) > 0) \\leftrightarrow M(sx)$ (с. 76): ${tm(a)} > 0$, значит, $M(sx)$."])))
    out.append(card(16, 2, "C", "vary", "def", "sym", "short", S, ["вероятность", "обращение"],
        f"{D} Известно: $p({{\\sim}}x) = 1$. Что можно сказать о возможности $sx$?",
        "$\\urcorner M(sx)$.",
        steps(["$\\vdash p({\\sim}x) = 1 - p(x)$ (с. 76): $p(x) = 1 - 1 = 0$.",
               "$\\vdash (p(x) = 0) \\leftrightarrow \\urcorner M(sx)$ (с. 76): $\\urcorner M(sx)$."])))
    out.append(card(16, 2, "E", "iso", "def", "sym", "short", S, ["вероятность", "диагностика"],
        f"{D} Известно: $p(x) = 0{{,}}5$, $p(y) = 0{{,}}4$. Студент: «по правилу для конъюнкции $p(x \\wedge y) = 0{{,}}4$». Найдите ошибку.",
        "Правило для $\\wedge$ — неравенство $\\vdash p(x \\wedge y) \\leqslant min(p(x), p(y))$ (с. 76): можно утверждать лишь $p(x \\wedge y) \\leqslant 0{,}4$.",
        "С. 76: для конъюнкции принимается $\\vdash p(x \\wedge y) \\leqslant min(p(x), p(y))$, а не равенство (ср. степени истинности, где "
        "$v(x \\wedge y) = min$, с. 60). Из данных следует только $p(x \\wedge y) \\leqslant 0{,}4$."))
    for k in range(2):
        a, b = sorted(rnd.sample([0.1, 0.2, 0.3, 0.4, 0.6, 0.7, 0.8], 2))
        if k == 0:
            out.append(card(16, 3, "C", "iso", "def", "sym", "short", S, ["вероятность"],
                f"{D} Известно: $p(x) = {tm(a)}$, $p(y) = {tm(b)}$. Какие оценки дают правила § 16 для $p(x \\wedge y)$, $p(x \\vee y)$ и $p({{\\sim}}x \\wedge y)$?",
                f"$p(x \\wedge y) \\leqslant {tm(a)}$; $p(x \\vee y) \\geqslant {tm(b)}$; $p({{\\sim}}x \\wedge y) \\leqslant {tm(min(round(1 - a, 2), b))}$.",
                steps([f"$\\vdash p(x \\wedge y) \\leqslant min(p(x), p(y))$ (с. 76): $p(x \\wedge y) \\leqslant min({tm(a)}, {tm(b)}) = {tm(a)}$.",
                       f"$\\vdash p(x \\vee y) \\geqslant max(p(x), p(y))$ (с. 76): $p(x \\vee y) \\geqslant {tm(b)}$.",
                       f"$p({{\\sim}}x) = 1 - {tm(a)} = {tm(round(1 - a, 2))}$ (с. 76).",
                       f"$p({{\\sim}}x \\wedge y) \\leqslant min({tm(round(1 - a, 2))}, {tm(b)}) = {tm(min(round(1 - a, 2), b))}$."])))
        else:
            out.append(card(16, 3, "C", "iso", "def", "sym", "short", S, ["вероятность"],
                f"{D} Известно: $p(x \\vee y) = {tm(a)}$, $p(y) = {tm(b)}$. Совместимы ли эти данные с правилами § 16? Если нет — какое правило нарушено?",
                f"Нет: нарушено $\\vdash p(x \\vee y) \\geqslant max(p(x), p(y))$ (с. 76), так как ${tm(a)} < {tm(b)}$.",
                steps(["$\\vdash p(x \\vee y) \\geqslant max(p(x), p(y))$ (с. 76).",
                       f"$max(p(x), p(y)) \\geqslant p(y) = {tm(b)}$.",
                       f"Следовательно, должно быть $p(x \\vee y) \\geqslant {tm(b)}$, а дано ${tm(a)}$ — данные несовместимы."])))
    out.append(card(16, 3, "E", "iso", "def", "nat", "short", "с. 77, гл. 2, § 16", ["вероятность", "диагностика"],
        "Студент: «Встреча двух определённых людей в определённый день на улице чужого города возможна, значит, её вероятность больше нуля. "
        "Если ждать достаточно долго, она рано или поздно произойдёт». Найдите ошибку.",
        "Логическая ошибка, разобранная на с. 77: из $M(sx)$ следует $p(x) > 0$, но «рано или поздно осуществится» верно лишь при частотном методе с большим числом испытаний.",
        steps(["Из $M(sx)$ действительно следует $p(x) > 0$: $\\vdash (p(x) > 0) \\leftrightarrow M(sx)$ (с. 76).",
               "Вывод «рано или поздно» был бы верен, если бы частотный метод был единственным способом установления вероятности (с. 77).",
               "Этот метод неприменим для индивидуальных событий и там, где число испытаний не может быть достаточно большим; к тому же $p(x) > 0$ может быть просто следствием $M(sx)$, принятого лишь потому, что $x$ не ведёт к противоречию (с. 77)."])))
    return out


# ================================================================ § 18 сравнение
def g18():
    out = []
    S = "с. 79, гл. 2, § 18"
    D = "Буквы $a, b, c$ — термины; $p$ — признак (и способ сравнения); используются определения и аксиомы C1–C7 (с. 79)."
    out.append(card(18, 2, "D", "iso", "def", "sym", "short", S, ["сравнение", "аксиомы сравнения"],
        f"{D} Дано: $a > pb$, $b > pc$. Какое заключение даёт одна аксиома и какая?",
        "$a > pc$ по C4.",
        "C4 (с. 79): $(a > pb) \\wedge (b > pc) \\vdash (a > pc)$ — транзитивность отношения $> p$."))
    out.append(card(18, 2, "D", "iso", "def", "nat", "short", S, ["сравнение", "аксиомы сравнения"],
        "Буквы $a, b, c$ — термины; $p$ — признак «вес» вместе со способом взвешивания. Дано: «$a$ тяжелее $b$, а $b$ весит столько же, сколько $c$». "
        "Запишите данные в символах и получите заключение одной аксиомой C1–C7 (с. 79).",
        "$(a > pb) \\wedge (b = pc)$; по C5 $a > pc$: «$a$ тяжелее $c$».",
        "«Тяжелее» — частный случай знака $> p$, «весит столько же» — $= p$ (с. 78–79). C5 (с. 79): $(a > pb) \\wedge (b = pc) \\vdash (a > pc)$."))
    out.append(card(18, 2, "E", "iso", "def", "sym", "short", S, ["сравнение", "диагностика"],
        f"{D} Студент: «Дано $a \\urcorner > pb$; по аксиоме C3 получаем $b > pa$». Найдите ошибку.",
        "C3 (с. 79) даёт $(a \\urcorner > pb) \\vdash (b > pa) : (a = pb)$ — сильную дизъюнкцию; $b > pa$ отдельно не следует.",
        "С. 79: C3 — $(a \\urcorner > pb) \\vdash (b > pa) : (a = pb)$, где «:» — «одно и только одно из двух». Из $a \\urcorner > pb$ "
        "может оказаться и $a = pb$; студент отбросил второй член дизъюнкции."))
    out.append(card(18, 3, "D", "iso", "def", "sym", "proof", S, ["сравнение", "вывод"],
        f"{D} Выведите $a > pc$ из $a > pb$ и $c = pb$.",
        "$a > pc$ — по определению $= p$ и C5.",
        steps(["$a > pb$ [посылка].",
               "$c = pb$ [посылка].",
               "$(c \\urcorner > pb) \\wedge (b \\urcorner > pc)$ [2; определение $= p$, с. 79].",
               "$(b \\urcorner > pc) \\wedge (c \\urcorner > pb)$ [3; перестановка членов конъюнкции].",
               "$b = pc$ [4; определение $= p$].",
               "$a > pc$ [1, 5; C5, с. 79]."])))
    out.append(card(18, 3, "D", "iso", "def", "sym", "proof", S, ["сравнение", "вывод"],
        f"{D} Выведите $c \\urcorner > pa$ из $a > pb$ и $b > pc$.",
        "$c \\urcorner > pa$ — по C4 и C2.",
        steps(["$a > pb$ [посылка].", "$b > pc$ [посылка].", "$a > pc$ [1, 2; C4, с. 79].", "$c \\urcorner > pa$ [3; C2, с. 79]."])))
    out.append(card(18, 3, "E", "iso", "def", "sym", "short", S, ["сравнение", "диагностика"],
        f"{D} Студент вывел $a < pc$ из $b > pa$ и $c > pb$:\n\n" +
        steps(["$b > pa$ [посылка].", "$c > pb$ [посылка].", "$b > pc$ [2; C2].", "$c > pa$ [2, 1; C4].", "$a < pc$ [4; определение $< p$]."]) +
        "\n\nНайдите все ошибки.",
        "Шаг 3: C2 даёт $(c > pb) \\vdash (b \\urcorner > pc)$, а не $b > pc$ (с. 79); шаг 3 к тому же лишний. Шаги 4 и 5 верны.",
        steps(["C2 (с. 79): $(a > pb) \\vdash (b \\urcorner > pa)$ — из $c > pb$ получается $b \\urcorner > pc$; запись $b > pc$ ему противоречит.",
               "Шаг 4: $(c > pb) \\wedge (b > pa) \\vdash (c > pa)$ — C4, верно.",
               "Шаг 5: $(a < pc) \\equiv Df.(c > pa)$ (с. 79) — верно. Заключение получено правильно, неверна лишь строка 3."])))
    return out


# ================================================================ § 23–26 ряды
def row_model(n, gaps):
    gl = ", ".join(f"$a^{k}$ и $a^{k + 1}$" for k in sorted(gaps))
    return (f"Ряд $A$ относительно $\\alpha$ образован индивидами $a^1, …, a^{n}$, причём $a^{{i+1}} > \\alpha a^i$ ($i = 1, …, {n - 1}$). "
            f"Подразумеваемый класс индивидов (§ 24) включает элементы $A$; между {gl} можно поместить индивид этого класса, "
            "между остальными соседними элементами — нельзя.")


def g23_26():
    out = []
    # § 23 соседние элементы
    for k in range(2):
        n = rnd.choice([6, 7, 8])
        gaps = set(rnd.sample(range(1, n), 2))
        pairs = []
        while len(pairs) < 4:
            i = rnd.randrange(1, n)
            j = i + 1 if len(pairs) % 2 == 0 else min(n, i + rnd.choice([2, 3]))
            if j > i and (i, j) not in pairs:
                pairs.append((i, j))
        sol = []
        for t, (i, j) in enumerate(pairs):
            if j == i + 1:
                sol.append(f"{'абвг'[t]}) между $a^{i}$ и $a^{j}$ нет элемента $A$ — соседние" + (" (то, что между ними можно поместить индивид, на соседство не влияет)" if i in gaps else "") + ".")
            else:
                sol.append(f"{'абвг'[t]}) $a^{i + 1}$ — элемент $A$ и находится между ними: $(a^{i + 1} > \\alpha a^{i}) \\wedge (a^{j} > \\alpha a^{i + 1})$ — не соседние.")
        out.append(card(23, 1, "R", "iso", "def", "sym", "short", "с. 85, гл. 2, § 23", ["упорядоченный ряд", "соседние элементы"],
            row_model(n, gaps) + " Какие пары — соседние элементы $A$ относительно $\\alpha$ (с. 85)?\n\n" + items([f"$a^{i}$, $a^{j}$" for i, j in pairs]),
            ans_items(["соседние" if j == i + 1 else "не соседние" for i, j in pairs]),
            "Элементы $a$ и $b$ ряда соседние, если и только если ни один элемент $A$ не находится между ними относительно $\\alpha$ (с. 85); "
            "«между» — по § 20 (с. 82).\n\n" + "\n".join(sol)))
    n, gaps = 6, {3}
    out.append(card(23, 1, "E", "iso", "def", "sym", "short", "с. 85–86, гл. 2, § 23", ["упорядоченный ряд", "соседние элементы", "диагностика"],
        row_model(n, gaps) + " Студент: «$a^3$ и $a^4$ — не соседние элементы $A$: между ними можно поместить индивид». Найдите ошибку.",
        "Соседство определяется по элементам $A$ (с. 85): между $a^3$ и $a^4$ нет элемента $A$, значит, $a^3 \\mid \\alpha a^4$. Возможность поместить индивид касается соприкосновения (с. 86): $a^3 \\urcorner \\parallel \\alpha a^4$.",
        "Определение с. 85: $a$ и $b$ соседние, если и только если ни один элемент $A$ не находится между ними. Ср. рис. 1: $a^3$ и $a^4$ не соприкасаются, "
        "«поскольку между ними можно поместить некоторый индивид $b$» (с. 86), — это признак несоприкосновения, а не несоседства."))
    # § 24 соприкосновение
    n, gaps = 7, {2, 5}
    out.append(card(24, 1, "R", "iso", "def", "sym", "short", "с. 86, гл. 2, § 24", ["соприкосновение"],
        row_model(n, gaps) + " Соприкасаются ли $a^5$ и $a^6$ относительно $\\alpha$?",
        "Нет: $a^5 \\urcorner \\parallel \\alpha a^6$.",
        "По определению (с. 86) $a$ и $b$ соприкасаются, если $a > \\alpha b$ или $b > \\alpha a$ и при этом никакой индивид класса невозможно поместить "
        "между ними. $a^6 > \\alpha a^5$, но между ними можно поместить индивид, поэтому $a^5 \\urcorner \\parallel \\alpha a^6$ (п. 2, с. 87)."))
    n = 8
    gaps = set(rnd.sample(range(1, n), 3))
    prs = [(min(gaps), min(gaps) + 1), (max(set(range(1, n)) - gaps), max(set(range(1, n)) - gaps) + 1), (2, 4), (6, 8)]
    sol = []
    for t, (i, j) in enumerate(prs):
        if j == i + 1:
            sol.append(f"{'абвг'[t]}) $a^{j} > \\alpha a^{i}$; " + ("между ними можно поместить индивид — $a^%d \\urcorner \\parallel \\alpha a^%d$." % (i, j) if i in gaps
                       else "поместить индивид между ними нельзя — $a^%d \\parallel \\alpha a^%d$." % (i, j)))
        else:
            sol.append(f"{'абвг'[t]}) между $a^{i}$ и $a^{j}$ находится элемент $a^{i + 1}$ — индивид класса; $a^{i} \\urcorner \\parallel \\alpha a^{j}$.")
    vals = [("не соприкасаются" if (j != i + 1 or i in gaps) else "соприкасаются") for i, j in prs]
    out.append(card(24, 2, "C", "iso", "def", "sym", "short", "с. 86–87, гл. 2, § 24", ["соприкосновение"],
        row_model(n, gaps) + " Соприкасаются ли относительно $\\alpha$:\n\n" + items([f"$a^{i}$ и $a^{j}$" for i, j in prs]),
        ans_items(vals),
        "Определение 1–2 (с. 87): $a \\parallel \\alpha b$, если $(a > \\alpha b) \\vee (b > \\alpha a)$ и $(\\urcorner\\mathrm{M} I)$ поместить $I$ между $a$ и $b$.\n\n" + "\n".join(sol)))
    out.append(card(24, 2, "E", "iso", "def", "sym", "short", "с. 87, гл. 2, § 24", ["соприкосновение", "диагностика"],
        "Буквы $a, b$ — индивиды, $\\alpha$ — способ установления порядка. Известно: $a = \\alpha b$. Студент: «по следствию определения "
        "$(a = \\alpha b) \\vdash {\\sim}(a \\parallel \\alpha b)$ получаем $a \\urcorner \\parallel \\alpha b$: $a$ и $b$ не соприкасаются». Найдите ошибку.",
        "Смешаны ${\\sim}(a \\parallel \\alpha b)$ и $a \\urcorner \\parallel \\alpha b$ (с. 87): следствие даёт лишь «нельзя сказать, что $a \\parallel \\alpha b$»; $a \\urcorner \\parallel \\alpha b$ требует $(a > \\alpha b) \\vee (b > \\alpha a)$.",
        steps(["С. 87: «в рассматриваемом случае различение отрицаний $\\urcorner$ и $\\sim$ исключительно важно».",
               "$a \\urcorner \\parallel \\alpha b$ по п. 2 содержит член $(a > \\alpha b) \\vee (b > \\alpha a)$, а при $a = \\alpha b$ он неверен.",
               "${\\sim}(a \\parallel \\alpha b)$ значит лишь «нельзя сказать, что $a \\parallel \\alpha b$» — это может быть $a \\urcorner \\parallel \\alpha b$, $a = \\alpha b$, $a ? > \\alpha b$ и т. п. (с. 87)."])))
    # § 25 непрерывность эмпирического ряда
    n, gaps = 8, {3, 6}
    out.append(card(25, 1, "R", "iso", "def", "sym", "short", "с. 87, гл. 2, § 25", ["непрерывность", "эмпирический ряд"],
        row_model(n, gaps) + " Элементы $A$ — эмпирические индивиды. Непрерывен ли ряд $A$ относительно $\\alpha$?",
        "Нет, $A$ прерывен.",
        "Ряд непрерывен, если и только если все его соседние элементы попарно соприкасаются (с. 87). Соседние $a^3$ и $a^4$ не соприкасаются: "
        "между ними можно поместить индивид. Значит, $(\\exists a)(\\exists b)((a \\in A) \\wedge (b \\in A) \\wedge (a \\mid \\alpha b) \\wedge {\\sim}(a \\parallel \\alpha b))$ — $A$ прерывен (с. 87–88)."))
    n = 8
    gaps = {2, 6}
    subs = [("$a^3, a^4, a^5, a^6$", [3, 4, 5, 6]), ("$a^5, a^6, a^7$", [5, 6, 7]), ("$a^3, a^5$", [3, 5]), ("$a^7, a^8$", [7, 8])]
    sol, vals = [], []
    for t, (nm, el) in enumerate(subs):
        bad = None
        for u, w in zip(el, el[1:]):
            if w != u + 1:
                bad = (u, w, f"между ними находится индивид $a^{u + 1}$")
                break
            if u in gaps:
                bad = (u, w, "между ними можно поместить индивид")
                break
        if bad:
            vals.append("прерывен")
            sol.append(f"{'абвг'[t]}) соседние в этом ряду $a^{bad[0]}$ и $a^{bad[1]}$ не соприкасаются: {bad[2]} — прерывен.")
        else:
            vals.append("непрерывен")
            sol.append(f"{'абвг'[t]}) все соседние элементы идут подряд и между ними ничего поместить нельзя — попарно соприкасаются, ряд непрерывен.")
    out.append(card(25, 2, "C", "iso", "def", "sym", "short", "с. 87–88, гл. 2, § 25", ["непрерывность", "эмпирический ряд"],
        row_model(n, gaps) + " Элементы $A$ — эмпирические индивиды. Для каждого ряда, образованного указанными элементами $A$ (порядок — тот же), выясните, непрерывен он или прерывен относительно $\\alpha$.\n\n" +
        items([s[0] for s in subs]),
        ans_items(vals),
        "Определения с. 87–88: ряд непрерывен, если все его соседние элементы попарно соприкасаются; прерывен, если для некоторой пары соседних ${\\sim}(a \\parallel \\alpha b)$. "
        "Соседство берётся в данном ряду, соприкосновение — относительно класса индивидов, включающего элементы $A$.\n\n" + "\n".join(sol)))
    out.append(card(25, 2, "E", "iso", "def", "sym", "short", "с. 87–88, гл. 2, § 25", ["непрерывность", "диагностика"],
        row_model(8, {4}) + " Студент: «Ряд из элементов $a^1, a^3, a^5$ непрерывен: он выбран из $A$, а в $A$ между $a^1$ и $a^3$, $a^3$ и $a^5$ "
        "соседние элементы соприкасаются». Найдите ошибку.",
        "По определению непрерывности (с. 87) соседними в ряду $a^1, a^3, a^5$ будут $a^1$ и $a^3$; они не соприкасаются — между ними находится индивид $a^2$. Ряд прерывен.",
        steps(["Ряд $B$: $a^1, a^3, a^5$; в нём между $a^1$ и $a^3$ нет элемента $B$, значит, $a^1 \\mid \\alpha a^3$ в $B$ (с. 85).",
               "$a^2$ — индивид подразумеваемого класса и находится между $a^1$ и $a^3$, поэтому они не соприкасаются (с. 86).",
               "Пара соседних элементов не соприкасается — ряд прерывен (с. 87–88). Студент перенёс соприкосновение соседних элементов $A$ на ряд, где соседи другие."])))
    # § 26 начало и конец
    for k in range(2):
        n = 8
        lo, hi = sorted(rnd.sample(range(1, n + 1), 2))
        if hi - lo < 2:
            hi = min(n, lo + 3)
        out.append(card(26, 1, "R", "iso", "def", "sym", "short", "с. 88, гл. 2, § 26", ["начало и конец ряда"],
            f"Ряд $A$ относительно $\\alpha$ образован индивидами $a^1, …, a^{n}$, причём $a^{{i+1}} > \\alpha a^i$. $B$ — ряд из элементов "
            f"$a^{lo}, …, a^{hi}$ того же ряда. Какой элемент $B$ — начальный и какой — конечный относительно $\\alpha$?",
            f"Начальный — $a^{lo}$, конечный — $a^{hi}$.",
            f"Начальный: любой другой элемент ряда превосходит его по порядку (с. 88) — для $a^{lo}$ это так, поскольку все $a^i$ с $i > {lo}$ "
            f"превосходят $a^{lo}$. Конечный: он превосходит все остальные (с. 88) — это $a^{hi}$."))
    out.append(card(26, 1, "E", "iso", "def", "nat", "short", "с. 89–90, гл. 2, § 26", ["начало и конец ряда", "диагностика"],
        "Студент: «Последний корабль первой колонны, прошедшей мост, и первый корабль второй колонны — один и тот же корабль: конец одного ряда всегда "
        "есть начало следующего». Найдите ошибку.",
        "С. 89–90: конечный элемент одного ряда не всегда есть начальный элемент другого; утверждение «конец одного ряда есть начало другого» либо бессмысленно, либо неверно.",
        "С. 89–90: ряд $A$ может быть таким, что с некоторого момента порядок установить невозможно, а для ряда $B$ относительно другого способа $\\beta$ "
        "из существования начального или конечного элемента $A$ не следует существование конечного или начального элемента $B$. Если тот же корабль "
        "входит в обе колонны, это особый случай, установленный не по логике, а по данным о колоннах."))
    return out


# ================================================================ § 31 структуры
def rank_text(el, ranks, w):
    """ranks: dict elem -> rank (больше ранг — выше по порядку)."""
    parts = []
    for x, y in itertools.combinations(el, 2):
        if ranks[x] == ranks[y]:
            parts.append(f"${x} = {w} {y}$")
        elif ranks[x] > ranks[y]:
            parts.append(f"${x} > {w} {y}$")
        else:
            parts.append(f"${y} > {w} {x}$")
    return ", ".join(parts)


def partner(x, el, R):
    for w, rk in R.items():
        for y in el:
            if y != x and rk[y] != rk[x]:
                return y, w
    return None


def g31():
    out = []
    S = "с. 96–97, гл. 2, § 31"
    letters = ["a", "b", "c", "d"]
    # ступень 1: структура или нет
    configs = []
    for k in range(4):
        el = letters[:rnd.choice([3, 4])]
        while True:
            R = {"\\alpha^1": {x: rnd.choice([0, 0, 1]) for x in el}, "\\alpha^2": {x: rnd.choice([0, 1, 1]) for x in el}}
            use = ["\\alpha^1"] if k % 2 == 0 else ["\\alpha^1", "\\alpha^2"]
            ok = all(partner(x, el, {w: R[w] for w in use}) for x in el)
            if ok == (k in (0, 3)) and (str(R), use) not in configs:
                configs.append((str(R), use))
                break
        RU = {w: R[w] for w in use}
        model = "; ".join(f"относительно ${w}$: " + rank_text(el, R[w], w) for w in RU)
        sol = []
        for x in el:
            pw = partner(x, el, RU)
            if pw:
                y, w = pw
                rel = f"{x} > {w} {y}" if RU[w][x] > RU[w][y] else f"{y} > {w} {x}"
                sol.append(f"для ${x}$: ${rel}$")
            else:
                sol.append(f"для ${x}$ нет другого элемента, отличного от него по порядку ни относительно одного способа из $B$")
        B = "\\{" + ", ".join(use) + "\\}"
        out.append(card(31, 1, "R", "iso", "def", "sym", "short", S, ["структура"],
            f"Скопление $A$ состоит из индивидов ${', '.join(el)}$; $B = {B}$ — класс способов установления порядка. Известно: {model}. "
            "Образуют ли элементы $A$ структуру относительно $B$ (с. 97)?",
            "Да." if ok else "Нет.",
            "Элементы $A$ образуют структуру относительно $B$, если и только если для любого элемента $a$ найдётся другой элемент $b$ и способ $\\alpha$ из $B$, "
            "что $a > \\alpha b$ или $b > \\alpha a$ (с. 97). Проверка: " + "; ".join(sol) + ". " + ("Условие выполнено." if ok else "Условие нарушено.")))
    out.append(card(31, 1, "E", "iso", "def", "nat", "short", "с. 96, гл. 2, § 31", ["структура", "диагностика"],
        "Студент: «Груда камней на берегу — структура или нет? Это можно выяснить, рассмотрев сами камни». Найдите ошибку.",
        "С. 96: индивиды скопления образуют структуру лишь относительно некоторых данных способов установления порядка; не задав (не выбрав) класс способов $B$, "
        "исследователь не имеет права спрашивать, структура ли скопление.",
        "Определение структуры (с. 96–97) содержит класс способов $B$. «Если последние не даны, ни о какой структуре и речи быть не может» (с. 96). Кроме того, "
        "для любого скопления из двух и более индивидов могут быть найдены способы, относительно которых оно будет структурой."))
    # ступень 2: подструктуры
    for k in range(6):
        el2 = letters[:4]
        el1 = sorted(rnd.sample(el2, rnd.choice([2, 3])))
        if k == 5:
            el1 = list(el2)
        R = {"\\alpha": {x: i for i, x in enumerate(rnd.sample(el2, 4))}}
        sub = set(el1) <= set(el2)
        proper = sub and not set(el2) <= set(el1)
        order = sorted(el2, key=lambda x: R["\\alpha"][x])
        chain = " < \\alpha ".join(order)
        out.append(card(31, 2, "C", "iso", "def", "sym", "short", "с. 99, гл. 2, § 31", ["структура", "подструктура"],
            f"Относительно способа $\\alpha$ индивиды упорядочены так: ${chain}$ (запись $x < \\alpha y$ — «$x$ уступает $y$ по порядку»). "
            f"$B = \\{{\\alpha\\}}$. Скопление $A^1$ — ${', '.join(el1)}$, скопление $A^2$ — ${', '.join(el2)}$; $C$ и $D$ — образуемые ими структуры относительно $B$. "
            "Является ли $C$ подструктурой $D$ относительно $B$, и если да — собственной ли?",
            ("Да; собственной." if proper else "Да, но не собственной.") if sub else "Нет.",
            steps(["Оба скопления образуют структуру: любые два элемента упорядочены относительно $\\alpha$ (с. 97).",
                   f"$A^1 \\subset A^2$: каждый элемент $A^1$ входит в $A^2$ — $C$ есть подструктура $D$ относительно $B$ (с. 99).",
                   ("${\\sim}(A^2 \\subset A^1)$: в $A^2$ есть " + f"${sorted(set(el2) - set(el1))[0]}$" + ", не входящий в $A^1$, — подструктура собственная (с. 99)."
                    if proper else "$A^2 \\subset A^1$ — условие ${\\sim}(A^2 \\subset A^1)$ не выполнено, подструктура не собственная (с. 99).")])))
    out.append(card(31, 2, "E", "iso", "def", "sym", "short", "с. 99, гл. 2, § 31", ["структура", "подструктура", "диагностика"],
        "Скопление $A^1$ из индивидов $a, b, c$ образует структуру $C$ относительно $B$, скопление $A^2$ из $a, b, c, d$ — структуру $D$ относительно того же $B$ (ср. рис. 7). "
        "Студент: «$D$ — собственная подструктура $C$: в ней больше элементов». Найдите ошибку.",
        "Перепутано направление (с. 99): при $A^1 \\subset A^2$ подструктура — $C$, а не $D$; $C$ — собственная подструктура $D$, так как ${\\sim}(A^2 \\subset A^1)$.",
        "Определение с. 99: если $A^1 \\subset A^2$, то $C$ — подструктура $D$; если ещё ${\\sim}(A^2 \\subset A^1)$, то $C$ — собственная подструктура. "
        "На рис. 7 скопление индивидов $a, b, c$ есть подструктура скопления $a, b, c, d$."))
    # ступень 3: «внутри»
    for k in range(5):
        el = ["a", "b", "c"]
        others = ["d", "e"]
        allx = el + others
        while True:
            rk = {x: rnd.randrange(5) for x in allx}
            if len({rk[x] for x in el}) == 3:
                break
        lo, hi = min(rk[x] for x in el), max(rk[x] for x in el)
        inside = all(lo < rk[x] < hi for x in others)
        order_desc = rank_text(allx, rk, "\\alpha")
        sol = []
        for x in others:
            if lo < rk[x] < hi:
                y = next(z for z in el if rk[z] == lo)
                z = next(z for z in el if rk[z] == hi)
                sol.append(f"${x}$ между ${y}$ и ${z}$: $({x} > \\alpha {y}) \\wedge ({z} > \\alpha {x})$ (с. 82)")
            else:
                sol.append(f"${x}$ не находится между элементами $A$: нет элемента $A$, который {'уступал бы' if rk[x] <= lo else 'превосходил бы'} ${x}$ по порядку")
        out.append(card(31, 3, "C", "iso", "def", "sym", "short", "с. 99, 82, гл. 2, § 31", ["структура", "внутри структуры"],
            f"$B = \\{{\\alpha\\}}$; скопление $A$ из индивидов $a, b, c$ образует структуру $C$ относительно $B$. Известно: {order_desc}. "
            "Находится ли скопление $D$ из индивидов $d, e$ внутри $C$ относительно $B$?",
            "Да." if inside else "Нет.",
            "По определению (с. 99) $D$ находится внутри $C$ относительно $B$, если и только если все элементы $D$ находятся между элементами $A$ относительно $B$. "
            + "; ".join(sol) + ". " + ("Оба элемента $D$ — между элементами $A$." if inside else "Не все элементы $D$ находятся между элементами $A$.")))
    out.append(card(31, 3, "E", "iso", "def", "sym", "short", "с. 99, гл. 2, § 31", ["структура", "объединение структур", "диагностика"],
        "Скопление $A^1$ ($a, b$) образует структуру $C^1$, скопление $A^2$ ($c, d$) — структуру $C^2$ относительно одного и того же $B$. "
        "Студент: «Объединение $C^1$ и $C^2$ — это структура из всех элементов $A^1$ и $A^2$ относительно $B$, независимо от того, являются ли $C^1$ и $C^2$ её подструктурами». Найдите ошибку.",
        "Определение объединения (с. 99) требует, чтобы $C$ была образована элементами $A^1$ и $A^2$ относительно $B$ и $C^1$, $C^2$ были подструктурами $C$; второе условие студент отбросил.",
        "С. 99: «Объединением структур $C^1$ и $C^2$ будем называть такую структуру $C$, которая образована из элементов скоплений $A^1$ и $A^2$ относительно $B$, "
        "причём $C^1$ и $C^2$ — подструктуры $C$». Подструктура определяется через $A^i \\subset A$ при одном и том же $B$ (с. 99)."))
    return out


# ================================================================ § 35 соответствие классов
def g35():
    out = []
    S = "с. 103, гл. 2, § 35"
    D = "Буквы $A$, $B$ — термины классов; известно, какие индивиды в них включаются (и только они), и какие соответствия установлены (запись $a \\Leftarrow b$ — «$b$ соответствует $a$», с. 101)."

    def model(A, B, corr):
        cs = ", ".join(f"${a} \\Leftarrow {b}$" for a, b in corr) if corr else "никаких соответствий не установлено"
        return f"{D} $A$: {', '.join('$' + x + '$' for x in A) or 'пуст'}; $B$: {', '.join('$' + x + '$' for x in B) or 'пуст'}; соответствия: {cs}."

    def check(A, B, corr):
        reasons = []
        if not A or not B:
            reasons.append("один из классов пуст")
        if set(A) & set(B):
            reasons.append(f"классы пересекаются (общий элемент ${sorted(set(A) & set(B))[0]}$)")
        miss = [a for a in A if not any(c[0] == a for c in corr)]
        if miss:
            reasons.append(f"элементу ${miss[0]}$ класса $A$ не поставлен в соответствие ни один элемент $B$")
        return reasons

    # ступень 1: A ⇐ B ?
    cfgs = [(["a_1", "a_2"], ["b_1", "b_2", "b_3"], [("a_1", "b_1"), ("a_2", "b_3")]),
            (["a_1", "a_2", "a_3"], ["b_1", "b_2"], [("a_1", "b_1"), ("a_2", "b_2")]),
            (["a_1", "c"], ["b_1", "c"], [("a_1", "b_1"), ("c", "b_1")])]
    for A, B, corr in cfgs:
        r = check(A, B, corr)
        out.append(card(35, 1, "R", "iso", "def", "sym", "short", S, ["соответствие классов"],
            model(A, B, corr) + " Верно ли, что класс $B$ поставлен в соответствие классу $A$ ($A \\Leftarrow B$)?",
            "Да." if not r else "Нет: " + r[0] + ".",
            "Определение (с. 103): $B$ поставлен в соответствие $A$, если и только если $A$ и $B$ не пересекаются, оба непусты и каждому элементу $A$ "
            "поставлен в соответствие по крайней мере один элемент $B$. " + ("Все три условия выполнены." if not r else "Нарушено: " + "; ".join(r) + ".")))
    out.append(card(35, 1, "E", "iso", "def", "sym", "short", "с. 101, 103, гл. 2, § 35", ["соответствие классов", "диагностика"],
        "Буква $A$ — термин непустого класса. Студент: «каждому элементу $A$ можно поставить в соответствие его самого, поэтому $A \\Leftarrow A$». Найдите ошибку.",
        "Следствие 4 определения (с. 103): ${\\sim}(A \\Leftarrow A)$ — класс пересекается сам с собой, а соответствие классов требует непересекающихся классов; к тому же соответствие устанавливается только между различными предметами (с. 101).",
        "Определение с. 103 требует, чтобы $A$ и $B$ не пересекались; $A$ и $A$ пересекаются (если $A$ непуст). Отсюда следствие 4: ${\\sim}(A \\Leftarrow A)$. "
        "С. 101: «предмет сам с собой не сопоставляется», соответствие устанавливается только между различными предметами."))
    # ступень 2: условия y и z
    cfgs = [(["a_1", "a_2", "a_3"], ["b_1", "b_2", "b_3"], [("a_1", "b_2"), ("a_2", "b_1"), ("a_3", "b_3")]),
            (["a_1", "a_2"], ["b_1", "b_2", "b_3"], [("a_1", "b_1"), ("a_1", "b_2"), ("a_2", "b_3")]),
            (["a_1", "a_2", "a_3"], ["b_1", "b_2"], [("a_1", "b_1"), ("a_2", "b_1"), ("a_3", "b_2")]),
            (["a_1", "a_2"], ["b_1", "b_2", "b_3"], [("a_1", "b_3"), ("a_2", "b_1")])]
    for A, B, corr in cfgs:
        y = all(sum(1 for c in corr if c[0] == a) == 1 for a in A)
        img = {}
        for a, b in corr:
            img.setdefault(a, set()).add(b)
        z = all(not (img[a1] & img[a2]) for a1, a2 in itertools.combinations(A, 2))
        sol = []
        if y:
            sol.append("$y$: каждому элементу $A$ поставлен в соответствие ровно один элемент $B$ — выполнено.")
        else:
            a = next(a for a in A if sum(1 for c in corr if c[0] == a) != 1)
            bs = sorted(img.get(a, []))
            sol.append(f"$y$: элементу ${a}$ поставлены в соответствие ${bs[0]}$ и ${bs[1]}$, а по $y$ из $(a \\Leftarrow b) \\wedge (a \\Leftarrow c)$ следует $b \\rightleftharpoons c$ — не выполнено.")
        if z:
            sol.append("$z$: разным элементам $A$ поставлены в соответствие разные элементы $B$ — выполнено.")
        else:
            a1, a2 = next((p, q) for p, q in itertools.combinations(A, 2) if img[p] & img[q])
            sol.append(f"$z$: разным ${a1}$ и ${a2}$ соответствует один и тот же ${sorted(img[a1] & img[a2])[0]}$ — не выполнено.")
        out.append(card(35, 2, "C", "iso", "def", "sym", "short", S, ["соответствие классов", "однозначное соответствие"],
            model(A, B, corr) + " Выполнены ли условия $y$ («каждому элементу $A$ ставится в соответствие один и только один элемент $B$») и $z$ («разным элементам $A$ ставятся в соответствие разные элементы $B$», с. 103)?",
            f"$y$ — {'да' if y else 'нет'}; $z$ — {'да' if z else 'нет'}.",
            "Условия $y$ и $z$ — с. 103.\n" + "\n".join(sol)))
    out.append(card(35, 2, "E", "iso", "def", "sym", "short", S, ["соответствие классов", "диагностика"],
        "Буквы $A$, $B$ — термины классов, $A \\subset B$, оба непусты. Студент: «каждому элементу $A$ поставим в соответствие его самого как элемент $B$; значит, $A \\Leftarrow B$». Найдите ошибку.",
        "Следствие 3 (с. 103): если $A \\subset B$, то ${\\sim}(A \\Leftarrow B) \\wedge {\\sim}(B \\Leftarrow A)$ — непустой подкласс пересекается с классом.",
        "По определению (с. 103) соответствие классов требует, чтобы классы не пересекались. При $A \\subset B$ и непустом $A$ любой элемент $A$ входит в $B$ — классы "
        "пересекаются. Отсюда следствие 3: ${\\sim}(A \\Leftarrow B) \\wedge {\\sim}(B \\Leftarrow A)$."))
    # ступень 3: однозначное соответствие и мощность
    cfgs = [(["a_1", "a_2"], ["b_1", "b_2", "b_3"], [("a_1", "b_2"), ("a_2", "b_3")], True),
            (["a_1", "a_2", "a_3"], ["b_1", "b_2", "b_3"], [("a_1", "b_1"), ("a_2", "b_1"), ("a_3", "b_3")], False),
            (["a_1", "a_2"], ["b_1", "a_2"], [("a_1", "b_1"), ("a_2", "b_1")], False),
            (["a_1", "a_2", "a_3"], ["b_1", "b_2", "b_3", "b_4"], [("a_1", "b_4"), ("a_2", "b_2"), ("a_3", "b_1")], True)]
    for A, B, corr, exp in cfgs:
        r = check(A, B, corr)
        img = {}
        for a, b in corr:
            img.setdefault(a, set()).add(b)
        y = all(len(img.get(a, ())) == 1 for a in A)
        z = all(not (img.get(p, set()) & img.get(q, set())) for p, q in itertools.combinations(A, 2))
        ok = not r and y and z
        assert ok == exp
        sol = ["$x$: " + ("$A$ и $B$ непусты и не пересекаются — выполнено." if not [t for t in r if "пуст" in t or "пересека" in t] else
                          [t for t in r if "пуст" in t or "пересека" in t][0] + " — не выполнено."),
               "$y$: " + ("выполнено." if y else "не выполнено."),
               "$z$: " + ("выполнено." if z else "не выполнено — разным элементам $A$ соответствует один элемент $B$."),
               ("$(A \\langle\\equiv B) \\equiv Df.(x \\wedge y \\wedge z)$ (с. 104): $A \\langle\\equiv B$. По утверждению 3 (с. 104) $\\vdash (A \\langle\\equiv B) \\to (A \\urcorner > mB)$: $A \\urcorner > mB$."
                if ok else "Конъюнкция $x \\wedge y \\wedge z$ неверна, поэтому $A \\langle\\equiv B$ по определению (с. 104) не имеет места; утверждение 3 применить нельзя.")]
        out.append(card(35, 3, "D", "iso", "def", "sym", "short", "с. 103–104, гл. 2, § 35", ["однозначное соответствие", "мощность"],
            model(A, B, corr) + " Соответствует ли $B$ классу $A$ однозначно ($A \\langle\\equiv B$)? Если да, что следует о мощностях $A$ и $B$ по утверждениям 1–9 (с. 104)?",
            ("Да; $A \\urcorner > mB$." if ok else "Нет; о мощностях по утверждению 3 ничего не следует."),
            steps(sol)))
    out.append(card(35, 3, "E", "iso", "def", "sym", "short", "с. 104, гл. 2, § 35", ["мощность", "диагностика"],
        "Классы $A$ и $B$ эквивалентны и непусты. Студент рассуждает: «Эквивалентные классы пересекаются, поэтому между ними нет соответствия; "
        "по утверждению 9 они не находятся во взаимнооднозначном соответствии, значит, не равномощны». Найдите ошибку.",
        "Утверждение 9 (с. 104) — $(A \\langle\\equiv\\rangle B) \\to (A = mB)$; из отсутствия соответствия неравномощность не следует. Равномощность эквивалентных классов — следствие 6 из утверждения 1 (с. 104).",
        steps(["Соответствие классов действительно требует непересекающихся классов (с. 103), так что ${\\sim}(A \\langle\\equiv\\rangle B)$ верно.",
               "Утверждение 9 — условное: из его антецедента следует консеквент, но из отрицания антецедента отрицание консеквента не следует.",
               "Для эквивалентных классов по утверждению 1 (с. 104) $A \\urcorner > mB$ и $B \\urcorner > mA$ — отсюда следствие 6: эквивалентные классы равномощны."])))
    return out


def main():
    cards = g05() + g06() + g09() + g11() + g16() + g18() + g23_26() + g31() + g35()
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from g18_open import process_card  # условия без «тестовой» формы
    cards = [process_card(c) for c in cards]
    path = ROOT / "drafts" / "18-gen.md"
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n=====\n\n".join(cards), encoding="utf-8")
    print(f"Карточек: {len(cards)} → {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
