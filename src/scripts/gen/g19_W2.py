"""Задачи раздела 19 (ЛФ, гл. 3), § 13, 14, 17, 19, 20: сгенерированные и проверенные программой карточки.

  python3 src/scripts/gen/g19_W2.py OUTDIR   — пишет OUTDIR/19.PP-gen.md для PP = 13, 14, 17, 19, 20

§ 14 — выводы о пространственных (временных) интервалах по аксиомам сложения, деления, X^1, X^2 (с. 136)
с правилами уместности (с. 146) и транзитивности порядка (аксиома УП, аналогичная C4, с. 79, 82);
§ 17 — выводы из утверждений 1, 4, 5, 6 (с. 140) по правилам Д^i, У^i (с. 34–35);
§ 19 — значения и принятие формул при трёх (неклассический случай) и двух (классический) возможностях (с. 144);
§ 13 — проверка части определения «порождает» (с. 135) на таблице существования;
§ 20 — проверка условий процесса (с. 144).
Вывод проверяется lf_engine.check; опровержение — замкнутым множеством фактов.
"""
import itertools
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lf_engine  # noqa: E402

rnd = random.Random(1972_19)


def card(meta, cond, ans, sol):
    head = {"chapter": 19, "step": "iso", "condition": "def", "form": "sym", "answer": "proof", "generated": True}
    head.update(meta)
    order = ["chapter", "section", "level", "type", "step", "condition", "form", "answer", "source", "case", "generated",
             "tags"]
    lines = ["---"]
    for k in order:
        if k not in head:
            continue
        v = head[k]
        if k == "tags":
            lines.append(f"tags: [{', '.join(v)}]")
        elif k == "source":
            lines.append(f'source: "{v}"')
        elif isinstance(v, bool):
            lines.append(f"{k}: {'true' if v else 'false'}")
        else:
            lines.append(f"{k}: {v}")
    lines.append("---")
    return "\n".join(lines) + f"\n\n## Условие\n\n{cond.strip()}\n\n## Ответ\n\n{ans.strip()}\n\n## Решение\n\n{sol.strip()}\n"


# =============================================================== § 14: интервалы

def iv(a, b):
    return ("I", a, b)


def gt(a, b):
    return ("G", a, b)


def r_add(p):
    (f, g) = p
    if f[0] == g[0] == "I" and f[2] == g[1] and f[1] != g[2]:
        return iv(f[1], g[2])


def r_div1(p):
    (f, g, h) = p
    if f[0] == g[0] == "G" and h[0] == "I" and f[2] == g[1] and h[1] == f[1] and h[2] == g[2]:
        return iv(f[1], f[2])


def r_div2(p):
    (f, g, h) = p
    if f[0] == g[0] == "G" and h[0] == "I" and f[2] == g[1] and h[1] == f[1] and h[2] == g[2]:
        return iv(g[1], g[2])


def r_x1(p):
    (f, g, h) = p
    if f[0] == g[0] == "I" and h[0] == "G" and h[1] == f[2] and h[2] == g[1] and f != g:
        return iv(f[2], g[1])


def r_x2(p):
    (f, g, h) = p
    if f[0] == g[0] == "I" and h[0] == "G" and h[1] == f[2] and h[2] == g[1] and f != g:
        return iv(f[1], g[2])


def r_tr(p):
    (f, g) = p
    if f[0] == g[0] == "G" and f[2] == g[1] and f[1] != g[2]:
        return gt(f[1], g[2])


def r_um(p):
    (f,) = p
    if f[0] == "I":
        return gt(f[1], f[2])


R_COMMON = [("уместность", 1, r_um), ("транзитивность", 2, r_tr)]
PATH1 = [("сложение", 2, r_add), ("$X^1$", 3, r_x1)] + R_COMMON
PATH2 = [("деление", 3, r_div1), ("деление", 3, r_div2), ("$X^2$", 3, r_x2)] + R_COMMON
ALL = [("сложение", 2, r_add), ("$X^1$", 3, r_x1), ("деление", 3, r_div1), ("деление", 3, r_div2), ("$X^2$", 3, r_x2)] + R_COMMON

KIND = {"s": ("пространственный интервал", "пространственные интервалы", "способ установления пространственного порядка"),
        "t": ("временной интервал", "временные интервалы", "способ установления временного порядка")}


def fact_tex(f, kind="s"):
    if f[0] == "I":
        return f"$\\{{{f[1]}, {f[2]}, \\alpha\\}}$ — {KIND[kind][0]}"
    return f"${f[1]} > \\alpha {f[2]}$"


def rules_text(rules, kind="s"):
    one, many = KIND[kind][0], KIND[kind][1]
    parts = {
        "сложение": f"аксиома сложения интервалов: если $\\{{a, b, \\alpha\\}}$ и $\\{{b, c, \\alpha\\}}$ — {many}, то $\\{{a, c, \\alpha\\}}$ — {one}",
        "деление": f"аксиома деления интервалов: если $a > \\alpha b$, $b > \\alpha c$ и $\\{{a, c, \\alpha\\}}$ — {one}, то $\\{{a, b, \\alpha\\}}$ и $\\{{b, c, \\alpha\\}}$ — {many}",
        "$X^1$": f"аксиома $X^1$: если $\\{{a, b, \\alpha\\}}$ и $\\{{c, d, \\alpha\\}}$ — {many} и $b > \\alpha c$, то $\\{{b, c, \\alpha\\}}$ — {one}",
        "$X^2$": f"аксиома $X^2$: если $\\{{a, b, \\alpha\\}}$ и $\\{{c, d, \\alpha\\}}$ — {many} и $b > \\alpha c$, то $\\{{a, d, \\alpha\\}}$ — {one}",
        "уместность": "уместность (с. 146): выражение «интервал $\\{a, b, \\alpha\\}$» уместно лишь при $a > \\alpha b$, так что из «$\\{a, b, \\alpha\\}$ — интервал» берём $a > \\alpha b$",
        "транзитивность": "транзитивность: $(a > \\alpha b) \\wedge (b > \\alpha c) \\vdash (a > \\alpha c)$ (аксиома УП, аналогичная C4, с. 79, 82)",
    }
    names = []
    for n, _, _ in rules:
        if n not in names:
            names.append(n)
    return "; ".join(f"({i + 1}) {parts[n]}" for i, n in enumerate(names))


def proof_lines(goal, how, kind="s"):
    pl = lf_engine.proof(goal, how)
    return pl


def render(pl, kind="s", hide_base=(), hide_formula=()):
    out = []
    for i, (f, name, refs) in enumerate(pl, 1):
        ft = "…" if i in hide_formula else fact_tex(f, kind)
        if name == "посылка":
            base = "посылка"
        else:
            base = (", ".join(map(str, refs)) + "; " if refs else "") + name
        b = "…" if i in hide_base else base
        out.append(f"{i}. {ft} [{b}]")
    return "\n".join(out)


LETTERS = "abcdef"


def make_premises(rnd, n_iv=3, n_gt=1):
    # линейный порядок букв: a > b > c > d > e > f (буквы переставляются)
    order = list(LETTERS)
    rnd.shuffle(order)
    prem = set()
    while len(prem) < n_iv:
        i, j = sorted(rnd.sample(range(6), 2))
        if j - i <= 2:
            prem.add(iv(order[i], order[j]))
    while len(prem) < n_iv + n_gt:
        i, j = sorted(rnd.sample(range(6), 2))
        prem.add(gt(order[i], order[j]))
    return order, sorted(prem)


def find_task(rules, minlen, maxlen, want_iv=True, tries=4000, derivable=True, kinds=1):
    for _ in range(tries):
        order, prem = make_premises(rnd, rnd.choice([2, 3, 4]), rnd.choice([0, 1, 2, 2, 3]))
        how = lf_engine.closure(prem, rules, limit=300)
        cands = []
        for f in how:
            if f in prem or (want_iv and f[0] != "I"):
                continue
            pl = lf_engine.proof(f, how)
            if minlen <= len(pl) <= maxlen:
                used = {p[0] for p in pl if p[1] == "посылка"}
                names = {p[1] for p in pl if p[1] != "посылка"}
                if used == set(prem) and len(names) >= kinds:
                    cands.append((f, pl))
        if derivable and cands:
            f, pl = rnd.choice(cands)
            return prem, f, pl, how
        if not derivable:
            # недоказуемая цель: интервал между буквами, которого нет в замыкании, но «правдоподобный»
            ivs = [iv(order[i], order[j]) for i in range(6) for j in range(i + 1, 6)]
            letters = {x for p in prem for x in p[1:]}
            miss = [g for g in ivs if g not in how and g[1] in letters and g[2] in letters]
            if miss and len([f for f in how if f[0] == "I"]) >= len([p for p in prem if p[0] == "I"]) + 2:
                return prem, rnd.choice(miss), None, how
    raise SystemExit("нет задачи")


def check_lines(pl, rules, prem):
    """Номера строк с неверным основанием (правила с одинаковым именем перебираются все)."""
    bad = []
    for i, (f, name, refs) in enumerate(pl, 1):
        if name == "посылка":
            if f not in prem:
                bad.append(i)
            continue
        if any(r >= i or r < 1 for r in refs):
            bad.append(i)
            continue
        args = tuple(pl[r - 1][0] for r in refs)
        if not any(n == name and k == len(refs) and fn(args) == f for n, k, fn in rules):
            bad.append(i)
    return bad


def check_pl(pl, rules, prem):
    bad = check_lines(pl, rules, set(prem))
    assert not bad, (bad, pl)


def prem_text(prem, kind="s"):
    return "; ".join(fact_tex(p, kind) for p in prem)


def s14_cards():
    out = []
    src = "с. 136, 146, гл. 3, § 14; с. 79, 82"
    intro = ("Буквы $a, b, c, d, e, f$ — эмпирические предметы, $\\alpha$ — {sp}. По с. 136 возможны два пути: "
             "аксиома сложения с аксиомой непрерывности $X^1$ или аксиома деления с аксиомой непрерывности $X^2$. "
             "Буквы в формулировках правил — любые предметы.")

    # 1. ступень 3: короткий вывод, путь 1
    prem, goal, pl, how = find_task(PATH1, 5, 7, kinds=2)
    check_pl(pl, PATH1, prem)
    cond = (intro.format(sp=KIND["s"][2]) + " Примем первый путь. Разрешены: " + rules_text(PATH1) + ". "
            f"Посылки: {prem_text(prem)}. Выведите: {fact_tex(goal)}. Пронумеруйте строки и укажите основание каждой.")
    out.append(card(dict(section=14, level=3, type="D", tags=["непрерывность", "интервал", "вывод"], source=src),
                    cond, f"Вывод в {len(pl)} строк, последняя — {fact_tex(goal)} (см. решение).",
                    render(pl) + "\n\nИсточник: с. 136 (аксиомы), с. 146 (уместность), с. 79, 82 (транзитивность)."))

    # 2. ступень 4: дополнение, путь 2, скрыты основания и формулы
    while True:
        prem, goal, pl, how = find_task(PATH2, 8, 11, kinds=3)
        if sum(1 for l in pl if l[1] != "посылка") >= 5:
            break
    check_pl(pl, PATH2, prem)
    n = len(pl)
    inner = [i for i in range(1, n + 1) if pl[i - 1][1] != "посылка"]
    hb = set(rnd.sample(inner[:-1], 2))
    hf = set(rnd.sample([i for i in inner[:-1] if i not in hb], 2))
    cond = (intro.format(sp=KIND["s"][2]) + " Примем второй путь. Разрешены: " + rules_text(PATH2) + ". "
            "В выводе ниже пропущены основания двух строк и формулы двух других строк (отмечены «…»). Восстановите их.\n\n"
            + render(pl, hide_base=hb, hide_formula=hf))
    ans = "; ".join([f"строка {i}: {fact_tex(pl[i - 1][0])}" for i in sorted(hf)] +
                    [f"основание {i}: {', '.join(map(str, pl[i - 1][2]))}; {pl[i - 1][1]}" for i in sorted(hb)])
    out.append(card(dict(section=14, level=4, type="D", step="complete", tags=["непрерывность", "интервал", "дополнение"],
                         source=src), cond, ans, render(pl) + "\n\nИсточник: с. 136, 146; с. 79, 82."))

    # 3. ступень 5: длинный вывод, путь 1
    prem, goal, pl, how = find_task(PATH1, 7, 11, kinds=2)
    check_pl(pl, PATH1, prem)
    cond = (intro.format(sp=KIND["s"][2]) + " Примем первый путь. Разрешены: " + rules_text(PATH1) + ". "
            f"Посылки: {prem_text(prem)}. Выведите: {fact_tex(goal)}. Пронумеруйте строки и укажите основание каждой.")
    out.append(card(dict(section=14, level=5, type="D", step="vary", tags=["непрерывность", "интервал", "вывод"], source=src),
                    cond, f"Вывод в {len(pl)} строк, последняя — {fact_tex(goal)} (см. решение).",
                    render(pl) + "\n\nИсточник: с. 136, 146; с. 79, 82."))

    # 4. ступень 6: открытый исход, недоказуемо (путь 2)
    prem, goal, _, how = find_task(PATH2, 0, 0, derivable=False)
    facts = sorted(how)
    cond = (intro.format(sp=KIND["s"][2]) + " Примем второй путь. Разрешены: " + rules_text(PATH2) + ". "
            f"Посылки: {prem_text(prem)}. Исследуйте, выводится ли {fact_tex(goal)}: если да — постройте вывод, "
            "если нет — докажите, что вывода нет.")
    fl = "; ".join(fact_tex(f) for f in facts)
    sol = (f"1. Рассмотрим множество утверждений $M$: {fl}.\n"
           "2. $M$ содержит все посылки и замкнуто относительно разрешённых правил: применение любого правила "
           "к утверждениям из $M$ даёт утверждение из $M$ (проверяется перебором всех применений).\n"
           "3. Значит, каждая строка любого вывода из посылок лежит в $M$.\n"
           f"4. Утверждение «{fact_tex(goal)}» не входит в $M$. Вывода нет.\n\nИсточник: с. 136, 146; с. 79, 82.")
    out.append(card(dict(section=14, level=6, type="C", step="open", tags=["непрерывность", "интервал", "открытый исход"],
                         source=src), cond, f"Не выводится: множество из {len(facts)} утверждений (см. решение) содержит "
                                            "посылки, замкнуто относительно правил и не содержит цели.", sol))

    # 5. ступень 6: диагностика, две ошибки
    for _ in range(200):
        try:
            prem, goal, pl, how = find_task(PATH1, 7, 10, kinds=2)
            check_pl(pl, PATH1, prem)
            bad_pl = list(pl)
            inner = [i for i in range(1, len(pl)) if pl[i - 1][1] != "посылка"]
            # ошибка 1: неверное название правила (сложение <-> X^1 или транзитивность <-> уместность)
            swap = {"сложение": "$X^1$", "$X^1$": "сложение", "транзитивность": "сложение", "уместность": "$X^1$"}
            e1 = rnd.choice(inner)
            f, nm, refs = bad_pl[e1 - 1]
            bad_pl[e1 - 1] = (f, swap[nm], refs)
            # ошибка 2: последняя строка (цель) «получена сложением» двух несмежных интервалов
            goal_f = pl[-1][0]
            extra = None
            for i1, l1 in enumerate(pl[:-1], 1):
                for i2, l2 in enumerate(pl[:-1], 1):
                    f1, f2 = l1[0], l2[0]
                    if f1[0] == f2[0] == "I" and f1[1] == goal_f[1] and f2[2] == goal_f[2] and f1[2] != f2[1] and i1 != i2:
                        extra = (goal_f, "сложение", (i1, i2))
                        break
                if extra:
                    break
            if not extra or e1 == len(pl):
                raise RuntimeError("retry")
            bad_pl = bad_pl[:-1] + [extra]
            e2 = len(bad_pl)
            break
        except RuntimeError:
            continue
    badlines = check_lines(bad_pl, PATH1, set(prem))
    assert set(badlines) == {e1, e2}, (badlines, e1, e2)
    cond = (intro.format(sp=KIND["s"][2]) + " Примем первый путь. Разрешены: " + rules_text(PATH1) + ". "
            f"Студент из посылок {prem_text(prem)} получил вывод:\n\n" + render(bad_pl) +
            "\n\nНайдите все ошибки и назовите нарушенное правило книги.")
    n1 = pl[e1 - 1][1]
    a1, a2 = extra[2]
    ans = (f"Строка {e1}: правило названо неверно — это {n1}; строка {e2}: аксиома сложения (с. 136) требует смежных "
           f"интервалов $\\{{a, b, \\alpha\\}}$, $\\{{b, c, \\alpha\\}}$, а интервалы строк {a1} и {a2} не смежны — цель не обоснована.")
    sol = (f"Проверка строк по правилам. Строка {e1}: {fact_tex(pl[e1 - 1][0])} получается из строк "
           f"{', '.join(map(str, pl[e1 - 1][2]))} по правилу «{n1}», а не «{swap[n1]}». "
           f"Строка {e2}: {fact_tex(extra[0])} записана по сложению из строк {a1} ({fact_tex(bad_pl[a1 - 1][0])}) и "
           f"{a2} ({fact_tex(bad_pl[a2 - 1][0])}); правый конец первого интервала не совпадает с левым концом второго, "
           "так что аксиома сложения (с. 136) неприменима. Верный вывод цели:\n\n" + render(pl) +
           "\n\nИсточник: с. 136, 146; с. 79, 82.")
    out.append(card(dict(section=14, level=6, type="E", step="vary", answer="short",
                         tags=["непрерывность", "интервал", "диагностика"], source=src), cond, ans, sol))

    # 6. ступень 6: перенос на время (путь 2), естественный язык событий
    prem, goal, pl, how = find_task(PATH2, 7, 10, kinds=3)
    check_pl(pl, PATH2, prem)
    cond = ("Буквы $a, b, c, d, e, f$ — события (вспышки), $\\alpha$ — способ установления временного порядка; "
            "$u > \\alpha v$ читается «$u$ позже $v$» (с. 123). По с. 136 сказанное об интервалах пространства "
            "«совершенно аналогично» для времени. Примем второй путь (деление и $X^2$). Разрешены: " +
            rules_text(PATH2, "t") + f". Посылки: {prem_text(prem, 't')}. Выведите: {fact_tex(goal, 't')}. "
            "Укажите основание каждой строки.")
    out.append(card(dict(section=14, level=6, type="D", step="transfer", tags=["непрерывность", "время", "вывод"],
                         source="с. 136, 123, 146, гл. 3, § 7, 14"),
                    cond, f"Вывод в {len(pl)} строк, последняя — {fact_tex(goal, 't')} (см. решение).",
                    render(pl, "t") + "\n\nИсточник: с. 136 («аналогично для времени»), с. 123 (чтение $>$), с. 146."))
    return out


# =============================================================== § 17: утверждения о предикате изменения

X, Y = ("v", "x"), ("v", "y")


def N(f):
    return ("n", f)


def AND(f, g):
    return ("and", f, g)


def OR(f, g):
    return ("or", f, g)


def IMP(f, g):
    return ("imp", f, g)


def CH(p, q):
    return ("ch", p, q)


def tex(f, top=False):
    k = f[0]
    if k == "v":
        return f[1]
    if k == "n":
        g = f[1]
        inner = tex(g)
        if g[0] in ("v", "ch"):
            return "{\\sim}" + inner
        if g[0] == "n":
            return "{\\sim}" + inner
        return "{\\sim}(" + inner + ")"
    if k == "ch":
        def st(p):
            return "s" + tex(p)
        return f"({st(f[1])} \\Rightarrow {st(f[2])})"

    def par(g):
        return "(" + tex(g) + ")" if g[0] in ("and", "or", "imp") else tex(g)
    if k == "and":
        return f"{par(f[1])} \\wedge {par(f[2])}"
    if k == "or":
        return f"{par(f[1])} \\vee {par(f[2])}"
    if k == "imp":
        return f"{par(f[1])} \\to {par(f[2])}"


def th(f):
    return f"$\\vdash {tex(f)}$"


def subst(f, s):
    k = f[0]
    if k == "v":
        return s.get(f[1], f)
    return (k,) + tuple(subst(g, s) for g in f[1:])


def dneg(f):
    if f[0] == "n" and f[1][0] == "n":
        return dneg(f[1][1])
    if f[0] == "v":
        return f
    return (f[0],) + tuple(dneg(g) for g in f[1:])


def has_dneg(f):
    if f[0] == "n" and f[1][0] == "n":
        return True
    return f[0] != "v" and any(has_dneg(g) for g in f[1:])


AX = {
    1: IMP(CH(X, Y), N(CH(X, N(Y)))),
    4: IMP(N(Y), N(CH(X, Y))),
    5: IMP(X, N(CH(X, Y))),
    6: IMP(CH(X, Y), AND(CH(X, N(X)), CH(N(Y), Y))),
}
LITS = {"x": [X, N(X), Y, N(Y)], "y": [Y, N(Y), X, N(X)]}


def ax_instances(nums):
    out = {}
    for n in nums:
        for sx in LITS["x"][:2] + ([N(Y)] if n == 5 else []):
            for sy in LITS["y"][:2] + ([N(X)] if n == 4 else []):
                f = subst(AX[n], {"x": sx, "y": sy})
                s = []
                if sx != X:
                    s.append(f"$x$ — ${tex(sx)}$")
                if sy != Y:
                    s.append(f"$y$ — ${tex(sy)}$")
                lab = f"схема {n}" + (" при замене " + ", ".join(s) if s else "")
                out[f] = (lab, ())
    return out


def c_contra(p):
    (f,) = p
    if f[0] == "imp":
        return IMP(N(f[2]), N(f[1]))


def c_dn(p):
    (f,) = p
    if has_dneg(f):
        return dneg(f)


def c_trans(p):
    (f, g) = p
    if f[0] == g[0] == "imp" and f[2] == g[1] and f[1] != g[2]:
        return IMP(f[1], g[2])


def c_join(p):
    (f, g) = p
    if f[0] == g[0] == "imp" and f[1] == g[1] and f[2] != g[2] and repr(f[2]) < repr(g[2]):
        return IMP(f[1], AND(f[2], g[2]))


def c_split1(p):
    (f,) = p
    if f[0] == "imp" and f[2][0] == "and":
        return IMP(f[1], f[2][1])


def c_split2(p):
    (f,) = p
    if f[0] == "imp" and f[2][0] == "and":
        return IMP(f[1], f[2][2])


def c_or(p):
    (f, g) = p
    if f[0] == g[0] == "imp" and f[2] == g[2] and f[1] != g[1] and repr(f[1]) < repr(g[1]):
        return IMP(OR(f[1], g[1]), f[2])


def size(f):
    return 1 if f[0] == "v" else 1 + sum(size(g) for g in f[1:])


def lim(fn, m=13):
    def g(p):
        r = fn(p)
        if r is not None and size(r) <= m:
            return r
    return g


R17 = [("У$^3$, Д$^{14}$", 1, lim(c_contra)), ("Д$^1$, Д$^{11}$", 1, lim(c_dn)),
       ("Д$^{16}$, У$^4$, Д$^{14}$", 2, lim(c_trans)), ("Д$^{16}$, У$^5$, Д$^{14}$", 2, lim(c_join)),
       ("У$^5$, Д$^2$, Д$^{8}$, Д$^{14}$", 1, lim(c_split1)), ("У$^5$, Д$^2$, Д$^{8}$, Д$^{14}$", 1, lim(c_split2)),
       ("Д$^{16}$, У$^6$, Д$^{14}$", 2, lim(c_or))]

RULES17_TEXT = ("правила гл. 1 (с. 34–35): Д$^1$ ${\\sim}{\\sim}x \\dashv\\vdash x$ и Д$^{11}$ (замена в любом месте "
                "равносильным); Д$^2$ $x \\wedge y \\vdash x$ (и $\\vdash y$); Д$^8$ «если $x \\vdash y$ и $y \\vdash z$, то $x \\vdash z$»; "
                "Д$^{14}$ «если $x \\vdash y$ и $\\vdash x$, то $\\vdash y$»; Д$^{16}$ «если $\\vdash x$ и $\\vdash y$, то "
                "$\\vdash x \\wedge y$»; У$^3$ $(x \\to y) \\vdash ({\\sim}y \\to {\\sim}x)$; У$^4$ $(x \\to y) \\wedge (y \\to z) \\vdash "
                "(x \\to z)$; У$^5$ $(x \\to y \\wedge z) \\dashv\\vdash (x \\to y) \\wedge (x \\to z)$; У$^6$ $(x \\vee y \\to z) "
                "\\dashv\\vdash (x \\to z) \\wedge (y \\to z)$")
AX17_TEXT = ("утверждения из имплицитного определения предиката изменения (с. 140): "
             "1. $\\vdash (sx \\Rightarrow sy) \\to {\\sim}(sx \\Rightarrow s{\\sim}y)$; "
             "4. $\\vdash {\\sim}y \\to {\\sim}(sx \\Rightarrow sy)$; 5. $\\vdash x \\to {\\sim}(sx \\Rightarrow sy)$; "
             "6. $\\vdash (sx \\Rightarrow sy) \\to ((sx \\Rightarrow s{\\sim}x) \\wedge (s{\\sim}y \\Rightarrow sy))$ "
             "(буквы $x, y$ — любые высказывания, в том числе ${\\sim}x$, ${\\sim}y$)")
INTRO17 = ("Буквы $x, y$ — высказывания; $sx$, $sy$ — состояния; $(sx \\Rightarrow sy)$ — «$sx$ превращается в $sy$». "
           "Даны " + AX17_TEXT + " и " + RULES17_TEXT + ". Каждая строка вывода — теорема вида $\\vdash \\ldots$; основание "
           "строки — номера строк и применённые правила (например, [2; У$^3$, Д$^{14}$]); подстановка в схему "
           "указывается как «схема 4 при замене $y$ — ${\\sim}x$».")


def render17(pl, hide_base=(), hide_formula=()):
    out = []
    for i, (f, name, refs) in enumerate(pl, 1):
        ft = "…" if i in hide_formula else th(f)
        base = (", ".join(map(str, refs)) + "; " if refs else "") + name
        out.append(f"{i}. {ft} [{'…' if i in hide_base else base}]")
    return "\n".join(out)


def proof17(goal, nums):
    extra = ax_instances(nums)
    how = lf_engine.closure([], R17, limit=900, extra=extra)
    assert goal in how, tex(goal)
    order = []
    seen = set()

    def visit(f):
        if f in seen:
            return
        for p in how[f][1]:
            visit(p)
        seen.add(f)
        order.append(f)
    visit(goal)
    num = {f: i + 1 for i, f in enumerate(order)}
    pl = [(f, how[f][0], tuple(num[p] for p in how[f][1])) for f in order]
    # проверка: каждая не-аксиомная строка — по правилу
    rules = {n: fn for n, _, fn in R17}
    for i, (f, name, refs) in enumerate(pl, 1):
        if name.startswith("схема"):
            assert f in extra
            continue
        fn = None
        ok = False
        for n, k, fn in R17:
            if n == name and len(refs) == k and fn(tuple(pl[r - 1][0] for r in refs)) == f:
                ok = True
        assert ok, (i, name)
    return pl


def s17_cards():
    out = []
    src = "с. 140, гл. 3, § 17; с. 34–35"
    C = CH(X, Y)
    # 1. дополнение: ⊢ (sx⇒sy) → (~x ∧ y)
    g1 = IMP(C, AND(N(X), Y))
    pl = proof17(g1, [4, 5])
    n = len(pl)
    inner = [i for i in range(1, n + 1) if not pl[i - 1][1].startswith("схема")]
    hb = set(rnd.sample(inner, 3))
    hf = set(rnd.sample([i for i in range(1, n) if i not in hb], 2))
    cond = (INTRO17 + " В выводе теоремы " + th(g1) + " («если $sx$ превращается в $sy$, то неверно $x$ и верно $y$») "
            "пропущены основания трёх строк и формулы двух строк (отмечены «…»). Восстановите их.\n\n" +
            render17(pl, hb, hf))
    ans = "; ".join([f"строка {i}: {th(pl[i - 1][0])}" for i in sorted(hf)] +
                    [f"основание {i}: {(', '.join(map(str, pl[i - 1][2])) + '; ') if pl[i - 1][2] else ''}{pl[i - 1][1]}"
                     for i in sorted(hb)])
    out.append(card(dict(section=17, level=4, type="D", step="complete", tags=["изменение", "дополнение", "вывод"],
                         source=src), cond, ans, render17(pl) + "\n\nИсточник: утверждения 4, 5 — с. 140; правила — с. 34–35."))

    # 2. дополнение: ⊢ (x ∨ ~y) → ~(sx⇒sy) ∧ ... — берём ⊢ (sx⇒sy) → ((sx⇒s~x) ∧ ~x)
    g2 = IMP(C, AND(CH(X, N(X)), N(X)))
    pl = proof17(g2, [5, 6])
    n = len(pl)
    hb = set(rnd.sample([i for i in range(1, n + 1)], 3))
    cond = (INTRO17 + " Ниже — вывод теоремы " + th(g2) + "; основания трёх строк пропущены («…»). Восстановите их "
            "и прочтите теорему на обычном языке, взяв $x$ — «вода в сосуде жидкая», $y$ — «вода в сосуде твёрдая».\n\n"
            + render17(pl, hb))
    ans = ("; ".join(f"основание {i}: {(', '.join(map(str, pl[i - 1][2])) + '; ') if pl[i - 1][2] else ''}{pl[i - 1][1]}"
                     for i in sorted(hb)) + ". Чтение: «если жидкая вода превращается в твёрдую, то жидкая вода исчезает "
           "и неверно, что вода жидкая»."[:400])
    out.append(card(dict(section=17, level=4, type="D", step="complete", form="nat",
                         tags=["изменение", "дополнение", "чтение"], source=src), cond, ans,
                    render17(pl) + "\n\nЧтение $(sx \\Rightarrow s{\\sim}x)$ — «$sx$ исчезает» (с. 113, 141). "
                                   "Источник: утверждения 5, 6 — с. 140; правила — с. 34–35."))

    # 3. ступень 5: короткий вывод ⊢ ~(sx⇒s~x) → ~(sx⇒sy)
    g3 = IMP(N(CH(X, N(X))), N(C))
    pl = proof17(g3, [6])
    cond = (INTRO17 + " Выведите " + th(g3) + " («если $sx$ не исчезает, то $sx$ не превращается в $sy$»).")
    out.append(card(dict(section=17, level=5, type="D", step="vary", tags=["изменение", "вывод"], source=src),
                    cond, f"Вывод в {len(pl)} строки (см. решение).", render17(pl) + "\n\nИсточник: с. 140; с. 34–35."))

    # 4. ступень 6: открытый исход — выводится ли схема 4 из схем 5 и 6
    g4 = AX[4]
    pl = proof17(g4, [5, 6])
    assert not any(l[1].startswith("схема 4") for l in pl)
    cond = (INTRO17 + " Исследуйте, можно ли получить утверждение 4, пользуясь лишь утверждениями 5 и 6 (и их "
            "подстановочными частными случаями) и указанными правилами: если можно — постройте вывод, если нельзя — "
            "объясните почему.")
    out.append(card(dict(section=17, level=6, type="C", step="open", condition="over",
                         tags=["изменение", "открытый исход", "вывод"], source=src),
                    cond, f"Можно: вывод в {len(pl)} строк из схем 5 (при замене $x$ — ${{\\sim}}y$) и 6 (см. решение).",
                    render17(pl) + "\n\nУтверждения 1 и 4 при этом не использованы (лишние данные). Источник: с. 140; с. 34–35."))

    # 5. ступень 6: открытый исход — схема 5 из 4 и 6
    g5 = AX[5]
    pl = proof17(g5, [4, 6])
    assert not any(l[1].startswith("схема 5") for l in pl)
    cond = (INTRO17 + " Докажите, что утверждение 5 не независимо: оно выводится из утверждений 4 и 6 (и их "
            "подстановочных частных случаев) по указанным правилам. Постройте вывод.")
    out.append(card(dict(section=17, level=6, type="M", step="vary", tags=["изменение", "зависимость утверждений", "вывод"],
                         source=src),
                    cond, f"Вывод в {len(pl)} строк из схем 4 (при замене $y$ — ${{\\sim}}x$) и 6 (см. решение).",
                    render17(pl) + "\n\nИсточник: с. 140; с. 34–35."))

    # 6. ступень 6: диагностика с двумя ошибками в выводе g1
    pl = proof17(g1, [4, 5])
    bad = list(pl)
    # ошибка 1: Д1 применено к одиночному отрицанию: из ⊢ ~~C → ~x записано ⊢ C → x
    i_dn = next(i for i, l in enumerate(pl, 1) if l[1].startswith("Д$^1$") and l[0][2] == N(X))
    wrong = IMP(C, X)
    bad[i_dn - 1] = (wrong, pl[i_dn - 1][1], pl[i_dn - 1][2])
    # ошибка 2: в последней строке основание с У6 вместо У5; формула следует за неверной строкой
    last = len(pl)
    wrong_goal = IMP(C, AND(X, Y))
    bad[last - 1] = (wrong_goal, "Д$^{16}$, У$^6$, Д$^{14}$", pl[last - 1][2])
    src_line = pl[pl[i_dn - 1][2][0] - 1][0]
    cond = (INTRO17 + " Студент вывел " + th(wrong_goal) + " так:\n\n" + render17(bad) +
            "\n\nНайдите все ошибки, назовите нарушенное правило книги и исправьте вывод.")
    ans = (f"Строка {i_dn}: Д$^1$ (с. 34) снимает лишь двойное отрицание — из {th(src_line)} следует "
           f"{th(pl[i_dn - 1][0])}; строка {last}: консеквенты соединяет У$^5$, а не У$^6$ (с. 35). Верный итог: {th(g1)}.")
    sol = ("Д$^1$: ${\\sim}{\\sim}x \\dashv\\vdash x$; в строке " + str(i_dn) + " двойное отрицание стоит только перед "
           "$(sx \\Rightarrow sy)$, а ${\\sim}x$ остаётся. У$^6$ относится к дизъюнкции антецедентов, а в последней строке "
           "объединены два консеквента при одном антецеденте — это У$^5$. Исправленный вывод:\n\n" + render17(pl) +
           "\n\nИсточник: с. 140; с. 34–35.")
    out.append(card(dict(section=17, level=6, type="E", step="vary", answer="short",
                         tags=["изменение", "диагностика"], source=src), cond, ans, sol))
    return out


# =============================================================== § 19: три и две возможности

P_, NP, QP = ("p", "P"), ("p", "N"), ("p", "Q")


def tex19(f):
    k = f[0]
    if k == "p":
        return {"P": "P(a)", "N": "\\urcorner P(a)", "Q": "?P(a)"}[f[1]]
    if k == "n":
        g = f[1]
        return "{\\sim}" + (tex19(g) if g[0] in ("p", "n") else "(" + tex19(g) + ")")

    def par(g):
        return "(" + tex19(g) + ")" if g[0] in ("and", "or") else tex19(g)
    return f"{par(f[1])} {'\\wedge' if k == 'and' else '\\vee'} {par(f[2])}"


def val19(f, w):
    k = f[0]
    if k == "p":
        return f[1] == w
    if k == "n":
        return not val19(f[1], w)
    if k == "and":
        return val19(f[1], w) and val19(f[2], w)
    return val19(f[1], w) or val19(f[2], w)


W3 = ["P", "N", "Q"]
W2 = ["P", "N"]
WNAME = {"P": "$P(a)$", "N": "$\\urcorner P(a)$", "Q": "${\\sim}P(a) \\wedge {\\sim}\\urcorner P(a)$"}


def s19_cards():
    out = []
    src = "с. 143–144, гл. 3, § 19; с. 35"
    intro = ("Буква $a$ — индивид, $P(a)$ — «$a$ находится в месте $\\alpha$»; ${\\sim}$ — внешнее, $\\urcorner$ — внутреннее "
             "отрицание. В неклассическом случае предполагаются три возможности (с. 144): $P(a)$, $\\urcorner P(a)$, "
             "${\\sim}P(a) \\wedge {\\sim}\\urcorner P(a)$ (последняя — переходное состояние, она же $?P(a)$ по П$^1$, с. 35); "
             "при каждой возможности истинно ровно одно из $P(a)$, $\\urcorner P(a)$, $?P(a)$ (П$^6$, П$^7$, с. 35), а "
             "${\\sim}z$ истинно, когда $z$ неистинно. ")
    # 1. ступень 3: значения
    fs = [AND(N(P_), N(NP)), OR(P_, NP), N(AND(P_, NP)), OR(N(NP), NP)]
    rows = []
    for i, f in enumerate(fs):
        vals = ", ".join(f"при {WNAME[w]} — {'истинно' if val19(f, w) else 'неистинно'}" for w in W3)
        acc = all(val19(f, w) for w in W3)
        rows.append((f, vals, acc))
    items = "\n".join(f"{'абвг'[i]}) ${tex19(f)}$" for i, (f, _, _) in enumerate(rows))
    cond = (intro + "Для каждой формулы ниже найдите её значение при каждой из трёх возможностей и установите, "
            "принимается ли она из логических соображений (истинна при всех возможностях).\n\n" + items)
    ans = "; ".join(f"{'абвг'[i]}) {'принимается' if acc else 'не принимается'}" for i, (_, _, acc) in enumerate(rows))
    sol = "\n".join(f"{'абвг'[i]}) ${tex19(f)}$: {vals}; {'принимается' if acc else 'не принимается'}."
                    for i, (f, vals, acc) in enumerate(rows))
    sol += ("\n\nВ частности, б) $\\vdash P(a) \\vee \\urcorner P(a)$ неверно в неклассическом случае (с. 144; с. 36, § 25), "
            "а в) — правило П$^7$ (с. 35).")
    out.append(card(dict(section=19, level=3, type="V", answer="short", case="nonclassical",
                         tags=["парадокс движения", "неклассический случай", "значения"], source=src), cond, ans, sol))

    # 2. ступень 7: перенос — классический и неклассический случаи
    fs = [N(AND(N(P_), N(NP))), OR(N(P_), N(NP)), OR(P_, N(P_)), AND(N(NP), N(P_)), OR(NP, N(NP)), OR(P_, NP)]
    rnd.shuffle(fs)
    fs = fs[:5]
    res = []
    for f in fs:
        nc = all(val19(f, w) for w in W3)
        cl = all(val19(f, w) for w in W2)
        res.append((f, nc, cl))
    assert any(cl and not nc for _, nc, cl in res)
    items = "\n".join(f"{'абвгд'[i]}) ${tex19(f)}$" for i, (f, _, _) in enumerate(res))
    cond = (intro + "В классическом случае отрицания $\\urcorner$ и ${\\sim}$ не различаются и допускаются лишь две "
            "возможности: $P(a)$, $\\urcorner P(a)$ (с. 144). Для каждой формулы установите, принимается ли она из логических "
            "соображений в неклассическом и в классическом случае; укажите формулы, разделяющие случаи.\n\n" + items)

    def word(b):
        return "принимается" if b else "не принимается"
    ans = "; ".join(f"{'абвгд'[i]}) неклас. — {word(nc)}, клас. — {word(cl)}" for i, (_, nc, cl) in enumerate(res))
    sol = []
    for i, (f, nc, cl) in enumerate(res):
        bad3 = [WNAME[w] for w in W3 if not val19(f, w)]
        sol.append(f"{'абвгд'[i]}) ${tex19(f)}$: неклассический случай — {word(nc)}"
                   + (f" (неистинна при {', '.join(bad3)})" if bad3 else "") + f"; классический — {word(cl)}.")
    sep = [f"{'абвгд'[i]})" for i, (_, nc, cl) in enumerate(res) if cl and not nc]
    sepw = (f"Разделяет случаи формула {sep[0]}: она верна" if len(sep) == 1 else
            f"Разделяют случаи формулы {', '.join(sep)}: они верны")
    sol = "\n".join(sol) + (f"\n\n{sepw} лишь при двух возможностях. "
                            "Именно утверждения классического случая применяет к переходному состоянию тот, кто получает парадокс движения "
                            "(с. 144).")
    out.append(card(dict(section=19, level=7, type="S", step="transfer", answer="short",
                         tags=["парадокс движения", "классический случай", "неклассический случай"], source=src),
                    cond, ans, sol))
    return out


# =============================================================== § 13: порождение

def s13_cards():
    out = []
    src = "с. 135, гл. 3, § 13"
    T = list(range(1, 9))
    pairs = []
    names = [("m", "c"), ("p", "q"), ("u", "v"), ("g", "h")]
    want = [True, False, True, False]
    rnd2 = random.Random(13)
    i = 0
    while len(pairs) < 4:
        a1, a2 = sorted(rnd2.sample(T, 2))
        b1, b2 = sorted(rnd2.sample(T, 2))
        A = set(range(a1, a2 + 1))
        B = set(range(b1, b2 + 1))
        wit = [(al, be) for al in T for be in T if al in A and al not in B and be in B and be > al]
        ok = bool(wit)
        if ok != want[len(pairs)] or A == B:
            continue
        pairs.append((names[len(pairs)], (a1, a2), (b1, b2), wit))
    items = "\n".join(f"{'абвг'[k]}) ${n[0]}$ существует в моменты {a[0]}–{a[1]}, ${n[1]}$ — в моменты {b[0]}–{b[1]}"
                      for k, (n, a, b, _) in enumerate(pairs))
    cond = ("Моменты времени $1, 2, \\ldots, 8$ упорядочены способом $\\alpha$: $\\beta > \\alpha$ — «$\\beta$ позже $\\alpha$» "
            "(с. 123); $E\\alpha(a)$ — «$a$ существует в момент $\\alpha$», $\\urcorner E\\alpha(a)$ — «$a$ не существует в "
            "момент $\\alpha$». По с. 135 частью имплицитного определения «$a$ порождает $b$» служит "
            "$(\\exists\\alpha)(\\exists\\beta)(E\\alpha(a) \\wedge \\urcorner E\\alpha(b) \\wedge E\\beta(b) \\wedge (\\beta > \\alpha))$. "
            "Для каждой пары индивидов (вне указанных моментов индивид не существует) проверьте, выполнено ли это условие "
            "для «первый порождает второго»; если выполнено — укажите подходящие $\\alpha$ и $\\beta$, если нет — объясните.\n\n"
            + items)
    ans_parts, sol_parts = [], []
    for k, (n, a, b, wit) in enumerate(pairs):
        A = range(a[0], a[1] + 1)
        B = range(b[0], b[1] + 1)
        L = "абвг"[k]
        if wit:
            al, be = wit[0]
            ans_parts.append(f"{L}) выполнено ($\\alpha = {al}$, $\\beta = {be}$)")
            sol_parts.append(f"{L}) При $\\alpha = {al}$, $\\beta = {be}$: ${n[0]}$ существует в момент {al}, ${n[1]}$ в момент {al} "
                             f"не существует, ${n[1]}$ существует в момент {be}, и {be} позже {al} — все четыре члена "
                             "конъюнкции истинны.")
        else:
            ans_parts.append(f"{L}) не выполнено")
            alphas = [t for t in A if t not in B]
            if not alphas:
                why = (f"в каждый момент существования ${n[0]}$ ({a[0]}–{a[1]}) существует и ${n[1]}$ ({b[0]}–{b[1]}), "
                       "так что член $\\urcorner E\\alpha(b)$ ложен при любом подходящем $\\alpha$")
            else:
                why = (f"моменты, когда ${n[0]}$ существует, а ${n[1]}$ нет: {', '.join(map(str, alphas))}; позже любого из них "
                       f"${n[1]}$ не существует (он существует лишь в {b[0]}–{b[1]}), так что подходящего $\\beta$ нет")
            sol_parts.append(f"{L}) {why}; условие не выполнено.")
    out.append(card(dict(section=13, level=3, type="C", answer="short", form="sym",
                         tags=["порождение", "время существования"], source=src),
                    cond, "; ".join(ans_parts), "\n".join(sol_parts) + "\n\nИсточник: с. 135 (формула), с. 123 (чтение $>$)."))
    return out


# =============================================================== § 20: процесс

def s20_cards():
    out = []
    src = "с. 144, гл. 3, § 20"
    seqs = [
        ("состояния $a$, $b$, $c$ индивида $A$; $t^a = 1$, $t^b = 3$, $t^c = 5$", True, None),
        ("состояния $a$, $b$ индивида $A$ и состояние $c$ индивида $B$; $t^a = 1$, $t^b = 2$, $t^c = 4$", False,
         "состояния $a$, $b$, $c$ должны быть состояниями одного и того же индивида"),
        ("состояния $a$, $b$, $c$ индивида $A$; $t^a = 2$, $t^b = 4$, $t^c = 3$", False, "$t^c > t^b$ не выполнено"),
        ("состояния $a$, $b$, $c$ индивида $A$; $t^a = 3$, $t^b = 3$, $t^c = 6$", False, "$t^b > t^a$ не выполнено"),
        ("состояния $a$, $b$, $c$, $d$ индивида $A$ (изменения $a \\Rightarrow b$, $b \\Rightarrow c$, $c \\Rightarrow d$); "
         "$t^a = 1$, $t^b = 2$, $t^c = 4$, $t^d = 7$", True, None),
    ]
    items = "\n".join(f"{'абвгд'[i]}) {s}" for i, (s, _, _) in enumerate(seqs))
    cond = ("По с. 144 процесс — упорядоченный во времени ряд изменений, у которого для любой пары соседних элементов "
            "$a \\Rightarrow b$ и $b \\Rightarrow c$ при существовании $a$ в $t^a$, $b$ в $t^b$, $c$ в $t^c$ верно $t^c > t^b$ и "
            "$t^b > t^a$, а состояния $a$, $b$, $c$ — состояния одного и того же индивида $A$. Большее число — более позднее "
            "время. Для каждого ряда изменений $a \\Rightarrow b$, $b \\Rightarrow c$, … установите, удовлетворяет ли он "
            "определению процесса, и назовите нарушенное условие.\n\n" + items)
    ans = "; ".join(f"{'абвгд'[i]}) {'процесс' if ok else 'не процесс'}" for i, (_, ok, _) in enumerate(seqs))
    sol = "\n".join(f"{'абвгд'[i]}) " + ("все пары соседних изменений упорядочены по времени, индивид один — процесс."
                                         if ok else f"{why} — не процесс.") for i, (_, ok, why) in enumerate(seqs))
    # проверка
    for s, ok, why in seqs:
        import re
        ts = [int(v) for v in re.findall(r"t\^[a-d] = (\d+)", s)]
        same = "индивида $B$" not in s
        assert ok == (same and all(ts[i + 1] > ts[i] for i in range(len(ts) - 1))), s
    out.append(card(dict(section=20, level=3, type="R", answer="short", form="sym", tags=["процесс"], source=src),
                    cond, ans, sol + "\n\nИсточник: с. 144."))
    return out


def main():
    outdir = Path(sys.argv[1] if len(sys.argv) > 1 else "drafts_gen")
    outdir.mkdir(parents=True, exist_ok=True)
    groups = {13: s13_cards(), 14: s14_cards(), 17: s17_cards(), 19: s19_cards(), 20: s20_cards()}
    for sec, cards in groups.items():
        (outdir / f"19.{sec}-gen.md").write_text("\n=====\n\n".join(cards), encoding="utf-8")
        print(sec, len(cards))


if __name__ == "__main__":
    main()
