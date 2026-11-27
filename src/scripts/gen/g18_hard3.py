"""Трудные задачи раздела 18, часть 3: упорядоченные конъюнкции, дизъюнкции и условные высказывания (§ 37–38),
структуры (§ 31). Вызывается из g18_hard.main()."""
import itertools

from g18 import items, ans_items

card = fresh = rnd = None

# ================================================================ § 37–38

PAIRS = {"t": [("после этого", "до этого"), ("через час после этого", "за час до этого"), ("позже этого", "раньше этого"),
               ("сразу после этого", "непосредственно перед этим")],
         "s": [("правее этого", "левее этого"), ("выше этого", "ниже этого"), ("севернее этого", "южнее этого"),
               ("дальше от входа, чем это", "ближе к входу, чем это")]}
EVENTS = [("t", "прозвенел звонок", "начался урок"), ("t", "включили насос", "вода поднялась в бак"),
          ("t", "пришла телеграмма", "уехал гость"), ("t", "остыл металл", "раскололась форма"),
          ("t", "сверкнула молния", "загремел гром"), ("t", "открыли шлюз", "уровень воды упал"),
          ("s", "стоит словарь", "стоит атлас"), ("s", "висит картина", "висят часы"),
          ("s", "стоит почта", "стоит школа"), ("s", "лежит ковёр", "стоит кресло")]

O37 = ("Буквы $x, y$ — высказывания; $R^1$, $R^2$ — отношения порядка. По с. 106 для упорядоченных конъюнкций и дизъюнкций "
       "не принимаются правила коммутации $x \\wedge (Rx)y \\vdash y \\wedge (Ry)x$, $x \\vee (Rx)y \\vdash y \\vee (Ry)x$; верны лишь "
       "(K1) $(x \\wedge (R^1x)y) \\wedge ((aR^1b) \\to (bR^2a)) \\vdash (y \\wedge (R^2y)x)$ и "
       "(K2) $(x \\vee (R^1x)y) \\wedge ((aR^1b) \\to (bR^2a)) \\vdash (y \\vee (R^2y)x)$. Для условных высказываний (с. 106): "
       "(У1) $(x \\to (Rx)y) \\dashv\\vdash (\\forall sx)((Rx)y)$; "
       "(У2) $(x \\to (R^1x)y) \\wedge ((aR^1b) \\to (bR^2a)) \\vdash ({\\sim}y \\to (R^2{\\sim}y){\\sim}x)$.")


def ord_item():
    (typ, ex, ey) = rnd.choice(EVENTS)
    (r1, r2) = rnd.choice(PAIRS[typ])
    kind = rnd.choice(["and", "or", "if"])
    if kind == "and":
        nl = f"«{ex}, и {r1} — {ey}»"
        st = nl + " ($x \\wedge (R^1x)y$)"
        res = f"«{ey}, и {r2} — {ex}» ($y \\wedge (R^2y)x$) по K1"
        bad = f"«{ey}, и {r1} — {ex}»"
    elif kind == "or":
        nl = f"«{ex}, или {r1} — {ey}»"
        st = nl + " ($x \\vee (R^1x)y$)"
        res = f"«{ey}, или {r2} — {ex}» ($y \\vee (R^2y)x$) по K2"
        bad = f"«{ey}, или {r1} — {ex}»"
    else:
        nl = f"«если {ex}, то {r1} — {ey}»"
        st = nl + " ($x \\to (R^1x)y$)"
        res = f"«если неверно, что {ey}, то {r2} — неверно, что {ex}» (${{\\sim}}y \\to (R^2{{\\sim}}y){{\\sim}}x$) по У2"
        bad = f"«если неверно, что {ey}, то {r1} — неверно, что {ex}»"
    return dict(r1=r1, r2=r2, x=ex, y=ey, kind=kind, st=st, nl=nl, res=res, res_nl=res.split(" ($")[0], bad=bad)


def ord_series():
    def make():
        its = []
        kinds = set()
        while len(its) < 4:
            it = ord_item()
            if it["x"] in {i["x"] for i in its}:
                continue
            its.append(it)
            kinds.add(it["kind"])
        if len(kinds) < 3:
            return None
        U = (f"{O37} Для каждого высказывания ($x$ и $y$ — его члены, $R^1$ — указанное в нём отношение) получите по правилам с. 106 "
             "высказывание, в котором члены поменялись местами (для условного — с отрицаниями членов), и укажите отношение $R^2$ "
             "и дополнительную посылку.\n\n" + items([it["st"] for it in its]))
        A = ans_items([it["res"] + f", $R^2$ — «{it['r2']}», посылка $(aR^1b) \\to (bR^2a)$" for it in its])
        R = "\n".join(f"{'абвг'[i]}) $R^1$ — «{it['r1']}»; обратное отношение $R^2$ — «{it['r2']}», т. е. $(aR^1b) \\to (bR^2a)$. "
                      + ("Правило K1 (с. 106)" if it["kind"] == "and" else "Правило K2 (с. 106)" if it["kind"] == "or" else "Правило У2 (с. 106)")
                      + f" даёт {it['res'].rsplit(' по ', 1)[0]}." for i, it in enumerate(its))
        return U, A, R + "\n\nКоммутация с тем же отношением $R^1$ не принимается (с. 106)."
    r = fresh(make)
    if r:
        card(37, 4, "T", "iso", "def", "nat", "short", "с. 106, гл. 2, § 37–38", ["упорядоченные конъюнкции", "условные высказывания"], *r)


def ord_errors():
    def make():
        its = []
        while len(its) < 5:
            it = ord_item()
            if it["x"] in {i["x"] for i in its}:
                continue
            its.append(it)
        bad = sorted(rnd.sample(range(5), 2))
        lines = []
        for i, it in enumerate(its):
            concl = it["bad"] if i in bad else it["res_nl"]
            lines.append(f"Из {it['nl']} студент получил {concl}.")
        U = (f"{O37} Студент переставлял члены упорядоченных высказываний:\n\n" + items(lines)
             + "\n\nРовно два заключения ошибочны. Найдите их, назовите нарушенное правило с. 106 и исправьте.")
        A = "; ".join(f"{'абвгд'[i]}) верно {its[i]['res_nl']} — при перестановке отношение «{its[i]['r1']}» заменяется обратным «{its[i]['r2']}» (с. 106)" for i in bad)
        R = "\n".join(f"{'абвгд'[i]}) " + ("ошибка: сохранено отношение $R^1$, т. е. применена непринимаемая коммутация; " if i in bad else "верно: ")
                      + f"{it['res']}, посылка $(aR^1b) \\to (bR^2a)$ для «{it['r1']}» и «{it['r2']}»." for i, it in enumerate(its))
        return U, A, R
    r = fresh(make)
    if r:
        card(37, 6, "E", "vary", "def", "nat", "text", "с. 106, гл. 2, § 37–38", ["упорядоченные конъюнкции", "диагностика"], *r)


# ================================================================ § 31 структуры

S31 = ("Буквы $a, b, c, d, e, f$ — индивиды; $\\alpha^1, \\alpha^2$ — способы установления порядка. По с. 97 элементы скопления $A$ "
       "образуют структуру относительно класса способов $B$, если и только если для любого элемента $u$ скопления найдётся другой "
       "элемент $v$ и способ $\\alpha$ из $B$, что $u > \\alpha v$ или $v > \\alpha u$. Для каждого способа принимается аналог аксиомы C4 "
       "(с. 82): $(u > \\alpha v) \\wedge (v > \\alpha w) \\vdash (u > \\alpha w)$.")


def str_data():
    ind = list("abcdef")
    for _ in range(100):
        facts = set()
        for w in (1, 2):
            order = rnd.sample(ind, rnd.choice([3, 4]))
            for i in range(len(order) - 1):
                facts.add((w, order[i + 1], order[i]))
        rel = tclose(facts)
        # без противоречий: не бывает u > v и v > u в одном способе
        if not any((w, b, a) in rel for (w, a, b) in rel):
            return ind, sorted(facts)
    return ind, sorted(facts)


def tclose(facts):
    """Замыкание по аналогу C4 внутри каждого способа: {(w, a, b): (w, a, c, b) или None}."""
    rel = {f: None for f in facts}
    changed = True
    while changed:
        changed = False
        for (w, a, c), (w2, c2, b) in itertools.product(list(rel), repeat=2):
            if w == w2 and c == c2 and a != b and (w, a, b) not in rel:
                rel[(w, a, b)] = (c,)
                changed = True
    return rel


def partner(u, S, Bw, facts):
    rel = tclose(facts)
    best = None
    for (w, a, b), via in rel.items():
        if w in Bw and ((a == u and b in S and b != u) or (b == u and a in S and a != u)):
            if via is None:
                return (w, a, b)
            best = best or (w, a, b, via[0])
    return best


def forms(S, Bw, facts):
    return all(partner(u, S, Bw, facts) for u in S)


def ftx(f):
    w, a, b = f[:3]
    s = f"${a} > \\alpha^{w} {b}$"
    if len(f) == 4:
        c = f[3]
        s += f" (из ${a} > \\alpha^{w} {c}$ и ${c} > \\alpha^{w} {b}$ по аналогу C4, с. 82)"
    return s


def str_series():
    def make():
        ind, facts = str_data()
        cases = []
        seen = set()
        for _ in range(60):
            used = sorted({x for f in facts for x in f[1:]})
            S = tuple(sorted(rnd.sample(used, min(len(used), rnd.choice([2, 3, 4])))))
            Bw = rnd.choice([(1,), (2,), (1, 2)])
            if (S, Bw) in seen:
                continue
            seen.add((S, Bw))
            cases.append((S, Bw))
            if len(cases) == 4:
                break
        res = [forms(S, Bw, facts) for S, Bw in cases]
        if sum(res) != 2:
            return None
        Btx = lambda Bw: "\\{" + ", ".join(f"\\alpha^{w}" for w in Bw) + "\\}"
        U = (f"{S31} Известно: " + "; ".join(ftx(f) for f in facts) + "; других отношений по $\\alpha^1$ и $\\alpha^2$ между этими индивидами нет, кроме выводимых из данных по аналогу C4. Для каждого скопления и класса "
             "способов $B$ установите, образуют ли его элементы структуру относительно $B$, и обоснуйте.\n\n"
             + items([f"скопление ${', '.join(S)}$, $B = {Btx(Bw)}$" for S, Bw in cases]))
        A = ans_items(["образуют" if r_ else "не образуют" for r_ in res])
        R = []
        for i, (S, Bw) in enumerate(cases):
            parts = []
            for u in S:
                p_ = partner(u, S, Bw, facts)
                parts.append(f"для ${u}$ — {ftx(p_)}" if p_ else f"для ${u}$ нет ни другого элемента скопления, ни способа из $B$")
            R.append(f"{'абвг'[i]}) " + "; ".join(parts) + (" — образуют (с. 97)." if res[i] else " — не образуют (с. 97)."))
        return U, A, "\n".join(R)
    r = fresh(make)
    if r:
        card(31, 5, "C", "iso", "over", "sym", "short", "с. 96–97, гл. 2, § 31", ["структура"], *r)


def str_errors():
    def make():
        ind, facts = str_data()
        cases, seen = [], set()
        for _ in range(80):
            used = sorted({x for f in facts for x in f[1:]})
            S = tuple(sorted(rnd.sample(used, min(len(used), rnd.choice([2, 3, 4])))))
            Bw = rnd.choice([(1,), (2,), (1, 2)])
            if (S, Bw) not in seen:
                seen.add((S, Bw))
                cases.append((S, Bw))
            if len(cases) == 5:
                break
        res = [forms(S, Bw, facts) for S, Bw in cases]
        if sum(res) < 2 or sum(res) > 3:
            return None
        bad = sorted(rnd.sample(range(5), 2))
        stud = [(not r_) if i in bad else r_ for i, r_ in enumerate(res)]
        Btx = lambda Bw: "\\{" + ", ".join(f"\\alpha^{w}" for w in Bw) + "\\}"
        U = (f"{S31} Известно: " + "; ".join(ftx(f) for f in facts) + "; других отношений по $\\alpha^1$ и $\\alpha^2$ между этими индивидами нет, кроме выводимых из данных по аналогу C4. Студент утверждает:\n\n"
             + items([f"элементы скопления ${', '.join(S)}$ {'образуют' if s else 'не образуют'} структуру относительно $B = {Btx(Bw)}$" for (S, Bw), s in zip(cases, stud)])
             + "\n\nРовно два утверждения ошибочны. Найдите их и обоснуйте по определению с. 97.")
        A = "; ".join(f"{'абвгд'[i]}) {'образуют' if res[i] else 'не образуют'}" for i in bad)
        R = []
        for i, (S, Bw) in enumerate(cases):
            parts = []
            for u in S:
                p_ = partner(u, S, Bw, facts)
                parts.append(f"для ${u}$ — {ftx(p_)}" if p_ else f"для ${u}$ партнёра нет")
            R.append(f"{'абвгд'[i]}) " + "; ".join(parts) + (" — образуют." if res[i] else " — не образуют."))
        return U, A, "\n".join(R) + "\n\nОпределение — с. 97: партнёр нужен каждому элементу, и способ должен принадлежать $B$."
    r = fresh(make)
    if r:
        card(31, 6, "E", "vary", "def", "sym", "text", "с. 96–97, гл. 2, § 31", ["структура", "диагностика"], *r)


def run(card_, fresh_, rnd_):
    global card, fresh, rnd
    card, fresh, rnd = card_, fresh_, rnd_
    for f, n in [(ord_series, 14), (ord_errors, 9), (str_series, 14), (str_errors, 9)]:
        for _ in range(n):
            f()
