"""Гл. 6, § 1–3: язык условных высказываний, условность и следование, условность и материальная импликация."""
from hard06_lib import F, C, IF, IFN, IFQ, IMP, N, V, W, ftex, tex, rnd, x, y, z, v, u, L, CV, card
from hard06_sem import comp, nn, explain_non, explain_taut, INTERP, lit_tex, c_tex
import hard06_sem as S

KINDS = {"if": IF, "ifn": IFN, "ifq": IFQ}
D1 = ("D1 § 1 (с. 82): $(x \\rightarrow y)$, $(x \\urcorner\\!\\rightarrow y)$ и $(x? \\rightarrow y)$ суть высказывания, если и "
      "только если $x$ и $y$ суть высказывания; $\\rightarrow$ — оператор условности, $\\urcorner$ — внутреннее отрицание, "
      "$?$ — оператор неопределённости. D2 § 1: $x$ и $y$ — антецедент и консеквент этих высказываний.")
D2E = ("D2 (второе) § 1 (с. 82): 1) если оператор условности не входит в $x$ и $y$, то $x$ и $y$ — элементарные высказывания, "
       "входящие в $(x \\rightarrow y)$, $(x \\urcorner\\!\\rightarrow y)$, $(x? \\rightarrow y)$; 2) если одно из этих "
       "высказываний входит в $z$, то элементарные высказывания, входящие в $x$ и $y$, — элементарные высказывания, входящие в "
       "$z$; 3) высказывание элементарно лишь в силу 1 и 2.")


def lit():
    t = rnd.choice([x, y, z, v, u])
    return N(t) if rnd.random() < 0.3 else t


def plain(d=1):
    if d == 0 or rnd.random() < 0.45:
        return lit()
    a, b = plain(d - 1), plain(d - 1)
    if a == b:
        return a
    return C(a, b) if rnd.random() < 0.6 else W(a, b)


def cformula(depth=2, kinds=("if", "if", "ifn", "ifq")):
    """Высказывание с условными высказываниями."""
    k = rnd.random()
    if depth == 0:
        return KINDS[rnd.choice(kinds)](plain(1), plain(1))
    if k < 0.35:
        return KINDS[rnd.choice(kinds)](cformula(depth - 1, kinds) if rnd.random() < 0.5 else plain(1),
                                        cformula(depth - 1, kinds) if rnd.random() < 0.6 else plain(1))
    if k < 0.6:
        return C(cformula(depth - 1, kinds), cformula(depth - 1, kinds) if rnd.random() < 0.6 else lit())
    if k < 0.8:
        return W(cformula(depth - 1, kinds), cformula(depth - 1, kinds))
    return N(cformula(depth - 1, kinds))


def main_op(f):
    return {"if": "оператор условности $\\rightarrow$", "ifn": "$\\urcorner\\!\\rightarrow$ (внутреннее отрицание)",
            "ifq": "$? \\rightarrow$ (неопределённость)", "conj": "конъюнкция", "wdis": "дизъюнкция $\\vee$",
            "neg": "отрицание $\\sim$", "v": "—"}[f[0]]


def malform(f, kind):
    """Испорченная запись: (текст, объяснение) или None."""
    s = tex(f)
    cs = [g for g in F.conds(f)]
    if kind == "noparen":
        cand = [g for g in F.subs(f) if g[0] == "conj" and any(t[0] in F.COND for t in g[1])]
        if not cand:
            return None
        g = rnd.choice(cand)
        t = [t for t in g[1] if t[0] in F.COND][0]
        ts = tex(t)
        if s.count(ts) != 1:
            return None
        return s.replace(ts, ts[1:-1]), (f"условное высказывание ${ts[1:-1]}$ записано без скобок, а по D1 высказывание "
                                         f"с оператором условности имеет вид $(x \\rightarrow y)$; без скобок неясно, что "
                                         f"антецедент и что консеквент")
    if kind == "term":
        g = rnd.choice(cs)
        ts = tex(g)
        if s.count(ts) != 1:
            return None
        cons = tex(g[2])
        new = ts[: len(ts) - len(cons) - 1] + "a)"
        return s.replace(ts, new), (f"в ${new}$ консеквент $a$ — термин, а не высказывание; по D1 и антецедент, и "
                                    f"консеквент должны быть высказываниями")
    if kind == "qpos":
        g = rnd.choice(cs)
        ts = tex(g)
        if s.count(ts) != 1:
            return None
        new = f"({tex(g[1])} \\rightarrow {tex(g[2])}?)"
        return s.replace(ts, new), f"знак $?$ стоит после консеквента: по D1 высказывание неопределённости имеет вид $(x? \\rightarrow y)$"
    if kind == "noante":
        g = rnd.choice(cs)
        ts = tex(g)
        if s.count(ts) != 1:
            return None
        new = f"(\\rightarrow {tex(g[2])})"
        return s.replace(ts, new), f"в ${new}$ нет антецедента; по D1 нужны оба высказывания $x$ и $y$"
    if kind == "noarrow":
        g = rnd.choice(cs)
        ts = tex(g)
        if s.count(ts) != 1:
            return None
        new = f"({tex(g[1])} \\urcorner {tex(g[2])})"
        return s.replace(ts, new), (f"в ${new}$ знак $\\urcorner$ стоит без оператора условности; D1 вводит только "
                                    f"$(x \\urcorner\\!\\rightarrow y)$")
    raise ValueError(kind)


def wf_items(n_good=2, kinds=("noparen", "term", "qpos", "noante", "noarrow")):
    items = []
    for _ in range(n_good):
        while True:
            f = cformula(2)
            if 14 <= F.size(f) <= 34 and len(F.conds(f)) >= 2 and not nn(f):
                items.append((tex(f), None, f))
                break
    for kd in kinds:
        for _ in range(200):
            f = cformula(2)
            if not (14 <= F.size(f) <= 34 and len(F.conds(f)) >= 2) or nn(f):
                continue
            r = malform(f, kd)
            if r:
                items.append((r[0], r[1], None))
                break
    rnd.shuffle(items)
    return items


def c_wf(level=4, src="с. 82, гл. 6, § 1"):
    items = wf_items(2, rnd.sample(["noparen", "term", "qpos", "noante", "noarrow"], 3))
    cond = (f"Буквы $x, y, z, v, u$ — высказывания, $a$ — термин (не высказывание). Проверьте каждое выражение по D1 § 1 "
            f"(и определениям $\\sim$, конъюнкции и $\\vee$ из предыдущих глав): для высказывания назовите главный оператор, "
            f"для остальных укажите место, нарушающее определение. {D1}\n\n" +
            "\n".join(f"{L[i]}) ${s}$" for i, (s, _, _) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) " + (f"высказывание, главный оператор — {main_op(f)}" if f else "не высказывание")
                    for i, (_, _, f) in enumerate(items))
    sol = "\n".join(f"{L[i]}) " + (f"Высказывание: части построены по D1 и определениям предыдущих глав; главный оператор — "
                                   f"{main_op(f)}." if f else f"Не высказывание: {why}.")
                    for i, (_, why, f) in enumerate(items))
    return card(level, "A", "iso", "short", src, "условные высказывания, D1", cond, ans, sol)


def c_wf_diag(level=4, src="с. 82, гл. 6, § 1"):
    items = wf_items(2, rnd.sample(["noparen", "term", "qpos", "noante", "noarrow"], 2))
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, (s, why, f) in enumerate(items):
        ok = f is not None
        claim = ok if i not in wrong else not ok
        lines.append(f"{i + 1}. ${s}$ — {'высказывание' if claim else 'не высказывание'}.")
        if i in wrong:
            ans.append(f"{i + 1}: {'высказывание' if ok else 'не высказывание'}")
            sol.append(f"{i + 1}. " + (f"Высказывание: все части построены по D1 и определениям предыдущих глав (главный "
                                       f"оператор — {main_op(f)}); студент, видимо, счёл недопустимым вложение условных "
                                       f"высказываний, но D1 требует лишь, чтобы $x$ и $y$ были высказываниями." if ok
                                       else f"Не высказывание: {why} (D1 § 1, с. 82)."))
    cond = (f"Буквы $x, y, z, v, u$ — высказывания, $a$ — термин. Студент проверил выражения по D1 § 1:\n\n" + "\n".join(lines) +
            f"\n\nРовно две оценки ошибочны. Найдите их и объясните, какое условие D1 (или определений предыдущих глав) "
            f"нарушено или соблюдено. {D1}")
    return card(level, "E", "vary", "text", src, "условные высказывания, D1, диагностика", cond, "; ".join(ans) + ".",
                "\n".join(sol) + "\n\nОстальные оценки верны.")


def parts_of(f):
    return [(g, g[1], g[2]) for g in F.conds(f)]


def c_parts(level=5, src="с. 82, гл. 6, § 1"):
    while True:
        f = cformula(3)
        if 22 <= F.size(f) <= 44 and len(F.conds(f)) >= 3 and not nn(f):
            break
    ps = parts_of(f)
    cond = (f"Буквы $x, y, z, v, u$ — высказывания. Выпишите все высказывания с операторами $\\rightarrow$, "
            f"$\\urcorner\\!\\rightarrow$, $?\\rightarrow$, входящие в ${tex(f)}$, и для каждого укажите антецедент и "
            f"консеквент (D2 § 1, с. 82). Назовите главный оператор всего высказывания. {D1}")
    ans = (f"Главный оператор — {main_op(f)}; " + "; ".join(f"${tex(g)}$: ант. ${tex(a)}$, конс. ${tex(b)}$" for g, a, b in ps)
           + ".")
    sol = (f"Разбираем снаружи внутрь: каждая пара скобок с оператором условности выделяет высказывание $(x \\rightarrow y)$; "
           f"всё до знака — антецедент, после — консеквент.\n\n" +
           "\n".join(f"{i + 1}. ${tex(g)}$ — антецедент ${tex(a)}$, консеквент ${tex(b)}$." for i, (g, a, b) in enumerate(ps)))
    return card(level, "A", "iso", "short", src, "условные высказывания, D2", cond, ans, sol)


def clear_d2(f):
    """Формулы, где D2 (второе) читается однозначно: у каждого условного обе части либо без →, либо с →;
    вне условных высказываний нет частей без →."""
    for g in F.conds(f):
        if F.has(g[1]) != F.has(g[2]):
            return False
    def outer(h):
        if h[0] in F.COND:
            return True
        if h[0] == "v":
            return False
        if h[0] == "neg":
            return outer(h[1])
        return all(outer(t) for t in h[1])
    return outer(f)


def elem(f):
    out = []
    for g in F.conds(f):
        if not F.has(g[1]) and not F.has(g[2]):
            for t in (g[1], g[2]):
                if t not in out:
                    out.append(t)
    return out


def d2_formula():
    def inner():
        return KINDS[rnd.choice(["if", "if", "ifn", "ifq"])](plain(1), plain(1))

    def build(d):
        if d == 0:
            return inner()
        r = rnd.random()
        if r < 0.4:
            return KINDS[rnd.choice(["if", "if", "ifq"])](build(d - 1), build(d - 1))
        if r < 0.7:
            return C(build(d - 1), build(d - 1))
        if r < 0.85:
            return W(build(d - 1), build(d - 1))
        return N(build(d - 1))
    for _ in range(500):
        f = build(2)
        if clear_d2(f) and 14 <= F.size(f) <= 40 and not nn(f) and len(F.conds(f)) >= 2:
            return f


def c_elem(level=5, src="с. 82, гл. 6, § 1"):
    fs = []
    while len(fs) < 3:
        f = d2_formula()
        if f and f not in fs:
            fs.append(f)
    cond = (f"Буквы $x, y, z, v, u$ — высказывания, в которые не входит оператор условности. Для каждого высказывания найдите "
            f"все элементарные высказывания по D2 (второму) § 1 и объясните, по какому пункту каждое элементарно. {D2E}\n\n" +
            "\n".join(f"{L[i]}) ${tex(f)}$" for i, f in enumerate(fs)))
    ans = "; ".join(f"{L[i]}) " + ", ".join(f"${tex(t)}$" for t in elem(f)) for i, f in enumerate(fs))
    sol = "\n".join(f"{L[i]}) Условные высказывания, в части которых оператор условности не входит: " +
                    ", ".join(f"${tex(g)}$" for g in F.conds(f) if not F.has(g[1])) +
                    " — их антецеденты и консеквенты элементарны по п. 1; по п. 2 они элементарны и во всём высказывании; "
                    "высказывания с оператором условности по п. 3 не элементарны. Итого: " +
                    ", ".join(f"${tex(t)}$" for t in elem(f)) + "." for i, f in enumerate(fs))
    return card(level, "A", "iso", "short", src, "условные высказывания, элементарные высказывания", cond, ans, sol)


def c_parse_diag(level=5, src="с. 82, гл. 6, § 1"):
    f = d2_formula()
    ps = parts_of(f)
    el = elem(f)
    # ошибка 1: переставлены антецедент и консеквент в одном условном высказывании
    i = rnd.randrange(len(ps))
    shown = []
    for k, (g, a, b) in enumerate(ps):
        shown.append(f"${tex(g)}$: антецедент ${tex(b if k == i else a)}$, консеквент ${tex(a if k == i else b)}$")
    # ошибка 2: в список элементарных добавлено условное высказывание
    extra = [g for g in F.conds(f) if not F.has(g[1])][0]
    el_bad = el + [extra]
    cond = (f"Буквы $x, y, z, v, u$ — высказывания без оператора условности. Студент разобрал высказывание ${tex(f)}$:\n\n" +
            "\n".join(f"{k + 1}. {s_}." for k, s_ in enumerate(shown)) +
            f"\n{len(shown) + 1}. Элементарные высказывания по D2 (второму): " + ", ".join(f"${tex(t)}$" for t in el_bad) + "." +
            f"\n\nВ разборе ровно две ошибки. Найдите их, назовите нарушенное определение и исправьте. {D1} {D2E}")
    g, a, b = ps[i]
    ans = (f"Строка {i + 1}: у ${tex(g)}$ антецедент ${tex(a)}$, консеквент ${tex(b)}$ (D2 § 1); строка {len(shown) + 1}: "
           f"${tex(extra)}$ не элементарно (D2 второе, п. 3).")
    sol = (f"1. В $(x \\rightarrow y)$ антецедент стоит до знака, консеквент — после (D2 § 1, с. 82): у ${tex(g)}$ антецедент "
           f"${tex(a)}$, консеквент ${tex(b)}$.\n2. По D2 (второму) элементарны антецеденты и консеквенты, в которые не входит "
           f"оператор условности (п. 1), и они же в объемлющих высказываниях (п. 2); само ${tex(extra)}$ содержит оператор "
           f"условности и по п. 3 элементарным не является. Верный список: " + ", ".join(f"${tex(t)}$" for t in el) + ".")
    return card(level, "E", "vary", "text", src, "условные высказывания, D2, диагностика", cond, ans, sol)


# ---------------------------------------------------------------- естественный язык
PH = {"x": ("идёт дождь", "дождя нет"), "y": ("улица мокрая", "улица сухая"), "z": ("дует ветер", "ветра нет"),
      "v": ("горит фонарь", "фонарь не горит"), "u": ("открыт зонт", "зонт закрыт")}
PH2 = {"x": ("ток включён", "ток выключен"), "y": ("лампа горит", "лампа не горит"), "z": ("цепь замкнута", "цепь разомкнута"),
       "v": ("предохранитель цел", "предохранитель сгорел"), "u": ("реле сработало", "реле не сработало")}


def nat(f, ph, top=True):
    k = f[0]
    if k == "v":
        return ph[f[1]][0]
    if k == "neg":
        if f[1][0] == "v":
            return ph[f[1][1]][1]
        return "неверно, что " + nat(f[1], ph, False)
    if k == "conj":
        return " и ".join(nat(t, ph, False) for t in f[1])
    if k == "wdis":
        return " или ".join(nat(t, ph, False) for t in f[1])
    if k == "if":
        a = nat(f[1], ph, False)
        if f[1][0] == "if":
            a = "верно, что " + a
        b = nat(f[2], ph, False)
        return f"если {a}, то {b}"
    if k == "imp":
        return f"{nat(f[1], ph, False)} влечёт материально {nat(f[2], ph, False)}"
    raise ValueError(k)


def cap(s):
    return s[0].upper() + s[1:]


def nat_shapes(ph):
    out = []
    while len(out) < 4:
        X, Y, Zz = (lit() for _ in range(3))
        if len({X[1] if X[0] == 'neg' else X, Y[1] if Y[0] == 'neg' else Y, Zz[1] if Zz[0] == 'neg' else Zz}) < 3:
            continue
        f = rnd.choice([IF(X, IF(Y, Zz)), IF(IF(X, Y), Zz), IF(C(X, Y), Zz), IF(X, W(Y, Zz)), IF(W(X, Y), N(C(Y, Zz)))
                        if False else IF(W(X, Y), Zz), IF(X, C(Y, Zz))])
        if f not in out:
            out.append(f)
    return out


def c_nat_formal(level=5, src="с. 82, гл. 6, § 1"):
    ph = rnd.choice([PH, PH2])
    fs = nat_shapes(ph)
    leg = "; ".join(f"${k}$ — «{a}»" for k, (a, _) in ph.items())
    cond = (f"Обозначения: {leg}; отрицание буквы читается как противоположное высказывание. Запишите каждое высказывание "
            f"символически по D1 § 1 (с. 82), расставив скобки, и укажите антецедент и консеквент главного условного "
            f"высказывания.\n\n" + "\n".join(f"{L[i]}) «{cap(nat(f, ph))}»." for i, f in enumerate(fs)))
    ans = "; ".join(f"{L[i]}) ${tex(f)}$" for i, f in enumerate(fs))
    sol = "\n".join(f"{L[i]}) ${tex(f)}$: антецедент ${tex(f[1])}$, консеквент ${tex(f[2])}$." +
                    (" Оборот «если верно, что если …, то …» делает антецедентом условное высказывание." if f[1][0] == "if"
                     else " Консеквент сам — условное высказывание." if f[2][0] == "if" else "")
                    for i, f in enumerate(fs))
    return card(level, "T", "iso", "short", src, "условные высказывания, перевод", cond, ans, sol, form="nat")


def c_nat_e(level=6, src="с. 82, гл. 6, § 1"):
    ph = rnd.choice([PH, PH2])
    fs = nat_shapes(ph)
    wrong = rnd.sample(range(4), 2)
    shown = []
    for i, f in enumerate(fs):
        if i in wrong:
            if f[2][0] == "if":
                g = IF(IF(f[1], f[2][1]), f[2][2])
            elif f[1][0] == "if":
                g = IF(f[1][1], IF(f[1][2], f[2]))
            else:
                g = IF(f[2], f[1])
        else:
            g = f
        shown.append(g)
    leg = "; ".join(f"${k}$ — «{a}»" for k, (a, _) in ph.items())
    cond = (f"Обозначения: {leg}. Студент записал высказывания символически:\n\n" +
            "\n".join(f"{i + 1}. «{cap(nat(f, ph))}» — ${tex(g)}$." for i, (f, g) in enumerate(zip(fs, shown))) +
            "\n\nРовно две записи ошибочны. Найдите их, объясните ошибку (что стало антецедентом и консеквентом) и исправьте "
            "по D1–D2 § 1 (с. 82).")
    ans = "; ".join(f"{i + 1}: ${tex(fs[i])}$" for i in sorted(wrong)) + "."
    sol = []
    for i in sorted(wrong):
        f, g = fs[i], shown[i]
        if f[2][0] == "if":
            sol.append(f"{i + 1}. В «если A, то если B, то C» консеквент — условное высказывание «если B, то C»; студент сделал "
                       f"антецедентом ${tex(g[1])}$. Верно: ${tex(f)}$, антецедент ${tex(f[1])}$, консеквент ${tex(f[2])}$.")
        elif f[1][0] == "if":
            sol.append(f"{i + 1}. «Если верно, что если A, то B, — то C»: антецедент — условное высказывание ${tex(f[1])}$; "
                       f"студент переставил скобки. Верно: ${tex(f)}$.")
        else:
            sol.append(f"{i + 1}. Студент поменял местами антецедент и консеквент: в «если A, то B» антецедент — A (D2 § 1). "
                       f"Верно: ${tex(f)}$.")
    return card(level, "E", "vary", "text", src, "условные высказывания, перевод, диагностика", cond, ans,
                "\n".join(sol) + "\n\nОстальные записи верны.", form="nat")


# ---------------------------------------------------------------- § 2: условность и следование
SENT = [("ключ повернули", "дверь открыта"), ("вода нагрета до 100 °C", "вода кипит"), ("число делится на 4", "число чётное"),
        ("идёт дождь", "улица мокрая"), ("нажали выключатель", "лампа горит"), ("договор подписан", "сделка заключена")]


def c_comp(level=4, src="с. 83, гл. 6, § 2"):
    items = []
    pairs = rnd.sample(SENT, 4)
    forms = ["if", "ent", "if_ent", "ent_if"]
    rnd.shuffle(forms)
    for (a, b), fm in zip(pairs, forms):
        if fm == "if":
            items.append((f"Если {a}, то {b}", f"условное высказывание: высказывания «{a}» (антецедент), «{b}» (консеквент) и "
                          f"высказываниеобразующий оператор «если, то»"))
        elif fm == "ent":
            items.append((f"Из высказывания «{a}» следует высказывание «{b}»", f"высказывание о следовании: субъекты "
                          f"«высказывание „{a}“» и «высказывание „{b}“» и предикат «из первого следует второе»"))
        elif fm == "if_ent":
            items.append((f"Если из высказывания «{a}» следует высказывание «{b}», то верно: если {a}, то {b}",
                          f"условное высказывание; его антецедент — высказывание о следовании (субъекты «высказывание „{a}“», "
                          f"«высказывание „{b}“», предикат «из первого следует второе»), консеквент — условное высказывание "
                          f"«если {a}, то {b}» (высказывания и оператор)"))
        else:
            items.append((f"Из высказывания «если {a}, то {b}» следует высказывание «если неверно, что {b}, то неверно, что {a}»",
                          f"высказывание о следовании: субъекты — «высказывание „если {a}, то {b}“» и «высказывание „если "
                          f"неверно, что {b}, то неверно, что {a}“», предикат «из первого следует второе»; сами субъекты "
                          f"обозначают условные высказывания"))
    cond = ("По § 2 гл. 6 (с. 83) высказывание «Если $x$, то $y$» состоит из высказываний $x$, $y$ и высказываниеобразующего "
            "оператора, а «Из $x$ следует $y$» — из субъектов «высказывание $x$», «высказывание $y$» и предиката «из первого "
            "следует второе». Разберите состав каждого высказывания по этому образцу (если высказывание составное — и состав "
            "его частей).\n\n" + "\n".join(f"{L[i]}) «{t}»." for i, (t, _) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {'условное' if s_.startswith('условное') else 'о следовании'}" for i, (_, s_) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {s_[0].upper() + s_[1:]}." for i, (_, s_) in enumerate(items)) + (
        "\n\nСмешение двух видов — грубая ошибка (с. 83): в первом случае высказывания $x$, $y$ — части, во втором о них "
        "говорится как о предметах.")
    return card(level, "T", "iso", "short", src, "условность и следование", cond, ans, sol, form="nat")


SS_CRIT = ("Следование здесь — сильное следование $S^s$: $x \\vdash y$ доказуема в $S^s$ тогда и только тогда, когда это "
           "сильная тавтология — нет значений, где $x$ = 1, $y$ = 0, и в $y$ нет элементарных высказываний, отсутствующих в "
           "$x$ (гл. 2, § 2, MT5; гл. 1, § 4).")


P_STRONG = [lambda X, Y, Z: (C(X, Y), X), lambda X, Y, Z: (C(X, Y), W(X, Y)), lambda X, Y, Z: (C(X, Y), C(Y, X)),
            lambda X, Y, Z: (C(X, N(X)), X), lambda X, Y, Z: (C(N(X), N(Y)), N(X)), lambda X, Y, Z: (C(X, Y, Z), C(X, Z))]
P_NON = [lambda X, Y, Z: (W(X, Y), X), lambda X, Y, Z: (X, C(X, Y)), lambda X, Y, Z: (X, W(X, Y)),
         lambda X, Y, Z: (X, W(Y, N(Y))), lambda X, Y, Z: (W(X, Y), C(X, Y)), lambda X, Y, Z: (C(X, Y), Z)]


def principle_items(n=4):
    items = []
    want = [True, False, True, False]
    while len(items) < n:
        X, Y, Z = (N(t) if rnd.random() < 0.3 else t for t in rnd.sample([x, y, z, v], 3))
        a, b = rnd.choice(P_STRONG if want[len(items)] else P_NON)(X, Y, Z)
        if nn(a) or nn(b) or (a, b) in items:
            continue
        if F.strong_p(a, b) == want[len(items)]:
            items.append((a, b))
    rnd.shuffle(items)
    return items


def principle_just(a, b):
    if F.strong_p(a, b):
        return True, "из $X$ следует $Y$ (сильная тавтология); по принципу § 2 истинно «Если $X$, то $Y$» — в $S^5_{if}$ это R1 § 8"
    e = F.entails([a], b, F.atoms(a) | F.atoms(b))
    if e:
        return False, f"при {lit_tex(e)} $X$ = 1, $Y$ = 0 — из $X$ не следует $Y$; логика по принципу § 2 не решает вопроса"
    new = ", ".join(f"${t}$" for t in sorted(F.atoms(b) - F.atoms(a)))
    return False, f"тавтология, но в $Y$ входит {new}, которого нет в $X$, — сильного следования нет; принцип § 2 неприменим"


def c_principle(level=6, src="с. 83, гл. 6, § 2"):
    ph = rnd.choice([PH, PH2])
    items = principle_items()
    leg = "; ".join(f"${k}$ — «{a}»" for k, (a, _) in ph.items() if k in "xyzv")
    cond = (f"Обозначения: {leg}. По § 2 гл. 6 (с. 83) вопрос об истинности «Если $x$, то $y$» решается в логике лишь в силу "
            f"принципа: если верно, что из $x$ следует $y$, то верно «Если $x$, то $y$»; в остальных случаях логика не "
            f"компетентна. Для каждой пары высказываний $X$, $Y$ исследуйте, позволяет ли логика по этому принципу признать "
            f"истинным «Если $X$, то $Y$», и обоснуйте значениями. {SS_CRIT}\n\n" +
            "\n".join(f"{L[i]}) $X = {tex(a)}$ («{nat(a, ph)}»), $Y = {tex(b)}$ («{nat(b, ph)}»)" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) " + ("позволяет" if principle_just(a, b)[0] else "не позволяет") for i, (a, b) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {cap(principle_just(a, b)[1])}." for i, (a, b) in enumerate(items))
    return card(level, "C", "open", "short", src, "условность и следование", cond, ans, sol, form="nat")


def c_principle_e(level=6, src="с. 83, гл. 6, § 2"):
    ph = rnd.choice([PH, PH2])
    items = principle_items()
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, (a, b) in enumerate(items):
        ok, just = principle_just(a, b)
        claim = ok if i not in wrong else not ok
        reason = ("высказывания связаны по смыслу" if claim and not ok else "из $X$ следует $Y$" if claim else
                  "условное высказывание не есть высказывание о следовании" if ok else "сильного следования нет")
        lines.append(f"{i + 1}. «Если {nat(a, ph)}, то {nat(b, ph)}» ($X = {tex(a)}$, $Y = {tex(b)}$) — логика "
                     f"{'позволяет' if claim else 'не позволяет'} признать истинным: {reason}.")
        if i in wrong:
            ans.append(f"{i + 1}: {'позволяет' if ok else 'не позволяет'}")
            sol.append(f"{i + 1}. Неверно: {just}.")
    leg = "; ".join(f"${k}$ — «{a}»" for k, (a, _) in ph.items() if k in "xyzv")
    cond = (f"Обозначения: {leg}. Студент применял принцип § 2 гл. 6 (с. 83): если верно, что из $X$ следует $Y$, то верно "
            f"«Если $X$, то $Y$»; в остальных случаях логика не компетентна.\n\n" + "\n".join(lines) +
            f"\n\nРовно два вывода неверны. Найдите их и исправьте, обосновав значениями. {SS_CRIT}")
    return card(level, "E", "vary", "text", src, "условность и следование, диагностика", cond, "; ".join(ans) + ".",
                "\n".join(sol) + "\n\nОстальные выводы верны.", form="nat")


def c_s5_r1(level=7, src="с. 83, 91–92, гл. 6, § 2, 8"):
    import hard06_sys as SY
    items = []
    want = ["strong", "par", "no", rnd.choice(["strong", "par"])]
    while len(items) < 4:
        lt = rnd.sample("xyz", 2)
        a = SY.rnd_w(lt, 2)
        b = SY.rnd_w(lt + (["v"] if want[len(items)] == "par" else []), 2)
        if a == b or nn(a) or nn(b) or not 6 <= F.size(a) + F.size(b) <= 24:
            continue
        k = "strong" if F.strong_p(a, b) else "par" if F.taut_imp(a, b) else "no"
        if k == want[len(items)] and (a, b) not in items:
            items.append((a, b))
    rnd.shuffle(items)
    cond = (f"{CV} Принцип § 2 (с. 83) «если верно, что из $x$ следует $y$, то верно “Если $x$, то $y$”» в $S^5_{{if}}$ выражен "
            f"правилом R1 § 8: если $x \\vdash y$, то $\\vdash (x \\rightarrow y)$ (с. 91). Для каждой формулы установите: "
            f"получается ли она по R1 § 8 из теоремы $S^s$; если нет — доказуема ли она в $S^5_{{if}}$ иначе. {SS_CRIT} "
            f"{SY.S5_CRIT}\n\n" + "\n".join(f"{L[i]}) $\\vdash ({tex(a)} \\rightarrow {tex(b)})$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        if F.strong_p(a, b):
            ans.append(f"{L[i]}) по R1 § 8")
            sol.append(f"{L[i]}) ${tex(a)} \\vdash {tex(b)}$ — сильная тавтология, теорема $S^s$; по R1 § 8 — $\\vdash ({tex(a)} "
                       f"\\rightarrow {tex(b)})$.")
        elif F.taut_imp(a, b):
            new = ", ".join(f"${t}$" for t in sorted(F.atoms(b) - F.atoms(a)))
            ans.append(f"{L[i]}) не по R1, но доказуема")
            sol.append(f"{L[i]}) В заключение входит {new}: ${tex(a)} \\vdash {tex(b)}$ не теорема $S^s$, R1 § 8 сразу не "
                       f"применить. Но ${tex(a)} \\supset {tex(b)}$ — тавтология, и по MT4 гл. 4 и MT5 § 8 формула доказуема. "
                       f"Логика здесь даёт истинное условное высказывание без следования — ср. с. 83: не всегда, когда "
                       f"истинно «Если $x$, то $y$», истинно «Из $x$ следует $y$».")
        else:
            e = F.entails([a], b, F.atoms(a) | F.atoms(b))
            ans.append(f"{L[i]}) недоказуема")
            sol.append(f"{L[i]}) При {lit_tex(e)} антецедент 1, консеквент 0: по MT2 § 8 недоказуема.")
    return card(level, "S", "transfer", "short", src, "условность и следование, S5if", cond, "; ".join(ans) + ".",
                "\n".join(sol), system="S^5_if")


CLAIMS2 = [
    ("Высказывание «Если $x$, то $y$» состоит из высказываний $x$, $y$ и высказываниеобразующего оператора", True, "с. 83."),
    ("Высказывание «Из $x$ следует $y$» состоит из высказываний $x$, $y$ и оператора следования", False,
     "оно состоит из субъектов «высказывание $x$», «высказывание $y$» и предиката «из первого следует второе» (с. 83)."),
    ("Вопрос о том, когда истинны высказывания вида «Из $x$ следует $y$», решается в рамках логики", True, "с. 83: это главная задача логики."),
    ("Логика полностью решает вопрос об истинности высказываний «Если $x$, то $y$»", False,
     "он лишь частично решается в логике — в силу принципа «если из $x$ следует $y$, то верно “Если $x$, то $y$”» (с. 83)."),
    ("Если верно «Если $x$, то $y$», то из $x$ следует $y$", False, "не во всех случаях, когда истинно «Если $x$, то $y$», "
     "истинно «Из $x$ следует $y$» (с. 83)."),
    ("Если верно, что из $x$ следует $y$, то верно «Если $x$, то $y$»", True, "это принцип, через который логика судит об "
     "условных высказываниях (с. 83)."),
    ("Истинное условное высказывание всегда имеет общие термины или высказывания в антецеденте и консеквенте", False,
     "известны многочисленные истинные условные высказывания без одинаковых терминов и высказываний (с. 83)."),
    ("Смешение «Если $x$, то $y$» и «Из $x$ следует $y$» — грубая ошибка", True, "с. 83."),
    ("Когда условное высказывание получено не из отношения следования, логика совершенно не компетентна судить о его "
     "истинности", True, "с. 83."),
    ("Условные высказывания в науке получаются только из отношений следования", False, "они получаются из наблюдений и "
     "экспериментов или постулируются ради каких-то целей (с. 85)."),
]
CLAIMS3 = [
    ("Для материальной импликации $xy \\vdash (x \\supset y)$ — тавтология, доказуемая в $S^s$", True, "с. 84 (полнота $S^s$)."),
    ("Для оператора условности верно $xy \\vdash (x \\rightarrow y)$", False, "истинность $x$ и $y$ в какой-то ситуации ещё не "
     "даёт права принимать $y$ всякий раз, когда истинно $x$ (с. 84)."),
    ("Из $\\sim(x \\rightarrow y)$ следует $x\\sim y$", False, "утверждение $\\sim(x \\rightarrow y) \\vdash x\\sim y$ ошибочно "
     "(с. 84): отрицание $x \\rightarrow y$ означает лишь, что признание $x$ не даёт права на признание $y$."),
    ("$(xy \\rightarrow z) \\vdash (x \\rightarrow z) \\vee (y \\rightarrow z)$ ошибочно, хотя аналог для $\\supset$ — тавтология", True,
     "с. 84–85: $xy \\rightarrow xy$ истинно, а $x \\rightarrow xy$ и $y \\rightarrow xy$ могут быть ложными."),
    ("Для оператора условности, как и для $\\supset$, верно $(x \\rightarrow y)x \\vdash y$", True, "сходные утверждения (с. 85)."),
    ("Для оператора условности верно $(x \\rightarrow y) \\vdash (\\sim y \\rightarrow \\sim x)$", True, "сходные утверждения (с. 85)."),
    ("В математике отождествление $\\rightarrow$ и $\\supset$ возникло потому, что антецеденты и консеквенты математических "
     "условных высказываний универсальны", True, "с. 85: они не меняют значений истинности в зависимости от условий, места, "
     "времени."),
    ("Всякому приемлемому $x \\vdash y$ с оператором $\\supset$ соответствует приемлемое утверждение, полученное заменой "
     "$\\supset$ на $\\rightarrow$ хотя бы в одном месте", False, "это отвергается: таково априорное основание теории условных "
     "высказываний (с. 86)."),
    ("Между $\\rightarrow$ и $\\supset$ есть логическая связь: $\\vdash ((x \\rightarrow y) \\rightarrow (x \\supset y))$", True, "с. 86."),
    ("Из истинности $x \\supset y$ следует истинность $x \\rightarrow y$", False, "не всякому истинному $x \\supset y$ соответствует "
     "истинное $x \\rightarrow y$; обратное верно (с. 88)."),
]


# ---------------------------------------------------------------- § 3: ⊃ и →
IMPL = {
    "c1": lambda X, Y, Z, Vv: (C(X, Y), IMP(X, Y)),
    "c2": lambda X, Y, Z, Vv: (C(N(X), N(Y)), IMP(X, Y)),
    "c3": lambda X, Y, Z, Vv: (C(N(X), Y), IMP(X, Y)),
    "c4": lambda X, Y, Z, Vv: (N(C(X, N(Y))), IMP(X, Y)),
    "c5": lambda X, Y, Z, Vv: (N(IMP(X, Y)), C(X, N(Y))),
    "c6": lambda X, Y, Z, Vv: (W(N(X), Y), IMP(X, Y)),
    "c7": lambda X, Y, Z, Vv: (IMP(C(X, Y), W(Z, Vv)), W(IMP(X, Z), IMP(Y, Vv))),
    "c8": lambda X, Y, Z, Vv: (IMP(C(X, Y), Z), W(IMP(X, Z), IMP(Y, Z))),
    "s1": lambda X, Y, Z, Vv: (C(IMP(X, Y), X), Y),
    "s2": lambda X, Y, Z, Vv: (C(IMP(X, Y), N(Y)), N(X)),
    "s3": lambda X, Y, Z, Vv: (IMP(X, Y), IMP(N(Y), N(X))),
    "s4": lambda X, Y, Z, Vv: (C(IMP(X, Y), IMP(Y, Z)), IMP(X, Z)),
}


def to_if(f):
    k = f[0]
    if k == "v":
        return f
    if k == "neg":
        return N(to_if(f[1]))
    if k == "imp":
        return IF(to_if(f[1]), to_if(f[2]))
    return (k, tuple(to_if(t) for t in f[1]))


def imp_item(keys):
    for _ in range(500):
        k = rnd.choice(keys)
        args = comp(4)
        if not args:
            continue
        a, b = IMPL[k](*args)
        A, B = to_if(a), to_if(b)
        if nn(a) or nn(b) or not F.strong_p(a, b) or not F.flat(C(A, B)):
            continue
        r = F.sem_robust(A, B)
        if r is None:
            continue
        return k, a, b, A, B, r
    raise RuntimeError


def c_imp_series(level=6, src="с. 84–85, гл. 6, § 3"):
    keys_bad = ["c1", "c2", "c3", "c4", "c5", "c6", "c7", "c8"]
    keys_good = ["s1", "s2", "s3", "s4"]
    items = [imp_item(keys_bad), imp_item(keys_bad), imp_item(keys_good), imp_item(rnd.choice([keys_bad, keys_good]))]
    rnd.shuffle(items)
    cond = (f"{CV} Для каждой формулы с $\\supset$ проверьте, что она доказуема в $S^s$ (сильная тавтология), а затем исследуйте "
            f"формулу, полученную заменой всех $\\supset$ на $\\rightarrow$, при интерпретации § 4 и обоснуйте значениями. "
            f"{INTERP}\n\n" + "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (_, a, b, *_) in enumerate(items)))
    ans, sol = [], []
    for i, (k, a, b, A, B, r) in enumerate(items):
        ans.append(f"{L[i]}) с $\\supset$ — доказуема; с $\\rightarrow$ — " + ("тавтология" if r[0] else "не тавтология"))
        sol.append(f"{L[i]}) ${ftex(a, b)}$: нет значений, где посылка 1, а заключение 0, новых букв нет — сильная тавтология, "
                   f"доказуема в $S^s$ (полнота, с. 84). С $\\rightarrow$: ${ftex(A, B)}$. " +
                   (explain_taut(A, B, "ср. сходные утверждения с. 85") if r[0] else explain_non(A, B, r[1]) +
                    " Ср. ошибочные утверждения с. 84."))
    return card(level, "C", "transfer", "short", src, "условность, материальная импликация", cond, "; ".join(ans) + ".",
                "\n".join(sol))


def c_imp_diag(level=6, src="с. 84–85, гл. 6, § 3"):
    items = [imp_item(["c1", "c2", "c3", "c4", "c5", "c6", "c7", "c8"]) for _ in range(2)] + \
        [imp_item(["s1", "s2", "s3", "s4"]) for _ in range(2)]
    rnd.shuffle(items)
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, (k, a, b, A, B, r) in enumerate(items):
        claim = r[0] if i not in wrong else not r[0]
        reason = ("аналог с $\\supset$ — тавтология" if claim and not r[0] else "приписав антецеденту 1, вынуждены приписать "
                  "консеквенту 1" if claim else "оператор условности не совпадает с материальной импликацией" if r[0] else
                  "условное высказывание заключения можно приписать 0 по пп. 7–8")
        lines.append(f"{i + 1}. ${ftex(A, B)}$ — {'тавтология' if claim else 'не тавтология'}: {reason}.")
        if i in wrong:
            ans.append(f"{i + 1}: {'тавтология' if r[0] else 'не тавтология'}")
            sol.append(f"{i + 1}. Неверно: " + (explain_taut(A, B, "сходное утверждение с. 85") if r[0] else
                                               "тавтологичность аналога с $\\supset$ ничего не решает (с. 84). " +
                                               explain_non(A, B, r[1])))
    cond = (f"{CV} Студент исследовал при интерпретации § 4 формулы, полученные из тавтологий с $\\supset$ заменой $\\supset$ на "
            f"$\\rightarrow$:\n\n" + "\n".join(lines) + f"\n\nРовно два вывода неверны. Найдите их, назовите нарушенный пункт "
            f"правил интерпретации и дайте верный ответ. {INTERP}")
    return card(level, "E", "vary", "text", src, "условность, материальная импликация, диагностика", cond,
                "; ".join(ans) + ".", "\n".join(sol) + "\n\nОстальные выводы верны.")


def imp_positions(f, path=()):
    out = []
    k = f[0]
    if k == "imp":
        out.append(path)
        out += imp_positions(f[1], path + (1,))
        out += imp_positions(f[2], path + (2,))
    elif k == "neg":
        out += imp_positions(f[1], path + (1,))
    elif k in ("conj", "wdis"):
        for i, t in enumerate(f[1]):
            out += imp_positions(t, path + (("m", i),))
    return out


def replace_at(f, path):
    if not path:
        return IF(f[1], f[2])
    p = path[0]
    if f[0] == "imp":
        return IMP(replace_at(f[1], path[1:]), f[2]) if p == 1 else IMP(f[1], replace_at(f[2], path[1:]))
    if f[0] == "neg":
        return N(replace_at(f[1], path[1:]))
    i = p[1]
    ts = list(f[1])
    ts[i] = replace_at(ts[i], path[1:])
    return (f[0], tuple(ts))


def c_apriori(level=7, src="с. 86, гл. 6, § 3"):
    for _ in range(500):
        k = rnd.choice(["s4", "s1", "s3", "c8", "s2", "c7"])
        args = comp(4)
        if not args:
            continue
        a, b = IMPL[k](*args)
        if nn(a) or nn(b) or not F.strong_p(a, b):
            continue
        pos = [("п", p) for p in imp_positions(a)] + [("з", p) for p in imp_positions(b)]
        if not 2 <= len(pos) <= 3:
            continue
        res = []
        okk = True
        for side, p in pos:
            A, B = (replace_at(a, p), b) if side == "п" else (a, replace_at(b, p))
            if not F.flat(C(A, B)):
                okk = False
                break
            r = F.sem_robust(A, B)
            if r is None:
                okk = False
                break
            res.append((A, B, r))
        if okk and any(r[0] for *_, r in res) != all(r[0] for *_, r in res) or (okk and len(res) == 3):
            break
    cond = (f"{CV} Формула ${ftex(a, b)}$ — тавтология и доказуема в $S^s$. По с. 86 «не всякому приемлемому утверждению "
            f"$x \\vdash y$, содержащему $\\supset$, соответствует приемлемое утверждение, получающееся заменой $\\supset$ на "
            f"$\\rightarrow$ по крайней мере в одном месте». Замените $\\supset$ на $\\rightarrow$ поочерёдно в каждом месте (по "
            f"одному) и исследуйте каждую полученную формулу при интерпретации § 4, обосновав значениями. {INTERP}")
    ans, sol = [], []
    for i, (A, B, r) in enumerate(res):
        ans.append(f"{L[i]}) ${ftex(A, B)}$ — " + ("тавтология" if r[0] else "не тавтология"))
        sol.append(f"{L[i]}) ${ftex(A, B)}$. " + (explain_taut(A, B) if r[0] else explain_non(A, B, r[1])))
    return card(level, "C", "transfer", "short", src, "условность, материальная импликация, априорная предпосылка", cond,
                "; ".join(ans) + ".", "\n".join(sol))


def c_nat_counter(level=6, src="с. 84–88, гл. 6, § 3–4", diag=False):
    ph = rnd.choice([PH, PH2])
    for _ in range(300):
        k = rnd.choice(["c1", "c2", "c3", "c7", "c8", "c6"])
        X, Y, Z, Vv = (lit() for _ in range(4))
        if len({t[1] if t[0] == "neg" else t for t in (X, Y, Z, Vv)}) < 4:
            continue
        a, b = IMPL[k](X, Y, Z, Vv)
        A, B = to_if(a), to_if(b)
        if nn(A) or nn(B) or not F.flat(C(A, B)):
            continue
        r = F.sem_robust(A, B)
        if r and not r[0]:
            break
    leg = "; ".join(f"${kk}$ — «{p}»" for kk, (p, _) in ph.items())
    text = f"«{cap(nat(A, ph))}; следовательно, {nat(B, ph)}»"
    if not diag:
        cond = (f"Обозначения: {leg}. Запишите рассуждение {text} формулой с оператором условности и постройте по правилам § 4 "
                f"приписывание значений, при котором посылка истинна (1), а заключение ложно (0); объясните, почему для "
                f"материальной импликации такое приписывание невозможно. {INTERP}")
        ans = f"${ftex(A, B)}$; например, " + c_tex(r[1][1]) + "; " + lit_tex(r[1][0]) + "."
        sol = (f"Формула: ${ftex(A, B)}$. " + explain_non(A, B, r[1]) + f" Для $\\supset$: ${ftex(a, b)}$ — тавтология (нет "
               f"значений, где посылка 1, а заключение 0), так что там приписывание невозможно; различие — в том, что "
               f"$x \\rightarrow y$ может иметь значение 0 и при $x = 1$, $y = 1$, и при $x = 0$ (с. 88).")
        return card(level, "V", "open", "build", src, "условность, материальная импликация, контрпример", cond, ans, sol,
                    form="nat")
    cond = (f"Обозначения: {leg}. Студент утверждает: «Рассуждение {text} правильно: если записать его с материальной "
            f"импликацией, получится ${ftex(a, b)}$ — тавтология, доказуемая в $S^s$». Найдите ошибку и подтвердите "
            f"приписыванием значений по § 4. {INTERP}")
    ans = f"Неверно: $\\rightarrow$ не есть $\\supset$ (с. 84); ${ftex(A, B)}$ — не тавтология: " + c_tex(r[1][1]) + "; " + \
        lit_tex(r[1][0]) + "."
    sol = ("Отождествление оператора условности с материальной импликацией ошибочно (§ 3, с. 83–84): тавтологичность формулы "
           f"с $\\supset$ ничего не говорит о формуле с $\\rightarrow$. " + explain_non(A, B, r[1]))
    return card(level, "E", "open", "text", src, "условность, материальная импликация, диагностика", cond, ans, sol, form="nat")
