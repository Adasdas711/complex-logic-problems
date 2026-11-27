"""Трудные задачи раздела 18, часть 2: степени истинности (§ 5), вероятности (§ 16), существование энок и состояний (§ 9),
предикат M для родовых состояний (§ 11), классы (§ 6), ряды (§ 23–26), модальные определения (§ 10, 12, 13).
Вызывается из g18_hard.main(); все значения и выводы считает и проверяет программа.
"""
import itertools

from g18 import tx, tm, items, ans_items

card = fresh = rnd = None
LET = ["x", "y", "z", "w", "u"]


# ---------------------------------------------------------------- формулы: ('v', x) | ('n', F) | ('and', F, G) | ('or', F, G)

def ftex(f, top=True):
    k = f[0]
    if k == "v":
        return f[1]
    if k == "n":
        g = f[1]
        return "{\\sim}" + (g[1] if g[0] == "v" else "(" + ftex(g, True) + ")")
    s = ftex(f[1], False) + (" \\wedge " if k == "and" else " \\vee ") + ftex(f[2], False)
    return s if top else "(" + s + ")"


def letters(f):
    return {f[1]} if f[0] == "v" else set().union(*(letters(g) for g in f[1:]))


def depth(f):
    return 0 if f[0] == "v" else 1 + max(depth(g) for g in f[1:])


def size(f):
    return 1 if f[0] == "v" else 1 + sum(size(g) for g in f[1:])


def rand_f(d, lets, neg=True):
    if d == 0 or (d < 3 and rnd.random() < 0.25):
        a = ("v", rnd.choice(lets))
        return ("n", a) if neg and rnd.random() < 0.3 else a
    if neg and rnd.random() < 0.15:
        return ("n", rand_f(d - 1, lets, neg))
    return (rnd.choice(["and", "or"]), rand_f(d - 1, lets, neg), rand_f(d - 1, lets, neg))


def subs(f):
    """Подформулы снизу вверх (без повторов)."""
    out = []
    def go(g):
        if g[0] != "v":
            for h in g[1:]:
                go(h)
        if g not in out:
            out.append(g)
    go(f)
    return out


def truth(f, val):
    k = f[0]
    if k == "v":
        return val[f[1]]
    if k == "n":
        return not truth(f[1], val)
    a, b = truth(f[1], val), truth(f[2], val)
    return (a and b) if k == "and" else (a or b)


def clean(f):
    """Нет узлов с одинаковыми членами, двойного отрицания и пар x, ~x в одном узле."""
    if f[0] == "v":
        return True
    if f[0] == "n":
        return f[1][0] != "n" and clean(f[1])
    a, b = f[1], f[2]
    if a == b or a == ("n", b) or b == ("n", a):
        return False
    return clean(a) and clean(b)


def good_long(f, need_d=3, min_size=7):
    return depth(f) >= need_d and size(f) >= min_size and len(letters(f)) >= 3 and clean(f)


# ================================================================ § 5 степени истинности

V5 = ("Буквы $x, y, z, w, u$ — высказывания; $v(x)$ — степень истинности $x$. По с. 60: "
      "$\\vdash v(x \\wedge y) = min(v(x), v(y))$; $\\vdash v(x \\vee y) = max(v(x), v(y))$.")
VV = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]


def vval(f, v):
    if f[0] == "v":
        return v[f[1]]
    a, b = vval(f[1], v), vval(f[2], v)
    return min(a, b) if f[0] == "and" else max(a, b)


def vsteps(f, v):
    lines = []
    for g in subs(f):
        if g[0] == "v":
            continue
        a, b = vval(g[1], v), vval(g[2], v)
        op = "min" if g[0] == "and" else "max"
        lines.append(f"$v({ftex(g)}) = {op}({tm(a)}, {tm(b)}) = {tm(vval(g, v))}$")
    return lines


def v_series():
    def make():
        lets = LET[:5]
        v = {x: rnd.choice(VV) for x in lets}
        fs = []
        while len(fs) < 4:
            f = rand_f(3, lets, neg=False)
            if good_long(f, 3, 7) and f not in fs:
                fs.append(f)
        given = ", ".join(f"$v({x}) = {tm(v[x])}$" for x in lets)
        U = (f"{V5} Известно: {given}. Найдите степень истинности каждой формулы; для каждой подформулы укажите, "
             f"по какому правилу получено значение.\n\n" + items([f"${ftex(f)}$" for f in fs]))
        A = ans_items([f"${tm(vval(f, v))}$" for f in fs])
        R = "\n\n".join(f"{'абвг'[i]}) " + "; ".join(vsteps(f, v)) + "." for i, f in enumerate(fs))
        return U, A, R + "\n\nПравила для $\\wedge$ и $\\vee$ — с. 60."
    r = fresh(make)
    if r:
        card(5, 4, "C", "iso", "def", "sym", "short", "с. 60, гл. 2, § 5", ["степени истинности"], *r)


def v_errors():
    def make():
        lets = LET[:5]
        v = {x: rnd.choice(VV) for x in lets}
        f = None
        while not f or not good_long(f, 3, 9) or len([g for g in subs(f) if g[0] != "v"]) < 5:
            f = rand_f(3, lets, neg=False)
        nodes = [g for g in subs(f) if g[0] != "v"]
        # студент: в двух узлах перепутал min и max; ошибки должны менять значение узла
        bad = None
        for pair in itertools.combinations(range(len(nodes)), 2):
            ok = all(min(vval(nodes[i][1], v), vval(nodes[i][2], v)) != max(vval(nodes[i][1], v), vval(nodes[i][2], v)) for i in pair)
            if ok:
                bad = pair
                if rnd.random() < 0.4:
                    break
        if not bad:
            return None
        # значения студента (ошибки распространяются)
        sv = {}
        lines = []
        def sval(g):
            if g[0] == "v":
                return v[g[1]]
            return sv[g]
        for i, g in enumerate(nodes):
            a, b = sval(g[1]), sval(g[2])
            op = "min" if g[0] == "and" else "max"
            if i in bad:
                op = "max" if op == "min" else "min"
            sv[g] = min(a, b) if op == "min" else max(a, b)
            lines.append(f"$v({ftex(g)}) = {op}({tm(a)}, {tm(b)}) = {tm(sv[g])}$")
        given = ", ".join(f"$v({x}) = {tm(v[x])}$" for x in lets)
        U = (f"{V5} Известно: {given}. Студент вычислил $v({ftex(f)})$ так:\n\n" + "\n".join(f"{i+1}. {s}" for i, s in enumerate(lines))
             + "\n\nВ вычислении ровно две ошибки в выборе правила. Найдите их, назовите нарушенное правило и найдите верное значение.")
        A = ("Ошибки в строках " + " и ".join(str(i + 1) for i in bad) + ": для $\\wedge$ берётся min, для $\\vee$ — max (с. 60); "
             f"верно $v({ftex(f)}) = {tm(vval(f, v))}$.")
        R = ("Строки " + ", ".join(f"{i+1} (${ftex(nodes[i])}$ — " + ("конъюнкция, нужен min" if nodes[i][0] == 'and' else "дизъюнкция, нужен max") + ")" for i in bad)
             + ". Верное вычисление:\n\n" + "\n".join(f"{i+1}. {s}" for i, s in enumerate(vsteps(f, v))) + "\n\nПравила — с. 60.")
        return U, A, R
    r = fresh(make)
    if r:
        card(5, 6, "E", "vary", "def", "sym", "text", "с. 60, гл. 2, § 5", ["степени истинности", "диагностика"], *r)


def v_open():
    def make():
        lets = LET[:4]
        v = {x: rnd.choice(VV) for x in lets}
        f = None
        while not f or not good_long(f, 3, 7) or "z" not in letters(f):
            f = rand_f(3, lets, neg=False)
        t = rnd.choice(VV)
        ok = [c for c in VV if vval(f, dict(v, z=c)) == t]
        lo, hi = vval(f, dict(v, z=0.1)), vval(f, dict(v, z=0.9))
        if lo == hi:
            return None
        given = ", ".join(f"$v({x}) = {tm(v[x])}$" for x in lets if x != "z")
        cs = "; ".join(tm(c) for c in VV)
        U = (f"{V5} Известно: {given}; степень истинности $z$ может быть одним из чисел ${cs}$. Исследуйте, при каких из этих "
             f"значений $v(z)$ получится $v({ftex(f)}) = {tm(t)}$; если ни при каких — докажите это.")
        if ok:
            A = "При $v(z) \\in \\{" + "; ".join(tm(c) for c in ok) + "\\}$."
        else:
            A = f"Ни при каких: $v({ftex(f)})$ лежит между ${tm(lo)}$ и ${tm(hi)}$, а ${tm(t)}$ вне этих границ."
        R = ["1. Правила с. 60: $v$ конъюнкции — min, дизъюнкции — max. Функции min и max не убывают по каждому аргументу, "
             "поэтому с ростом $v(z)$ значение формулы не убывает.",
             f"2. При $v(z) = 0{{,}}1$: " + "; ".join(vsteps(f, dict(v, z=0.1))) + ".",
             f"3. При $v(z) = 0{{,}}9$: " + "; ".join(vsteps(f, dict(v, z=0.9))) + ".",
             f"4. Значит, при всех допустимых $v(z)$ значение формулы лежит между ${tm(lo)}$ и ${tm(hi)}$ (п. 1)."]
        if ok:
            R.append("5. Проверка по значениям: " + "; ".join(f"при $v(z) = {tm(c)}$ получаем ${tm(vval(f, dict(v, z=c)))}$" for c in VV) + ".")
        else:
            R.append(f"5. Число ${tm(t)}$ вне границ — такого значения нет.")
        return U, A, "\n".join(R)
    r = fresh(make)
    if r:
        card(5, 6, "C", "open", "def", "sym", "short", "с. 60, гл. 2, § 5", ["степени истинности", "открытый исход"], *r)


# ================================================================ § 16 вероятности

P16 = ("Буквы $x, y, z, w$ — высказывания; $p(x)$ — вероятность $sx$. По с. 76: $\\vdash 0 \\leqslant p(x) \\leqslant 1$; "
       "$\\vdash p(x \\wedge y) \\leqslant min(p(x), p(y))$; $\\vdash p(x \\vee y) \\geqslant max(p(x), p(y))$; $\\vdash p({\\sim}x) = 1 - p(x)$.")
PV = [0.1, 0.2, 0.25, 0.3, 0.4, 0.5, 0.6, 0.7, 0.75, 0.8, 0.9]


def pb(f, p):
    """Оценка [lo, hi] по строению формулы."""
    k = f[0]
    if k == "v":
        return (p[f[1]], p[f[1]])
    if k == "n":
        lo, hi = pb(f[1], p)
        return (round(1 - hi, 4), round(1 - lo, 4))
    (l1, h1), (l2, h2) = pb(f[1], p), pb(f[2], p)
    if k == "and":
        return (0.0, min(h1, h2))
    return (max(l1, l2), 1.0)


def ptxt(b, g):
    lo, hi = b
    if lo == hi:
        return f"$p({ftex(g)}) = {tm(lo)}$"
    return f"${tm(lo)} \\leqslant p({ftex(g)}) \\leqslant {tm(hi)}$"


def psteps(f, p):
    out = []
    for g in subs(f):
        if g[0] == "v":
            continue
        b = pb(g, p)
        if g[0] == "n":
            why = "по $p({\\sim}x) = 1 - p(x)$"
        elif g[0] == "and":
            why = "по $p(x \\wedge y) \\leqslant min$ и $p \\geqslant 0$"
        else:
            why = "по $p(x \\vee y) \\geqslant max$ и $p \\leqslant 1$"
        out.append(f"{ptxt(b, g)} [{why}]")
    return out


def p_formula(lets):
    f = None
    while not f or not good_long(f, 3, 6) or not any(g[0] == "n" and g[1][0] != "v" for g in subs(f)):
        f = rand_f(3, lets)
    return f


def p_series():
    def make():
        lets = LET[:4]
        p = {x: rnd.choice(PV) for x in lets}
        fs = []
        while len(fs) < 3:
            f = p_formula(lets)
            if f not in fs:
                fs.append(f)
        given = ", ".join(f"$p({x}) = {tm(p[x])}$" for x in lets)
        U = (f"{P16} Известно: {given}. Для каждой формулы найдите оценку вероятности, которую дают эти правила, применённые "
             "по строению формулы (снизу вверх), с обоснованием каждого шага.\n\n" + items([f"$p({ftex(f)})$" for f in fs]))
        A = ans_items([ptxt(pb(f, p), f) for f in fs])
        R = "\n\n".join(f"{'абв'[i]}) " + "; ".join(psteps(f, p)) + "." for i, f in enumerate(fs))
        return U, A, R + "\n\nПравила — с. 76. Для отрицания границы меняются местами: $1 - $ верхняя граница даёт нижнюю."
    r = fresh(make)
    if r:
        card(16, 4, "C", "iso", "def", "sym", "short", "с. 76, гл. 2, § 16", ["вероятность"], *r)


def p_errors():
    def make():
        lets = LET[:4]
        p = {x: rnd.choice(PV) for x in lets}
        f = p_formula(lets)
        nodes = [g for g in subs(f) if g[0] != "v"]
        cand = [i for i, g in enumerate(nodes) if g[0] in ("and", "n")]
        cand_and = [i for i in cand if nodes[i][0] == "and"]
        cand_n = [i for i in cand if nodes[i][0] == "n" and pb(nodes[i][1], p)[0] != pb(nodes[i][1], p)[1]]
        if not cand_and or not cand_n:
            return None
        ia, ineg = rnd.choice(cand_and), rnd.choice(cand_n)
        # студент: в ia пишет равенство min, в ineg забывает переставить границы; дальше — верные правила от его чисел
        sb = {}
        lines = []
        def get(g):
            return (p[g[1]], p[g[1]]) if g[0] == "v" else sb[g]
        for i, g in enumerate(nodes):
            if g[0] == "n":
                lo, hi = get(g[1])
                b = (round(1 - lo, 4), round(1 - hi, 4)) if i == ineg else (round(1 - hi, 4), round(1 - lo, 4))
                if b[0] > b[1]:
                    txt = f"${tm(b[0])} \\leqslant p({ftex(g)}) \\leqslant {tm(b[1])}$"
                else:
                    txt = ptxt(b, g)
            elif g[0] == "and":
                (l1, h1), (l2, h2) = get(g[1]), get(g[2])
                if i == ia:
                    m = min(h1, h2)
                    b = (m, m)
                else:
                    b = (0.0, min(h1, h2))
                txt = ptxt(b, g)
            else:
                (l1, h1), (l2, h2) = get(g[1]), get(g[2])
                b = (max(l1, l2), 1.0)
                txt = ptxt(b, g)
            sb[g] = b
            lines.append(txt)
        if sb[f] == pb(f, p):
            pass
        given = ", ".join(f"$p({x}) = {tm(p[x])}$" for x in lets)
        U = (f"{P16} Известно: {given}. Студент оценивал $p({ftex(f)})$ по строению формулы так:\n\n"
             + "\n".join(f"{i+1}. {s}" for i, s in enumerate(lines))
             + "\n\nВ рассуждении ровно две ошибки в применении правил. Найдите их, назовите нарушенные правила и дайте верную оценку.")
        bad = sorted([ia, ineg])
        A = (f"Строка {ia+1}: для конъюнкции правило даёт лишь $p \\leqslant min$, а не равенство; строка {ineg+1}: при "
             f"$p({{\\sim}}x) = 1 - p(x)$ границы меняются местами (с. 76). Верно: {ptxt(pb(f, p), f)}.")
        R = "Верная оценка снизу вверх:\n\n" + "\n".join(f"{i+1}. {s}" for i, s in enumerate(psteps(f, p)))
        return U, A, R
    r = fresh(make)
    if r:
        card(16, 6, "E", "vary", "def", "sym", "text", "с. 76, гл. 2, § 16", ["вероятность", "диагностика"], *r)


def p_open():
    def make():
        lets = LET[:4]
        p = {x: rnd.choice(PV) for x in lets}
        f = p_formula(lets)
        lo, hi = pb(f, p)
        if lo == 0 and hi == 1:
            return None
        if rnd.random() < 0.5 and (lo > 0.05 or hi < 0.95):
            t = round(rnd.choice([c for c in [i / 20 for i in range(1, 20)] if c < lo or c > hi] or [0.99]), 2)
        else:
            t = round(rnd.choice([c for c in [i / 20 for i in range(1, 20)] if lo <= c <= hi] or [lo]), 2)
        inside = lo <= t <= hi
        given = ", ".join(f"$p({x}) = {tm(p[x])}$" for x in lets)
        U = (f"{P16} Известно: {given}. Утверждается, что $p({ftex(f)}) = {tm(t)}$. Проверьте, не противоречит ли это "
             "правилам с. 76, применённым по строению формулы; если противоречит — докажите, если нет — укажите, какие границы "
             "эти правила дают.")
        if inside:
            A = f"Не противоречит: правила дают {ptxt((lo, hi), f)}, и ${tm(t)}$ в этих границах."
        else:
            A = f"Противоречит: правила дают {ptxt((lo, hi), f)}, а ${tm(t)}$ вне этих границ."
        R = "\n".join(f"{i+1}. {s}" for i, s in enumerate(psteps(f, p))) + (
            f"\n\nЧисло ${tm(t)}$ " + ("лежит в этих границах." if inside else "лежит вне этих границ — утверждение противоречит правилам с. 76."))
        return U, A, R
    r = fresh(make)
    if r:
        card(16, 6, "C", "open", "def", "sym", "short", "с. 76, гл. 2, § 16", ["вероятность", "открытый исход"], *r)


# ================================================================ § 9 существование энок и состояний

E9 = ("Буквы $x, y, z, w$ — высказывания; $a, b, c$ — индивидуальные термины. Аксиомы § 9 (с. 67): "
      "4. $E(a^1, …, a^n) \\dashv\\vdash E(a^1) \\wedge … \\wedge E(a^n)$; 5. $\\urcorner E(a^1, …, a^n) \\dashv\\vdash \\urcorner E(a^1) \\vee … \\vee \\urcorner E(a^n)$; "
      "6. $?E(a^1, …, a^n) \\dashv\\vdash {\\sim}E(a^1, …, a^n) \\wedge {\\sim}\\urcorner E(a^1, …, a^n)$; 3. $?E(a) \\dashv\\vdash {\\sim}E(a) \\wedge {\\sim}\\urcorner E(a)$; "
      "7. $E(sx) \\dashv\\vdash x$; 8. $\\urcorner E(sx) \\dashv\\vdash {\\sim}x$; 9. ${\\sim}E(sx) \\dashv\\vdash \\urcorner E(sx)$.")
ST = {"E": "E", "nE": "\\urcorner E", "qE": "?E"}


def e_member(m, val, ind):
    if m[0] == "s":
        return "E" if truth(m[1], val) else "nE"
    return ind[m[1]]


def e_status(ms, val, ind):
    st = [e_member(m, val, ind) for m in ms]
    if all(s == "E" for s in st):
        return "E"
    if any(s == "nE" for s in st):
        return "nE"
    return "qE"


def stex(f):
    return "s" + f[1] if f[0] == "v" else "s(" + ftex(f) + ")"


def mtex(m):
    return stex(m[1]) if m[0] == "s" else m[1]


def e_explain(ms, val, ind):
    parts = []
    for m in ms:
        if m[0] == "s":
            t = truth(m[1], val)
            parts.append(f"${ftex(m[1])}$ {'истинно' if t else 'ложно'}, по {'7' if t else '8'}: ${ST['E' if t else 'nE']}({mtex(m)})$")
        else:
            parts.append(f"${ST[ind[m[1]]]}({m[1]})$ (дано)")
    s = e_status(ms, val, ind)
    enk = ", ".join(mtex(m) for m in ms)
    if s == "E":
        tail = f"все члены существуют — по 4: $E({enk})$"
    elif s == "nE":
        tail = f"хотя бы один член не существует — по 5: $\\urcorner E({enk})$"
    else:
        tail = (f"не все члены существуют, поэтому по 4 ${{\\sim}}E({enk})$; ни один не имеет $\\urcorner E$ (для состояний по 9 "
                f"${{\\sim}}\\urcorner E$ при $E$, для индивидов с $?E$ по 3 ${{\\sim}}\\urcorner E$), поэтому по 5 ${{\\sim}}\\urcorner E({enk})$; по 6: $?E({enk})$")
    return "; ".join(parts) + "; " + tail + "."


def e_case():
    lets = ["x", "y", "z", "w"]
    val = {x: rnd.random() < 0.5 for x in lets}
    ind = {c: rnd.choice(["E", "nE", "qE"]) for c in ["a", "b", "c"]}
    return lets, val, ind


def e_given(val, ind):
    tv = ", ".join(f"${x}$" if val[x] else f"${{\\sim}}{x}$" for x in val)
    iv = ", ".join(f"${ST[s]}({c})$" for c, s in ind.items())
    return f"Истинны {tv}; известно {iv}."


def e_enkas(lets, val, ind, n=4):
    out = []
    want = ["E", "nE", "qE"]
    rnd.shuffle(want)
    tries = 0
    while len(out) < n and tries < 500:
        tries += 1
        k = rnd.choice([2, 3])
        ms = []
        for _ in range(k):
            if rnd.random() < 0.6:
                f = None
                while not f or depth(f) < 2 or not clean(f):
                    f = rand_f(2, lets)
                ms.append(("s", f))
            else:
                ms.append(("i", rnd.choice(["a", "b", "c"])))
        if len({m for m in ms}) < k or not any(m[0] == "s" for m in ms):
            continue
        st = e_status(ms, val, ind)
        if len(out) < 3 and st != want[len(out) % 3]:
            continue
        out.append(ms)
    return out


def e_series():
    def make():
        lets, val, ind = e_case()
        if "qE" not in ind.values():
            return None
        en = e_enkas(lets, val, ind)
        if len(en) < 4:
            return None
        U = (f"{E9} {e_given(val, ind)} Для каждой энки установите, какое из высказываний $E$, $\\urcorner E$, $?E$ о ней "
             "истинно, и обоснуйте по аксиомам.\n\n" + items([f"$({', '.join(mtex(m) for m in ms)})$" for ms in en]))
        A = ans_items([f"${ST[e_status(ms, val, ind)]}$" for ms in en])
        R = "\n\n".join(f"{'абвг'[i]}) " + e_explain(ms, val, ind) for i, ms in enumerate(en))
        return U, A, R
    r = fresh(make)
    if r:
        card(9, 4, "C", "iso", "def", "sym", "short", "с. 66–67, гл. 2, § 9", ["существование", "энки", "состояния"], *r)


def e_errors():
    def make():
        lets, val, ind = e_case()
        if "qE" not in ind.values():
            return None
        en = e_enkas(lets, val, ind, n=5)
        if len(en) < 5:
            return None
        truth_ = [e_status(ms, val, ind) for ms in en]
        bad = sorted(rnd.sample(range(5), 2))
        stud = list(truth_)
        reasons = {}
        for i in bad:
            ms = en[i]
            if truth_[i] == "qE":
                stud[i] = "nE"
                reasons[i] = "член с $?E$ не даёт $\\urcorner E$ энки: по 5 нужен член с $\\urcorner E$, а по 3 у такого члена ${\\sim}\\urcorner E$"
            elif truth_[i] == "nE":
                stud[i] = "E" if any(e_member(m, val, ind) == "E" for m in ms) else "qE"
                reasons[i] = "по 5 энка не существует, если не существует хотя бы один её член"
            else:
                stud[i] = "qE"
                reasons[i] = "по 4 энка существует, если существуют все её члены"
            if stud[i] == truth_[i]:
                return None
        U = (f"{E9} {e_given(val, ind)} Студент составил таблицу:\n\n"
             + items([f"$({', '.join(mtex(m) for m in ms)})$ — ${ST[stud[i]]}$" for i, ms in enumerate(en)])
             + "\n\nВ таблице ровно две ошибки. Найдите их, назовите нарушенные аксиомы и исправьте.")
        A = "; ".join(f"{'абвгд'[i]}) не ${ST[stud[i]]}$, а ${ST[truth_[i]]}$ — {reasons[i]}" for i in bad)
        R = "\n\n".join(f"{'абвгд'[i]}) " + e_explain(ms, val, ind) for i, ms in enumerate(en))
        return U, A, R
    r = fresh(make)
    if r:
        card(9, 6, "E", "vary", "def", "sym", "text", "с. 66–67, гл. 2, § 9", ["существование", "энки", "диагностика"], *r)


# ================================================================ § 11 M для родовых терминов состояний

M11 = ("Буквы $x, y, z, w, u$ — высказывания; $sx$ — родовой термин состояния. Аксиомы для $M$ (с. 70–71): "
       "(I) $M(s(x \\vee y)) \\dashv\\vdash M(sx) \\vee M(sy)$; (II) $\\urcorner M(s(x \\vee y)) \\dashv\\vdash \\urcorner M(sx) \\wedge \\urcorner M(sy)$; "
       "(III) $\\urcorner M(s(x \\wedge y)) \\dashv\\vdash \\urcorner M(sx) \\vee \\urcorner M(sy)$; "
       "(IV) $M(s(x \\wedge y)) \\dashv\\vdash M(sx) \\wedge M(sy) \\wedge {\\sim}(x \\to {\\sim}y)$.")


def m_derive(f, known, comp, lines, idx):
    """Строит вывод M(sf) или ¬M(sf); возвращает (статус, номер строки) или None. known: {буква: 'M'|'nM'};
    comp: множество пар (F, G), для которых дано ~(F → ~G)."""
    key = f
    if key in idx:
        return idx[key]
    if f[0] == "v":
        st = known.get(f[1])
        if not st:
            return None
        lines.append((f"{'' if st == 'M' else '\\urcorner '}M(s{f[1]})", "посылка", ()))
        idx[key] = (st, len(lines))
        return idx[key]
    a = m_derive(f[1], known, comp, lines, idx)
    b = m_derive(f[2], known, comp, lines, idx)
    F, G = ftex(f[1], False), ftex(f[2], False)
    SF, SG = stex(f[1]), stex(f[2])
    if f[0] == "or":
        if a and b and a[0] == b[0] == "nM":
            lines.append((f"\\urcorner M({SF}) \\wedge \\urcorner M({SG})", "∧", (a[1], b[1])))
            lines.append((f"\\urcorner M({stex(f)})", "(II)", (len(lines),)))
            idx[key] = ("nM", len(lines))
        elif (a and a[0] == "M") or (b and b[0] == "M"):
            src = a if a and a[0] == "M" else b
            lines.append((f"M({SF}) \\vee M({SG})", "∨", (src[1],)))
            lines.append((f"M({stex(f)})", "(I)", (len(lines),)))
            idx[key] = ("M", len(lines))
        else:
            return None
    else:
        if (a and a[0] == "nM") or (b and b[0] == "nM"):
            src = a if a and a[0] == "nM" else b
            lines.append((f"\\urcorner M({SF}) \\vee \\urcorner M({SG})", "∨", (src[1],)))
            lines.append((f"\\urcorner M({stex(f)})", "(III)", (len(lines),)))
            idx[key] = ("nM", len(lines))
        elif a and b and a[0] == b[0] == "M" and (f[1], f[2]) in comp:
            lines.append((f"{{\\sim}}({F} \\to {{\\sim}}{G})", "посылка", ()))
            c = len(lines)
            lines.append((f"M({SF}) \\wedge M({SG}) \\wedge {{\\sim}}({F} \\to {{\\sim}}{G})", "∧", (a[1], b[1], c)))
            lines.append((f"M({stex(f)})", "(IV)", (len(lines),)))
            idx[key] = ("M", len(lines))
        else:
            return None
    return idx[key]


WHY = {"посылка": "посылка", "∧": "соединение в конъюнкцию", "∨": "введение дизъюнкции",
       "(I)": "(I), справа налево", "(II)": "(II), справа налево", "(III)": "(III), справа налево", "(IV)": "(IV), справа налево"}


def m_show(lines, hide_f=(), hide_w=()):
    out = []
    for i, (f, w, refs) in enumerate(lines, 1):
        ff = "…" if i in hide_f else f"${f}$"
        ww = "…" if i in hide_w else (WHY[w] if not refs else f"{', '.join(map(str, refs))}; {WHY[w]}")
        out.append(f"{i}. {ff} [{ww}]")
    return "\n".join(out)


def m_reorder(lines):
    """Посылки — в начало (номера ссылок пересчитываются)."""
    prem = [i for i, l in enumerate(lines) if l[1] == "посылка"]
    rest = [i for i, l in enumerate(lines) if l[1] != "посылка"]
    order = prem + rest
    new = {old + 1: n + 1 for n, old in enumerate(order)}
    return [(lines[o][0], lines[o][1], tuple(new[r] for r in lines[o][2])) for o in order]


def m_problem(lo=8, hi=13, want=None):
    for _ in range(500):
        lets = LET[:5]
        known = {x: rnd.choice(["M", "nM"]) for x in lets}
        f = rand_f(3, lets, neg=False)
        if not good_long(f, 3, 7):
            continue
        comp = set()
        for g in subs(f):
            if g[0] == "and" and rnd.random() < 0.7:
                comp.add((g[1], g[2]))
        lines, idx = [], {}
        r = m_derive(f, known, comp, lines, idx)
        if not r or (want and r[0] != want):
            continue
        lines = m_reorder(lines)
        if lo <= len(lines) <= hi:
            return f, known, comp, lines, r[0]
    return None


def m_long():
    def make():
        r = m_problem()
        if not r:
            return None
        f, known, comp, lines, st = r
        prem = [l[0] for l in lines if l[1] == "посылка"]
        goal = lines[-1][0]
        U = (f"{M11} Выведите ${goal}$ из посылок " + "; ".join(f"${p}$" for p in prem)
             + ". Укажите основание каждой строки (номера строк и аксиому; соединение в конъюнкцию и введение дизъюнкции подразумеваются).")
        A = f"Вывод в {len(lines)} строк, последняя — ${goal}$ (см. решение)."
        return U, A, m_show(lines) + "\n\nАксиомы (I)–(III) — с. 70, (IV) — с. 71."
    r = fresh(make)
    if r:
        card(11, 5, "D", "iso", "def", "sym", "proof", "с. 70–71, гл. 2, § 11", ["возможность", "вывод"], *r)


def m_complete():
    def make():
        r = m_problem(9, 13)
        if not r:
            return None
        f, known, comp, lines, st = r
        inner = [i for i, l in enumerate(lines, 1) if l[1] != "посылка" and i != len(lines)]
        if len(inner) < 4:
            return None
        hide_f = set(rnd.sample(inner, 2))
        rest = [i for i, l in enumerate(lines, 1) if l[1] != "посылка" and i not in hide_f]
        hide_w = set(rnd.sample(rest, min(3, len(rest))))
        U = (f"{M11} В выводе формулы ${lines[-1][0]}$ пропущены формулы некоторых строк и основания некоторых шагов («…»). "
             f"Восстановите их.\n\n{m_show(lines, hide_f, hide_w)}")
        parts = []
        for i in sorted(hide_f | hide_w):
            fx, w, refs = lines[i - 1]
            s = f"{i} — " + (f"${fx}$" if i in hide_f else "")
            if i in hide_w:
                s += (" " if i in hide_f else "") + f"[{', '.join(map(str, refs))}; {WHY[w]}]"
            parts.append(s)
        return U, "; ".join(parts), "Полный вывод:\n\n" + m_show(lines) + "\n\nАксиомы — с. 70–71."
    r = fresh(make)
    if r:
        card(11, 5, "D", "complete", "def", "sym", "build", "с. 70–71, гл. 2, § 11", ["возможность", "дополнение"], *r)


def m_errors():
    def make():
        r = m_problem(9, 13)
        if not r:
            return None
        f, known, comp, lines, st = r
        ax = [i for i, l in enumerate(lines, 1) if l[1] in ("(I)", "(II)", "(III)", "(IV)")]
        if len(ax) < 3:
            return None
        bad = sorted(rnd.sample(ax, 2))
        wrong = {}
        L2 = list(lines)
        for i in bad:
            fx, w, refs = L2[i - 1]
            alt = {"(I)": "(II)", "(II)": "(I)", "(III)": "(IV)", "(IV)": "(III)"}[w]
            wrong[i] = alt
            L2[i - 1] = (fx, alt, refs)
        U = (f"{M11} В выводе формулы ${lines[-1][0]}$ ровно два основания указаны неверно. Найдите обе ошибки, объясните, "
             f"почему указанная аксиома не даёт эту строку, и исправьте.\n\n{m_show(L2)}")
        A = "; ".join(f"строка {i}: не {wrong[i]}, а {lines[i-1][1]}" for i in bad)
        exp = {"(I)": "(I) даёт $M$ дизъюнкции", "(II)": "(II) даёт $\\urcorner M$ дизъюнкции",
               "(III)": "(III) даёт $\\urcorner M$ конъюнкции", "(IV)": "(IV) даёт $M$ конъюнкции"}
        R = "\n".join(f"Строка {i}: {exp[wrong[i]]}, а в строке — {exp[lines[i-1][1]].split(' даёт ')[1]}; верно {lines[i-1][1]}." for i in bad)
        return U, A, R + "\n\nИсправленный вывод:\n\n" + m_show(lines)
    r = fresh(make)
    if r:
        card(11, 6, "E", "vary", "def", "sym", "text", "с. 70–71, гл. 2, § 11", ["возможность", "диагностика"], *r)


def m_open():
    """Разбор по строению: выводится M, ¬M или не хватает посылки о совместимости."""
    def make():
        for _ in range(300):
            lets = LET[:4]
            known = {x: rnd.choice(["M", "nM"]) for x in lets}
            f = rand_f(3, lets, neg=False)
            if not good_long(f, 3, 7):
                continue
            lines, idx = [], {}
            r = m_derive(f, known, set(), lines, idx)
            if r:
                if rnd.random() < 0.6:
                    continue
                lines = m_reorder(lines)
                res = ("M" if r[0] == "M" else "nM")
                A = f"Выводится ${lines[-1][0]}$ (вывод в {len(lines)} строк)."
                R = m_show(lines)
            else:
                # найти недостающие посылки о совместимости
                need = []
                def walk(g):
                    if g[0] == "v":
                        return known[g[1]]
                    a, b = walk(g[1]), walk(g[2])
                    if g[0] == "or":
                        if a == "M" or b == "M":
                            return "M"
                        if a == b == "nM":
                            return "nM"
                        return None
                    if a == "nM" or b == "nM":
                        return "nM"
                    if a == b == "M":
                        need.append(g)
                        return "M?"
                    return None
                walk(f)
                if not need:
                    continue
                comp = {(g[1], g[2]) for g in need}
                lines, idx = [], {}
                r2 = m_derive(f, known, comp, lines, idx)
                if not r2:
                    continue
                lines = m_reorder(lines)
                miss = "; ".join(f"${{\\sim}}({ftex(g[1], False)} \\to {{\\sim}}{ftex(g[2], False)})$" for g in need)
                A = (f"По строению из данных не выводится ни $M$, ни $\\urcorner M$: для конъюнкций с возможными членами нужна посылка {miss} "
                     f"(аксиома (IV)); с ней выводится ${lines[-1][0]}$.")
                R = ("Разбор снизу вверх: (III) даёт $\\urcorner M$ конъюнкции, если невозможен хотя бы один член; (II) — $\\urcorner M$ "
                     "дизъюнкции, если невозможны оба; (I) — $M$ дизъюнкции, если возможен хотя бы один. Для конъюнкции двух возможных "
                     "членов аксиома (IV) требует ещё совместимости ${\\sim}(x \\to {\\sim}y)$, а её в данных нет; дизъюнкция над такой "
                     "конъюнкцией без другого возможного члена тоже не решается.\n\nС недостающими посылками вывод таков:\n\n" + m_show(lines))
            given = "; ".join(f"${'' if known[x] == 'M' else '\\urcorner '}M(s{x})$" for x in sorted(letters(f)))
            U = (f"{M11} Известно: {given}; других сведений нет. Разбирая формулу по строению, установите, какое из высказываний "
                 f"$M(s({ftex(f)}))$, $\\urcorner M(s({ftex(f)}))$ выводится по аксиомам (I)–(IV), и постройте вывод; если по строению "
                 "не выводится ни одно, укажите, каких посылок не хватает.")
            return U, A, R
        return None
    r = fresh(make)
    if r:
        card(11, 6, "C", "open", "under", "sym", "proof", "с. 70–71, гл. 2, § 11", ["возможность", "открытый исход"], *r)


# ================================================================ § 6 классы

K6 = ("Индивидная переменная $d$ пробегает индивиды $e_1, …, e_7$; $A, B, C$ — термины классов. Правила с. 62: "
      "$(d \\in A) \\wedge (d \\in B) \\dashv\\vdash (d \\in A \\cap B)$; $(d \\in A) \\vee (d \\in B) \\dashv\\vdash (d \\in A \\cup B)$; "
      "$(d \\in B) \\dashv\\vdash (d \\in \\bar{\\bar{B}})$.")
IND = [f"e_{i}" for i in range(1, 8)]


def kterm(d, cl=("A", "B", "C")):
    if d == 0 or (d < 3 and rnd.random() < 0.2):
        t = ("c", rnd.choice(cl))
        return ("bb", t) if rnd.random() < 0.15 else t
    if rnd.random() < 0.12:
        return ("bb", kterm(d - 1, cl))
    return (rnd.choice(["cap", "cup"]), kterm(d - 1, cl), kterm(d - 1, cl))


def ktex(t, top=True):
    if t[0] == "c":
        return t[1]
    if t[0] == "bb":
        return "\\bar{\\bar{" + ktex(t[1], True) + "}}"
    s = ktex(t[1], False) + (" \\cap " if t[0] == "cap" else " \\cup ") + ktex(t[2], False)
    return s if top else "(" + s + ")"


def kset(t, mem):
    if t[0] == "c":
        return mem[t[1]]
    if t[0] == "bb":
        return kset(t[1], mem)
    a, b = kset(t[1], mem), kset(t[2], mem)
    return a & b if t[0] == "cap" else a | b


def kclean(t):
    if t[0] == "c":
        return True
    if t[0] == "bb":
        return t[1][0] != "bb" and kclean(t[1])
    return t[1] != t[2] and kclean(t[1]) and kclean(t[2])


def kdepth(t):
    return 0 if t[0] == "c" else 1 + max(kdepth(s) for s in t[1:])


def kclasses(t):
    return {t[1]} if t[0] == "c" else set().union(*(kclasses(s) for s in t[1:]))


def ksubs(t):
    out = []
    def go(s):
        if s[0] != "c":
            for h in s[1:]:
                go(h)
        if s not in out:
            out.append(s)
    go(t)
    return out


def setx(s):
    return "\\{" + ", ".join(sorted(s, key=lambda e: int(e[2:]))) + "\\}" if s else "\\varnothing"


def kmem():
    mem = {c: set(rnd.sample(IND, rnd.choice([2, 3, 4]))) for c in "ABC"}
    return mem


def kgiven(mem):
    return "; ".join(f"в ${c}$ включаются ${', '.join(sorted(mem[c], key=lambda e: int(e[2:])))}$ и только они" for c in "ABC")


def ksteps(t, mem):
    out = []
    for s in ksubs(t):
        if s[0] == "c":
            continue
        if s[0] == "bb":
            out.append(f"${ktex(s)}$: те же индивиды, что в ${ktex(s[1])}$ (двойное дополнение) — ${setx(kset(s, mem))}$")
        else:
            rule = "входят в оба (правило для $\\cap$)" if s[0] == "cap" else "входят хотя бы в один (правило для $\\cup$)"
            out.append(f"${ktex(s)}$: {rule} — ${setx(kset(s, mem))}$")
    return out


def k_series():
    def make():
        mem = kmem()
        ts = []
        while len(ts) < 4:
            t = kterm(3)
            if kdepth(t) >= 3 and len(kclasses(t)) == 3 and kclean(t) and t not in ts:
                ts.append(t)
        U = (f"{K6} Известно: {kgiven(mem)}. Для каждого термина найдите все включаемые в него индивиды; для каждой "
             "составной части укажите правило.\n\n" + items([f"${ktex(t)}$" for t in ts]))
        A = ans_items([f"${setx(kset(t, mem))}$" for t in ts])
        R = "\n\n".join(f"{'абвг'[i]}) " + "; ".join(ksteps(t, mem)) + "." for i, t in enumerate(ts))
        return U, A, R + "\n\nПравила — с. 62."
    r = fresh(make)
    if r:
        card(6, 4, "C", "iso", "def", "sym", "short", "с. 62, гл. 2, § 6", ["классы"], *r)


def k_relations():
    def make():
        mem = kmem()
        while True:
            t1, t2 = kterm(2), kterm(3)
            if kdepth(t1) >= 2 and kdepth(t2) >= 2 and t1 != t2 and kclean(t1) and kclean(t2):
                break
        s1, s2 = kset(t1, mem), kset(t2, mem)
        U = (f"{K6} Известно: {kgiven(mem)}. Пусть $P = {ktex(t1)}$, $Q = {ktex(t2)}$. По определениям с. 62–63 ($P \\subset Q$ — "
             "$(\\forall d)((d \\in P) \\to (d \\in Q))$; пересекаются — $(\\exists d)((d \\in P) \\wedge (d \\in Q))$; пустой — "
             "$(\\forall d){\\sim}(d \\in P)$; универсальный — $(\\forall d)(d \\in P)$; эквивалентны — $(P \\subset Q) \\wedge (Q \\subset P)$) "
             "установите для каждого высказывания, истинно оно или ложно, и обоснуйте.\n\n"
             + items(["$P \\subset Q$", "$Q \\subset P$", "$P$ и $Q$ пересекаются", "$P \\cap Q$ — пустой класс", "$P$ и $Q$ эквивалентны"]))
        sub, sup, inter, empty, eq = s1 <= s2, s2 <= s1, bool(s1 & s2), not (s1 & s2), s1 == s2
        A = ans_items(["истинно" if b else "ложно" for b in (sub, sup, inter, empty, eq)])
        def w(e):
            return f"${e}$"
        R = [f"По правилам с. 62: $P$ — ${setx(s1)}$ (" + "; ".join(ksteps(t1, mem)) + f"); $Q$ — ${setx(s2)}$ (" + "; ".join(ksteps(t2, mem)) + ").",
             "а) " + ("каждый индивид $P$ входит в $Q$" if sub else f"${sorted(s1 - s2, key=lambda e: int(e[2:]))[0]}$ входит в $P$, но не в $Q$") + ".",
             "б) " + ("каждый индивид $Q$ входит в $P$" if sup else f"${sorted(s2 - s1, key=lambda e: int(e[2:]))[0]}$ входит в $Q$, но не в $P$") + ".",
             "в) " + (f"общий индивид ${sorted(s1 & s2, key=lambda e: int(e[2:]))[0]}$" if inter else "общих индивидов нет") + ".",
             "г) " + ("общих индивидов нет — $P \\cap Q$ пустой" if empty else f"в $P \\cap Q$ входит ${sorted(s1 & s2, key=lambda e: int(e[2:]))[0]}$ — класс непустой") + ".",
             "д) " + ("оба включения истинны" if eq else "одно из включений ложно") + "."]
        return U, A, "\n".join(R)
    r = fresh(make)
    if r:
        card(6, 5, "C", "iso", "def", "sym", "short", "с. 62–63, гл. 2, § 6", ["классы", "подкласс"], *r)


def k_errors():
    def make():
        mem = kmem()
        ts = []
        while len(ts) < 5:
            t = kterm(3)
            if kdepth(t) >= 2 and len(kclasses(t)) >= 2 and kclean(t) and t not in ts:
                ts.append(t)
        bad = sorted(rnd.sample(range(5), 2))
        stud, why = [], {}
        for i, t in enumerate(ts):
            s = kset(t, mem)
            if i in bad:
                # перепутаны ∩ и ∪ во внешнем операторе, или потерян индивид
                if t[0] in ("cap", "cup"):
                    alt = ("cup" if t[0] == "cap" else "cap",) + t[1:]
                    s2 = kset(alt, mem)
                    why[i] = ("внешний оператор $\\cap$ прочитан как $\\cup$" if t[0] == "cap" else "внешний оператор $\\cup$ прочитан как $\\cap$")
                else:
                    s2 = s - {min(s)} if s else {IND[0]}
                    why[i] = "двойное дополнение не меняет включаемых индивидов"
                if s2 == s:
                    return None
                stud.append(s2)
            else:
                stud.append(s)
        U = (f"{K6} Известно: {kgiven(mem)}. Студент выписал индивиды, включаемые в термины:\n\n"
             + items([f"${ktex(t)}$ — ${setx(stud[i])}$" for i, t in enumerate(ts)])
             + "\n\nРовно в двух строках есть ошибка. Найдите их, назовите нарушенное правило с. 62 и исправьте.")
        A = "; ".join(f"{'абвгд'[i]}) верно ${setx(kset(ts[i], mem))}$ — {why[i]}" for i in bad)
        R = "\n\n".join(f"{'абвгд'[i]}) " + "; ".join(ksteps(t, mem)) + "." for i, t in enumerate(ts)) + "\n\nПравила — с. 62."
        return U, A, R
    r = fresh(make)
    if r:
        card(6, 6, "E", "vary", "def", "sym", "text", "с. 62, гл. 2, § 6", ["классы", "диагностика"], *r)


def k_build():
    """Постройте из A, B, C с помощью ∩ и ∪ термин с заданным составом или докажите, что такого нет (ступень 8)."""
    def make():
        mem = kmem()
        pat = {e: frozenset(c for c in "ABC" if e in mem[c]) for e in IND}
        target = set(rnd.sample(IND, rnd.choice([2, 3, 4])))
        ok = all(pat[e] and all(pat[e] <= pat[f] and True for f in []) for e in target)
        blocker = None
        for e in sorted(target):
            if not pat[e]:
                blocker = (e, None)
                break
            for f in IND:
                if f not in target and pat[e] <= pat[f]:
                    blocker = (e, f)
                    break
            if blocker:
                break
        U = (f"Индивидная переменная $d$ пробегает индивиды $e_1, …, e_7$; $A, B, C$ — термины классов. Известно: {kgiven(mem)}. "
             "По с. 62 из терминов классов операторами $\\cap$ и $\\cup$ образуются термины классов, и "
             "$(d \\in P) \\wedge (d \\in Q) \\dashv\\vdash (d \\in P \\cap Q)$, $(d \\in P) \\vee (d \\in Q) \\dashv\\vdash (d \\in P \\cup Q)$. "
             f"Постройте из $A$, $B$, $C$ с помощью $\\cap$ и $\\cup$ термин класса, в который включаются индивиды ${setx(target)}$ и только они, "
             "или докажите, что такого термина нет.")
        if blocker is None:
            parts = []
            for e in sorted(target, key=lambda e: int(e[2:])):
                cs = sorted(pat[e])
                parts.append(" \\cap ".join(cs) if len(cs) > 1 else cs[0])
            uniq = []
            for p_ in parts:
                if p_ not in uniq:
                    uniq.append(p_)
            term = " \\cup ".join(f"({p_})" if "\\cap" in p_ and len(uniq) > 1 else p_ for p_ in uniq)
            # проверка
            def ev(p_):
                return set.intersection(*(mem[c] for c in p_.split(" \\cap ")))
            got = set().union(*(ev(p_) for p_ in uniq))
            if got != target:
                return None
            A = f"Термин есть, например ${term}$."
            R = ("Для каждого индивида $e$ из нужного состава берём пересечение всех классов, в которые он включается; "
                 "объединяем эти пересечения.\n\n" + "\n".join(f"${e}$ включается в " + ", ".join(f"${c}$" for c in sorted(pat[e])) for e in sorted(target, key=lambda e: int(e[2:])))
                 + f"\n\nПроверка по правилам с. 62: " + "; ".join(f"${p_}$ — ${setx(ev(p_))}$" for p_ in uniq)
                 + f"; объединение — ${setx(got)}$.")
            lvl, typ = 7, "K"
        else:
            e, f = blocker
            if f is None:
                A = f"Термина нет: ${e}$ не включается ни в один из $A$, $B$, $C$, а значит, ни в один составной термин."
                R = (f"Индукцией по построению термина (с. 62): ${e}$ не входит в $A$, $B$, $C$; если не входит ни в $P$, ни в $Q$, "
                     f"то по правилу для $\\cap$ не входит в $P \\cap Q$, по правилу для $\\cup$ — в $P \\cup Q$. Значит, ни один термин "
                     f"из $A$, $B$, $C$ не включает ${e}$, а он нужен.")
            else:
                ce = ", ".join(f"${c}$" for c in sorted(pat[e]))
                A = (f"Термина нет: всякий класс из $A$, $B$, $C$, включающий ${e}$, включает и ${f}$, поэтому всякий составной термин, "
                     f"включающий ${e}$, включает ${f}$; а ${f}$ в нужный состав не входит.")
                R = (f"1. ${e}$ включается в {ce}; ${f}$ — в " + ", ".join(f"${c}$" for c in sorted(pat[f])) + f": каждый из классов, включающих ${e}$, включает и ${f}$.\n"
                     f"2. Утверждение: для всякого термина $T$, построенного из $A$, $B$, $C$ операторами $\\cap$ и $\\cup$, если $({e} \\in T)$, то $({f} \\in T)$. "
                     "Доказываем индукцией по построению (с. 62).\n"
                     f"3. Для $A$, $B$, $C$ — п. 1.\n"
                     f"4. $T = P \\cap Q$: из $({e} \\in P \\cap Q)$ по правилу для $\\cap$ — $({e} \\in P) \\wedge ({e} \\in Q)$; по предположению индукции "
                     f"$({f} \\in P) \\wedge ({f} \\in Q)$; по тому же правилу $({f} \\in P \\cap Q)$.\n"
                     f"5. $T = P \\cup Q$: из $({e} \\in P \\cup Q)$ — $({e} \\in P) \\vee ({e} \\in Q)$; по предположению индукции $({f} \\in P) \\vee ({f} \\in Q)$; "
                     f"значит, $({f} \\in P \\cup Q)$.\n"
                     f"6. Нужный термин включал бы ${e}$, но не ${f}$ — противоречие с п. 2. Термина нет.")
            lvl, typ = 8, "K"
        return U, A, R, lvl, ("M" if lvl == 8 else "D")
    r = fresh(make)
    if r:
        card(6, r[3], r[4], "open", "def", "meta" if r[3] == 8 else "sym", "proof", "с. 62, гл. 2, § 6", ["классы", "построение"], *r[:3])


# ================================================================ § 23–26 ряды

ROW = ("Буквы $a, b, c, d, e, f$ — индивиды, $\\alpha$ — способ установления порядка; для $> \\alpha$ принимаются аксиомы, "
       "аналогичные C1–C7 (с. 82), в частности C4: $(a > \\alpha b) \\wedge (b > \\alpha c) \\vdash (a > \\alpha c)$. "
       "Индивиды образуют ряд $A$ относительно $\\alpha$. По с. 85 элементы ряда соседние, если и только если ни один элемент $A$ "
       "не находится между ними; по § 20 (с. 82) $u$ находится между $v$ и $w$, если и только если $(u > \\alpha v) \\wedge (w > \\alpha u)$ "
       "или $(v > \\alpha u) \\wedge (u > \\alpha w)$. По с. 88 элемент начальный, если любой другой элемент ряда превосходит его по "
       "порядку, и конечный, если он превосходит все остальные.")


def row_problem():
    names = list("abcdef")
    order = names[:]
    rnd.shuffle(order)          # order[0] — младший
    # данные: цепочка соседей в перемешанном виде плюс одна лишняя связь
    facts = [(order[i + 1], order[i]) for i in range(5)]
    extra = rnd.sample([(order[j], order[i]) for i in range(6) for j in range(i + 2, 6)], 1)
    facts = facts + extra
    rnd.shuffle(facts)
    return order, facts


def gt_proof(order, facts, a, b):
    """Строки вывода a > αb из данных по C4 (цепочка)."""
    pos = {x: i for i, x in enumerate(order)}
    known = {f: n + 1 for n, f in enumerate(facts)}
    if (a, b) in known:
        return [f"${a} > \\alpha {b}$ — дано"]
    chain = [order[i] for i in range(pos[a], pos[b] - 1, -1)]
    out = []
    cur = chain[0]
    for nxt in chain[1:]:
        if cur == a and (a, nxt) in known:
            pass
        out.append(nxt)
    steps = []
    acc = (chain[0], chain[1])
    for i in range(2, len(chain)):
        acc2 = (chain[0], chain[i])
        steps.append(f"${chain[0]} > \\alpha {chain[i-1]}$ и ${chain[i-1]} > \\alpha {chain[i]}$ дают по C4 ${chain[0]} > \\alpha {chain[i]}$")
        acc = acc2
    return steps


def row_series():
    def make():
        order, facts = row_problem()
        first, last = order[0], order[-1]
        pairs = []
        near = [(order[i + 1], order[i]) if rnd.random() < 0.5 else (order[i], order[i + 1]) for i in range(5)]
        far = [(order[j], order[i]) if rnd.random() < 0.5 else (order[i], order[j]) for i in range(6) for j in range(i + 2, 6)]
        pairs = rnd.sample(near, 1) + rnd.sample(far, 2)
        rnd.shuffle(pairs)
        given = "; ".join(f"${u} > \\alpha {v}$" for u, v in facts)
        U = (f"{ROW} Известно: {given} (других сведений о порядке нет). Найдите начальный и конечный элементы ряда и для каждой пары "
             "установите, соседние ли это элементы; ответ обоснуйте выводом по C4 и определениям.\n\n"
             + items([f"${u}$, ${v}$" for u, v in pairs]))
        pos = {x: i for i, x in enumerate(order)}
        res = []
        for u, v in pairs:
            res.append("соседние" if abs(pos[u] - pos[v]) == 1 else "не соседние")
        A = f"Начальный — ${first}$, конечный — ${last}$; " + ans_items(res)
        chain = "(от уступающих к превосходящим) $" + ", ".join(order) + "$"
        R = [f"1. Цепочка данных: " + ", ".join(f"${order[i+1]} > \\alpha {order[i]}$" for i in range(5)) +
             f" (все они даны). По C4, применённой несколько раз, всякий элемент правее в цепочке превосходит всякий левее: "
             f"порядок {chain}.",
             f"2. ${first}$ уступает всем остальным — начальный; ${last}$ превосходит все остальные — конечный (с. 88)."]
        for k, (u, v) in enumerate(pairs):
            lo_, hi_ = sorted([u, v], key=lambda x: pos[x])
            if abs(pos[u] - pos[v]) == 1:
                R.append(f"{'абв'[k]}) ${hi_} > \\alpha {lo_}$, и между ними в цепочке нет элемента: любой другой элемент либо уступает ${lo_}$, "
                         f"либо превосходит ${hi_}$ (п. 1), поэтому ни одно из условий § 20 не выполнено — соседние.")
            else:
                mid = order[pos[lo_] + 1]
                R.append(f"{'абв'[k]}) ${mid}$ находится между ними: ${mid} > \\alpha {lo_}$ и ${hi_} > \\alpha {mid}$ (п. 1; § 20) — не соседние.")
        return U, A, "\n".join(R)
    r = fresh(make)
    if r:
        card(23, 5, "C", "iso", "over", "sym", "short", "с. 82, 85, 88, гл. 2, § 20, 23, 26", ["ряды", "порядок"], *r)


def row_touch_errors():
    def make():
        order, facts = row_problem()
        gaps = {i: rnd.random() < 0.4 for i in range(5)}   # между order[i] и order[i+1] можно поместить индивид
        pos = {x: i for i, x in enumerate(order)}
        allp = [(order[i], order[j]) for i in range(6) for j in range(i + 1, 6)]
        rnd.shuffle(allp)
        pairs = allp[:5]
        def touch(u, v):
            i, j = sorted([pos[u], pos[v]])
            return j == i + 1 and not gaps[i]
        truth_ = [touch(u, v) for u, v in pairs]
        bad = sorted(rnd.sample(range(5), 2))
        stud = [(not t) if i in bad else t for i, t in enumerate(truth_)]
        given = "; ".join(f"${u} > \\alpha {v}$" for u, v in facts)
        gp = [f"${order[i]}$ и ${order[i+1]}$" for i in range(5) if gaps[i]]
        gtxt = ("поместить индивид подразумеваемого класса можно лишь между " + ", ".join(gp)) if gp else "поместить индивид подразумеваемого класса нельзя ни между какими соседними элементами"
        U = (f"{ROW} По § 24 (с. 87) $u \\parallel \\alpha v$ («соприкасаются»), если и только если $(u > \\alpha v) \\vee (v > \\alpha u)$ и "
             f"невозможно поместить индивид между ними; подразумеваемый класс индивидов включает элементы $A$. Известно: {given}; {gtxt}. Студент утверждает:\n\n"
             + items([f"${u}$ и ${v}$ {'соприкасаются' if s else 'не соприкасаются'}" for (u, v), s in zip(pairs, stud)])
             + "\n\nРовно два утверждения ошибочны. Найдите их и обоснуйте.")
        A = "; ".join(f"{'абвгд'[i]}) ${pairs[i][0]}$ и ${pairs[i][1]}$ {'соприкасаются' if truth_[i] else 'не соприкасаются'}" for i in bad)
        R = ["Порядок по данным и C4 (от уступающих к превосходящим): $" + ", ".join(order) + "$."]
        for i, (u, v) in enumerate(pairs):
            a_, b_ = sorted([pos[u], pos[v]])
            if b_ > a_ + 1:
                R.append(f"{'абвгд'[i]}) между ними элемент ${order[a_+1]}$ — индивид класса; поместить индивид можно — не соприкасаются.")
            elif gaps[a_]:
                R.append(f"{'абвгд'[i]}) соседние, но между ними можно поместить индивид — не соприкасаются.")
            else:
                R.append(f"{'абвгд'[i]}) соседние, поместить индивид нельзя — соприкасаются (с. 87).")
        return U, A, "\n".join(R)
    r = fresh(make)
    if r:
        card(24, 6, "E", "vary", "def", "sym", "text", "с. 82, 87, гл. 2, § 24", ["соприкосновение", "диагностика"], *r)


def between_general():
    """Общее определение «между» (с. 82) для нескольких предметов и способов."""
    def make():
        ways = ["\\alpha^1", "\\alpha^2"]
        bs = ["b^1", "b^2", "b^3"]
        rel = {}
        for w in range(2):
            for b in bs:
                rel[(w, b)] = rnd.choice([">", "<"])   # a > w b  или  b > w a
        def ok_pair(i, k):
            for w in range(2):
                if (rel[(w, bs[i])] == ">" and rel[(w, bs[k])] == "<") or (rel[(w, bs[i])] == "<" and rel[(w, bs[k])] == ">"):
                    return w
            return None
        pairs = [(0, 1), (0, 2), (1, 2)]
        res = {p_: ok_pair(*p_) for p_ in pairs}
        allok = all(v is not None for v in res.values())
        facts = []
        for w in range(2):
            for b in bs:
                facts.append(f"$a > {ways[w]} {b}$" if rel[(w, b)] == ">" else f"${b} > {ways[w]} a$")
        U = ("Буквы $a, b^1, b^2, b^3$ — индивиды; $\\alpha^1, \\alpha^2$ — способы установления порядка. По § 20 (с. 82) $a$ находится "
             "между $b^1, …, b^n$ относительно $\\alpha^1, …, \\alpha^m$, если и только если для любой пары $b^i$ и $b^k$ найдётся такой "
             "$\\alpha^j$, что $(a > \\alpha^j b^i) \\wedge (b^k > \\alpha^j a)$ или $(b^i > \\alpha^j a) \\wedge (a > \\alpha^j b^k)$. "
             f"Известно: {'; '.join(facts)}. Установите, находится ли $a$ между $b^1, b^2, b^3$ относительно $\\alpha^1, \\alpha^2$; "
             "для каждой пары укажите подходящий способ или докажите, что его нет.")
        def ptxt(i, k):
            w = res[(i, k)]
            if w is None:
                return (f"для $b^{i+1}$, $b^{k+1}$ способа нет: относительно обоих способов $a$ с обоими в одном отношении "
                        f"(" + "; ".join(f"${ways[x]}$: " + ("$a$ превосходит оба" if rel[(x, bs[i])] == '>' else "оба превосходят $a$") for x in range(2)) + ")")
            o = "a" if rel[(w, bs[i])] == ">" else "b"
            if o == "a":
                return f"для $b^{i+1}$, $b^{k+1}$ подходит ${ways[w]}$: $(a > {ways[w]} b^{i+1}) \\wedge (b^{k+1} > {ways[w]} a)$"
            return f"для $b^{i+1}$, $b^{k+1}$ подходит ${ways[w]}$: $(b^{i+1} > {ways[w]} a) \\wedge (a > {ways[w]} b^{k+1})$"
        A = ("Находится" if allok else "Не находится") + ": " + "; ".join(ptxt(*p_) for p_ in pairs) + "."
        R = "\n".join(f"{n+1}. " + ptxt(*p_) + "." for n, p_ in enumerate(pairs)) + (
            "\n4. Условие выполнено для всех пар — $a$ находится между ними (с. 82)." if allok else
            "\n4. Хотя бы для одной пары способа нет — $a$ не находится между ними (с. 82).")
        if not allok and rnd.random() < 0.3:
            return None
        return U, A, R
    r = fresh(make)
    if r:
        card(20, 5, "C", "iso", "def", "sym", "short", "с. 82, гл. 2, § 20", ["между", "порядок"], *r)


# ================================================================ § 10, 12, 13 модальные определения

MD = ("Буква $x$ — высказывание, $sx$ — индивидуальное состояние. Определения и утверждения (с. 67, 69, 72–73): "
      "$N(sx) \\equiv Df.\\urcorner M(s{\\sim}x)$; $\\urcorner N(sx) \\equiv Df.M(s{\\sim}x)$; $C(sx) \\equiv Df.(x \\wedge M(s{\\sim}x))$; "
      "$\\urcorner C(sx) \\equiv Df.(x \\wedge \\urcorner M(s{\\sim}x))$; утверждения $A$: $x \\vdash M(sx)$, $N(sx) \\vdash x$; "
      "аксиомы 7 $E(sx) \\dashv\\vdash x$, 8 $\\urcorner E(sx) \\dashv\\vdash {\\sim}x$, 9 ${\\sim}E(sx) \\dashv\\vdash \\urcorner E(sx)$.")

MF = {"x": "x", "~x": "{\\sim}x", "M": "M(sx)", "M~": "M(s{\\sim}x)", "nM~": "\\urcorner M(s{\\sim}x)", "N": "N(sx)",
      "nN": "\\urcorner N(sx)", "C": "C(sx)", "nC": "\\urcorner C(sx)", "E": "E(sx)", "nE": "\\urcorner E(sx)", "~E": "{\\sim}E(sx)"}


def md_rules():
    def u(a, b, name):
        return (name, 1, lambda p: (b,) if p[0] == (a,) else None)
    R = [u("N", "nM~", "опр. N"), u("nM~", "N", "опр. N"), u("nN", "M~", "опр. ¬N"), u("M~", "nN", "опр. ¬N"),
         u("C", "x", "опр. C"), u("C", "M~", "опр. C"), u("nC", "x", "опр. ¬C"), u("nC", "nM~", "опр. ¬C"),
         u("x", "M", "A"), u("N", "x", "A"), u("E", "x", "7"), u("x", "E", "7"), u("nE", "~x", "8"), u("~x", "nE", "8"),
         u("~E", "nE", "9"), u("nE", "~E", "9"),
         ("опр. C", 2, lambda p: ("C",) if p[0] == ("x",) and p[1] == ("M~",) else None),
         ("опр. ¬C", 2, lambda p: ("nC",) if p[0] == ("x",) and p[1] == ("nM~",) else None)]
    return R


def md_show(lines):
    out = []
    for i, (f, w, refs) in enumerate(lines, 1):
        ww = "посылка" if w == "посылка" else f"{', '.join(map(str, refs))}; {w.replace('опр. ¬', 'определение $\\urcorner ').replace('опр. ', 'определение $') + ('$' if w.startswith('опр.') else '') if w.startswith('опр.') else ('утверждение $A$' if w == 'A' else 'аксиома ' + w)}"
        out.append(f"{i}. ${MF[f[0]]}$ [{ww}]")
    return "\n".join(out)


def md_problem(minlen=4):
    import lf_engine as E
    R = md_rules()
    for _ in range(300):
        prem = rnd.sample([("C",), ("nC",), ("N",), ("nN",), ("E",), ("~E",), ("M~",)], rnd.choice([1, 2]))
        how = E.closure(prem, R)
        # непротиворечивость: не вместе x и ~x, M~ и nM~
        fs = set(how)
        if ({("x",), ("~x",)} <= fs) or ({("M~",), ("nM~",)} <= fs):
            continue
        cands = []
        for f in how:
            if how[f][0] == "посылка":
                continue
            L = E.proof(f, how)
            if len(L) >= minlen and {l[0] for l in L if l[1] == "посылка"} == set(prem):
                cands.append((f, L))
        if cands:
            return prem, rnd.choice(cands), R
    return None


def md_long():
    def make():
        r = md_problem(4)
        if not r:
            return None
        prem, (f, L), R = r
        U = (f"{MD} Выведите ${MF[f[0]]}$ из " + " и ".join(f"${MF[p[0]]}$" for p in prem) + ", указывая основание каждой строки.")
        return U, f"Вывод в {len(L)} строк (см. решение).", md_show(L)
    r = fresh(make)
    if r:
        card(12, 5, "D", "iso", "def", "sym", "proof", "с. 67, 69, 72–73, гл. 2, § 9–13", ["модальности", "вывод"], *r)


def md_errors():
    import lf_engine as E

    def make():
        r = md_problem(5)
        if not r:
            return None
        prem, (f, L), R = r
        inner = [i for i, l in enumerate(L, 1) if l[1] != "посылка"]
        if len(inner) < 3:
            return None
        bad = sorted(rnd.sample(inner, 2))
        L2 = list(L)
        names = sorted({n for n, _, _ in R})
        for i in bad:
            fx, w, refs = L2[i - 1]
            alts = [n for n in names if n != w and n.split()[-1] != w.split()[-1]]
            rnd.shuffle(alts)
            for a in alts:
                L3 = list(L2)
                L3[i - 1] = (fx, a, refs)
                if i in E.check(L3, R, prem):
                    L2 = L3
                    break
            else:
                return None
        if sorted(E.check(L2, R, prem)) != bad:
            return None
        U = (f"{MD} В выводе ${MF[f[0]]}$ из " + " и ".join(f"${MF[p[0]]}$" for p in prem)
             + " ровно два основания указаны неверно. Найдите их, объясните ошибку и исправьте.\n\n" + md_show(L2))
        A = "; ".join(f"строка {i}" for i in bad) + " — см. решение."
        R_ = "Исправленный вывод:\n\n" + md_show(L)
        diff = []
        for i in bad:
            diff.append(f"Строка {i}: указано {md_show([L2[i-1]]).split('[')[1][:-1]}, верно {md_show([L[i-1]]).split('[')[1][:-1]}.")
        return U, "; ".join(diff), "\n".join(diff) + "\n\n" + R_
    r = fresh(make)
    if r:
        card(12, 6, "E", "vary", "def", "sym", "text", "с. 67, 69, 72–73, гл. 2, § 9–13", ["модальности", "диагностика"], *r)


# ================================================================ запуск

def run(card_, fresh_, rnd_):
    global card, fresh, rnd
    card, fresh, rnd = card_, fresh_, rnd_
    for f, n in [(v_series, 12), (v_errors, 8), (v_open, 8),
                 (p_series, 13), (p_errors, 9), (p_open, 9),
                 (e_series, 18), (e_errors, 12),
                 (m_long, 10), (m_complete, 9), (m_errors, 9), (m_open, 9),
                 (k_series, 12), (k_relations, 10), (k_errors, 9), (k_build, 15),
                 (row_series, 18), (row_touch_errors, 14), (between_general, 15),
                 (md_long, 16), (md_errors, 9)]:
        for _ in range(n):
            f()
