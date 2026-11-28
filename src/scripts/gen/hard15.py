#!/usr/bin/env python3
"""Приложение (с. 192–197), усиление по образцу занятия 10: серии, проверяемые программой.

Модель — src/scripts/logic/app15.py (правила 1–5 прямой интерпретации, D1; x → x*; D3, MT1–MT3) и ifq.py.
В задачи на D1 берутся только формулы, у которых проверка со стороны посылки и со стороны заключения
даёт один результат (с. 194: «проверка со стороны заключения даёт тот же результат»).

  python3 src/scripts/gen/hard15.py      — пишет drafts/15.00-hard-gen.md
"""
import random
import sys
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import app15 as A  # noqa: E402
from ifq import ALL, EX, C, N, V, W, EL  # noqa: E402

rnd = random.Random(1515)
x, y, z = V("x"), V("y"), V("z")
CARDS = []

PRE = ("Буквы $x, y, z$ — высказывания, $a, b$ — термины, входящие в $x, y, z$ (кванторные группы не вырождены); "
       "$\\sim$ и кванторная группа относятся к ближайшему следующему высказыванию: $(\\forall a)x\\sim(\\forall a)\\sim y$ — "
       "конъюнкция $(\\forall a)x$ и $\\sim(\\forall a)\\sim y$, а в $(\\forall a)(xy)$ квантор относится ко всей конъюнкции.")
STAR_RULES = ("Предварительное преобразование (с. 192): вхождения $\\sim(a^1a^2 \\ldots a^n)$, $\\sim(a^1 \\vee \\ldots \\vee a^n)$, "
              "$\\sim\\sim a$, $(\\exists a)b$ заменяются соответственно на $\\sim a^1 \\vee \\sim a^2 \\vee \\ldots \\vee \\sim a^n$, "
              "$\\sim a^1\\sim a^2 \\ldots \\sim a^n$, $a$, $\\sim(\\forall a)\\sim b$, пока такие вхождения есть.")
RULES = ("Правила прямой интерпретации (с. 192–193): обычные правила для конъюнкции, дизъюнкции и отрицания; "
         "1) всем вхождениям $(\\forall a)b$ в одно высказывание приписывается одно значение; "
         "2) если $(\\forall a)b$ приписали 1, то $b$ приписывается 1; если 0 — значение $b$ этим не определяется; "
         "3) если $b$ приписали 0, то $(\\forall a)b$ приписывается 0; если 1 — значение $(\\forall a)b$ не определяется; "
         "4) если, приписав $x$ значение 1 ($y$ — значение 0), мы вынуждены приписать 1 высказыванию $b$ из $y$ (из $x$), "
         "то $(\\forall a)b$ из $y$ (из $x$) приписывается 1; 5) если не вынуждены (можно приписать $b$ значение 0), то "
         "$(\\forall a)b$ приписывается 0. D1 (с. 193): $x \\vdash y$ — тавтология, если и только если она принимает значение 1 "
         "при всех вариантах приписывания значений частям $x$ и $y$.")


# ---------------------------------------------------------------- запись
def T(f, ctx="top"):
    k = f[0]
    if k == "v":
        return f[1]
    if k == "el":
        return f"({f[1]} \\leftarrow {f[2]})"
    if k == "neg":
        g = f[1]
        return f"\\sim {T(g)}" if g[0] in ("v", "el", "neg", "all", "ex") else f"\\sim({T(g)})"
    if k == "conj":
        return "".join(f"({T(a)})" if a[0] in ("conj", "wdis") else T(a) for a in f[1])
    if k == "wdis":
        out = " \\vee ".join(f"({T(a)})" if a[0] == "wdis" else T(a) for a in f[1])
        return f"({out})" if ctx == "in" else out
    if k in ("all", "ex"):
        q = "\\forall" if k == "all" else "\\exists"
        g = f[2]
        inner = T(g) if g[0] in ("v", "el", "all", "ex", "neg") else f"({T(g)})"
        return f"({q} {f[1]}){inner}"
    raise ValueError(k)


def F(a, b=None):
    return f"{T(a)} \\vdash {T(b)}" if b is not None else f"\\vdash {T(a)}"


def card(level, typ, step, cond, ans, sol, source, tags, *, condition="def", form="sym", answer="short", generated=True, system=None):
    head = ["---", "chapter: 15", "section: 0", f"level: {level}", f"type: {typ}", f"step: {step}", f"condition: {condition}",
            f"form: {form}", f"answer: {answer}", f'source: "{source}"']
    if system:
        head.append(f'system: "{system}"')
    if generated:
        head.append("generated: true")
    head += [f"tags: [{', '.join(tags)}]", "---", "", "## Условие", "", cond.strip(), "", "## Ответ", "", ans.strip(), "", "## Решение", "", sol.strip(), ""]
    CARDS.append("\n".join(head))


def letters(lst):
    return "абвгдежз"[lst]


def series(items):
    return "\n".join(f"{letters(i)}) {s}" for i, s in enumerate(items))


# ---------------------------------------------------------------- x → x* по шагам
def flat(k, ps):
    return A.flat(k, ps)


def rewrite_once(f, wrong=None):
    """Первое (сверху, слева) применимое преобразование с. 192: (новая формула, правило) или None.
    wrong — ошибочное правило студента для этого шага."""
    k = f[0]
    if k == "neg":
        g = f[1]
        if g[0] == "conj":
            if wrong == "conj":
                return flat("conj", [N(h) for h in g[1]]), "conj"
            return flat("wdis", [N(h) for h in g[1]]), "conj"
        if g[0] == "wdis":
            if wrong == "dis":
                return flat("wdis", [N(h) for h in g[1]]), "dis"
            return flat("conj", [N(h) for h in g[1]]), "dis"
        if g[0] == "neg":
            return g[1], "nn"
    if k == "ex":
        if wrong == "ex1":
            return N(EX(f[1], N(f[2]))), "ex"
        if wrong == "ex2":
            return ALL(f[1], N(f[2])), "ex"
        return N(ALL(f[1], N(f[2]))), "ex"
    if k in ("neg", "all"):
        r = rewrite_once(f[-1], wrong)
        if r:
            return ((k, f[1], r[0]) if k == "all" else N(r[0])), r[1]
        return None
    if k in ("conj", "wdis"):
        for i, h in enumerate(f[1]):
            r = rewrite_once(h, wrong)
            if r:
                ps = list(f[1])
                ps[i] = r[0]
                return flat(k, ps), r[1]
    return None


RN = {"conj": "$\\sim(a^1 \\ldots a^n) \\to \\sim a^1 \\vee \\ldots \\vee \\sim a^n$",
      "dis": "$\\sim(a^1 \\vee \\ldots \\vee a^n) \\to \\sim a^1 \\ldots \\sim a^n$",
      "nn": "$\\sim\\sim a \\to a$", "ex": "$(\\exists a)b \\to \\sim(\\forall a)\\sim b$"}


def trace(f):
    st = []
    cur = f
    while True:
        r = rewrite_once(cur)
        if not r:
            break
        cur = r[0]
        st.append((cur, r[1]))
    assert cur == A.star(f), (T(cur), T(A.star(f)))
    return st


def rnd_formula(depth, lets="xyz", qs="ab", p_leaf=0.22, bound=frozenset()):
    """Случайное высказывание; кванторная группа по уже связанному термину не ставится (иначе внешняя вырождена)."""
    if depth == 0 or rnd.random() < p_leaf:
        return V(rnd.choice(lets))
    free_q = [t for t in qs if t not in bound]
    kinds = ["neg", "neg", "conj", "wdis"] + (["all", "ex", "ex"] if free_q else [])
    k = rnd.choice(kinds)
    if k == "neg":
        return N(rnd_formula(depth - 1, lets, qs, p_leaf, bound))
    if k in ("all", "ex"):
        t = rnd.choice(free_q)
        return (k, t, rnd_formula(depth - 1, lets, qs, p_leaf, bound | {t}))
    a1, a2 = rnd_formula(depth - 1, lets, qs, p_leaf, bound), rnd_formula(depth - 1, lets, qs, p_leaf, bound)
    while a2 == a1:
        a2 = rnd_formula(depth - 1, lets, qs, p_leaf, bound)
    return flat(k, [a1, a2])


USED = set()


def fresh(gen, ok):
    for _ in range(20000):
        f = gen()
        key = repr(f)
        if key not in USED and ok(f):
            USED.add(key)
            return f
    raise RuntimeError("не нашлось")


# ---------------------------------------------------------------- A. x → x*
def a_complete():
    f = fresh(lambda: rnd_formula(5), lambda f: 6 <= len(trace(f)) <= 9)
    st = trace(f)
    hide = sorted(rnd.sample(range(1, len(st) - 1), 2))
    lines = []
    for i, (g, r) in enumerate(st):
        lines.append(f"{i + 1}. $\\ldots$ [$\\ldots$]" if i in hide else f"{i + 1}. ${T(g)}$ [{RN[r]}]")
    cond = (f"{PRE} {STAR_RULES} Ниже по шагам выполнено преобразование высказывания $x = {T(f)}$ в $x^*$; на каждом шаге заменяется "
            "одно вхождение (первое слева, начиная с внешних). В двух строках пропущены и формула, и основание. Восстановите их.\n\n"
            + "\n".join(lines))
    ans = "; ".join(f"шаг {i + 1}: ${T(st[i][0])}$ [{RN[st[i][1]]}]" for i in hide)
    sol = (f"С. 192. Шаги: " + "; ".join(f"{i + 1}) ${T(g)}$ ({RN[r]})" for i, (g, r) in enumerate(st)) +
           f". Получено $x^* = {T(st[-1][0])}$: вхождений четырёх видов не осталось; $x^*$ равнозначно $x$ (с. 192).")
    card(4, "D", "complete", cond, ans, sol, "с. 192, Приложение", ["приписывание значений", "предварительное преобразование"])


def a_iso():
    for _ in range(1):
        pairs = []
        for _ in range(4):
            a1 = fresh(lambda: rnd_formula(4), lambda f: len(trace(f)) >= 4)
            b1 = fresh(lambda: rnd_formula(4), lambda f: len(trace(f)) >= 3)
            pairs.append((a1, b1))
        cond = (f"{PRE} {STAR_RULES} Приведите каждую формулу к виду $x^* \\vdash y^*$ и укажите, сколько замен каждого вида потребовалось.\n\n"
                + series([f"${F(a1, b1)}$" for a1, b1 in pairs]))
        ans = "; ".join(f"{letters(i)}) ${F(A.star(a1), A.star(b1))}$" for i, (a1, b1) in enumerate(pairs))

        def cnt(f):
            st = trace(f)
            c = {r: sum(1 for _, q in st if q == r) for r in RN}
            return ", ".join(f"{RN[r]} — {c[r]}" for r in RN if c[r])
        sol = ("С. 192: $x \\vdash y$ равнозначна $x^* \\vdash y^*$. " +
               " ".join(f"{letters(i)}) Посылка: {cnt(a1)}; заключение: {cnt(b1)}." for i, (a1, b1) in enumerate(pairs)))
        card(5, "D", "iso", cond, ans, sol, "с. 192, Приложение", ["приписывание значений", "предварительное преобразование"])


WRONG = {"conj": ("$\\sim(a^1 \\ldots a^n)$ заменён конъюнкцией отрицаний, а нужна дизъюнкция $\\sim a^1 \\vee \\ldots \\vee \\sim a^n$"),
         "dis": ("$\\sim(a^1 \\vee \\ldots \\vee a^n)$ заменён дизъюнкцией отрицаний, а нужна конъюнкция $\\sim a^1 \\ldots \\sim a^n$"),
         "ex1": ("$(\\exists a)b$ заменён на $\\sim(\\exists a)\\sim b$, а нужно $\\sim(\\forall a)\\sim b$"),
         "ex2": ("при замене $(\\exists a)b$ потерян внешний знак $\\sim$: нужно $\\sim(\\forall a)\\sim b$, а не $(\\forall a)\\sim b$")}


def star_with(f, mistakes):
    """x → x* с ошибками студента: mistakes — список видов, каждый применяется один раз, в первом подходящем месте."""
    cur, todo = f, list(mistakes)
    for _ in range(200):
        r = None
        if todo:
            # ищем, применимо ли первое правило с ошибкой в первом месте, где применимо любое правило
            r0 = rewrite_once(cur)
            if r0 is None:
                break
            want = {"conj": "conj", "dis": "dis", "ex1": "ex", "ex2": "ex"}[todo[0]]
            if r0[1] == want:
                r = rewrite_once(cur, todo[0])
                todo.pop(0)
            else:
                r = r0
        else:
            r = rewrite_once(cur)
        if r is None:
            break
        cur = r[0]
    return cur, not todo


def a_diag():
    kinds = [("conj", "ex2"), ("ex1", "dis"), ("dis", "conj")]
    k = kinds[len([c for c in CARDS if "предварительное преобразование, диагностика" in c]) % len(kinds)]
    for _ in range(5000):
        f = fresh(lambda: rnd_formula(5), lambda f: len(trace(f)) >= 5)
        wrong, ok = star_with(f, list(k))
        if ok and wrong != A.star(f):
            break
    right = A.star(f)
    cond = (f"{PRE} {STAR_RULES} Студент привёл высказывание\n\n$${T(f)}$$\n\nк виду\n\n$${T(wrong)}$$\n\n"
            "Найдите все ошибки, назовите нарушенные правила и запишите верный результат.")
    ans = f"Две ошибки: {WRONG[k[0]]}; {WRONG[k[1]]} (с. 192). Верно: ${T(right)}$."
    sol = ("С. 192. Верный ход: " + "; ".join(f"${T(g)}$ ({RN[r]})" for g, r in trace(f)) +
           f". У студента: 1) {WRONG[k[0]]}; 2) {WRONG[k[1]]}. Обе замены не равнозначны исходным вхождениям.")
    card(6, "E", "open", cond, ans, sol, "с. 192, Приложение", ["приписывание значений", "предварительное преобразование, диагностика"])


# ---------------------------------------------------------------- B. правила 1–3 внутри высказывания
def forced_parts(s, target):
    vs = A.variants(s, target)
    p = A.parts(s)
    keys = sorted(p["v"], key=repr) + p["q"]
    out = {}
    for kk in keys:
        vals = {v[kk] for v in vs}
        out[kk] = vals.pop() if len(vals) == 1 else None
    return out, vs


def kname(kk):
    return f"${kk}$" if isinstance(kk, str) else f"${T(kk)}$"


def vword(v):
    return "не определяется" if v is None else str(v)


def b_series(level=3):
    for _ in range(5000):
        s = A.star(fresh(lambda: rnd_formula(4, "xy"), lambda f: True))
        target = rnd.choice([1, 0])
        if not A.variants(s, target):
            continue
        fp, vs = forced_parts(s, target)
        qs = [k for k in fp if not isinstance(k, str)]
        if len(qs) >= 2 and len(fp) >= 4 and any(v is None for v in fp.values()) and any(v is not None for v in fp.values()):
            break
    keys = list(fp)[:6]
    cond = (f"{PRE} {RULES.split(' 4)')[0]}. Высказывание $s = {T(s)}$ уже приведено к виду $s^*$; ему приписали значение {target}. "
            "Для каждой части ниже установите, какое значение она обязана получить по правилам для $\\sim$, конъюнкции, дизъюнкции и правилам 1–3, "
            "или покажите, что значение не определяется (приведите два допустимых варианта).\n\n" + series([kname(k) for k in keys]))
    ans = "; ".join(f"{letters(i)}) {vword(fp[k])}" for i, k in enumerate(keys))
    lines = []
    for i, kk in enumerate(keys):
        if fp[kk] is None:
            v1 = next(v for v in vs if v[kk] == 1)
            v0 = next(v for v in vs if v[kk] == 0)
            lines.append(f"{letters(i)}) допустимы варианты с {kname(kk)} = 1 ({env(v1)}) и = 0 ({env(v0)})")
        else:
            lines.append(f"{letters(i)}) во всех допустимых вариантах {kname(kk)} = {fp[kk]}")
    sol = (f"Перебираем приписывания значений буквам и вхождениям $(\\forall a)b$, при которых $s = {target}$ и выполнены правила 1–3 "
           f"(с. 192: $(\\forall a)b = 1$ влечёт $b = 1$, $b = 0$ влечёт $(\\forall a)b = 0$). Допустимых вариантов: {len(vs)}. " + "; ".join(lines) + ".")
    card(level, "V", "iso", cond, ans, sol, "с. 192, Приложение", ["приписывание значений", "правила 1–3"])


def env(v):
    parts_ = []
    for k, val in v.items():
        parts_.append(f"${k if isinstance(k, str) else T(k)} = {val}$")
    return ", ".join(parts_)


# ---------------------------------------------------------------- C. D1
def agree(a, b):
    r = A.taut(a, b)
    return r[1] == r[2], r[0]


def explain(a, b):
    xs, ys = A.star(a), A.star(b)
    ok, vs, qv = A.side(xs, ys, True)
    lines = [f"Приводим к виду ${F(xs, ys)}$ (с. 192)."]
    if not vs:
        lines.append("Посылке нельзя приписать 1 по правилам (противоречие) — формула тавтология (с. 193).")
        return True, " ".join(lines)
    fp, _ = forced_parts(xs, 1)
    fixed = [f"{kname(k)} = {v}" for k, v in fp.items() if v is not None]
    loose = [kname(k) for k, v in fp.items() if v is None]
    lines.append("Посылке 1. По правилам для $\\sim$, конъюнкции, дизъюнкции и правилам 1–3: " +
                 (", ".join(fixed) if fixed else "ни одна часть не получает обязательного значения") +
                 ("; не определяются: " + ", ".join(loose) if loose else "") + f" (допустимых вариантов: {len(vs)}).")
    known = set(k for k in vs[0] if not (isinstance(k, tuple) and k[0] == "all"))
    free = sorted(A.parts(ys)["v"] - known, key=repr)
    for q, val in qv.items():
        if val:
            lines.append(f"В заключении ${T(q)}$: при посылке 1 мы вынуждены приписать ${T(q[2])}$ значение 1 (во всех вариантах), по правилу 4 ${T(q)} = 1$.")
        else:
            wit = None
            for v in vs:
                for bits in product((0, 1), repeat=len(free)):
                    a_ = {**v, **dict(zip(free, bits)), **qv}
                    if not A.val(q[2], a_):
                        wit = {kk: vv for kk, vv in a_.items() if isinstance(kk, str)}
                        break
                if wit:
                    break
            lines.append(f"В заключении ${T(q)}$: ${T(q[2])}$ можно приписать 0 (при {env(wit)}), по правилу 5 ${T(q)} = 0$.")
    if ok:
        lines.append(f"Тогда ${T(ys)} = 1$ во всех вариантах.")
    else:
        for v in vs:
            for bits in product((0, 1), repeat=len(free)):
                a_ = {**v, **dict(zip(free, bits)), **qv}
                if not A.val(ys, a_):
                    wit = {kk: vv for kk, vv in a_.items() if isinstance(kk, str)}
                    lines.append(f"При {env(wit)} заключение получает 0: формула принимает значение 0 — не тавтология (D1).")
                    return False, " ".join(lines)
    ok2 = A.side(xs, ys, False)[0]
    assert ok2 == ok
    lines.append("Проверка со стороны заключения (приписываем $y^*$ значение 0) даёт тот же результат. По D1 — тавтология.")
    return True, " ".join(lines)


def rnd_pair(dx=3, dy=3):
    return rnd_formula(dx, "xy", "ab", 0.3), rnd_formula(dy, "xy", "ab", 0.3)


def has_q(f):
    return any(k in repr(f) for k in ("'all'", "'ex'"))


def c_series(level, n=4, want_mix=True):
    items = []
    while len(items) < n:
        a, b = fresh(lambda: rnd_pair(3, 3), lambda p: has_q(p[0]) and has_q(p[1]) and agree(*p)[0])
        t = agree(a, b)[1]
        if want_mix and sum(1 for _, _, tt in items if tt == t) >= (n + 1) // 2:
            continue
        items.append((a, b, t))
    cond = (f"{PRE} {STAR_RULES} {RULES} Исследуйте по этим правилам каждую формулу: приведите её к виду $x^* \\vdash y^*$, припишите посылке "
            "значение 1 и выясните, принимает ли формула значение 1 при всех вариантах. Для нетавтологии укажите вариант, где она равна 0.\n\n"
            + series([f"${F(a, b)}$" for a, b, _ in items]))
    ans = "; ".join(f"{letters(i)}) {'тавтология' if t else 'не тавтология'}" for i, (_, _, t) in enumerate(items))
    sol = " ".join(f"{letters(i)}) {explain(a, b)[1]}" for i, (a, b, _) in enumerate(items))
    card(level, "C", "iso" if level <= 5 else "open", cond, ans, sol, "с. 192–194, Приложение", ["приписывание значений", "тавтология, D1"])


def c_pair(level):
    """Прямая и обратная формулы — открытый исход."""
    for _ in range(20000):
        a, b = rnd_pair(3, 3)
        if not (has_q(a) and has_q(b)) or a == b:
            continue
        g1, t1 = agree(a, b)
        g2, t2 = agree(b, a)
        if g1 and g2 and t1 != t2 and repr((a, b)) not in USED:
            USED.add(repr((a, b)))
            break
    cond = (f"{PRE} {STAR_RULES} {RULES} Исследуйте обе формулы и обоснуйте результат для каждой:\n\n"
            f"а) ${F(a, b)}$\nб) ${F(b, a)}$")
    ans = f"а) {'тавтология' if t1 else 'не тавтология'}; б) {'тавтология' if t2 else 'не тавтология'}"
    sol = f"а) {explain(a, b)[1]} б) {explain(b, a)[1]}"
    card(level, "C", "open", cond, ans, sol, "с. 192–194, Приложение", ["приписывание значений", "тавтология, D1"])


# ---------------------------------------------------------------- D. D3, MT1–MT3
def clause_tex(c):
    return " \\vee ".join(("\\sim " if s == 0 else "") + n for n, s in c)


def rep_formulas(clauses):
    out = []
    for c in clauses:
        c2 = list(c) if len(c) > 1 else [c[0], c[0]]
        (n, s), d = c2[0], c2[1:]
        lhs = n if s == 0 else f"\\sim {n}"
        rhs = " \\vee ".join(("\\sim " if t == 0 else "") + m for m, t in d)
        out.append(f"{lhs} \\vdash {rhs}")
    return out


def lit(n, s):
    return V(n) if s else N(V(n))


def d_series(level=5):
    """Префиксные высказывания (K¹a¹)…(Kⁿaⁿ)M, M — конъюнкция двучленных дизъюнкций литер и литер (D3 без неоднозначности)."""
    items = []
    while len(items) < 3:
        k = rnd.randint(2, 3)
        cl = []
        for _ in range(k):
            if rnd.random() < 0.25:
                cl.append([(rnd.choice("xyz"), rnd.randint(0, 1))])
            else:
                n1, n2 = rnd.sample("xyz", 2) if rnd.random() < 0.6 else (lambda c: (c, c))(rnd.choice("xyz"))
                cl.append([(n1, rnd.randint(0, 1)), (n2, rnd.randint(0, 1))])
        if len({repr(c) for c in cl}) < len(cl):
            continue
        M = C(*[lit(*c[0]) if len(c) == 1 else W(lit(*c[0]), lit(*c[1])) for c in cl])
        pref = rnd.choice([[("all", "a"), ("ex", "b")], [("ex", "a"), ("all", "b"), ("ex", "a")][:2], [("all", "b")], [("ex", "a"), ("ex", "b")]])
        f = M
        for q, t in reversed(pref):
            f = (q, t, f)
        taut_ = all(any((n, 1) in c and (n, 0) in c for n in "xyz") for c in cl)
        if sum(1 for *_, tt in items if tt == taut_) >= 2 or repr(f) in USED:
            continue
        USED.add(repr(f))
        items.append((f, cl, taut_))
    cond = (f"{PRE} D3 (с. 194): представительство высказывания в классе формул следования получают так: 1) высказывание эквивалентными "
            "преобразованиями приводят к виду $(K^1a^1) \\ldots (K^na^n)y$, где $y$ есть $\\sim a$, $a \\vee b$ или $ab$; 2) $\\sim a$ приводят к виду "
            "$c \\vee d$ или $cd$; 3) к каждому из $a$ и $b$ в $ab$ применяют 1 и 2, пока не получится множество формул вида $c \\vee d$; элементарное "
            "$a$ заменяют на $a \\vee a$; 4) каждую $c \\vee d$ заменяют на $\\sim c \\vdash d$. MT1 (с. 195): высказывание — тавтология, если и только если "
            "тавтологии все формулы его представительства; MT3: $(K^1a^1) \\ldots (K^na^n)x$ — тавтология, если и только если $x$ — тавтология. "
            "Для каждого высказывания найдите представительство и установите, тавтология ли оно; результат проверьте по MT3.\n\n"
            + series([f"${T(f)}$" for f, _, _ in items]))
    ans = "; ".join(f"{letters(i)}) {'; '.join('$' + s.replace('\\sim \\sim ', '') + '$' for s in rep_formulas(cl))} — {'тавтология' if t else 'не тавтология'}"
                    for i, (_, cl, t) in enumerate(items))
    sols = []
    for i, (f, cl, t) in enumerate(items):
        reps = [s.replace("\\sim \\sim ", "") for s in rep_formulas(cl)]
        bad = [r for r, c in zip(reps, cl) if not any((n, 1) in c and (n, 0) in c for n in "xyz")]
        sols.append(f"{letters(i)}) Высказывание уже имеет вид п. 1; члены конъюнкции — " + "; ".join(f"${clause_tex(c)}$" for c in cl) +
                    " (элементарный член $a$ заменяется на $a \\vee a$); п. 4 даёт " + "; ".join(f"${r}$" for r in reps) + ". " +
                    ("Каждая формула — тавтология (посылке 1 — заключение 1 при любых значениях: в члене есть буква и её отрицание); по MT1 высказывание — тавтология." if t else
                     f"Формула ${bad[0]}$ не тавтология: посылке можно приписать 1, а заключению 0; по MT1 высказывание не тавтология.") +
                    f" MT3: матрица {'тавтология' if t else 'не тавтология'} — тот же результат.")
    card(level, "C", "iso", cond, ans, " ".join(sols), "с. 194–195, Приложение, D3, MT1, MT3", ["приписывание значений", "представительство"])


# ---------------------------------------------------------------- F. Aᵏ и Dⁱ на элементарных высказываниях
def subst_free(f, a, b, bound=frozenset()):
    k = f[0]
    if k == "el":
        return EL(*(b if (t == a and a not in bound) else t for t in f[1:]))
    if k == "neg":
        return N(subst_free(f[1], a, b, bound))
    if k in ("all", "ex"):
        return (k, f[1], subst_free(f[2], a, b, bound | {f[1]}))
    return (k, tuple(subst_free(g, a, b, bound) for g in f[1]))


def subst_all(f, a, b):
    k = f[0]
    if k == "el":
        return EL(*(b if t == a else t for t in f[1:]))
    if k == "neg":
        return N(subst_all(f[1], a, b))
    if k in ("all", "ex"):
        return (k, b if f[1] == a else f[1], subst_all(f[2], a, b))
    return (k, tuple(subst_all(g, a, b) for g in f[1]))


def terms_of(f):
    k = f[0]
    if k == "el":
        return set(f[1:])
    if k == "neg":
        return terms_of(f[1])
    if k in ("all", "ex"):
        return {f[1]} | terms_of(f[2])
    return set().union(*(terms_of(g) for g in f[1]))


def free_in(a, f, bound=frozenset()):
    k = f[0]
    if k == "el":
        return a in f[1:] and a not in bound
    if k == "neg":
        return free_in(a, f[1], bound)
    if k in ("all", "ex"):
        return free_in(a, f[2], bound | {f[1]})
    return any(free_in(a, g, bound) for g in f[1])


def capture(f, a, b):
    """В f есть (∀b)z или (∃b)z, в z которых a входит свободно (условие Aᵏ нарушено)."""
    k = f[0]
    if k == "el":
        return False
    if k == "neg":
        return capture(f[1], a, b)
    if k in ("all", "ex"):
        if f[1] == b and free_in(a, f[2]):
            return True
        return capture(f[2], a, b)
    return any(capture(g, a, b) for g in f[1])


def is_ak(xf, yf):
    """(∀a)x ⊢ y или y ⊢ (∃a)x — схема Aᵏ (с. 196): y — из x заменой всех свободных a на другой термин b,
    в x нет (∀b)z, (∃b)z со свободным a в z. Возвращает список (вид, a, b)."""
    res = []
    for q, f, g in (("all", xf, yf), ("ex", yf, xf)):
        if f[0] != q:
            continue
        a, body = f[1], f[2]
        for b in sorted(terms_of(g) | {"b", "c", "d", "e"}):
            if b != a and subst_free(body, a, b) == g and not capture(body, a, b):
                res.append((q, a, b))
    return res


def is_renaming(xf, yf):
    """Dⁱ (с. 197): y — из x заменой нуля или более вхождений (Ka)z на (Kb)v, v — из z заменой всех a на b, b не входит в z."""
    if xf == yf:
        return True
    if xf[0] != yf[0]:
        return False
    k = xf[0]
    if k == "el":
        return False
    if k == "neg":
        return is_renaming(xf[1], yf[1])
    if k in ("all", "ex"):
        if xf[1] == yf[1] and is_renaming(xf[2], yf[2]):
            return True
        a, z_, b = xf[1], xf[2], yf[1]
        return b != a and b not in terms_of(z_) and is_renaming(subst_all(z_, a, b), yf[2])
    return len(xf[1]) == len(yf[1]) and all(is_renaming(p, q) for p, q in zip(xf[1], yf[1]))


def main():
    for _ in range(2):
        a_complete()
    for _ in range(3):
        a_iso()
    for _ in range(3):
        a_diag()
    for _ in range(3):
        b_series(3)
    for lv in (5, 5, 5, 5):
        c_series(lv)
    for _ in range(4):
        c_pair(6)
    for _ in range(3):
        d_series(5)
    out = ROOT.parent / "drafts" / "15.00-hard-gen.md"
    out.parent.mkdir(exist_ok=True)
    out.write_text("\n=====\n\n".join(CARDS), encoding="utf-8")
    print(f"{len(CARDS)} карточек → {out}")


if __name__ == "__main__":
    main()
