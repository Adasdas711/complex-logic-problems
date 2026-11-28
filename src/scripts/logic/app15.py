"""Приложение «Комплексной логики» (с. 192–197): прямая интерпретация высказываний с кванторами и формул следования.

Формулы — узлы модели ifq: ('v', x), ('neg', F), ('conj', (…)), ('wdis', (…)), ('all', a, F), ('ex', a, F).
Буквы — высказывания (в них может входить термин квантора), поэтому кванторные группы не считаются вырожденными.

star(f)        — предварительное преобразование x → x* (с. 192).
variants(x)    — варианты приписывания значений частям x при x = 1: буквам и вхождениям (∀a)b;
                 правила 1–3 (с. 192): одинаковые вхождения (∀a)b — одно значение; (∀a)b = 1 ⇒ b = 1 (⇔ b = 0 ⇒ (∀a)b = 0).
qvals(y, vs)   — правила 4, 5 (с. 193): (∀a)b в y получает 1, если при x = 1 мы вынуждены приписать b значение 1
                 (b = 1 во всех вариантах), иначе 0; считается изнутри наружу.
taut(x, y)     — D1 (с. 193): со стороны посылки (x = 1) и со стороны заключения (y = 0); книга: результаты совпадают.
"""
from itertools import product

from ifq import ALL, C, EX, N, V, W, tex  # noqa: F401


def flat(k, parts):
    out = []
    for p in parts:
        out += list(p[1]) if p[0] == k else [p]
    return (k, tuple(out)) if len(out) > 1 else out[0]


def star(f):
    """x → x*: ~(a¹…aⁿ) → ~a¹∨…∨~aⁿ; ~(a¹∨…∨aⁿ) → ~a¹…~aⁿ; ~~a → a; (∃a)b → ~(∀a)~b (с. 192)."""
    k = f[0]
    if k == "neg":
        g = f[1]
        if g[0] == "conj":
            return flat("wdis", [star(N(h)) for h in g[1]])
        if g[0] == "wdis":
            return flat("conj", [star(N(h)) for h in g[1]])
        if g[0] == "neg":
            return star(g[1])
        if g[0] == "ex":
            return star(ALL(g[1], N(g[2])))
        return N(star(g))
    if k == "ex":
        return N(ALL(f[1], star(N(f[2]))))
    if k == "all":
        return ALL(f[1], star(f[2]))
    if k in ("conj", "wdis"):
        return flat(k, [star(h) for h in f[1]])
    return f


def parts(f, acc=None):
    """Буквы и вхождения (∀a)b в f (одинаковые вхождения — один ключ: правило 1)."""
    acc = {"v": set(), "q": []} if acc is None else acc
    k = f[0]
    if k == "v":
        acc["v"].add(f[1])
    elif k == "el":
        acc["v"].add(f)
    elif k == "neg":
        parts(f[1], acc)
    elif k == "all":
        parts(f[2], acc)
        if f not in acc["q"]:
            acc["q"].append(f)       # внутренние раньше внешних
    elif k in ("conj", "wdis"):
        for h in f[1]:
            parts(h, acc)
    else:
        raise ValueError("после x → x* остаются только ~, конъюнкция, дизъюнкция, ∀: " + k)
    return acc


def val(f, a):
    k = f[0]
    if k == "v":
        return a[f[1]]
    if k in ("all", "el"):
        return a[f]
    if k == "neg":
        return 1 - val(f[1], a)
    if k == "conj":
        return int(all(val(h, a) for h in f[1]))
    return int(any(val(h, a) for h in f[1]))


def variants(x, target=1):
    """Все приписывания значений буквам и (∀a)b из x с x = target, согласные с правилами 1–3."""
    p = parts(x)
    vs, qs = sorted(p["v"], key=repr), p["q"]
    out = []
    for bits in product((0, 1), repeat=len(vs) + len(qs)):
        a = dict(zip(vs, bits[:len(vs)]))
        a.update(zip(qs, bits[len(vs):]))
        if all(not a[q] or val(q[2], a) for q in qs) and val(x, a) == target:
            out.append(a)
    return out


def qvals(y, vs):
    """Правила 4, 5: значения вхождений (∀a)b в y по вариантам vs другой части формулы."""
    p = parts(y)
    known = set(k for k in vs[0] if not (isinstance(k, tuple) and k[0] == "all")) if vs else set()
    free = sorted(p["v"] - known, key=repr)
    res = {}
    for q in p["q"]:
        forced = True
        for v in vs:
            for bits in product((0, 1), repeat=len(free)):
                a = {**v, **dict(zip(free, bits)), **res}
                if not val(q[2], a):
                    forced = False
                    break
            if not forced:
                break
        res[q] = int(forced)
    return res, free


def side(x, y, from_premise=True):
    """Проверка со стороны посылки (x = 1 ⇒ y = 1 во всех вариантах) или заключения (y = 0 ⇒ x = 0)."""
    a_, b_ = (x, y) if from_premise else (y, x)
    vs = variants(a_, 1 if from_premise else 0)
    if not vs:
        return True, vs, {}
    qv, free = qvals(b_, vs)
    want = 1 if from_premise else 0
    for v in vs:
        for bits in product((0, 1), repeat=len(free)):
            a = {**v, **dict(zip(free, bits)), **qv}
            if val(b_, a) != want:
                return False, vs, qv
    return True, vs, qv


def taut(x, y=None):
    """D1, D2: x ⊢ y (или ⊢ x) — тавтология. Возвращает (результат, со стороны посылки, со стороны заключения)."""
    if y is None:           # D2 + п. 5: ⊢ x — тавтология, если x — тавтология
        return statement_taut(x)
    xs, ys = star(x), star(y)
    p = side(xs, ys, True)[0]
    c = side(xs, ys, False)[0]
    return p, p, c


def statement_taut(x):
    """Высказывание — тавтология по правилам: x = 1 при всех приписываниях, согласных с правилами 1–3."""
    return not variants(star(x), 0)


def T(f):
    return tex(f)


if __name__ == "__main__":
    x, y = V("x"), V("y")
    # с. 194: (∀a)(∃b)x ⊢ (∃b)(∀a)x — не тавтология; (∀a)x(∃a)y ⊢ (∃a)(xy) — тавтология
    f1 = (ALL("a", EX("b", x)), EX("b", ALL("a", x)))
    f2 = (C(ALL("a", x), EX("a", y)), EX("a", C(x, y)))
    for f in (f1, f2):
        print(T(star(f[0])), "⊢", T(star(f[1])), taut(*f))
