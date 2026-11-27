"""Модель условных высказываний (гл. 6) и высказываний с кванторами (гл. 7) «Комплексной логики».

Узлы: ('v', x) — высказывание-буква; ('el', a, b) — (a ← b); ('neg', F); ('conj', (…)); ('wdis', (…)); ('dis', (…)) — «:»;
('imp', F, G) — x ⊃ y; ('if', F, G) — x → y; ('ifn', F, G) — x ⌝→ y; ('ifq', F, G) — x? → y;
('all', a, F) — (∀a)F; ('ex', a, F) — (∃a)F.
"""
from itertools import product


def V(n): return ("v", n)
def EL(a, b): return ("el", a, b)
def N(f): return ("neg", f)
def C(*a): return ("conj", tuple(a))
def W(*a): return ("wdis", tuple(a))
def D(*a): return ("dis", tuple(a))
def IMP(a, b): return ("imp", a, b)
def IF(a, b): return ("if", a, b)
def IFN(a, b): return ("ifn", a, b)
def IFQ(a, b): return ("ifq", a, b)
def ALL(a, f): return ("all", a, f)
def EX(a, f): return ("ex", a, f)


BIN = {"imp": "\\supset", "if": "\\rightarrow", "ifn": "\\urcorner\\!\\rightarrow", "ifq": "? \\rightarrow"}


def tex(f, ctx="top"):
    k = f[0]
    if k == "v":
        return f[1]
    if k == "el":
        return f"({f[1]} \\leftarrow {f[2]})"
    if k == "neg":
        g = f[1]
        return f"\\sim {tex(g)}" if g[0] in ("v", "el", "neg", "all", "ex") else f"\\sim({tex(g, 'neg')})"
    if k == "conj":
        return "".join(f"({tex(a)})" if a[0] in ("conj", "wdis", "dis") else tex(a, "conj") for a in f[1])
    if k in ("wdis", "dis"):
        sep = " \\vee " if k == "wdis" else " : "
        out = sep.join(f"({tex(a)})" if a[0] in ("wdis", "dis") else tex(a) for a in f[1])
        return f"({out})" if ctx in ("conj", "neg") else out
    if k in BIN:
        a, b = f[1], f[2]
        lt = tex(a) if a[0] in ("v", "el", "neg", "conj", "all", "ex", "wdis") + tuple(BIN) else f"({tex(a)})"
        rt = tex(b) if b[0] in ("v", "el", "neg", "conj", "all", "ex", "wdis") + tuple(BIN) else f"({tex(b)})"
        if k == "ifq":
            return f"({lt}? \\rightarrow {rt})"
        return f"({lt} {BIN[k]} {rt})"
    if k in ("all", "ex"):
        q = "\\forall" if k == "all" else "\\exists"
        g = f[2]
        inner = tex(g) if g[0] in ("el", "all", "ex", "v") else f"({tex(g)})"
        return f"({q} {f[1]}){inner}"
    raise ValueError(k)


def ftex(a, b=None):
    return f"\\vdash {tex(a)}" if b is None else f"{tex(a)} \\vdash {tex(b)}"


# ---------- пропозициональная часть ----------
def atoms(f):
    k = f[0]
    if k == "v":
        return {f[1]}
    if k == "el":
        return {f"{f[1]}←{f[2]}"}
    if k == "neg":
        return atoms(f[1])
    if k in ("all", "ex"):
        return atoms(f[2])
    if k in BIN:
        return atoms(f[1]) | atoms(f[2])
    return set().union(*(atoms(a) for a in f[1]))


def value(f, e):
    k = f[0]
    if k == "v":
        return e[f[1]]
    if k == "el":
        return e[f"{f[1]}←{f[2]}"]
    if k == "neg":
        return 1 - value(f[1], e)
    if k == "imp":
        return int(not value(f[1], e) or value(f[2], e))
    if k in ("if", "ifn", "ifq", "all", "ex"):
        raise ValueError("не пропозициональная формула")
    vs = [value(a, e) for a in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs)) if k == "wdis" else int(sum(vs) == 1)


def rows(*fs):
    names = sorted(set().union(*(atoms(f) for f in fs)))
    for v in product((0, 1), repeat=len(names)):
        yield dict(zip(names, v))


def is_taut(f):
    return all(value(f, e) for e in rows(f))


def counter(f):
    for e in rows(f):
        if not value(f, e):
            return e


def env_text(e):
    return ", ".join(f"${k.replace('←', ' \\leftarrow ')} = {v}$" if "←" not in k else f"$({k.replace('←', ' \\leftarrow ')}) = {v}$"
                     for k, v in sorted(e.items()))


def has(f, kinds):
    k = f[0]
    if k in kinds:
        return True
    if k in ("v", "el"):
        return False
    if k == "neg":
        return has(f[1], kinds)
    if k in ("all", "ex"):
        return has(f[2], kinds)
    if k in BIN:
        return has(f[1], kinds) or has(f[2], kinds)
    return any(has(a, kinds) for a in f[1])


def to_imp(f):
    """Замена всех → на ⊃ (MT7 § 8 гл. 6)."""
    k = f[0]
    if k in ("v", "el"):
        return f
    if k == "neg":
        return N(to_imp(f[1]))
    if k in BIN:
        return ("imp" if k == "if" else k, to_imp(f[1]), to_imp(f[2]))
    if k in ("all", "ex"):
        return (k, f[1], to_imp(f[2]))
    return (k, tuple(to_imp(a) for a in f[1]))


# ---------- S⁵_if: ⊢(x → y) для x, y без → (MT2, MT5 § 8 гл. 6) ----------
def s5if_provable(x, y):
    assert not has(x, BIN.keys() - {"imp"}) and not has(y, BIN.keys() - {"imp"})
    return is_taut(IMP(x, y))


# ---------- три состояния условной связи (гл. 6, § 4, пп. 10–12; § 5) ----------
def cval(f, st):
    """st: состояние пары (x, y): 'if' — истинно x→y, 'ifn' — x⌝→y, 'ifq' — x?→y (ровно одно)."""
    k = f[0]
    if k in ("if", "ifn", "ifq"):
        return int(st == k)
    if k == "neg":
        return 1 - cval(f[1], st)
    vs = [cval(a, st) for a in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs))


def ctaut(a, b=None, states=("if", "ifn", "ifq")):
    if b is None:
        return all(cval(a, s) for s in states)
    return all(not cval(a, s) or cval(b, s) for s in states)


# ---------- кванторы (гл. 7, § 1) ----------
def terms(f):
    k = f[0]
    if k == "el":
        return {f[1], f[2]}
    if k == "v":
        return set()
    if k == "neg":
        return terms(f[1])
    if k in ("all", "ex"):
        return {f[1]} | terms(f[2])
    if k in BIN:
        return terms(f[1]) | terms(f[2])
    return set().union(*(terms(a) for a in f[1]))


def groups(f):
    """Термины, для которых в f есть кванторная группа."""
    k = f[0]
    if k in ("el", "v"):
        return set()
    if k == "neg":
        return groups(f[1])
    if k in ("all", "ex"):
        return {f[1]} | groups(f[2])
    if k in BIN:
        return groups(f[1]) | groups(f[2])
    return set().union(*(groups(a) for a in f[1]))


def free_d4(a, f):
    """D4: a свободен в f, если входит в f, а (∀a), (∃a) в f не входят."""
    return a in terms(f) and a not in groups(f)


def occurrences(f, bound=frozenset()):
    """Список (термин, свободно ли вхождение) по D5 — вхождения в элементарные высказывания."""
    k = f[0]
    if k == "el":
        return [(f[1], f[1] not in bound), (f[2], f[2] not in bound)]
    if k == "v":
        return []
    if k == "neg":
        return occurrences(f[1], bound)
    if k in ("all", "ex"):
        return occurrences(f[2], bound | {f[1]})
    if k in BIN:
        return occurrences(f[1], bound) + occurrences(f[2], bound)
    return [o for a in f[1] for o in occurrences(a, bound)]


def free_occ(a, f):
    return any(t == a and fr for t, fr in occurrences(f))


def degenerate(f):
    """D6 для формулы вида (Ka)x: группа вырождена, если a не входит свободно в x."""
    assert f[0] in ("all", "ex")
    return not free_occ(f[1], f[2])


def qfree(f):
    """D7: бескванторная форма — исключение всех кванторных групп."""
    k = f[0]
    if k in ("el", "v"):
        return f
    if k == "neg":
        return N(qfree(f[1]))
    if k in ("all", "ex"):
        return qfree(f[2])
    if k in BIN:
        return (k, qfree(f[1]), qfree(f[2]))
    return (k, tuple(qfree(a) for a in f[1]))


def strong(a, b):
    return all(not value(a, e) or value(b, e) for e in rows(a, b)) and atoms(b) <= atoms(a)


if __name__ == "__main__":
    x, y = V("x"), V("y")
    A = [(IF(x, y), C(N(IFN(x, y)), N(IFQ(x, y)))), (C(N(IFN(x, y)), N(IFQ(x, y))), IF(x, y)),
         (IFN(x, y), C(N(IF(x, y)), N(IFQ(x, y)))), (C(N(IF(x, y)), N(IFQ(x, y))), IFN(x, y)),
         (IFQ(x, y), C(N(IF(x, y)), N(IFN(x, y)))), (C(N(IF(x, y)), N(IFN(x, y))), IFQ(x, y))]
    print("A^n1–6:", [ctaut(a, b) for a, b in A], "MT3:", ctaut(N(IFN(x, y)), IF(x, y)), ctaut(N(IF(x, y)), IFN(x, y)))
    print("A^n7 classical: ~(x→y) ⊢ x⌝→y:", ctaut(N(IF(x, y)), IFN(x, y), ("if", "ifn")))
    f = C(ALL("a", EL("a", "b")), EL("a", "c"))
    print(tex(f), free_d4("a", f), occurrences(f), degenerate(ALL("a", EL("b", "c"))), tex(qfree(f)))
    print(s5if_provable(C(x, y), x), s5if_provable(x, C(x, y)), tex(IF(C(x, y), W(x, y))))


# ---------- гл. 7, § 7: интерпретационная форма (косвенная интерпретация) ----------
def interp(f, n, env=None):
    """Интерпретационная форма: (∀b)z → z(1b)·…·z(nb), (∃b)z → z(1b)∨…∨z(nb); n — словарь числа отмеченных терминов."""
    env = env or {}
    k = f[0]
    if k == "el":
        return V(f"{env.get(f[1], f[1])}←{env.get(f[2], f[2])}")
    if k == "v":
        return f
    if k == "neg":
        return N(interp(f[1], n, env))
    if k in ("all", "ex"):
        a = f[1]
        parts = [interp(f[2], n, {**env, a: f"{i}{a}"}) for i in range(1, n.get(a, 2) + 1)]
        if len(parts) == 1:
            return parts[0]
        return C(*parts) if k == "all" else W(*parts)
    if k == "imp":
        return IMP(interp(f[1], n, env), interp(f[2], n, env))
    return (k, tuple(interp(a, n, env) for a in f[1]))


def bound_terms(f, acc=None):
    acc = set() if acc is None else acc
    k = f[0]
    if k in ("all", "ex"):
        acc.add(f[1])
        bound_terms(f[2], acc)
    elif k == "neg":
        bound_terms(f[1], acc)
    elif k in ("conj", "wdis", "dis"):
        for a in f[1]:
            bound_terms(a, acc)
    elif k == "imp":
        bound_terms(f[1], acc)
        bound_terms(f[2], acc)
    return acc


def qtaut(x, y, nmax=3, restrict=True):
    """Тавтология ли x ⊢ y при любом числе (1..nmax) отмеченных терминов для каждого связанного термина;
    restrict — ограничение § 9 гл. 5 (элементарные высказывания бескванторной формы заключения входят в посылку)."""
    import itertools
    ts = sorted(bound_terms(x) | bound_terms(y))
    for combo in itertools.product(range(1, nmax + 1), repeat=len(ts)):
        n = dict(zip(ts, combo))
        if not is_taut(IMP(interp(x, n), interp(y, n))):
            return False
    if restrict and not atoms(qfree(y)) <= atoms(qfree(x)):
        return False
    return True


def itex(f):
    """tex для интерпретационной формы: «1a←b» → (1a \\leftarrow b)."""
    k = f[0]
    if k == "v" and "←" in f[1]:
        s, p = f[1].split("←")
        return f"({s} \\leftarrow {p})"
    if k == "neg":
        return "\\sim " + itex(f[1])
    if k == "conj":
        return "".join(f"({itex(a)})" if a[0] == "wdis" else itex(a) for a in f[1])
    if k == "wdis":
        return " \\vee ".join(itex(a) for a in f[1])
    return tex(f)
