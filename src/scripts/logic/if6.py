"""Системы условных высказываний гл. 6 «Комплексной логики» (с. 82–97): запись, схемы, проверка выводов, модели.

Узлы формул — как в ifq.py: ('v', x); ('neg', F); ('conj', (…)); ('wdis', (…)); ('imp', F, G) — x ⊃ y;
('if', F, G) — x → y; ('ifn', F, G) — x ⌝→ y; ('ifq', F, G) — x? → y.

Строка вывода: (посылка, заключение, основание); посылка None — формула «⊢ x» (S⁵, гл. 4, § 3).
Основания: 'A1'…'A9' (§ 6–7), 'B1'…'B3' (A1–A3 § 9), 'N1'…'N7' (Aⁿ1–Aⁿ7 § 5), 'Ss' — шаг общей теории дедукции
(сильная тавтология, если условные высказывания считать элементарными), 'S5' — ⊢ x, где x — тавтология в том же
смысле (MT4 § 3 гл. 4), ('R1', i, j), ('R2', i, j), ('R3', i, j) — правила с. 17; ('Rd1', i, j) — Rᵈ1 (с. 67):
из x ⊢ y (строка i) и ⊢ x (строка j) — ⊢ y; ('MT6', i, j) — MT6 § 3 гл. 4 (с. 69): из ⊢ x и ⊢ y — ⊢ xy;
('Rif', i) — R1 § 8 (§ 9): из x ⊢ y — ⊢ (x → y).
"""
from itertools import product

COND = ("if", "ifn", "ifq")


def V(n): return ("v", n)
def N(f): return ("neg", f)
def IMP(a, b): return ("imp", a, b)
def IF(a, b): return ("if", a, b)
def IFN(a, b): return ("ifn", a, b)
def IFQ(a, b): return ("ifq", a, b)


def C(*a):
    return ("conj", tuple(a))


def W(*a):
    return ("wdis", tuple(a))


x, y, z, v, u, w = (V(c) for c in "xyzvuw")


# ---------------------------------------------------------------- запись
def tex(f, ctx="top"):
    k = f[0]
    if k == "v":
        return f[1]
    if k == "neg":
        g = f[1]
        if g[0] in ("v", "neg"):
            return "\\sim " + tex(g, "neg")
        if g[0] in COND or g[0] == "imp":
            return "\\sim" + tex(g)
        return f"\\sim({tex(g)})"
    if k == "conj":
        out = ""
        for a in f[1]:
            s = f"({tex(a)})" if a[0] in ("conj", "wdis") else tex(a, "conj")
            out += s
        return out
    if k == "wdis":
        out = " \\vee ".join(f"({tex(a)})" if a[0] == "wdis" else tex(a) for a in f[1])
        return f"({out})" if ctx in ("conj", "neg") else out
    if k == "imp":
        return f"({tex(f[1])} \\supset {tex(f[2])})"
    if k == "if":
        return f"({tex(f[1])} \\rightarrow {tex(f[2])})"
    if k == "ifn":
        return f"({tex(f[1])} \\urcorner\\!\\rightarrow {tex(f[2])})"
    if k == "ifq":
        return f"({tex(f[1])}? \\rightarrow {tex(f[2])})"
    raise ValueError(k)


def ftex(a, b):
    return f"\\vdash {tex(b)}" if a is None else f"{tex(a)} \\vdash {tex(b)}"


def size(f):
    return len(tex(f).replace("\\rightarrow", ">").replace("\\sim", "~").replace("\\vee", "v").replace(" ", ""))


# ---------------------------------------------------------------- структура
def has(f, kinds=COND):
    k = f[0]
    if k in kinds:
        return True
    if k == "v":
        return False
    if k == "neg":
        return has(f[1], kinds)
    if k in COND or k == "imp":
        return has(f[1], kinds) or has(f[2], kinds)
    return any(has(a, kinds) for a in f[1])


def atoms(f):
    k = f[0]
    if k == "v":
        return {f[1]}
    if k == "neg":
        return atoms(f[1])
    if k in COND or k == "imp":
        return atoms(f[1]) | atoms(f[2])
    return set().union(*(atoms(a) for a in f[1]))


def subs(f):
    """Все подформулы (с повторами), сверху вниз."""
    yield f
    k = f[0]
    if k == "neg":
        yield from subs(f[1])
    elif k in COND or k == "imp":
        yield from subs(f[1])
        yield from subs(f[2])
    elif k in ("conj", "wdis"):
        for a in f[1]:
            yield from subs(a)


def conds(f):
    """Условные высказывания (→, ⌝→, ?→) в f, без повторов, в порядке появления."""
    out = []
    for g in subs(f):
        if g[0] in COND and g not in out:
            out.append(g)
    return out


def subst(f, m):
    """Одновременная замена букв по словарю m (буква → формула)."""
    k = f[0]
    if k == "v":
        return m.get(f[1], f)
    if k == "neg":
        return N(subst(f[1], m))
    if k in COND or k == "imp":
        return (k, subst(f[1], m), subst(f[2], m))
    return (k, tuple(subst(a, m) for a in f[1]))


def match(p, f, m):
    """Сопоставление образца p (буквы — метапеременные) с формулой f; m дополняется. True/False."""
    if p[0] == "v":
        if p[1] in m:
            return m[p[1]] == f
        m[p[1]] = f
        return True
    if p[0] != f[0]:
        return False
    if p[0] == "neg":
        return match(p[1], f[1], m)
    if p[0] in COND or p[0] == "imp":
        return match(p[1], f[1], m) and match(p[2], f[2], m)
    if len(p[1]) != len(f[1]):
        return False
    return all(match(a, b, m) for a, b in zip(p[1], f[1]))


# ---------------------------------------------------------------- аксиомные схемы
SCH = {
    # § 6, с. 90
    "A1": (C(IF(x, y), x), y),
    "A2": (IF(x, y), IF(N(y), N(x))),
    "A3": (C(IF(x, y), IF(y, z)), IF(x, z)),
    "A4": (IF(x, C(y, z)), C(IF(x, y), IF(x, z))),
    "A5": (IF(C(x, y), z), IF(x, IF(y, z))),
    "A6": (IF(x, IF(y, z)), IF(C(x, y), z)),
    "A7": (C(IF(x, y), IF(z, v)), IF(C(x, z), C(y, v))),
    "A8": (W(IF(x, y), IF(z, v)), IF(C(x, z), W(y, v))),
    # § 7, с. 91
    "A9": (IF(x, y), IF(C(x, z), y)),
    # § 9, с. 93: A1–A3 системы S⁵*_if
    "B1": (C(IF(x, y), x), y),
    "B2": (C(IF(x, y), N(y)), N(x)),
    "B3": (None, IF(IF(C(x, y), z), IF(x, IF(y, z)))),
    # теоремные схемы § 6, с. 91 (доказаны в книге; используются как основания)
    "T1": (C(IF(x, y), IF(C(y, z), v)), IF(C(x, z), v)),
    "T4": (C(IF(x, y), N(y)), N(x)),
    "T6": (C(IF(C(x, y), z), x), IF(y, z)),
    "T7": (IF(W(x, y), z), C(IF(x, z), IF(y, z))),
    "T8": (C(IF(x, z), IF(y, z)), IF(W(x, y), z)),
    "T11": (C(IF(x, y), IF(v, z)), IF(W(x, v), W(y, z))),
    # § 5, с. 89
    "N1": (IF(x, y), C(N(IFN(x, y)), N(IFQ(x, y)))),
    "N2": (C(N(IFN(x, y)), N(IFQ(x, y))), IF(x, y)),
    "N3": (IFN(x, y), C(N(IF(x, y)), N(IFQ(x, y)))),
    "N4": (C(N(IF(x, y)), N(IFQ(x, y))), IFN(x, y)),
    "N5": (IFQ(x, y), C(N(IF(x, y)), N(IFN(x, y)))),
    "N6": (C(N(IF(x, y)), N(IFN(x, y))), IFQ(x, y)),
    "N7": (N(IF(x, y)), IFN(x, y)),
}
SYSTEMS = {
    "s": ["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8"],
    "w": ["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9"],
    "5": ["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8"],
    "sT": ["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "T1", "T4", "T6", "T7", "T8", "T11"],
    "5s": ["B1", "B2", "B3"],
    "n": ["N1", "N2", "N3", "N4", "N5", "N6"],
    "n7": ["N1", "N2", "N3", "N4", "N5", "N6", "N7"],
}
LABEL = {f"A{i}": f"A{i}" for i in range(1, 10)}
LABEL.update({"B1": "A1", "B2": "A2", "B3": "A3"})
LABEL.update({f"N{i}": f"$A^n{i}$" for i in range(1, 8)})
LABEL.update({t: t for t in ("T1", "T4", "T6", "T7", "T8", "T11")})


def instance(name, a, b):
    """Подстановка: является ли a ⊢ b (a = None — ⊢ b) примером схемы name; возвращает замену или None."""
    pa, pb = SCH[name]
    m = {}
    if (pa is None) != (a is None):
        return None
    if pa is not None and not match(pa, a, m):
        return None
    if not match(pb, b, m):
        return None
    return m


def inst(name, **m):
    pa, pb = SCH[name]
    return (None if pa is None else subst(pa, m), subst(pb, m))


# ---------------------------------------------------------------- шаги общей теории дедукции
def opaque(f, tab):
    k = f[0]
    if k in COND:
        tab.setdefault(f, f"c{len(tab)}")
        return V(tab[f])
    if k == "v":
        return f
    if k == "neg":
        return N(opaque(f[1], tab))
    if k == "imp":
        return IMP(opaque(f[1], tab), opaque(f[2], tab))
    return (k, tuple(opaque(a, tab) for a in f[1]))


def pval(f, e):
    k = f[0]
    if k == "v":
        return e[f[1]]
    if k == "neg":
        return 1 - pval(f[1], e)
    if k == "imp":
        return int(not pval(f[1], e) or pval(f[2], e))
    if k in COND:
        raise ValueError("условное высказывание")
    vs = [pval(a, e) for a in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs))


def envs(names):
    names = sorted(names)
    for vs in product((0, 1), repeat=len(names)):
        yield dict(zip(names, vs))


def taut_imp(a, b):
    return all(not pval(a, e) or pval(b, e) for e in envs(atoms(a) | atoms(b)))


def strong_p(a, b):
    return atoms(b) <= atoms(a) and taut_imp(a, b)


def s_step(a, b):
    """a ⊢ b — теорема Sˢ при условных высказываниях как элементарных (MT5 § 2 гл. 2 и схемы)."""
    tab = {}
    A, B = opaque(a, tab), opaque(b, tab)
    return strong_p(A, B)


def s_counter(a, b):
    tab = {}
    A, B = opaque(a, tab), opaque(b, tab)
    for e in envs(atoms(A) | atoms(B)):
        if pval(A, e) and not pval(B, e):
            return e, {v_: k for k, v_ in tab.items()}
    return None


def s5_taut(b):
    tab = {}
    B = opaque(b, tab)
    return all(pval(B, e) for e in envs(atoms(B)))


def replaceable(z, v_, a, b):
    """v получается из z заменой некоторых (не обязательно всех) вхождений a на b (R3, с. 17)."""
    if z == v_:
        return True
    if z == a and v_ == b:
        return True
    if z[0] != v_[0] or z[0] == "v":
        return False
    if z[0] == "neg":
        return replaceable(z[1], v_[1], a, b)
    if z[0] in COND or z[0] == "imp":
        return replaceable(z[1], v_[1], a, b) and replaceable(z[2], v_[2], a, b)
    return len(z[1]) == len(v_[1]) and all(replaceable(p, q, a, b) for p, q in zip(z[1], v_[1]))


def check(lines, sysk="s"):
    """Проверка вывода; возвращает список ошибок «шаг N: …» (пустой — вывод верен)."""
    errs = []
    allowed = SYSTEMS[sysk]
    five = sysk in ("5", "5s", "n", "n7")
    for n, (a, b, wh) in enumerate(lines, 1):
        if isinstance(wh, str):
            if wh == "Ss":
                ok = a is not None and s_step(a, b)
            elif wh == "S5":
                ok = five and a is None and s5_taut(b)
            elif wh == "given":
                ok = True
            else:
                ok = wh in allowed and instance(wh, a, b) is not None
            if not ok:
                errs.append(f"шаг {n}: не {wh}")
            continue
        r, refs = wh[0], wh[1:]
        if not all(1 <= i < n for i in refs):
            errs.append(f"шаг {n}: ссылка вперёд")
            continue
        L = [lines[i - 1] for i in refs]
        if r == "R1":
            (a1, b1, _), (a2, b2, _) = L
            ok = a is not None and a1 == a and a2 == b1 and b2 == b
        elif r == "R2":
            (a1, b1, _), (a2, b2, _) = L
            ok = a is not None and a1 == a2 == a and b == C(b1, b2)
        elif r == "R3":
            (a1, b1, _), (a2, b2, _) = L
            ok = (a is not None and a1 is not None and a2 is not None and a1 == b2 and b1 == a2
                  and replaceable(a, b, a1, b1) and a != b)
        elif r == "Rd1":
            (a1, b1, _), (a2, b2, _) = L
            ok = five and a is None and a1 is not None and a2 is None and b2 == a1 and b == b1
        elif r == "MT6":
            (a1, b1, _), (a2, b2, _) = L
            ok = five and a is None and a1 is None and a2 is None and b == C(b1, b2)
        elif r == "Rif":
            (a1, b1, _), = L
            ok = sysk in ("5", "5s") and a is None and a1 is not None and b == IF(a1, b1)
        elif r == "MT3":
            (a1, b1, _), (a2, b2, _) = L
            ok = five and a is None and a1 is None and a2 is None and b1 == IF(b2, b)
        else:
            ok = False
        if not ok:
            errs.append(f"шаг {n}: неверно применено {r}")
    return errs


def why_text(wh, sysk="s"):
    if isinstance(wh, str):
        return {"Ss": "$S^s$", "S5": "$S^5$", "given": "дано"}.get(wh, LABEL.get(wh, wh))
    r = wh[0]
    refs = ", ".join(str(i) for i in wh[1:])
    name = {"R1": "R1", "R2": "R2", "R3": "R3", "Rd1": "$R^d1$", "MT6": "MT6 гл. 4",
            "Rif": "R1 § 9" if sysk == "5s" else "R1 § 8"}[r]
    return f"{name}: {refs}"


def show(lines, sysk="s"):
    return "\n".join(f"{n}. ${ftex(a, b)}$ [{why_text(wh, sysk)}]" for n, (a, b, wh) in enumerate(lines, 1))


def prune(lines):
    need, stack = set(), [len(lines)]
    while stack:
        n = stack.pop()
        if n in need:
            continue
        need.add(n)
        wh = lines[n - 1][2]
        if not isinstance(wh, str):
            stack += list(wh[1:])
    keep = sorted(need)
    new = {old: i for i, old in enumerate(keep, 1)}
    out = []
    for o in keep:
        a, b, wh = lines[o - 1]
        out.append((a, b, wh if isinstance(wh, str) else (wh[0], *(new[i] for i in wh[1:]))))
    return out


# ---------------------------------------------------------------- модель интерпретации § 4 (с. 86–88)
def flat(f):
    """Условные высказывания в f не содержат условных высказываний и ⊃ внутри."""
    return all(not has(g[1], COND + ("imp",)) and not has(g[2], COND + ("imp",)) for g in conds(f)) and \
        all(g[0] == "if" for g in conds(f))


def cv(f, e, c):
    """Значение формулы при значениях букв e и значениях условных высказываний c."""
    k = f[0]
    if k == "v":
        return e[f[1]]
    if k == "if":
        return c[f]
    if k == "neg":
        return 1 - cv(f[1], e, c)
    if k == "imp":
        return int(not cv(f[1], e, c) or cv(f[2], e, c))
    vs = [cv(a, e, c) for a in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs))


def facts(a):
    """Факты посылки: члены конъюнкции верхнего уровня без оператора условности."""
    if a is None:
        return []
    parts = a[1] if a[0] == "conj" else (a,)
    return [p for p in parts if not has(p)]


def entails(prem, concl, names):
    for e in envs(names):
        if all(pval(p, e) for p in prem) and not pval(concl, e):
            return e
    return None


def forced(g, laws, names, fs=(), mode="A"):
    """Вынуждает ли антецедент g консеквент при законах laws (пп. 5–8). Режим A — факты не учитываются;
    режим C — учитываются факты fs, но консеквент, следующий из законов и фактов без антецедента, не вынужден."""
    p, q = g[1], g[2]
    if mode == "A":
        return entails(list(laws) + [p], q, names) is None
    base = list(laws) + list(fs)
    return entails(base + [p], q, names) is None and entails(base, q, names) is not None


def situations(a, b, mode="A"):
    """Допустимые приписывания: (e, c). Пп. 1–2: при c = 1 нет x = 1, y = 0; пп. 5–8: c = 0 только если не вынуждено."""
    fs_all = [f for f in (a, b) if f is not None]
    cs = []
    for f in fs_all:
        for g in conds(f):
            if g not in cs:
                cs.append(g)
    names = set().union(*(atoms(f) for f in fs_all))
    fs = facts(a)
    out = []
    for vals in product((0, 1), repeat=len(cs)):
        c = dict(zip(cs, vals))
        laws = [IMP(g[1], g[2]) for g in cs if c[g]]
        if any(not c[g] and forced(g, laws, names, fs, mode) for g in cs):
            continue
        for e in envs(names):
            if all(not c[g] or pval(IMP(g[1], g[2]), e) for g in cs):
                out.append((e, c))
    return out, names


def sem_taut(a, b, mode="A"):
    """Тавтология ли a ⊢ b (a = None — ⊢ b) в модели § 4; возвращает (True, None) или (False, (e, c))."""
    sits, _ = situations(a, b, mode)
    for e, c in sits:
        if (a is None or cv(a, e, c)) and not cv(b, e, c):
            return False, (e, c)
    return True, None


def sem_robust(a, b):
    """Вердикт, одинаковый в обоих режимах, или None."""
    r1, w1 = sem_taut(a, b, "A")
    r2, w2 = sem_taut(a, b, "C")
    if r1 != r2:
        return None
    if r1:
        return True, None
    sA, _ = situations(a, b, "A")
    sC, _ = situations(a, b, "C")
    keyC = {(tuple(sorted(e.items())), tuple(sorted((tex(g), vv) for g, vv in c.items()))) for e, c in sC}
    for e, c in sA:
        k = (tuple(sorted(e.items())), tuple(sorted((tex(g), vv) for g, vv in c.items())))
        if k in keyC and (a is None or cv(a, e, c)) and not cv(b, e, c):
            return False, (e, c)
    return None


def not_forced_witness(g, laws, names):
    """Значения букв, при которых законы и антецедент истинны, а консеквент ложен (п. 7–8)."""
    return entails(list(laws) + [g[1]], g[2], names)


# ---------------------------------------------------------------- три состояния (§ 4, пп. 10–12; § 5)
def pairs(f):
    out = []
    for g in subs(f):
        if g[0] in COND and (g[1], g[2]) not in out:
            out.append((g[1], g[2]))
    return out


def tval(f, st):
    k = f[0]
    if k in COND:
        return int(st[(f[1], f[2])] == k)
    if k == "neg":
        return 1 - tval(f[1], st)
    vs = [tval(a_, st) for a_ in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs))


def three_taut(a, b, classical=False):
    ps = []
    for f in (a, b):
        if f is not None:
            for p_ in pairs(f):
                if p_ not in ps:
                    ps.append(p_)
    states = ("if", "ifn") if classical else COND
    for combo in product(states, repeat=len(ps)):
        st = dict(zip(ps, combo))
        if (a is None or tval(a, st)) and not tval(b, st):
            return False, st
    return True, None


# ---------------------------------------------------------------- S⁵_if: ⊢ (x → y) при x, y без → (MT2, MT5 § 8)
def s5if_prov(a, b):
    assert not has(a) and not has(b)
    return taut_imp(a, b)


def to_imp(f):
    """MT7 § 8: замена всех вхождений → на ⊃."""
    k = f[0]
    if k == "v":
        return f
    if k == "neg":
        return N(to_imp(f[1]))
    if k in COND or k == "imp":
        return ("imp" if k == "if" else k, to_imp(f[1]), to_imp(f[2]))
    return (k, tuple(to_imp(a) for a in f[1]))


def env_tex(e):
    return ", ".join(f"${k} = {vv}$" for k, vv in sorted(e.items()))


if __name__ == "__main__":
    # схемы § 6 — тавтологии модели § 4 (кроме вложенных A5, A6)
    for n in ("A1", "A2", "A3", "A4", "A7", "A8"):
        a, b = SCH[n]
        print(n, sem_taut(a, b, "A")[0], sem_taut(a, b, "C")[0], s_step(a, b))
    bad = [(C(x, y), IF(x, y)), (N(IF(x, y)), C(x, N(y))), (IF(C(x, y), z), W(IF(x, z), IF(y, z))),
           (IF(x, W(y, z)), W(IF(x, y), IF(x, z))), (z, IF(x, z)), (C(IF(C(x, y), z), x), IF(y, z))]
    for a, b in bad:
        print(ftex(a, b), sem_taut(a, b, "A")[0], sem_taut(a, b, "C")[0], sem_robust(a, b) and sem_robust(a, b)[0])
    print(sem_taut(None, IF(C(x, y), x)), sem_taut(None, IF(y, W(N(x), x)), "A")[0])
    print(three_taut(N(IFN(x, y)), IF(x, y)), three_taut(N(IF(x, y)), IFN(x, y), True))
