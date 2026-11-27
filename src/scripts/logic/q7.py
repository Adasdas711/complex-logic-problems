"""Модель теории кванторов гл. 7 «Комплексной логики» для генератора hard07.py.

Узлы — как в ifq.py: ('el', a, b) — (a ← b); ('v', x) — буква-высказывание; ('neg', F); ('conj', (…)); ('wdis', (…));
('dis', (…)) — «:»; ('imp', F, G) — ⊃; ('all', a, F); ('ex', a, F); неклассические группы (§ 12):
('nall', a, F) — (⌝∀a)F, ('nex', a, F) — (⌝∃a)F, ('qall', a, F) — (?∀a)F, ('qex', a, F) — (?∃a)F.

Здесь: запись (tex), свободные и связанные вхождения (D4–D6 § 1), бескванторные формы (D7 § 1, D1 § 13), аксиомные
и теоремные схемы S^s_cq (§ 2, § 6) и S^s_nq (§ 12) как образцы с метабуквами, проверка выводов (схемы, R1, R2,
ссылка на S^s, R1 и R2 системы S^s), интерпретационная форма § 7 и поиск опровергающих значений.
"""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ifq  # noqa: E402

QK = ("all", "ex", "nall", "nex", "qall", "qex")


def V(n): return ("v", n)
def EL(a, b): return ("el", a, b)
def N(f): return ("neg", f)
def C(*a): return ("conj", tuple(a))
def W(*a): return ("wdis", tuple(a))
def D(*a): return ("dis", tuple(a))
def IMP(a, b): return ("imp", a, b)
def ALL(a, f): return ("all", a, f)
def EX(a, f): return ("ex", a, f)
def NALL(a, f): return ("nall", a, f)
def NEX(a, f): return ("nex", a, f)
def QALL(a, f): return ("qall", a, f)
def QEX(a, f): return ("qex", a, f)


QTEX = {"all": "\\forall ", "ex": "\\exists ", "nall": "\\urcorner\\forall ", "nex": "\\urcorner\\exists ",
        "qall": "?\\forall ", "qex": "?\\exists "}
PRIM = ("v", "el", "neg") + QK


def term_tex(t):
    """Термин: 'a', отмеченный '1a' (§ 7), с индексом 'a1' → a^1, отмеченный с индексом '2a1' → 2a^1."""
    import re
    m = re.match(r"^(\d*)([a-z])(\d+)$", t)
    if m:
        return f"{m.group(1)}{m.group(2)}^{m.group(3)}"
    return t


def tex(f):
    k = f[0]
    if k == "v":
        return f[1]
    if k == "el":
        return f"({term_tex(f[1])} \\leftarrow {term_tex(f[2])})"
    if k == "neg":
        g = f[1]
        return f"\\sim {tex(g)}" if g[0] in PRIM else f"\\sim({tex(g)})"
    if k == "conj":
        return "".join(f"({tex(a)})" if a[0] in ("conj", "wdis", "dis", "imp") else tex(a) for a in f[1])
    if k in ("wdis", "dis"):
        sep = " \\vee " if k == "wdis" else " : "
        return sep.join(f"({tex(a)})" if a[0] in ("wdis", "dis", "imp") else tex(a) for a in f[1])
    if k == "imp":
        a, b = f[1], f[2]
        lt = tex(a) if a[0] in PRIM + ("conj",) else f"({tex(a)})"
        rt = tex(b) if b[0] in PRIM + ("conj",) else f"({tex(b)})"
        return f"{lt} \\supset {rt}"
    if k in QK:
        g = f[2]
        inner = tex(g) if g[0] in PRIM else f"({tex(g)})"
        return f"({QTEX[k]}{term_tex(f[1])}){inner}"
    raise ValueError(k)


def ftex(a, b=None):
    return f"\\vdash {tex(a)}" if b is None else f"{tex(a)} \\vdash {tex(b)}"


def size(f):
    return len(tex(f).replace("\\leftarrow", "<").replace("\\forall", "A").replace("\\exists", "E").replace("\\sim", "~")
               .replace(" ", ""))


# ---------------------------------------------------------------- вхождения (D4–D6 § 1)
def occurrences(f, bound=frozenset()):
    """Вхождения терминов в элементарные высказывания: список (термин, свободно ли), D5."""
    k = f[0]
    if k == "el":
        return [(f[1], f[1] not in bound), (f[2], f[2] not in bound)]
    if k == "v":
        return []
    if k == "neg":
        return occurrences(f[1], bound)
    if k in QK:
        return occurrences(f[2], bound | {f[1]})
    if k == "imp":
        return occurrences(f[1], bound) + occurrences(f[2], bound)
    return [o for a in f[1] for o in occurrences(a, bound)]


def free_in(a, f):
    return any(t == a and fr for t, fr in occurrences(f))


def free_terms(f):
    return {t for t, fr in occurrences(f) if fr}


def terms(f):
    k = f[0]
    if k == "el":
        return {f[1], f[2]}
    if k == "v":
        return set()
    if k == "neg":
        return terms(f[1])
    if k in QK:
        return {f[1]} | terms(f[2])
    if k == "imp":
        return terms(f[1]) | terms(f[2])
    return set().union(*(terms(a) for a in f[1]))


def groups(f, acc=None):
    """Все вхождения кванторных групп: список (вид, термин, тело)."""
    acc = [] if acc is None else acc
    k = f[0]
    if k in QK:
        acc.append((k, f[1], f[2]))
        groups(f[2], acc)
    elif k == "neg":
        groups(f[1], acc)
    elif k == "imp":
        groups(f[1], acc)
        groups(f[2], acc)
    elif k in ("conj", "wdis", "dis"):
        for a in f[1]:
            groups(a, acc)
    return acc


def degenerate(k_a_body):
    _, a, body = k_a_body
    return not free_in(a, body)


def qfree(f):
    """D7 § 1: исключение всех кванторных групп (классические группы)."""
    k = f[0]
    if k in ("el", "v"):
        return f
    if k == "neg":
        return N(qfree(f[1]))
    if k in QK:
        return qfree(f[2])
    if k == "imp":
        return IMP(qfree(f[1]), qfree(f[2]))
    if k in ("conj", "wdis", "dis"):
        return (k, tuple(qfree(a) for a in f[1]))
    raise ValueError(k)


def qf13(f):
    """Бескванторная форма D1 § 13 (с. 123) для S^s_nq."""
    k = f[0]
    if k == "qall":
        return qf13(C(N(ALL(f[1], f[2])), N(NALL(f[1], f[2]))))
    if k == "qex":
        return qf13(C(N(EX(f[1], f[2])), N(NEX(f[1], f[2]))))
    if k == "nall":
        return N(qf13(ALL(f[1], f[2])))
    if k == "nex":
        return N(qf13(EX(f[1], f[2])))
    if k in ("all", "ex"):
        return qf13(f[2])
    if k == "neg":
        return N(qf13(f[1]))
    if k in ("v", "el"):
        return f
    if k == "imp":
        return IMP(qf13(f[1]), qf13(f[2]))
    return (k, tuple(qf13(g) for g in f[1]))


def repl18(f):
    """Замена § 18 (с. 127): (⌝∀b)z → (∃b)∼z, (?∀b)z → ∼(∀b)z∼(∃b)∼z, (⌝∃b)z → (∀b)∼z, (?∃b)z → ∼(∃b)z∼(∀b)∼z."""
    k = f[0]
    if k in ("v", "el"):
        return f
    if k == "neg":
        return N(repl18(f[1]))
    if k in ("all", "ex"):
        return (k, f[1], repl18(f[2]))
    if k == "nall":
        return EX(f[1], N(repl18(f[2])))
    if k == "nex":
        return ALL(f[1], N(repl18(f[2])))
    if k == "qall":
        z = repl18(f[2])
        return C(N(ALL(f[1], z)), N(EX(f[1], N(z))))
    if k == "qex":
        z = repl18(f[2])
        return C(N(EX(f[1], z)), N(ALL(f[1], N(z))))
    if k == "imp":
        return IMP(repl18(f[1]), repl18(f[2]))
    return (k, tuple(repl18(g) for g in f[1]))


# ---------------------------------------------------------------- пропозициональная часть
def patoms(f):
    """«Буквы» для ссылки на S^s: элементарные высказывания и высказывания с кванторами."""
    k = f[0]
    if k in ("v", "el") + QK:
        return {f}
    if k == "neg":
        return patoms(f[1])
    if k == "imp":
        return patoms(f[1]) | patoms(f[2])
    return set().union(*(patoms(a) for a in f[1]))


def pval(f, e):
    k = f[0]
    if k in ("v", "el") + QK:
        return e[f]
    if k == "neg":
        return 1 - pval(f[1], e)
    if k == "imp":
        return int(not pval(f[1], e) or pval(f[2], e))
    vs = [pval(a, e) for a in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs)) if k == "wdis" else int(sum(vs) == 1)


def penvs(*fs):
    names = sorted(set().union(*(patoms(f) for f in fs)), key=repr)
    for vs in itertools.product((0, 1), repeat=len(names)):
        yield dict(zip(names, vs))


def ptaut(p, q):
    return all(not pval(p, e) or pval(q, e) for e in penvs(p, q))


def ss_theorem(p, q):
    """Формула доказуема в S^s, если считать буквами элементарные высказывания и высказывания с кванторами:
    сильная тавтология (тавтология, в заключение не входят «буквы», отсутствующие в посылке)."""
    return patoms(q) <= patoms(p) and ptaut(p, q)


def is_contr(f):
    return not any(pval(f, e) for e in penvs(f))


def is_taut1(f):
    return all(pval(f, e) for e in penvs(f))


def strong_q(p, q):
    """Бескванторная форма (классическая) доказуема в S^s."""
    return ss_theorem(qfree(p), qfree(q))


# ---------------------------------------------------------------- образцы схем
x_, y_ = V("x"), V("y")


def match(pat, f, sb):
    k = pat[0]
    if k == "v":
        if pat[1] in sb:
            return sb[pat[1]] == f
        sb[pat[1]] = f
        return True
    if k != f[0]:
        return False
    if k in QK:
        t = "@" + pat[1]
        if t in sb and sb[t] != f[1]:
            return False
        sb[t] = f[1]
        return match(pat[2], f[2], sb)
    if k == "el":
        return pat == f
    if k == "neg":
        return match(pat[1], f[1], sb)
    if k == "imp":
        return match(pat[1], f[1], sb) and match(pat[2], f[2], sb)
    if len(pat[1]) != len(f[1]):
        return False
    return all(match(p, g, sb) for p, g in zip(pat[1], f[1]))


def inst_of(scheme, p, q):
    """Подстановка, при которой формула p ⊢ q — пример схемы, или None."""
    P, Qp, conds = scheme
    sb = {}
    if not (match(P, p, sb) and match(Qp, q, sb)):
        return None
    for a, xv in conds:
        if free_in(sb["@" + a], sb[xv]):
            return None
    return sb


def build_inst(scheme, sb):
    def go(t):
        k = t[0]
        if k == "v":
            return sb[t[1]]
        if k == "el":
            return t
        if k == "neg":
            return N(go(t[1]))
        if k in QK:
            return (k, sb["@" + t[1]], go(t[2]))
        if k == "imp":
            return IMP(go(t[1]), go(t[2]))
        return (k, tuple(go(a) for a in t[1]))
    return go(scheme[0]), go(scheme[1])


x, y = x_, y_
NF = [("a", "x")]
# § 2, с. 99: A5 — с условием «a не входит свободно в x»
SCQ = {
    "A1": (ALL("a", x), x, []),
    "A2": (x, EX("a", x), []),
    "A3": (C(ALL("a", x), EX("a", y)), EX("a", C(x, y)), []),
    "A4": (ALL("a", W(x, y)), W(ALL("a", x), EX("a", y)), []),
    "A5": (EX("a", x), ALL("a", x), NF),
    "A6": (ALL("a", x), N(EX("a", N(x))), []),
    "A7": (N(EX("a", N(x))), ALL("a", x), []),
}
SCQ_TEX = {"A1": "(\\forall a)x \\vdash x", "A2": "x \\vdash (\\exists a)x",
           "A3": "(\\forall a)x(\\exists a)y \\vdash (\\exists a)(xy)",
           "A4": "(\\forall a)(x \\vee y) \\vdash (\\forall a)x \\vee (\\exists a)y",
           "A5": "(\\exists a)x \\vdash (\\forall a)x", "A6": "(\\forall a)x \\vdash \\sim(\\exists a)\\sim x",
           "A7": "\\sim(\\exists a)\\sim x \\vdash (\\forall a)x"}
# § 6, с. 102–105 (номера книги)
T6 = {
    "T1": (N(ALL("a", x)), EX("a", N(x)), []), "T2": (EX("a", x), N(ALL("a", N(x))), []),
    "T3": (N(x), N(ALL("a", x)), []), "T4": (N(EX("a", x)), N(x), []),
    "T7": (N(ALL("a", x)), N(EX("a", x)), NF),
    "T8": (N(N(EX("a", N(x)))), N(ALL("a", x)), []), "T9": (N(ALL("a", x)), N(N(EX("a", N(x)))), []),
    "T14": (ALL("a", ALL("b", x)), ALL("b", ALL("a", x)), []),
    "T15": (EX("a", ALL("b", x)), ALL("b", EX("a", x)), []),
    "T16": (EX("a", EX("b", x)), EX("b", EX("a", x)), []),
    "T17": (x, ALL("a", x), NF), "T18": (EX("a", x), x, NF),
    "T19": (C(ALL("a", x), ALL("a", y)), ALL("a", C(x, y)), []),
    "T20": (ALL("a", C(x, y)), C(ALL("a", x), ALL("a", y)), []),
    "T21": (EX("a", C(x, y)), C(EX("a", x), EX("a", y)), []),
    "T22": (EX("a", W(x, y)), W(EX("a", x), EX("a", y)), []),
    "T23": (W(EX("a", x), EX("a", y)), EX("a", W(x, y)), []),
    "T24": (W(ALL("a", x), ALL("a", y)), ALL("a", W(x, y)), []),
    "T25": (W(ALL("a", x), EX("a", y)), EX("a", W(x, y)), []),
    "T26": (W(EX("a", x), ALL("a", y)), EX("a", W(x, y)), []),
    "T27": (ALL("a", x), EX("a", x), []),
    "T28": (N(EX("a", x)), N(ALL("a", x)), []),
    "T29": (ALL("a", C(x, y)), C(ALL("a", x), EX("a", y)), []),
    "T30": (ALL("a", C(x, y)), C(EX("a", x), ALL("a", y)), []),
    "T32": (ALL("a", W(x, y)), W(EX("a", x), ALL("a", y)), []),
    "T33": (EX("a", ALL("b", x)), EX("b", EX("a", x)), []),
    "T34": (ALL("a", W(x, y)), W(EX("a", x), EX("a", y)), []),
    "T35": (W(ALL("a", x), ALL("a", y)), EX("a", W(x, y)), []),
    "T36": (C(ALL("a", x), ALL("a", y)), EX("a", C(x, y)), []),
    "T37": (N(ALL("a", N(x))), EX("a", x), []),
    "T38": (ALL("a", ALL("b", x)), ALL("b", EX("a", x)), []),
    "T39": (ALL("a", ALL("b", x)), EX("b", ALL("a", x)), []),
    "T40": (ALL("a", ALL("b", x)), EX("b", EX("a", x)), []),
    "T41": (ALL("a", EX("b", x)), EX("b", EX("a", x)), []),
    "T42": (C(EX("a", x), ALL("a", y)), EX("a", C(x, y)), []),
}
T6_TEX = {k: ftex(*v[:2]) for k, v in T6.items()}
T6_BASIS = {"T1": "A6, A7", "T2": "A6, A7", "T3": "A2, T2", "T4": "A6, A7, A1", "T7": "A5, T1, T2, A6, A7",
            "T8": "A6, A7", "T9": "A6, A7", "T14": "A1, R1, T17", "T15": "A1, A2, R1, T17, R2, T18",
            "T16": "A2, R2, T18", "T17": "A2", "T18": "A1", "T19": "A1, R1, T17", "T20": "A1, R1, T17", "T21": "R2",
            "T22": "T19, T20, A6, A7", "T23": "T19, T20, A6, A7", "T24": "T21, MT2, A6, A7", "T25": "T23, A1, A2, MT4",
            "T26": "T23, A1, A2, MT4", "T27": "A1, A2", "T28": "T27, MT2", "T29": "T20, T27", "T30": "T20, T27",
            "T32": "A3", "T33": "T15, T27", "T34": "A3, MT3", "T35": "T24, T27", "T36": "T19, T27", "T37": "A6, A7",
            "T38": "A1, A2, R1, T17", "T39": "A1, R1, R2, T18", "T40": "A1, A2", "T41": "A1, T16", "T42": "A3"}

# § 12, с. 123: схемы S^s_nq вместо A6, A7 и дополнительные
NQ = {
    "A^16": (ALL("a", x), NEX("a", N(x)), []), "A^26": (NALL("a", x), EX("a", N(x)), []),
    "A^36": (QALL("a", x), QEX("a", N(x)), []), "A^17": (NEX("a", N(x)), ALL("a", x), []),
    "A^27": (EX("a", N(x)), NALL("a", x), []), "A^37": (QEX("a", N(x)), QALL("a", x), []),
    "A^18": (ALL("a", x), C(N(NALL("a", x)), N(QALL("a", x))), []),
    "A^28": (NALL("a", x), C(N(ALL("a", x)), N(QALL("a", x))), []),
    "A^38": (QALL("a", x), C(N(ALL("a", x)), N(NALL("a", x))), []),
    "A^19": (C(N(NALL("a", x)), N(QALL("a", x))), ALL("a", x), []),
    "A^29": (C(N(ALL("a", x)), N(QALL("a", x))), NALL("a", x), []),
    "A^39": (C(N(ALL("a", x)), N(NALL("a", x))), QALL("a", x), []),
    "A10": (NALL("a", C(x, y)), W(NALL("a", x), NALL("a", y)), []),
    "A11": (W(NALL("a", x), NALL("a", y)), NALL("a", C(x, y)), []),
    "A12": (W(NEX("a", x), NEX("a", y)), NEX("a", C(x, y)), []),
}
NQ_TEX = {k: ftex(*v[:2]) for k, v in NQ.items()}
# § 14, с. 124: теоремные схемы S^s_nq (⊣⊢ — две формулы)
T14 = {
    "T1": (EX("a", x), NALL("a", N(x)), []), "T1'": (NALL("a", N(x)), EX("a", x), []),
    "T2": (NEX("a", x), ALL("a", N(x)), []), "T2'": (ALL("a", N(x)), NEX("a", x), []),
    "T7": (EX("a", W(x, y)), W(EX("a", x), EX("a", y)), []),
    "T8": (W(ALL("a", x), ALL("a", y)), ALL("a", W(x, y)), []),
}
A_STAR5_TEX = "(\\exists a)x \\vdash (\\forall a)x"


def scheme_name(name):
    """Метка схемы в тексте: A^16 → A^1 6 по книге ($A^16$)."""
    if name.startswith("A^"):
        return f"$A^{name[2]}{name[3:]}$"
    return name


# ---------------------------------------------------------------- проверка выводов
# Строка вывода: (посылка, заключение, основание). Основания:
#   'A1'…'A7', 'T…', 'A^16'… — пример схемы;  ('Ss',) — формула доказуема в S^s (ссылка на систему, § 6, с. 102);
#   ('R1', k), ('R2', k) — правила S^s_cq (с. 100) из строки k;  ('tr', i, j) — R1 системы S^s (с. 17): из x ⊢ y (i) и
#   y ⊢ z (j) — x ⊢ z;  ('cj', i, j) — R2 системы S^s: из x ⊢ y (i) и x ⊢ z (j) — x ⊢ yz.
def why_text(w):
    if isinstance(w, str):
        return scheme_name(w)
    k = w[0]
    if k == "Ss":
        return "$S^s$"
    if k in ("R1", "R2"):
        return f"{k}: {w[1]}"
    if k == "tr":
        return f"R1 $S^s$: {w[1]}, {w[2]}"
    if k == "cj":
        return f"R2 $S^s$: {w[1]}, {w[2]}"
    raise ValueError(w)


def schemes_for(allowed):
    out = {}
    for k in allowed:
        if k in SCQ:
            out[k] = SCQ[k]
        elif k in T6:
            out[k] = T6[k]
        elif k in NQ:
            out[k] = NQ[k]
    return out


def check(lines, allowed):
    sch = schemes_for(allowed)
    errs = []
    for n, (p, q, w) in enumerate(lines, 1):
        if isinstance(w, str):
            if w not in sch:
                errs.append(f"шаг {n}: схема {w} не разрешена")
            elif inst_of(sch[w], p, q) is None:
                errs.append(f"шаг {n}: не пример {w}")
            continue
        k = w[0]
        if k == "Ss":
            if not ss_theorem(p, q):
                errs.append(f"шаг {n}: не теорема S^s")
            continue
        refs = w[1:]
        if any(not (1 <= r < n) for r in refs):
            errs.append(f"шаг {n}: ссылка вперёд")
            continue
        if k in ("R1", "R2"):
            a0, b0 = lines[refs[0] - 1][:2]
            qk = "all" if k == "R1" else "ex"
            if not (p[0] == q[0] == qk and p[1] == q[1] and p[2] == a0 and q[2] == b0):
                errs.append(f"шаг {n}: не {k}")
        elif k == "tr":
            (a1, b1), (a2, b2) = lines[refs[0] - 1][:2], lines[refs[1] - 1][:2]
            if not (a1 == p and b1 == a2 and b2 == q):
                errs.append(f"шаг {n}: не R1 S^s")
        elif k == "cj":
            (a1, b1), (a2, b2) = lines[refs[0] - 1][:2], lines[refs[1] - 1][:2]
            if not (a1 == p and a2 == p and q == C(b1, b2)):
                errs.append(f"шаг {n}: не R2 S^s")
        else:
            errs.append(f"шаг {n}: неизвестное основание")
    return errs


# ---------------------------------------------------------------- интерпретационная форма (D2 § 7) и значения
def interp(f, n, env=None):
    """(∀b)z → z(1b)·…·z(nb), (∃b)z → z(1b) ∨ … ∨ z(nb); выражения с отмеченными терминами — ('el', '1a', 'b')."""
    env = env or {}
    k = f[0]
    if k == "el":
        return EL(env.get(f[1], f[1]), env.get(f[2], f[2]))
    if k == "v":
        return f
    if k == "neg":
        return N(interp(f[1], n, env))
    if k in ("all", "ex"):
        a = f[1]
        if not free_in(a, f[2]):          # D2, п. 2: вырожденные группы отбрасываются
            return interp(f[2], n, env)
        parts = [interp(f[2], n, {**env, a: f"{i}{a}"}) for i in range(1, n[a] + 1)]
        if len(parts) == 1:
            return parts[0]
        return C(*parts) if k == "all" else W(*parts)
    if k == "imp":
        return IMP(interp(f[1], n, env), interp(f[2], n, env))
    return (k, tuple(interp(a, n, env) for a in f[1]))


def bound_terms(f):
    return {a for _, a, body in groups(f) if free_in(a, body)}


def restrict_ok(p, q):
    """Ограничение § 9 гл. 5: элементарные высказывания бескванторной формы заключения входят в посылку."""
    return patoms(qfree(q)) <= patoms(qfree(p))


def closures(p, q):
    """D2 § 7, п. 1: термины, входящие в x ⊢ y свободно и имеющие в ней кванторные группы, закрываются кванторами
    (каждый — квантором общности или существования). Прочие свободные термины на значение не влияют:
    при любом числе отмеченных терминов их интерпретационные формы — переименования одной формулы."""
    qs = {a for _, a, _ in groups(p) + groups(q)}
    ts = sorted((free_terms(p) | free_terms(q)) & qs)
    out = []
    for order in itertools.permutations(ts):
        for ks in itertools.product(("all", "ex"), repeat=len(ts)):
            P, Q = p, q
            for t, k in zip(order, ks):
                P, Q = (k, t, P), (k, t, Q)
            if (P, Q) not in out:
                out.append((P, Q))
    return out


def countermodel(p, q, nmax=3):
    """Первая (по сумме n) интерпретационная форма p ⊢ q со значением 0 (посылка 1, заключение 0):
    (замкнутая формула P ⊢ Q, n, форма посылки, форма заключения, значения); None, если таких нет при n ≤ nmax."""
    best = None
    for P, Q in closures(p, q):
        ts = sorted(bound_terms(P) | bound_terms(Q))
        combos = sorted(itertools.product(range(1, nmax + 1), repeat=len(ts)), key=lambda c: (sum(c), c))
        for combo in combos:
            if best is not None and sum(combo) >= sum(best[1].values()):
                break
            n = dict(zip(ts, combo))
            ip, iq = interp(P, n), interp(Q, n)
            for e in penvs(ip, iq):
                if pval(ip, e) and not pval(iq, e):
                    best = ((P, Q), n, ip, iq, e)
                    break
            if best is not None and best[1] == n:
                break
    return best


def qtaut(p, q, nmax=3, restrict=False):
    """Тавтология по D3 § 7 (проверка при n ≤ nmax); restrict — ещё и ограничение § 9 гл. 5 («с ограничением», § 8)."""
    return (not restrict or restrict_ok(p, q)) and countermodel(p, q, nmax) is None


def countermodel1(f, nmax=3, closure="all"):
    """Для ⊢ f (S^5_cq, D1–D2 § 10): свободные термины закрываются квантором общности (D1 § 10); как и в closures,
    достаточно закрыть термины, имеющие в f кванторные группы."""
    g = f
    qs = {a for _, a, _ in groups(f)}
    for t in sorted(free_terms(f) & qs):
        g = ALL(t, g)
    ts = sorted(bound_terms(g))
    combos = sorted(itertools.product(range(1, nmax + 1), repeat=len(ts)), key=lambda c: (sum(c), c))
    for combo in combos:
        n = dict(zip(ts, combo))
        ig = interp(g, n)
        for e in penvs(ig):
            if not pval(ig, e):
                return n, ig, e
    return None


def env_tex(e, only=None):
    keys = sorted(e, key=lambda t: tex(t))
    if only is not None:
        keys = [k for k in keys if k in only]
    return ", ".join(f"${tex(k)} = {e[k]}$" for k in keys)


NUMW = {1: "одном отмеченном термине", 2: "двух отмеченных терминах", 3: "трёх отмеченных терминах"}


def n_text(n):
    """«двух отмеченных терминах для $a$ ($1a$, $2a$) и одном для $b$ ($1b$)» — после «при»."""
    parts = []
    for t, k in sorted(n.items()):
        marks = ", ".join(f"${term_tex(f'{i}{t}')}$" for i in range(1, k + 1))
        parts.append((NUMW[k] if not parts else NUMW[k].split()[0]) + f" для ${term_tex(t)}$ ({marks})")
    return " и ".join(parts)


if __name__ == "__main__":
    a = "a"
    ab, ac, cd = EL("a", "b"), EL("a", "c"), EL("c", "d")
    for k, (p, q, c) in list(SCQ.items()) + list(T6.items()):
        sb = {"x": ab, "y": ac, "@a": "a", "@b": "b"}
        if k in ("T14", "T15", "T16", "T33", "T38", "T39", "T40", "T41"):
            sb["x"] = EL("a", "b")
        if c:
            sb["x"] = cd
        P, Qq = build_inst((p, q, c), sb)
        assert inst_of((p, q, c), P, Qq) is not None, k
        assert qtaut(P, Qq), (k, ftex(P, Qq))
    assert not qtaut(EX("a", ab), ALL("a", ab))
    assert not qtaut(ALL("a", W(ab, ac)), W(ALL("a", ab), ALL("a", ac)))
    assert not qtaut(ALL("a", EX("b", ab)), EX("b", ALL("a", ab)))
    print(countermodel(ALL("a", EX("b", ab)), EX("b", ALL("a", ab))))
    print(tex(C(ALL("a", ab), N(EX("a", N(W(ab, ac)))))), tex(NALL("a", ab)))
    print("ok")
