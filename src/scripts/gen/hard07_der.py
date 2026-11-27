"""Выводы в S^s_cq и S^s_nq для hard07.py: случайное построение длинных выводов (8–12 строк) по схемам и правилам,
проверка q7.check, дополнение, две ошибки в основаниях, ошибочный шаг (почти-пример схемы)."""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import q7  # noqa: E402
from q7 import ALL, C, EL, EX, N, NALL, NEX, QALL, QEX, W, free_in, ftex, tex, why_text  # noqa: E402

AX2 = ["A1", "A2", "A3", "A4", "A5", "A6", "A7"]
T6USE = ["T1", "T2", "T3", "T4", "T14", "T15", "T16", "T17", "T18", "T19", "T20", "T21", "T22", "T23", "T24", "T25",
         "T26", "T27", "T29", "T30", "T32", "T34", "T35", "T36", "T37", "T38", "T39", "T40", "T41", "T42"]
AXNQ = ["A1", "A2", "A3", "A4", "A5", "A^16", "A^26", "A^36", "A^17", "A^27", "A^37", "A^18", "A^28", "A^38", "A^19",
        "A^29", "A^39", "A10", "A11", "A12"]


def size(f):
    return q7.size(f)


def ss_moves(q):
    """Шаги по S^s (ссылка на систему): удаление и перестановка членов конъюнкции, двойное отрицание, законы
    де Моргана, перестановка членов дизъюнкции."""
    out = []
    k = q[0]
    if k == "conj" and len(q[1]) == 2:
        a, b = q[1]
        out += [a, b, C(b, a)]
    if k == "neg" and q[1][0] == "neg":
        out.append(q[1][1])
    if k == "neg" and q[1][0] == "conj" and len(q[1][1]) == 2:
        out.append(W(N(q[1][1][0]), N(q[1][1][1])))
    if k == "neg" and q[1][0] == "wdis" and len(q[1][1]) == 2:
        out.append(C(N(q[1][1][0]), N(q[1][1][1])))
    if k == "wdis" and len(q[1]) == 2:
        a, b = q[1]
        out.append(W(b, a))
        if a[0] == "neg" and b[0] == "neg":
            out.append(N(C(a[1], b[1])))
    if k == "conj" and len(q[1]) == 2 and all(t[0] == "neg" for t in q[1]):
        out.append(N(W(q[1][0][1], q[1][1][1])))
    res = []
    for r in out:
        assert q7.ss_theorem(q, r), (tex(q), tex(r))
        res.append((("Ss",), r))
    return res


def scheme_moves(q, allowed, rnd=None, terms_pool=("a",)):
    """Применение схем: все r, для которых q ⊢ r — пример разрешённой схемы (кроме A2 и T17 — их даёт add_moves)."""
    out = []
    sch = q7.schemes_for(allowed)
    for name, (P, Qp, conds) in sch.items():
        if name in ("A2", "T17"):
            continue
        sb = {}
        if not q7.match(P, q, sb):
            continue
        # все метабуквы заключения должны быть определены посылкой
        need = {t[1] for t in walk(Qp) if t[0] == "v"} | {"@" + t[1] for t in walk(Qp) if t[0] in q7.QK}
        if not need <= set(sb):
            continue
        if any(free_in(sb["@" + a], sb[xv]) for a, xv in conds):
            continue
        r = q7.build_inst((P, Qp, conds), sb)[1]
        out.append((name, r))
    return out


def walk(f):
    yield f
    k = f[0]
    if k == "neg":
        yield from walk(f[1])
    elif k in q7.QK:
        yield from walk(f[2])
    elif k == "imp":
        yield from walk(f[1])
        yield from walk(f[2])
    elif k in ("conj", "wdis", "dis"):
        for a in f[1]:
            yield from walk(a)


def add_moves(q, allowed):
    """A2: q ⊢ (∃t)q для термина t, входящего свободно в q (невырожденная группа); T17 — для t, не входящего свободно."""
    out = []
    if "A2" in allowed and size(q) <= 14:
        for t in sorted(q7.free_terms(q) & {"a"}):
            out.append(("A2", EX(t, q)))
    return out


def all_moves(q, allowed, ss=True):
    mv = scheme_moves(q, allowed) + add_moves(q, allowed)
    if ss:
        mv += ss_moves(q)
    for name, r in mv:
        if isinstance(name, str):
            assert q7.inst_of(q7.schemes_for([name])[name], q, r) is not None, (name, tex(q), tex(r))
    return mv


WEIGHT = {"A1": 1, "A2": 1, "A6": 1.5, "A7": 2, "Ss": 0.7}


def pick(opts, rnd):
    ws = [WEIGHT.get(w if isinstance(w, str) else w[0], 3) for w, _ in opts]
    return rnd.choices(opts, weights=ws)[0]


def build(P, want, allowed, rnd, maxsize=46, lift=0.3, conj=0.15, t17=False):
    for _ in range(80):
        lines, facts = [], []
        first = [m for m in all_moves(P, allowed) if size(m[1]) <= maxsize]
        if not first:
            return None
        w, r = pick(first, rnd)
        lines.append((P, r, w))
        facts.append((r, 1))
        tries = 0
        while len(lines) < want and tries < 120:
            tries += 1
            u = rnd.random()
            if u < conj and len(facts) >= 2:
                (q1, i), (q2, j) = rnd.sample(facts, 2)
                cq = C(q1, q2)
                if size(cq) > maxsize or cq in [f for f, _ in facts]:
                    continue
                lines.append((P, cq, ("cj", i, j)))
                facts.append((cq, len(lines)))
                continue
            q, i = rnd.choice(facts)
            if t17 and u > 0.9 and "A5" in allowed and size(q) <= 26:
                ts = [t for t in ("a", "b") if t in q7.terms(q) and not free_in(t, q)
                      and not (q[0] in ("all", "ex") and q[1] == t)]
                if not ts:
                    continue
                t = rnd.choice(ts)
                e, r = EX(t, q), ALL(t, q)
                if r in [f for f, _ in facts]:
                    continue
                lines.append((q, e, "A2"))
                lines.append((P, e, ("tr", i, len(lines))))
                lines.append((e, r, "A5"))
                lines.append((P, r, ("tr", len(lines) - 1, len(lines))))
                facts.append((r, len(lines)))
                continue
            if u < conj + lift and q[0] in ("all", "ex"):
                inner = [m for m in all_moves(q[2], allowed) if m[0] not in ("A2",) and size(m[1]) <= maxsize]
                if not inner:
                    continue
                w, h = pick(inner, rnd)
                r = (q[0], q[1], h)
                if r in [f for f, _ in facts] or r == P or size(r) > maxsize:
                    continue
                lines.append((q[2], h, w))
                lines.append((q, r, ("R1" if q[0] == "all" else "R2", len(lines))))
                lines.append((P, r, ("tr", i, len(lines))))
                facts.append((r, len(lines)))
                continue
            opts = [m for m in all_moves(q, allowed) if size(m[1]) <= maxsize and m[1] not in [f for f, _ in facts]
                    and m[1] != P]
            if not opts:
                continue
            w, r = pick(opts, rnd)
            lines.append((q, r, w))
            lines.append((P, r, ("tr", i, len(lines))))
            facts.append((r, len(lines)))
        if lines[-1][0] == P:
            return lines
    return None


def prune(lines):
    need, stack = set(), [len(lines)]
    while stack:
        n = stack.pop()
        if n in need:
            continue
        need.add(n)
        w = lines[n - 1][2]
        if isinstance(w, tuple) and w[0] != "Ss":
            stack += list(w[1:])
    keep = sorted(need)
    new = {old: i for i, old in enumerate(keep, 1)}

    def ren(w):
        if isinstance(w, str) or w[0] == "Ss":
            return w
        return (w[0],) + tuple(new[k] for k in w[1:])
    return [(a, b, ren(w)) for a, b, w in (lines[o - 1] for o in keep)]


def stats(lines):
    names = [w for _, _, w in lines if isinstance(w, str)]
    rules = [w[0] for _, _, w in lines if isinstance(w, tuple)]
    return names, rules


RICH = {"A3", "A4", "A5", "T15", "T22", "T24", "T32", "T34", "T19", "T21", "T42", "T14", "T16", "T17", "T18",
        "A^16", "A^26", "A^36", "A^17", "A^27", "A^37", "A^18", "A^28", "A^38", "A^19", "A^29", "A^39", "A10", "A11", "A12"}


def dup_conj(f):
    return any(g[0] in ("conj", "wdis") and len(set(g[1])) < len(g[1]) for g in walk(f))


def good(lines, allowed, least, most, need_q=2, semantic=True):
    if not (least <= len(lines) <= most):
        return False
    P0, Q0 = lines[-1][0], lines[-1][1]
    if dup_conj(Q0) or not any(g[0] in q7.QK for g in walk(Q0)) or Q0 in list(walk(P0)):
        return False
    if any(tex(b).count("\\sim \\sim") > 1 or "\\sim \\sim \\sim" in tex(b) for _, b, _ in lines):
        return False
    if q7.check(lines, allowed):
        return False
    names, rules = stats(lines)
    qax = [n for n in names if n not in ("Ss",)]
    if len(qax) < need_q or len(set(qax)) < min(need_q, 3):
        return False
    if not (set(qax) & RICH) or not (set(rules) & {"R1", "R2", "cj"}):
        return False
    P, Qf = lines[-1][0], lines[-1][1]
    if q7.inst_of(q7.schemes_for(allowed).get(names[0], q7.SCQ["A1"]), P, Qf) and len(lines) < 3:
        return False
    if semantic and not q7.qtaut(P, Qf, nmax=2):
        raise AssertionError("вывод недопустимой формулы: " + ftex(P, Qf))
    return True


SEEN = set()


def make(premises, allowed, rnd, least=8, most=12, want=None, need_q=3, maxsize=46, final_max=40):
    for _ in range(4000):
        P = rnd.choice(premises)() if callable(premises[0]) else rnd.choice(premises)
        lines = build(P, want or rnd.choice([least + 3, least + 5, most + 3]), allowed, rnd, maxsize=maxsize)
        if not lines:
            continue
        lines = prune(lines)
        key = ftex(lines[-1][0], lines[-1][1])
        if key in SEEN or size(lines[-1][1]) > final_max or size(lines[-1][1]) < 8:
            continue
        if good(lines, allowed, least, most, need_q=need_q):
            SEEN.add(key)
            return lines
    raise RuntimeError("вывод не построен")


def show(lines):
    return "\n".join(f"{n}. ${ftex(a, b)}$ [{why_text(w)}]" for n, (a, b, w) in enumerate(lines, 1))


def show_hidden(lines, hide_why, hide_f):
    return "\n".join(f"{n}. {'…' if n in hide_f else '$' + ftex(a, b) + '$'} [{'…' if n in hide_why else why_text(w)}]"
                     for n, (a, b, w) in enumerate(lines, 1))


# ---------------------------------------------------------------- две ошибки в основаниях
WRONG = {"A6": "A7", "A7": "A6", "A1": "A2", "A2": "A1", "A3": "A4", "A4": "A3", "A5": "A1",
         "T20": "T19", "T19": "T20", "T21": "T22", "T22": "T21", "T27": "A1", "T1": "T2", "T2": "T1",
         "T14": "T15", "T15": "T14", "T32": "A4", "T29": "T30", "T30": "T29", "T24": "T23", "T23": "T24",
         "A^16": "A^17", "A^17": "A^16", "A^26": "A^27", "A^27": "A^26", "A^18": "A^19", "A^19": "A^18",
         "A^28": "A^29", "A^29": "A^28", "A10": "A11", "A11": "A10"}


def two_errors(lines, allowed, rnd):
    """Два неверных основания: путаница схем и правил (R1 ↔ R2; R1 S^s ↔ R2 S^s; схема ↔ соседняя схема)."""
    cand = [i for i, (*_, w) in enumerate(lines) if isinstance(w, str) and w in WRONG and WRONG[w] in allowed]
    rr = [i for i, (*_, w) in enumerate(lines) if isinstance(w, tuple) and w[0] in ("R1", "R2", "tr")]
    for _ in range(200):
        if not cand or not rr:
            return None
        i, j = rnd.choice(cand), rnd.choice(rr)
        bad = list(lines)
        a, b, w = bad[i]
        bad[i] = (a, b, WRONG[w])
        a2, b2, w2 = bad[j]
        if w2[0] == "tr":
            nw = ("cj", w2[1], w2[2])
        else:
            nw = ("R2" if w2[0] == "R1" else "R1", w2[1])
        bad[j] = (a2, b2, nw)
        errs = q7.check(bad, allowed)
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        if steps == sorted([i + 1, j + 1]):
            return bad, i, j
    return None


# ---------------------------------------------------------------- ошибочный шаг (почти-пример)
def bad_moves(q, allowed):
    """Правдоподобные неверные шаги: (метка, заключение, объяснение)."""
    out = []
    k = q[0]
    if k == "ex" and free_in(q[1], q[2]) and "A5" in allowed:
        out.append(("A5", ALL(q[1], q[2]), "A5bad"))
    if k == "all" and q[2][0] == "wdis" and len(q[2][1]) == 2:
        u, v = q[2][1]
        out.append(("A4", W(ALL(q[1], u), ALL(q[1], v)), "A4bad"))
    if k == "conj" and len(q[1]) == 2 and all(t[0] == "ex" for t in q[1]) and q[1][0][1] == q[1][1][1]:
        out.append(("A3", EX(q[1][0][1], C(q[1][0][2], q[1][1][2])), "A3bad"))
    if k == "all" and q[2][0] == "el" and q[1] in (q[2][1], q[2][2]):
        a = q[1]
        rep = "c" if "c" not in (q[2][1], q[2][2]) else "d"
        body = EL(rep if q[2][1] == a else q[2][1], rep if q[2][2] == a else q[2][2])
        out.append(("A1", body, "A1bad"))
    if k == "ex" and free_in(q[1], q[2]) and "T18" in allowed:
        out.append(("T18", q[2], "T18bad"))
    if k == "all" and q[2][0] == "ex" and "T15" in allowed:
        out.append(("T15", EX(q[2][1], ALL(q[1], q[2][2])), "T15bad"))
    return out


BAD_SHORT = {"A5bad": "условие A5 нарушено: $a$ входит свободно в $x$", "A4bad": "в A4 второй член — с $(\\exists a)$",
             "A3bad": "в посылке A3 первый множитель — с $(\\forall a)$", "A1bad": "A1 не позволяет заменять термин $a$",
             "T18bad": "условие T18 нарушено: $a$ входит свободно в $x$", "T15bad": "T15 переставляет кванторы в другую сторону"}
BAD_WHY = {
    "A5bad": "A5 (с. 99) применима, только если $a$ не входит свободно в $x$, а здесь $a$ входит в $x$ свободно",
    "A4bad": "по A4 (с. 99) во втором члене дизъюнкции стоит квантор существования: $(\\forall a)(x \\vee y) \\vdash "
             "(\\forall a)x \\vee (\\exists a)y$, а не $(\\forall a)y$",
    "A3bad": "в посылке A3 (с. 99) первый множитель — с квантором общности: $(\\forall a)x(\\exists a)y$; из "
             "$(\\exists a)x(\\exists a)y$ схема ничего не даёт",
    "A1bad": "A1 (с. 99) снимает квантор, оставляя тот же $x$: $(\\forall a)x \\vdash x$; заменять в $x$ термин $a$ другим "
             "термином схема не позволяет (такие формулы недоказуемы по MT2 § 3, с. 100)",
    "T18bad": "T18 (с. 104) требует, чтобы $a$ не входил свободно в $x$, а здесь он входит свободно",
    "T15bad": "T15 (с. 104) переставляет $(\\exists a)(\\forall b)$ в $(\\forall b)(\\exists a)$, а не наоборот",
}


# ---------------------------------------------------------------- планы выводов (естественные цели)
class Der:
    def __init__(self, P):
        self.P, self.lines = P, []

    def add(self, a, b, w):
        self.lines.append((a, b, w))
        return len(self.lines)

    def step(self, i, r, w):
        """Из строки i (P ⊢ q) и q ⊢ r [w] — P ⊢ r; i = 0 — посылка P сама."""
        q = self.P if i == 0 else self.lines[i - 1][1]
        k = self.add(q, r, w)
        if i == 0:
            return k
        return self.add(self.P, r, ("tr", i, k))

    def lift(self, i, h, w):
        """Строка i: P ⊢ (Ka)g; g ⊢ h [w]; (Ka)g ⊢ (Ka)h [R1/R2]; P ⊢ (Ka)h."""
        q = self.P if i == 0 else self.lines[i - 1][1]
        k = self.add(q[2], h, w)
        k2 = self.add(q, (q[0], q[1], h), ("R1" if q[0] == "all" else "R2", k))
        if i == 0:
            return k2
        return self.add(self.P, (q[0], q[1], h), ("tr", i, k2))

    def cj(self, i, j):
        return self.add(self.P, C(self.lines[i - 1][1], self.lines[j - 1][1]), ("cj", i, j))

    def t17(self, i, t):
        """Строка i: P ⊢ q, t не входит свободно в q: A2, A5 — P ⊢ (∀t)q."""
        q = self.P if i == 0 else self.lines[i - 1][1]
        k = self.step(i, EX(t, q), "A2")
        return self.step(k, ALL(t, q), "A5")

    def last(self):
        return len(self.lines)


def plan_t20(X, Y, a, rnd, post=True):
    """(∀a)(XY) ⊢ (∀a)X(∃a)Y [+ A3]."""
    d = Der(ALL(a, C(X, Y)))
    i = d.lift(0, X, ("Ss",))
    j = d.lift(0, Y, ("Ss",))
    if not post:
        d.cj(i, j)
        return d
    k = d.step(j, Y, "A1")
    k = d.step(k, EX(a, Y), "A2")
    m = d.cj(i, k)
    if rnd.random() < 0.6:
        d.step(m, EX(a, C(X, Y)), "A3")
    return d


def plan_t19(X, Y, a, rnd):
    u = C(ALL(a, X), ALL(a, Y))
    d = Der(u)
    i = d.step(0, ALL(a, X), ("Ss",))
    i = d.step(i, X, "A1")
    j = d.step(0, ALL(a, Y), ("Ss",))
    j = d.step(j, Y, "A1")
    k = d.cj(i, j)
    r = d.add(ALL(a, u), ALL(a, C(X, Y)), ("R1", k))
    e = d.add(u, EX(a, u), "A2")
    f = d.add(EX(a, u), ALL(a, u), "A5")
    g = d.add(u, ALL(a, u), ("tr", e, f))
    d.add(u, ALL(a, C(X, Y)), ("tr", g, r))
    return d


def plan_t14(X, a, b, rnd, kind="all"):
    """(∀a)(∀b)X ⊢ (∀b)(∀a)X или (∃a)(∀b)X ⊢ (∀b)(∃a)X (T14, T15 из аксиом)."""
    u = (kind, a, ALL(b, X))
    d = Der(u)
    i = d.add(ALL(b, X), X, "A1")
    j = d.add(u, (kind, a, X), ("R1" if kind == "all" else "R2", i))
    e = d.add(u, EX(b, u), "A2")
    f = d.add(EX(b, u), ALL(b, u), "A5")
    g = d.add(u, ALL(b, u), ("tr", e, f))
    h = d.add(ALL(b, u), ALL(b, (kind, a, X)), ("R1", j))
    d.add(u, ALL(b, (kind, a, X)), ("tr", g, h))
    return d


def plan_a5(X, Z, a, rnd):
    """(∃a)(XZ), a не входит свободно в Z: (∃a)X(∀a)Z или далее Z."""
    d = Der(EX(a, C(X, Z)))
    i = d.lift(0, X, ("Ss",))
    j = d.lift(0, Z, ("Ss",))
    j = d.step(j, ALL(a, Z), "A5")
    if rnd.random() < 0.5:
        j2 = d.step(j, Z, "A1")
        d.cj(i, j2) if rnd.random() < 0.5 else d.cj(j2, i)
    else:
        m = d.cj(j, i)
        d.step(m, EX(a, C(Z, X)), "A3")
    return d


def plan_a3(X, Y, a, rnd):
    d = Der(C(N(EX(a, N(X))), EX(a, Y)))
    i = d.step(0, N(EX(a, N(X))), ("Ss",))
    i = d.step(i, ALL(a, X), "A7")
    j = d.step(0, EX(a, Y), ("Ss",))
    m = d.cj(i, j)
    m = d.step(m, EX(a, C(X, Y)), "A3")
    d.lift(m, C(Y, X), ("Ss",))
    return d


def plan_a4(X, Y, Z, a, rnd):
    d = Der(ALL(a, C(W(X, Y), Z)))
    i = d.lift(0, W(X, Y), ("Ss",))
    i = d.step(i, W(ALL(a, X), EX(a, Y)), "A4")
    j = d.lift(0, Z, ("Ss",))
    if rnd.random() < 0.5:
        j = d.step(j, N(EX(a, N(Z))), "A6")
    d.cj(j, i) if rnd.random() < 0.5 else d.cj(i, j)
    return d


def plan_a4b(X, Y, a, rnd):
    d = Der(N(EX(a, N(W(Y, X)))))
    i = d.step(0, ALL(a, W(Y, X)), "A7")
    i = d.lift(i, W(X, Y), ("Ss",))
    i = d.step(i, W(ALL(a, X), EX(a, Y)), "A4")
    if rnd.random() < 0.5:
        d.step(i, W(EX(a, Y), ALL(a, X)), ("Ss",))
    return d


def plan_t40(X, a, b, rnd):
    d = Der(ALL(a, ALL(b, X)))
    i = d.step(0, ALL(b, X), "A1")
    i = d.step(i, X, "A1")
    i = d.step(i, EX(a, X), "A2")
    i = d.step(i, EX(b, EX(a, X)), "A2")
    return d
