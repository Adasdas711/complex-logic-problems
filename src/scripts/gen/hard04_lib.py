"""Построение выводов в системах гл. 4 (S_3, S_4, S_4*, S^4, S^5, S^6) для генератора hard04.py.

Каждый построенный вывод проверяется sys4.check по схемам и правилам системы, а каждая строка — по критерию
системы (тавтологичность и условие на элементарные высказывания: гл. 4, § 1–4; гл. 5, § 2, с. 72–73).
"""
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import sys4 as S4  # noqa: E402
import systems as SY  # noqa: E402
from s1 import C, D, N, V, atoms  # noqa: E402
from s1w import W  # noqa: E402

rnd = random.Random(1970_0400)
x, y, z, u, w = (V(c) for c in "pqrst")   # элементарные высказывания p, q, r, s, t


def size(f, lang="w"):
    return len(S4.tex(f, lang))


def sub(a, b):
    return a == b or (b[0] == "neg" and sub(a, b[1])) or (b[0] in ("conj", "wdis", "dis") and any(sub(a, c) for c in b[1]))


# критерий строки для каждой системы
S4.SYSTEMS["S_1A12"] = dict(lang="w", schemes=S4.W_SCHEMES + ["A12"], a3="free", rules={"R1", "R2", "R3"})
CRIT_KEY = {"S_1A12": "q", "S_3": "m", "S^3": "m", "S_4": "c", "S_4*": "c", "S^4": "c", "S_1": "s", "S^5": "s", "S^6": "q"}


def line_ok(sysname, a, b):
    if a is None:
        return S4.taut_line(None, b)
    return SY.provable(CRIT_KEY[sysname], a, b)


def all_ok(sysname, lines):
    return not S4.check(sysname, lines) and all(line_ok(sysname, a, b) for a, b, _ in lines)


SMALL = [x, y, z, N(x), N(y), u, N(u), w]


def new_small(avoid):
    """Небольшое высказывание с элементарным высказыванием, отсутствующим в avoid."""
    fresh = [t for t in "strqp" if t not in avoid]
    if not fresh:
        return None
    t = V(rnd.choice(fresh[:2]))
    return rnd.choice([t, N(t), C(t, rnd.choice([x, y])), t])


# ---------- шаги в языке S₁ ----------
def w_moves(q, sysname, lim=36):
    cfg = S4.SYSTEMS[sysname]
    out = []
    sch = cfg["schemes"]
    if q[0] == "neg" and q[1][0] == "neg":
        out.append(("A1", q[1][1]))
    if q[0] == "conj" and len(q[1]) == 2:
        a, b = q[1]
        out += [("A3", a), ("A4", C(b, a))]
        if a[0] == "wdis" and len(a[1]) == 2:
            out.append(("A7", W(C(a[1][0], b), a[1][1])))
        if a[0] == "conj" and len(a[1]) == 2 and all(t[0] != "conj" for t in a[1]) and b[0] != "conj":
            out.append(("A6", C(a[1][0], a[1][1], b)))
        if b[0] == "conj" and len(b[1]) == 2 and all(t[0] != "conj" for t in b[1]) and a[0] != "conj":
            out.append(("A6", C(a, b[1][0], b[1][1])))
    if q[0] == "conj" and len(q[1]) == 3 and all(t[0] != "conj" for t in q[1]):
        a, b, c = q[1]
        out += [("A5", C(C(a, b), c)), ("A5", C(a, C(b, c)))]
    if q[0] == "neg" and q[1][0] == "conj":
        out.append(("A9", W(*(N(t) for t in q[1][1]))))
    if q[0] == "wdis" and all(t[0] == "neg" for t in q[1]):
        out.append(("A10", N(C(*(t[1] for t in q[1])))))
    if q[0] == "wdis" and len(q[1]) == 2:
        a, b = q[1]
        if a[0] == "conj" and b[0] == "conj" and len(a[1]) == 2 and len(b[1]) == 2 and a[1][1] == b[1][1]:
            out.append(("A8", C(W(a[1][0], b[1][0]), a[1][1])))
        if a[0] == "conj" and len(a[1]) == 2 and size(q) < 16:
            out.append(("A11", C(q, W(a[1][1], N(a[1][1])))))
    if q[0] in ("v", "neg") and size(q) < 6:
        out.append(("A2", N(N(q))))
    if "A12" in sch and size(q) < 18:
        Y = new_small(atoms(q)) if rnd.random() < 0.7 else rnd.choice(SMALL)
        if Y is not None and Y != q:
            out.append(("A12", W(q, Y)))
    if "A**12" in sch and size(q) < 14:
        t = rnd.choice([V(c) for c in "pqrs"])
        out.append(("A**12", C(q, W(t, N(t)))))
    res = []
    for n, r in out:
        if n in sch and size(r) <= lim and S4.is_axiom(sysname, n, q, r):
            res.append((n, r))
    return res


# ---------- шаги в языке S¹ (S^3, S^4) ----------
def c_moves(q, sysname, lim=40):
    out = []
    if size(q, "c") < 7:
        out.append(("A1", N(N(q))))
    if q[0] == "neg" and q[1][0] == "neg":
        out.append(("A2", q[1][1]))
    if q[0] == "conj" and len(q[1]) == 2:
        a, b = q[1]
        out += [("A3", a), ("A4", C(b, a))]
    if q[0] == "neg" and q[1][0] == "conj" and len(q[1][1]) == 2:
        a, b = q[1][1]
        out.append(("A7", D(C(N(a), b), C(a, N(b)), C(N(a), N(b)))))
    if q[0] == "dis" and len(q[1]) == 3:
        p0 = q[1][2]
        if p0[0] == "conj" and len(p0[1]) == 2 and all(t[0] == "neg" for t in p0[1]):
            a, b = p0[1][0][1], p0[1][1][1]
            out.append(("A8", N(C(a, b))))
    if q[0] == "neg" and q[1][0] == "dis" and len(q[1][1]) == 2:
        a, b = q[1][1]
        out.append(("A9", D(C(a, b), C(N(a), N(b)))))
    if q[0] == "dis" and len(q[1]) == 2 and q[1][0][0] == "conj" and len(q[1][0][1]) == 2:
        a, b = q[1][0][1]
        out.append(("A10", N(D(a, b))))
    if q[0] == "neg" and "A15" in S4.SYSTEMS[sysname]["schemes"] and size(q, "c") < 14:
        Y = new_small(atoms(q)) if rnd.random() < 0.7 else rnd.choice([x, y, N(x), z])
        if Y is not None and Y != q[1]:
            out.append(("A15", N(C(q[1], Y))))
    return [(n, r) for n, r in out if size(r, "c") <= lim and S4.is_axiom(sysname, n, q, r)]


def moves_for(sysname):
    return c_moves if S4.SYSTEMS[sysname]["lang"] == "c" else w_moves


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
    return [(a, b, wh if isinstance(wh, str) else (wh[0], *(new[i] for i in wh[1:]))) for a, b, wh in
            (lines[o - 1] for o in keep)]


def build_ent(sysname, P, want, accept, lim=36, start=None):
    """Случайный вывод с посылкой P (R1, R2): строки (P, r) и шаги-аксиомы (q, r)."""
    mv = moves_for(sysname)
    lang = S4.SYSTEMS[sysname]["lang"]
    for _ in range(60):
        lines, facts = list(start or []), []
        if start:
            facts = [(b, n) for n, (a, b, _) in enumerate(start, 1) if a == P]
        else:
            first = mv(P, sysname)
            if not first:
                return None
            name, r = rnd.choice(first)
            lines.append((P, r, name))
            facts.append((r, 1))
        tries = 0
        while len(lines) < want and tries < 90:
            tries += 1
            if len(facts) >= 2 and rnd.random() < 0.28:
                (q1, i), (q2, j) = rnd.sample(facts, 2)
                if size(C(q1, q2), lang) > lim or C(q1, q2) in [f for f, _ in facts] or sub(q1, q2) or sub(q2, q1):
                    continue
                lines.append((P, C(q1, q2), ("R2", i, j)))
                facts.append((C(q1, q2), len(lines)))
                continue
            q, i = rnd.choice(facts)
            opts = [(n, r) for n, r in mv(q, sysname) if r not in [f for f, _ in facts] and r != P]
            if not opts:
                continue
            main = [o for o in opts if o[0] not in ("A5", "A6")]
            if main and rnd.random() < 0.85:
                opts = main
            name, r = rnd.choice(opts)
            lines.append((q, r, name))
            lines.append((P, r, ("R1", i, len(lines))))
            facts.append((r, len(lines)))
        if lines and lines[-1][0] == P:
            pl = prune(lines)
            if all_ok(sysname, pl) and accept(pl):
                return pl
    return None


SEEN = set()


def derivation(sysname, premises, want, least, accept=lambda ls: True, lim=36):
    for _ in range(4000):
        P = premises()
        ls = build_ent(sysname, P, want + 4, accept, lim=lim)
        if ls and len(ls) >= least:
            key = (sysname, S4.ltex(ls[-1][0], ls[-1][1], S4.SYSTEMS[sysname]["lang"]))
            if key not in SEEN and sum(1 for *_, wh in ls if not isinstance(wh, str)) >= 3:
                SEEN.add(key)
                return ls
    raise RuntimeError(f"вывод в {sysname} не построен")


def rule_count(ls, name):
    return sum(1 for *_, wh in ls if (wh if isinstance(wh, str) else wh[0]) == name)


# ---------- S^5: вырожденное следование ----------
def compound():
    return rnd.choice([x, y, z, N(x), C(x, y), W(y, z), N(C(x, z)), C(N(y), z), W(x, N(y)), u])


def build_deg(want, sysname="S^5", lim=34, need=("Rd1",)):
    """Вывод формулы ⊢ x в S^5: A^d1, схемы S₁, R1, R^d1–R^d3."""
    for _ in range(200):
        X = compound()
        lines = [(None, N(C(N(X), X)), "Ad1")]
        deg = [(lines[0][1], 1)]
        tries = 0
        while len(lines) < want and tries < 120:
            tries += 1
            k = rnd.random()
            if k < 0.12 and len(deg) < 3:
                X2 = compound()
                f = N(C(N(X2), X2))
                if f not in [d for d, _ in deg]:
                    lines.append((None, f, "Ad1"))
                    deg.append((f, len(lines)))
                continue
            if k < 0.25 and len(deg) >= 2:
                (q1, i), (q2, j) = rnd.sample(deg, 2)
                f = C(q1, q2)
                if size(f) <= lim and f not in [d for d, _ in deg]:
                    lines.append((None, f, ("Rd3", i, j)))
                    deg.append((f, len(lines)))
                continue
            if k < 0.37:
                cand = [(q, j) for q, j in deg if q[0] == "neg"]
                if not cand:
                    continue
                q, j = rnd.choice(cand)
                Y = q[1]
                Z = rnd.choice([x, y, z, u, N(z), N(u)])
                opts = [("A3", C(Y, Z))]
                if conj2 := (Y[0] == "conj" and len(Y[1]) == 2):
                    opts.append(("A4", C(Y[1][1], Y[1][0])))
                if size(Y) < 8:
                    opts.append(("A1", N(N(Y))))
                name, X1 = rnd.choice(opts)
                f = N(X1)
                if size(f) > lim or f in [d for d, _ in deg] or not S4.is_axiom(sysname, name, X1, Y):
                    continue
                lines.append((X1, Y, name))
                lines.append((None, f, ("Rd2", len(lines), j)))
                deg.append((f, len(lines)))
                continue
            q, j = rnd.choice(deg)
            opts = [(n, r) for n, r in w_moves(q, sysname, lim) if r not in [d for d, _ in deg]]
            if not opts:
                continue
            name, r = rnd.choice(opts)
            lines.append((q, r, name))
            i = len(lines)
            if rnd.random() < 0.35:
                opts2 = [(n, r2) for n, r2 in w_moves(r, sysname, lim) if r2 not in [d for d, _ in deg] and r2 != q]
                if opts2:
                    n2, r2 = rnd.choice(opts2)
                    lines.append((r, r2, n2))
                    lines.append((q, r2, ("R1", i, len(lines))))
                    i, r = len(lines), r2
            lines.append((None, r, ("Rd1", i, j)))
            deg.append((r, len(lines)))
        if lines[-1][0] is None and not isinstance(lines[-1][2], str):
            pl = prune(lines)
            if all_ok(sysname, pl) and all(rule_count(pl, n) for n in need):
                return pl
    return None


def deg_derivation(want, least, need=("Rd1",), lim=34):
    for _ in range(3000):
        ls = build_deg(want + 3, need=need, lim=lim)
        if ls and least <= len(ls) <= want + 2:
            key = ("S^5", S4.ltex(None, ls[-1][1]))
            if key not in SEEN and 8 <= size(ls[-1][1]) <= lim:
                SEEN.add(key)
                return ls
    raise RuntimeError("вывод в S^5 не построен")


# ---------- S^6: квазиследование ----------
def q_derivation(want, least):
    """Вывод паразитарной для S^s формулы x ⊢ y в S^6: ⊢ z (S^5), xz ⊢ y (S₁), R^k1."""
    for _ in range(3000):
        deg = build_deg(rnd.choice([2, 3, 4]), need=())
        if not deg:
            continue
        deg = prune(deg)
        Z = deg[-1][1]
        X = rnd.choice([x, y, N(x), C(x, y), W(x, N(y)), N(C(x, y)), C(y, N(x))])
        if atoms(Z) <= atoms(X) or size(C(X, Z)) > 22:
            continue
        P = C(X, Z)
        start = list(deg)
        jz = len(deg)

        def acc(pl, X=X):
            a, b = pl[-1][0], pl[-1][1]
            return not atoms(b) <= atoms(X)
        ent = None
        for _ in range(30):
            cand = build_ent("S_1", P, rnd.choice([4, 5, 6, 7]), acc, lim=34)
            if cand:
                ent = cand
                break
        if not ent:
            continue
        off = len(start)
        ent = [(a, b, wh if isinstance(wh, str) else (wh[0], *(i + off for i in wh[1:]))) for a, b, wh in ent]
        lines = start + ent
        lines.append((X, lines[-1][1], ("Rk1", len(lines), jz)))
        pl = prune(lines)
        a, b = pl[-1][0], pl[-1][1]
        if (least <= len(pl) <= want + 2 and all_ok("S^6", pl) and not SY.provable("s", a, b)
                and S4.ltex(a, b) not in SEEN and size(b) <= 34):
            SEEN.add(S4.ltex(a, b))
            return pl
    raise RuntimeError("вывод в S^6 не построен")
