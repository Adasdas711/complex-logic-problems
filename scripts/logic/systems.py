"""Критерии доказуемости систем общей теории дедукции (гл. 2–5 «Комплексной логики»).

Формулы — кортежи s1.py/s1w.py: ('v', n), ('neg', A), ('conj', …), ('dis', …) — «:», ('wdis', …) — «∨».
Критерии (гл. 5, § 2, MT1–MT6, с. 72–73; гл. 2, § 2; гл. 3, § 3; гл. 4, § 1–4):
  s — сильное следование S^s: тавтология и в y нет элементарных высказываний, отсутствующих в x;
  w — ослабленное S^w: тавтология и в x и y есть общее элементарное высказывание;
  m — максимальное S^m: тавтология и множества совпадают;
  c — конверсное S^c: тавтология и в x нет элементарных высказываний, отсутствующих в y;
  q — квазиследование S^6: тавтология.
S₂¹ (гл. 3, § 6, с. 55–57): для каждого члена ДНФ посылки найдётся член ДНФ заключения, все конъюнктивные
составляющие которого входят в него.
"""
from itertools import product

from s1 import C, D, N, V, atoms  # noqa: F401
from s1w import W, value  # noqa: F401

NAMES = {"s": "S^s", "w": "S^w", "m": "S^m", "c": "S^c", "q": "S^6"}
COND = {
    "s": "в заключение не входят элементарные высказывания, отсутствующие в посылке",
    "w": "в посылке и заключении есть по крайней мере одно общее элементарное высказывание",
    "m": "множества элементарных высказываний посылки и заключения совпадают",
    "c": "в посылку не входят элементарные высказывания, отсутствующие в заключении",
    "q": "условий на элементарные высказывания нет",
}
MT = {"s": "гл. 5, § 2, MT1", "w": "гл. 5, § 2, MT3", "m": "гл. 5, § 2, MT2", "c": "гл. 5, § 2, MT4",
      "q": "гл. 5, § 2, MT6"}


def rows(*fs):
    names = sorted(set().union(*(atoms(f) for f in fs)))
    for v in product((0, 1), repeat=len(names)):
        yield dict(zip(names, v))


def taut(a, b):
    return all(not (value(a, e) and not value(b, e)) for e in rows(a, b))


def is_taut(f):
    return all(value(f, e) for e in rows(f))


def counter(a, b):
    for e in rows(a, b):
        if value(a, e) and not value(b, e):
            return e


def cond(k, a, b):
    A, B = atoms(a), atoms(b)
    return {"s": B <= A, "w": bool(A & B), "m": A == B, "c": A <= B, "q": True}[k]


def provable(k, a, b):
    return taut(a, b) and cond(k, a, b)


def env_text(e):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(e.items()))


def reason(k, a, b, tex):
    """Обоснование ответа «доказуема/недоказуема в системе k»."""
    if not taut(a, b):
        return f"не тавтология: при {env_text(counter(a, b))} посылка — 1, заключение — 0"
    if not cond(k, a, b):
        A, B = atoms(a), atoms(b)

        def lst(s):
            s = sorted(s)
            return ", ".join(f"${t}$" for t in s), len(s) > 1
        if k == "s":
            l, pl = lst(B - A)
            det = f"в заключение {'входят' if pl else 'входит'} {l}, {'которых' if pl else 'которого'} нет в посылке"
        elif k == "c":
            l, pl = lst(A - B)
            det = f"в посылку {'входят' if pl else 'входит'} {l}, {'которых' if pl else 'которого'} нет в заключении"
        elif k == "w":
            det = "общих элементарных высказываний нет"
        else:
            l, pl = lst(A ^ B)
            det = f"множества различны: {l} — только в одной части"
        return f"тавтология, но условие системы не выполнено: {det}"
    return "тавтология, и условие системы выполнено"


# ---------- ДНФ и S₂¹ ----------
def nnf(f, neg=False):
    k = f[0]
    if k == "v":
        return N(f) if neg else f
    if k == "neg":
        return nnf(f[1], not neg)
    if k == "dis":  # x : y — по D1 § 1 гл. 2: x∼y ∨ ∼xy (n членов — аналогично)
        xs = f[1]
        exp = W(*(C(*([xs[i]] + [N(xs[j]) for j in range(len(xs)) if j != i])) for i in range(len(xs))))
        return nnf(exp, neg)
    args = [nnf(a, neg) for a in f[1]]
    kk = {"conj": "wdis", "wdis": "conj"}[k] if neg else k
    return (kk, tuple(args))


def dnf(f):
    """Список членов ДНФ; член — frozenset литер ('v', n) / ('neg', ('v', n))."""
    g = nnf(f)

    def go(h):
        if h[0] in ("v", "neg"):
            return [frozenset([h])]
        parts = [go(a) for a in h[1]]
        if h[0] == "wdis":
            return [t for p in parts for t in p]
        out = [frozenset()]
        for p in parts:
            out = [o | t for o in out for t in p]
        return out
    res = []
    for t in go(g):
        if t not in res:
            res.append(t)
    return res


def s21(a, b):
    xs, ys = dnf(a), dnf(b)
    return all(any(yj <= xi for yj in ys) for xi in xs)


def term_tex(t, tex):
    lits = sorted(t, key=lambda l: (l[1] if l[0] == "v" else l[1][1], l[0] == "neg"))
    return "".join(tex(l) for l in lits)


def dnf_tex(ts, tex):
    return " \\vee ".join(term_tex(t, tex) for t in ts)


# ---------- неклассический случай S_n (гл. 5, § 5, с. 75–77) ----------
# Основное высказывание a принимает одно из трёх состояний: 'a' (a истинно), 'n' (⌝a истинно), 'q' (?a истинно):
# x и ⌝x не бывают истинны вместе; ?x равнозначно ∼x∼⌝x.
def nval(f, st):
    k = f[0]
    if k == "v":
        return int(st[f[1]] == "a")
    if k == "nn":       # ⌝a
        return int(st[f[1]] == "n")
    if k == "qq":       # ?a
        return int(st[f[1]] == "q")
    if k == "neg":
        return 1 - nval(f[1], st)
    vs = [nval(a, st) for a in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs)) if k == "wdis" else int(sum(vs) == 1)


def natoms(f):
    if f[0] in ("v", "nn", "qq"):
        return {f[1]}
    if f[0] == "neg":
        return natoms(f[1])
    return set().union(*(natoms(a) for a in f[1]))


def ntaut(a, b=None):
    names = sorted(natoms(a) | (natoms(b) if b else set()))
    for v in product("anq", repeat=len(names)):
        st = dict(zip(names, v))
        if b is None:
            if not nval(a, st):
                return False
        elif nval(a, st) and not nval(b, st):
            return False
    return True


if __name__ == "__main__":
    x, y = V("x"), V("y")
    NN = lambda n: ("nn", n)
    QQ = lambda n: ("qq", n)
    # A^n1–A^n6, T1–T14 (с. 76–77) — тавтологии
    a = "x"
    tests = [(N(V(a)), W(NN(a), QQ(a))), (W(NN(a), QQ(a)), N(V(a))), (N(NN(a)), W(V(a), QQ(a))),
             (W(V(a), QQ(a)), N(NN(a))), (N(QQ(a)), W(V(a), NN(a))), (W(V(a), NN(a)), N(QQ(a)))]
    print("A^n1–6:", [ntaut(p, q) for p, q in tests])
    print("MT3:", ntaut(N(NN(a)), V(a)), ntaut(W(V(a), NN(a))), "T14:", ntaut(W(V(a), NN(a), QQ(a))))
    print("s21:", s21(C(x, N(x)), y), s21(x, W(x, y)), s21(C(x, W(N(x), y)), y))
