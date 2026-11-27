"""Модель системы S₁ (гл. 2, § 1, с. 36–37): операторы ·, ∨ (соединительная дизъюнкция), ∼.
Формулы — кортежи модели s1.py; дизъюнкция ∨ — ("wdis", args). Правила R1–R3 — те же, что в S¹.
"""
from itertools import product

from s1 import C, N, V, atoms, is_rebracketing, replaceable  # noqa: F401


def W(*a): return ("wdis", tuple(a))


def tex(f, ctx="top") -> str:
    k = f[0]
    if k == "v":
        return f[1]
    if k == "neg":
        a = f[1]
        return f"\\sim {tex(a)}" if a[0] in ("v", "neg") else f"\\sim({tex(a)})"
    if k == "conj":
        parts = [f"({tex(a)})" if a[0] in ("conj", "wdis", "dis") else tex(a) for a in f[1]]
        return "".join(parts)
    if k == "wdis":
        parts = [f"({tex(a)})" if a[0] == "wdis" else tex(a) for a in f[1]]
        out = " \\vee ".join(parts)
        return f"({out})" if ctx in ("conj", "neg") else out
    if k == "dis":
        parts = [f"({tex(a)})" if a[0] in ("dis", "wdis") else tex(a) for a in f[1]]
        return " : ".join(parts)
    raise ValueError(k)


def ftex(a, b) -> str:
    return f"{tex(a)} \\vdash {tex(b)}"


def value(f, env) -> int:
    k = f[0]
    if k == "v":
        return env[f[1]]
    if k == "neg":
        return 1 - value(f[1], env)
    vs = [value(a, env) for a in f[1]]
    if k == "conj":
        return int(all(vs))
    if k == "wdis":
        return int(any(vs))
    return int(sum(vs) == 1)


def rows(*fs):
    names = sorted(set().union(*(atoms(f) for f in fs)))
    for v in product((0, 1), repeat=len(names)):
        yield dict(zip(names, v))


def tautology(a, b):
    return all(not (value(a, e) and not value(b, e)) for e in rows(a, b))


def new_atoms(a, b):
    return atoms(b) - atoms(a)


def strong(a, b):
    return tautology(a, b) and not new_atoms(a, b)


def counterexample(a, b):
    for e in rows(a, b):
        if value(a, e) and not value(b, e):
            return e


def axiom(a, b):
    """Схема S₁ (с. 36–37), которой соответствует a ⊢ b, или None."""
    if a == N(N(b)):
        return "A1"
    if b == N(N(a)):
        return "A2"
    if a[0] == "conj" and len(a[1]) == 2:
        x, y = a[1]
        if b == x:
            return "A3"
        if b == C(y, x):
            return "A4"
    if is_rebracketing(a, b, "conj"):
        return "A5"
    if is_rebracketing(b, a, "conj"):
        return "A6"
    if a[0] == "conj" and len(a[1]) == 2 and a[1][0][0] == "wdis" and len(a[1][0][1]) == 2:
        (x, y), z = a[1][0][1], a[1][1]
        if b == W(C(x, z), y):
            return "A7"
    if b[0] == "conj" and len(b[1]) == 2 and b[1][0][0] == "wdis" and len(b[1][0][1]) == 2:
        (x, y), z = b[1][0][1], b[1][1]
        if a == W(C(x, z), C(y, z)):
            return "A8"
    if a[0] == "neg" and a[1][0] == "conj" and b == W(*(N(t) for t in a[1][1])):
        return "A9"
    if b[0] == "neg" and b[1][0] == "conj" and a == W(*(N(t) for t in b[1][1])):
        return "A10"
    if a[0] == "wdis" and len(a[1]) == 2 and a[1][0][0] == "conj" and len(a[1][0][1]) == 2:
        (x, y), z = a[1][0][1], a[1][1]
        if b == C(a, W(y, N(y))):
            return "A11"
    return None


AXIOM_TEXT = {
    "A1": "\\sim\\sim x \\vdash x", "A2": "x \\vdash \\sim\\sim x", "A3": "xy \\vdash x", "A4": "xy \\vdash yx",
    "A7": "(x \\vee y)z \\vdash xz \\vee y", "A8": "xz \\vee yz \\vdash (x \\vee y)z",
    "A9": "\\sim(xy) \\vdash \\sim x \\vee \\sim y", "A10": "\\sim x \\vee \\sim y \\vdash \\sim(xy)",
    "A11": "xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)",
}


def instance(name, x, y, z=None):
    return {"A1": (N(N(x)), x), "A2": (x, N(N(x))), "A3": (C(x, y), x), "A4": (C(x, y), C(y, x)),
            "A7": (C(W(x, y), z), W(C(x, z), y)), "A8": (W(C(x, z), C(y, z)), C(W(x, y), z)),
            "A9": (N(C(x, y)), W(N(x), N(y))), "A10": (W(N(x), N(y)), N(C(x, y))),
            "A11": (W(C(x, y), z), C(W(C(x, y), z), W(y, N(y))))}[name]


def check(lines):
    errs = []
    for n, (a, b, why) in enumerate(lines, 1):
        if isinstance(why, str):
            if axiom(a, b) != why:
                errs.append(f"шаг {n}: не аксиома {why}")
            continue
        r, i, j = why
        if not (1 <= i < n and 1 <= j < n):
            errs.append(f"шаг {n}: ссылка вперёд")
            continue
        (a1, b1, _), (a2, b2, _) = lines[i - 1], lines[j - 1]
        ok = {"R1": b1 == a2 and a == a1 and b == b2,
              "R2": a1 == a2 == a and b == C(b1, b2),
              "R3": a1 == b2 and b1 == a2 and replaceable(a, b, a1, b1) and (a != b or a1 == b1)}[r]
        if not ok:
            errs.append(f"шаг {n}: неверно применено {r}")
    return errs


def why_text(w):
    return w if isinstance(w, str) else f"{w[0]}: {w[1]}, {w[2]}"


def show(lines):
    return "\n".join(f"{n}. ${ftex(a, b)}$ [{why_text(w)}]" for n, (a, b, w) in enumerate(lines, 1))


def commute(x, y):
    """Вывод x ∨ y ⊢ y ∨ x из A1, A2, A4, A9, A10 (19 шагов)."""
    return [
        (N(N(x)), x, "A1"), (x, N(N(x)), "A2"),
        (W(x, y), W(N(N(x)), y), ("R3", 2, 1)),
        (N(N(y)), y, "A1"), (y, N(N(y)), "A2"),
        (W(N(N(x)), y), W(N(N(x)), N(N(y))), ("R3", 5, 4)),
        (W(N(N(x)), N(N(y))), N(C(N(x), N(y))), "A10"),
        (C(N(x), N(y)), C(N(y), N(x)), "A4"), (C(N(y), N(x)), C(N(x), N(y)), "A4"),
        (N(C(N(x), N(y))), N(C(N(y), N(x))), ("R3", 8, 9)),
        (N(C(N(y), N(x))), W(N(N(y)), N(N(x))), "A9"),
        (W(N(N(y)), N(N(x))), W(y, N(N(x))), ("R3", 4, 5)),
        (W(y, N(N(x))), W(y, x), ("R3", 1, 2)),
        (W(x, y), W(N(N(x)), N(N(y))), ("R1", 3, 6)),
        (W(x, y), N(C(N(x), N(y))), ("R1", 14, 7)),
        (W(x, y), N(C(N(y), N(x))), ("R1", 15, 10)),
        (W(x, y), W(N(N(y)), N(N(x))), ("R1", 16, 11)),
        (W(x, y), W(y, N(N(x))), ("R1", 17, 12)),
        (W(x, y), W(y, x), ("R1", 18, 13)),
    ]


if __name__ == "__main__":
    x, y, z = V("x"), V("y"), V("z")
    print(check(commute(x, y)))
    for nm in ["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10", "A11"]:
        a, b = instance(nm, x, y, z)
        print(nm, axiom(a, b), strong(a, b), ftex(a, b))
