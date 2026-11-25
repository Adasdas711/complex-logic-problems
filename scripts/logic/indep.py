"""Модель § 8 гл. 1 (с. 33–35): истинностные таблицы для независимости аксиомных схем и правил S¹.

Таблица задаёт: neg(v), conj(vals), dis(vals), ent(a, b) и множество отмеченных значений.
Формула следования «тавтологична» в таблице, если при всех значениях элементарных высказываний
её значение отмечено.
"""
from itertools import product

from s1 import C, D, N, V, atoms, ftex  # noqa: F401


def std_ent(a, b):
    return 0 if (a == 1 and b == 0) else 1


def T(neg, conj, dis, ent=std_ent, vals=(0, 1), des=(1,), note=""):
    return dict(neg=neg, conj=conj, dis=dis, ent=ent, vals=vals, des=set(des), note=note)


def all1(v): return int(all(x == 1 for x in v))
def one1(v): return int(sum(x == 1 for x in v) == 1)
def any1(v): return int(any(x == 1 for x in v))


def a11_dis(v):
    if len(v) == 2:
        return 0
    return 1 if all(x == 1 for x in v) else 0


def neg3(x): return {1: 1, 0: 2, 2: 0}[x]
def conj3(v): return 0 if all(x == 0 for x in v) else 1
def ent3_a5(a, b): return 2 if (a == 0 and b in (1, 2)) else 0
def ent3_a8(a, b): return 2 if (a in (0, 1) and b == 2) else 0


def conj_a8(v): return 2 if any(x == 2 for x in v) else 0


def dis_a8(v):
    if all(x == 2 for x in v):
        return 2
    if sum(x == 0 for x in v) == 1 and all(x in (0, 2) for x in v):
        return 0
    return 1


def neg4(x): return {1: 1, 2: 2, 0: 3, 3: 0}[x]
def conj4(v): return 0 if all(x == 0 for x in v) else 1
def ent4(a, b): return 2 if (a == 0 and b in (1, 2, 3)) else 0


TABLES = {
    "A1": T(lambda x: 0, all1, all1, note="$\\sim x = 0$; $x^1 : \\ldots : x^n = x^1 \\cdot \\ldots \\cdot x^n$"),
    "A2": T(lambda x: 1, all1, any1, note="$\\sim x = 1$; $x^1 : \\ldots : x^n = x^1 \\vee \\ldots \\vee x^n$"),
    "A3": T(lambda x: x, lambda v: 1, lambda v: 1, note="$\\sim x = x$; $xy = 1$; $x^1 : \\ldots : x^n = 1$"),
    "A4": T(lambda x: x, lambda v: v[0], lambda v: v[0], note="$\\sim x = x$; $xy = x$; $x^1 : \\ldots : x^n = x^1$"),
    "A7": T(lambda x: x, all1, lambda v: 0, note="$\\sim x = x$; $x^1 : \\ldots : x^n = 0$"),
    "A9": T(lambda x: x, all1, any1, note="$\\sim x = x$; $x^1 : \\ldots : x^n = x^1 \\vee \\ldots \\vee x^n$"),
    "A10": T(lambda x: 1 - x, all1, any1, note="$x^1 : \\ldots : x^n = x^1 \\vee \\ldots \\vee x^n$"),
    "A11": T(lambda x: x, all1, a11_dis, note="$\\sim x = x$; $x^1 : x^2 = 0$; $x^1 : \\ldots : x^n = 1$, если все $x^i = 1$, и 0 "
             "в остальных случаях ($n > 2$)"),
    "A5": T(neg3, lambda v: 0 if len(v) > 2 else conj3(v), lambda v: 1, ent3_a5, (0, 1, 2), (0,)),
    "A6": T(neg3, lambda v: 1 if len(v) > 2 else conj3(v), lambda v: 1, ent3_a5, (0, 1, 2), (0,)),
    "A8": T(neg3, conj_a8, dis_a8, ent3_a8, (0, 1, 2), (0, 1)),
    "A13": T(neg3, lambda v: 2 if any(x == 2 for x in v) else 1, lambda v: 1, ent3_a8, (0, 1, 2), (0, 1)),
    "A12": T(neg4, conj4, lambda v: 0 if v[-1] == 2 else 2, ent4, (0, 1, 2, 3), (0,)),
    "A14": T(neg4, conj4, lambda v: 1 if any(x == 1 for x in v) else 0, ent4, (0, 1, 2, 3), (0,)),
    "R1": T(lambda x: 0, lambda v: 0, lambda v: 0, lambda a, b: 0 if (a == 1 and b == 1) else 1),
    "R2": T(lambda x: x, lambda v: 0, lambda v: 0),
    "R3": T(neg3, conj3, lambda v: 1, ent3_a5, (0, 1, 2), (0,)),
}


def val(f, env, t):
    k = f[0]
    if k == "v":
        return env[f[1]]
    if k == "neg":
        return t["neg"](val(f[1], env, t))
    vs = [val(a, env, t) for a in f[1]]
    return t["conj"](vs) if k == "conj" else t["dis"](vs)


def fval(a, b, env, t):
    return t["ent"](val(a, env, t), val(b, env, t))


def valid(a, b, t):
    names = sorted(atoms(a) | atoms(b))
    for vs in product(t["vals"], repeat=len(names)):
        env = dict(zip(names, vs))
        if fval(a, b, env, t) not in t["des"]:
            return False, env
    return True, None


x, y, z = V("x"), V("y"), V("z")
a, b = V("a"), V("b")
# Примеры аксиомных схем из элементарных высказываний (с. 15–17)
SAMPLES = {
    "A1": [(x, N(N(x)))], "A2": [(N(N(x)), x)], "A3": [(C(x, y), x)], "A4": [(C(x, y), C(y, x))],
    "A5": [(C(x, y, z), C(C(x, y), z)), (C(x, y, z), C(x, C(y, z)))],
    "A6": [(C(C(x, y), z), C(x, y, z)), (C(x, C(y, z)), C(x, y, z))],
    "A7": [(N(C(x, y)), D(C(N(x), y), C(x, N(y)), C(N(x), N(y))))],
    "A8": [(D(C(N(x), y), C(x, N(y)), C(N(x), N(y))), N(C(x, y)))],
    "A9": [(N(D(x, y)), D(C(x, y), C(N(x), N(y))))],
    "A10": [(D(C(x, y), C(N(x), N(y))), N(D(x, y)))],
    "A11": [(D(x, y, z), D(D(x, y), z)), (D(x, y, z), D(x, D(y, z)))],
    "A11*": [(D(x, y, z), D(D(x, y), z))],   # A11 без заключения в скобки последнего члена (с. 34)
    "A12": [(D(C(a, b), D(C(a, N(b)), C(N(a), b))), D(C(a, b), C(a, N(b)), C(N(a), b))),
            (D(a, D(N(a), C(N(a), a))), D(a, N(a), C(N(a), a)))],
    "A13": [(D(C(x, z), C(y, z)), C(D(x, y), z))],   # общий вид, n = 2 (частный вид на с. 17 — опечатка)
    "A14": [(C(D(x, y), z), D(C(x, z), y))],
}


def matrix():
    rows = {}
    for tn, t in TABLES.items():
        rows[tn] = {an: all(valid(p, q, t)[0] for p, q in s) for an, s in SAMPLES.items()
                    if an != "A11*" or tn == "A12"}
        if tn == "A12":
            rows[tn].pop("A11")
    return rows


if __name__ == "__main__":
    m = matrix()
    for tn, r in m.items():
        bad = [an for an, ok in r.items() if not ok]
        print(f"{tn:4} не тавтологичны: {bad}")
    for tn in ("R1", "R2", "R3"):
        t = TABLES[tn]
        print(tn, "a⊢a", valid(a, a, t)[0], "a⊢aa", valid(a, C(a, a), t)[0], "a⊢a:~aa", valid(a, D(a, C(N(a), a)), t)[0])
