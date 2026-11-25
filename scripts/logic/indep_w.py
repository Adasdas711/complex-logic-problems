"""Таблицы независимости S₁ (гл. 2, § 3, с. 43–45). Только таблицы, задаваемые значениями операторов
(для A2, A7, A8 в книге меняются синтаксические соглашения — они здесь не моделируются)."""
from itertools import product

from s1 import C, N, V, atoms
from s1w import W, instance


def T(neg, conj, wdis, ent=lambda a, b: 0 if (a == 1 and b == 0) else 1, vals=(0, 1), good=lambda v: v == 1):
    return dict(neg=neg, conj=conj, wdis=wdis, ent=ent, vals=vals, good=good)


std_c = lambda v: int(all(v))
std_w = lambda v: int(any(v))
g3 = lambda v: v == 1
TABLES = {
    "A1": T(lambda x: 1, std_c, std_w),
    "A3": T(lambda x: x, lambda v: 1, lambda v: 1),
    "A4": T(lambda x: x, lambda v: v[0], lambda v: v[0]),
    "A5": T(lambda x: 1 - x, lambda v: 1 if len(v) > 2 else std_c(v), std_w),
    "A6": T(lambda x: 1 - x, lambda v: 0 if len(v) > 2 else std_c(v), std_w),
    "A9": T(lambda x: 1 - x, std_c, lambda v: v[-1]),
    "A10": T(lambda x: 4 - x, lambda v: 3 if 3 in v else 1, min,
             lambda a, b: 0 if (a == 1 and b == 3) or (a == 2 and b in (1, 3)) else 1, (1, 2, 3)),
    "A11": T(lambda x: 4 - x, max, min, lambda a, b: 1 if a >= b else 0, (1, 2, 3)),
    "R1": T(lambda x: 4 - x, max, min, lambda a, b: 0 if (a in (1, 2) and b == 3) else 1, (1, 2, 3)),
    "R2": T(lambda x: 1, lambda v: 1, lambda v: 1, lambda a, b: 0 if (a == 0 and b == 0) else 1),
    "R3": T(lambda x: 4 - x, lambda v: 1 if all(t == 1 for t in v) else 3, lambda v: 3 if all(t == 3 for t in v) else 1,
            lambda a, b: 1 if a >= b else 0, (1, 2, 3)),
}


def val(f, env, t):
    k = f[0]
    if k == "v":
        return env[f[1]]
    if k == "neg":
        return t["neg"](val(f[1], env, t))
    vs = [val(a, env, t) for a in f[1]]
    return t["conj"](vs) if k == "conj" else t["wdis"](vs)


def valid(a, b, t):
    names = sorted(atoms(a) | atoms(b))
    for vs in product(t["vals"], repeat=len(names)):
        env = dict(zip(names, vs))
        if t["ent"](val(a, env, t), val(b, env, t)) != 1:
            return False, env
    return True, None


x, y, z, p, q = (V(n) for n in "xyzpq")
SAMPLES = {n: [instance(n, x, y, z)] for n in ["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10", "A11"]}
SAMPLES["A5"] = [(C(x, y, z), C(C(x, y), z)), (C(x, y, z), C(x, C(y, z)))]
SAMPLES["A6"] = [(C(C(x, y), z), C(x, y, z)), (C(x, C(y, z)), C(x, y, z))]
SAMPLES["A9"].append((N(C(x, y, z)), W(N(x), N(y), N(z))))
SAMPLES["A10"].append((W(N(x), N(y), N(z)), N(C(x, y, z))))

if __name__ == "__main__":
    for tn, t in TABLES.items():
        bad = [an for an, s in SAMPLES.items() if not all(valid(a, b, t)[0] for a, b in s)]
        print(tn, "не тавтологичны:", bad)
    print("R1", valid(W(p, C(N(q), q)), C(p, W(q, N(q))), TABLES["R1"]))
    print("R2", valid(p, p, TABLES["R2"]))
    print("R3", valid(p, C(p, p), TABLES["R3"]))
