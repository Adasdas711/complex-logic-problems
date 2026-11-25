"""Система S¹ (гл. 1, § 1, с. 15–17): формулы, аксиомные схемы, правила вывода, проверка выводов.

Формула: ('v', 'x') — элементарное высказывание; ('neg', A); ('conj', (A, B, ...)); ('dis', (A, B, ...)) — сильная
дизъюнкция «:». Запись — по соглашению книги (с. 15): конъюнкция без знака и связывает сильнее дизъюнкции,
обе сильнее знака следования; отрицание относится к ближайшему высказыванию.

Реализованы схемы A1–A11 (A5, A6, A11 — перестановка скобок; A9, A10 — для n = 2).
A12 не реализована. A13 и A14 не используются: частный вид A13 на с. 17 не согласуется с общим видом (опечатка).
"""
from __future__ import annotations

from itertools import product


def V(n): return ("v", n)
def N(a): return ("neg", a)
def C(*a): return ("conj", tuple(a))
def D(*a): return ("dis", tuple(a))


def tex(f, ctx="top") -> str:
    k = f[0]
    if k == "v":
        return f[1]
    if k == "neg":
        a = f[1]
        inner = tex(a, "neg")
        return f"\\sim {inner}" if a[0] in ("v", "neg") else f"\\sim({tex(a)})"
    if k == "conj":
        parts = []
        for a in f[1]:
            s = tex(a, "conj")
            if a[0] in ("conj", "dis"):
                s = f"({tex(a)})"
            parts.append(s)
        out = "".join(p if i == 0 else (" " + p if parts[i - 1][-1].isalnum() and p[0].isalnum() else p)
                      for i, p in enumerate(parts))
        out = " ".join(parts) if any(" " in p for p in parts) else out
        out = "".join(parts) if all(len(a[0]) and a[0] in ("v", "neg", "conj", "dis") for a in f[1]) else out
        return f"({out})" if ctx == "neg" else out
    if k == "dis":
        parts = [f"({tex(a)})" if a[0] == "dis" else tex(a, "dis") for a in f[1]]
        out = " : ".join(parts)
        return f"({out})" if ctx in ("conj", "neg") else out
    raise ValueError(k)


def ftex(a, b) -> str:
    return f"{tex(a)} \\vdash {tex(b)}"


def atoms(f) -> set:
    if f[0] == "v":
        return {f[1]}
    if f[0] == "neg":
        return atoms(f[1])
    return set().union(*(atoms(a) for a in f[1]))


def value(f, env) -> int:
    k = f[0]
    if k == "v":
        return env[f[1]]
    if k == "neg":
        return 1 - value(f[1], env)
    if k == "conj":
        return int(all(value(a, env) for a in f[1]))
    return int(sum(value(a, env) for a in f[1]) == 1)


def tautology(a, b) -> bool:
    """x ⊢ y — тавтология при главной интерпретации (гл. 1, § 5, с. 22)."""
    names = sorted(atoms(a) | atoms(b))
    for vals in product((0, 1), repeat=len(names)):
        env = dict(zip(names, vals))
        if value(a, env) == 1 and value(b, env) == 0:
            return False
    return True


def leaves(f, k):
    """Члены, получаемые раскрытием скобок операции k (для A5, A6, A11)."""
    if f[0] != k:
        return [f]
    out = []
    for a in f[1]:
        out += leaves(a, k)
    return out


def is_rebracketing(flat, other, k) -> bool:
    return (flat[0] == k and other[0] == k and all(a[0] != k for a in flat[1])
            and leaves(other, k) == list(flat[1]) and other != flat)


def axiom(a, b) -> str | None:
    """Название аксиомной схемы, которой соответствует a ⊢ b (A1–A11), или None."""
    if b == N(N(a)):
        return "A1"
    if a == N(N(b)):
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
    if a[0] == "neg" and a[1][0] == "conj" and len(a[1][1]) == 2:
        x, y = a[1][1]
        if b == D(C(N(x), y), C(x, N(y)), C(N(x), N(y))):
            return "A7"
    if b[0] == "neg" and b[1][0] == "conj" and len(b[1][1]) == 2:
        x, y = b[1][1]
        if a == D(C(N(x), y), C(x, N(y)), C(N(x), N(y))):
            return "A8"
    if a[0] == "neg" and a[1][0] == "dis" and len(a[1][1]) == 2:
        x, y = a[1][1]
        if b == D(C(x, y), C(N(x), N(y))):
            return "A9"
    if b[0] == "neg" and b[1][0] == "dis" and len(b[1][1]) == 2:
        x, y = b[1][1]
        if a == D(C(x, y), C(N(x), N(y))):
            return "A10"
    if is_rebracketing(a, b, "dis"):
        return "A11"
    return None


AXIOM_TEXT = {
    "A1": "x \\vdash \\sim\\sim x", "A2": "\\sim\\sim x \\vdash x", "A3": "xy \\vdash x", "A4": "xy \\vdash yx",
    "A7": "\\sim(xy) \\vdash \\sim x y : x \\sim y : \\sim x \\sim y",
    "A8": "\\sim x y : x \\sim y : \\sim x \\sim y \\vdash \\sim(xy)",
    "A9": "\\sim(x : y) \\vdash xy : \\sim x \\sim y", "A10": "xy : \\sim x \\sim y \\vdash \\sim(x : y)",
}


def instance(name, x, y=None):
    return {"A1": (x, N(N(x))), "A2": (N(N(x)), x), "A3": (C(x, y), x), "A4": (C(x, y), C(y, x)),
            "A7": (N(C(x, y)), D(C(N(x), y), C(x, N(y)), C(N(x), N(y)))),
            "A8": (D(C(N(x), y), C(x, N(y)), C(N(x), N(y))), N(C(x, y))),
            "A9": (N(D(x, y)), D(C(x, y), C(N(x), N(y)))),
            "A10": (D(C(x, y), C(N(x), N(y))), N(D(x, y)))}[name]


def replaceable(z, v, x, y) -> bool:
    """v получается из z заменой некоторых (не обязательно всех) вхождений x на y (R3)."""
    if z == v:
        return True
    if z == x and v == y:
        return True
    if z[0] != v[0] or z[0] == "v":
        return False
    if z[0] == "neg":
        return replaceable(z[1], v[1], x, y)
    return len(z[1]) == len(v[1]) and all(replaceable(a, b, x, y) for a, b in zip(z[1], v[1]))


def check(lines) -> list[str]:
    """Проверка вывода. lines: [(посылка, заключение, основание)], основание: 'A4' или ('R1', i, j) (номера с 1).
    Возвращает список ошибок (пустой — вывод верен)."""
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


# ---- § 2: теоремные схемы T1–T7 (с. 18) как готовые леммы ----
def lemma(a, b) -> str | None:
    if a[0] == "conj" and len(a[1]) == 2 and b == a[1][1]:
        return "T1"                                   # xy ⊢ y
    if a == b:
        return "T2"                                   # x ⊢ x
    if b == C(a, a):
        return "T3"                                   # x ⊢ xx
    if a[0] == "conj" and len(a[1]) == 2 and a[1][0] == a[1][1] == b:
        return "T4"                                   # xx ⊢ x
    if a[0] == "dis" and len(a[1]) == 2 and b == D(a[1][1], a[1][0]):
        return "T6"                                   # x : y ⊢ y : x
    return None


def is_lemma(a, b, name) -> bool:
    """Соответствует ли a ⊢ b именно схеме name (одна формула может подходить под несколько схем)."""
    two = a[0] == "conj" and len(a[1]) == 2
    return {"T1": two and b == a[1][1], "T2": a == b, "T3": b == C(a, a),
            "T4": two and a[1][0] == a[1][1] == b, "T5": two and b == C(a[1][1], a[1][0]),
            "T6": a[0] == "dis" and len(a[1]) == 2 and b == D(a[1][1], a[1][0]),
            "T7": a[0] == "dis" and len(a[1]) == 2 and b == D(a[1][1], a[1][0])}.get(name, False)


LEMMA_TEXT = {"T1": "xy \\vdash y", "T2": "x \\vdash x", "T3": "x \\vdash xx", "T4": "xx \\vdash x",
              "T5": "yx \\vdash xy", "T6": "x : y \\vdash y : x", "T7": "y : x \\vdash x : y"}


def check2(lines) -> list[str]:
    """Как check, но основанием может быть и теоремная схема T1–T7 (§ 2)."""
    errs = []
    for n, (a, b, why) in enumerate(lines, 1):
        if isinstance(why, str):
            ok = axiom(a, b) == why or is_lemma(a, b, why)
            if not ok:
                errs.append(f"шаг {n}: не {why}")
            continue
        errs += [e for e in check(lines[:n])[-1:] if e.startswith(f"шаг {n}:")]
    return errs


# ---- § 4, 5, 7: критерий доказуемости ----
def new_atoms(a, b) -> set:
    return atoms(b) - atoms(a)


def strong_tautology(a, b) -> bool:
    """D1 § 7 (с. 25): тавтология и в b нет элементарных высказываний, отсутствующих в a."""
    return tautology(a, b) and not new_atoms(a, b)


def counterexample(a, b):
    names = sorted(atoms(a) | atoms(b))
    for vals in product((0, 1), repeat=len(names)):
        env = dict(zip(names, vals))
        if value(a, env) == 1 and value(b, env) == 0:
            return env
    return None


# ---- § 3: сокращения ----
def IMP(x, y): return D(C(x, y), C(N(x), y), C(N(x), N(y)))     # D1: x ⊃ y
def OR(x, y): return N(C(N(x), N(y)))                            # D2: x ∨ y
