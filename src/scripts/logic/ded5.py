"""Выводы в системах общей теории дедукции (гл. 5 «Комплексной логики»): S^s в форме S₁, S⁵, S⁶, S^s_n.

Формулы — кортежи s1.py/s1w.py: ('v', n), ('neg', A), ('conj', …), ('wdis', …) — «∨», ('dis', …) — «:»;
для неклассического случая (гл. 5, § 5, с. 75–77) — ('nn', n) = ⌝n и ('qq', n) = ?n, где n — буква-высказывание
с главным оператором ←, ∀, ∃ или → (дополнение к определению высказывания, с. 76).

Строка вывода: (a, b, why): a ⊢ b, или (None, b, why): ⊢ b. Основания:
  'A1'…'A11'      — аксиомные схемы S₁ (гл. 2, § 1, с. 36);
  'An1'…'An7'     — дополнительные схемы § 5 гл. 5 (с. 76–77); An7 — только классический случай;
  'Ad1'           — ⊢ ∼(∼xx) (гл. 4, § 3, с. 67);
  'Ts'            — теорема S^s: подстановка высказываний в сильную тавтологию (MT1 § 2 гл. 5, с. 72;
                    правило подстановки MT1 § 9 гл. 1, с. 35); ⌝n и ?n при этом — отдельные высказывания;
  ('R1'|'R2'|'R3', i, j) — правила S¹ (с. 17): R3 — строка i: x ⊢ y, строка j: y ⊢ x, сама строка z ⊢ v;
  ('Rd1', i, j)   — i: x ⊢ y, j: ⊢ x  ⇒  ⊢ y (с. 67); ('Rd2', i, j) — i: x ⊢ y, j: ⊢ ∼y ⇒ ⊢ ∼x (с. 69);
  ('Rd3', i, j)   — ⊢ x, ⊢ y ⇒ ⊢ xy (с. 69); ('Rk1', i, j) — i: xz ⊢ y, j: ⊢ z ⇒ x ⊢ y (гл. 4, § 4, с. 69).
"""
from itertools import product

from s1 import C, D, N, V, replaceable  # noqa: F401
from s1w import W, axiom as ax_s1  # noqa: F401


def NN(n): return ("nn", n)
def QQ(n): return ("qq", n)


LEAF = ("v", "nn", "qq")


def tex(f):
    k = f[0]
    if k == "v":
        return f[1]
    if k == "nn":
        return f"\\urcorner {f[1]}"
    if k == "qq":
        return f"?{f[1]}"
    if k == "neg":
        a = f[1]
        return f"\\sim {tex(a)}" if a[0] in LEAF + ("neg",) else f"\\sim({tex(a)})"
    if k == "conj":
        return "".join(f"({tex(a)})" if a[0] in ("conj", "wdis", "dis") else tex(a) for a in f[1])
    sep = " \\vee " if k == "wdis" else " : "
    return sep.join(f"({tex(a)})" if a[0] in ("wdis", "dis") else tex(a) for a in f[1])


def ftex(a, b):
    return f"\\vdash {tex(b)}" if a is None else f"{tex(a)} \\vdash {tex(b)}"


# ---------- семантика ----------
def key(f):
    return {"v": "", "nn": "⌝", "qq": "?"}[f[0]] + f[1]


def letters(f):
    """Высказывания-листья: x, ⌝x, ?x — разные."""
    if f is None:
        return set()
    if f[0] in LEAF:
        return {key(f)}
    if f[0] == "neg":
        return letters(f[1])
    return set().union(*(letters(a) for a in f[1]))


def atoms(f):
    """Элементарные высказывания: в ⌝x и ?x входит то же, что в x (они образованы из x, с. 76)."""
    if f is None:
        return set()
    if f[0] in LEAF:
        return {f[1]}
    if f[0] == "neg":
        return atoms(f[1])
    return set().union(*(atoms(a) for a in f[1]))


def val(f, e):
    k = f[0]
    if k in LEAF:
        return e[key(f)]
    if k == "neg":
        return 1 - val(f[1], e)
    vs = [val(a, e) for a in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs)) if k == "wdis" else int(sum(vs) == 1)


def envs(*fs):
    names = sorted(set().union(*(letters(f) for f in fs if f is not None)))
    for bits in product((0, 1), repeat=len(names)):
        yield dict(zip(names, bits))


def taut2(a, b):
    """Тавтология при главной интерпретации; ⌝x, ?x — независимые высказывания."""
    return all(not ((a is None or val(a, e)) and not val(b, e)) for e in envs(a, b))


def counter2(a, b):
    for e in envs(a, b):
        if (a is None or val(a, e)) and not val(b, e):
            return e


def strong2(a, b):
    return a is not None and taut2(a, b) and letters(b) <= letters(a)


# неклассический случай: у каждой буквы одно из трёх состояний — 'a' (x истинно), 'n' (⌝x), 'q' (?x)
def val3(f, st):
    k = f[0]
    if k == "v":
        return int(st[f[1]] == "a")
    if k == "nn":
        return int(st[f[1]] == "n")
    if k == "qq":
        return int(st[f[1]] == "q")
    if k == "neg":
        return 1 - val3(f[1], st)
    vs = [val3(a, st) for a in f[1]]
    return int(all(vs)) if k == "conj" else int(any(vs)) if k == "wdis" else int(sum(vs) == 1)


def states(names, classical=False):
    for v in product("an" if classical else "anq", repeat=len(names)):
        yield dict(zip(names, v))


def taut3(a, b, classical=False):
    names = sorted(atoms(a) | atoms(b))
    return all(not ((a is None or val3(a, st)) and not val3(b, st)) for st in states(names, classical))


def counter3(a, b, classical=False):
    names = sorted(atoms(a) | atoms(b))
    for st in states(names, classical):
        if (a is None or val3(a, st)) and not val3(b, st):
            return st


ST_TEXT = {"a": "истинном {0}", "n": "истинном $\\urcorner {0}$", "q": "истинном $?{0}$"}


def st_text(st):
    return ", ".join(ST_TEXT[v].format(f"${k}$" if v == "a" else k) for k, v in sorted(st.items()))


# ---------- аксиомные схемы ----------
def an_inst(name, n):
    p, q, r = V(n), NN(n), QQ(n)
    return {"An1": (N(p), W(q, r)), "An2": (W(q, r), N(p)), "An3": (N(q), W(p, r)), "An4": (W(p, r), N(q)),
            "An5": (N(r), W(p, q)), "An6": (W(p, q), N(r)), "An7": (N(p), q)}[name]


AN_TEXT = {"An1": "\\sim x \\vdash \\urcorner x \\vee ?x", "An2": "\\urcorner x \\vee ?x \\vdash \\sim x",
           "An3": "\\sim\\urcorner x \\vdash x \\vee ?x", "An4": "x \\vee ?x \\vdash \\sim\\urcorner x",
           "An5": "\\sim ?x \\vdash x \\vee \\urcorner x", "An6": "x \\vee \\urcorner x \\vdash \\sim ?x",
           "An7": "\\sim x \\vdash \\urcorner x"}


def an_axiom(a, b):
    for n in sorted(atoms(a) | atoms(b)):
        for k in ("An1", "An2", "An3", "An4", "An5", "An6", "An7"):
            if an_inst(k, n) == (a, b):
                return k
    return None


def ad1(b):
    return b[0] == "neg" and b[1][0] == "conj" and len(b[1][1]) == 2 and b[1][1][0] == N(b[1][1][1])


SYSTEMS = {
    "S1": {"A", "R1", "R2", "R3"},
    "S5": {"A", "R1", "R2", "R3", "Ad1", "Rd1", "Rd2", "Rd3", "Ts"},
    "S6": {"A", "R1", "R2", "R3", "Ad1", "Rd1", "Rd2", "Rd3", "Ts", "Rk1"},
    "Sn": {"A", "R1", "R2", "R3", "An", "Ts"},
    "Sn7": {"A", "R1", "R2", "R3", "An", "An7", "Ts"},
}


def check(lines, system="S1"):
    """Список ошибок вывода (пустой — вывод верен)."""
    ok_set = SYSTEMS[system]
    errs = []
    for n, (a, b, why) in enumerate(lines, 1):
        if isinstance(why, str):
            if why.startswith("An"):
                fine = ("An" in ok_set and (why != "An7" or "An7" in ok_set) and a is not None
                        and an_axiom(a, b) == why)
            elif why == "Ad1":
                fine = "Ad1" in ok_set and a is None and ad1(b)
            elif why == "Ts":
                fine = "Ts" in ok_set and strong2(a, b)
            else:
                fine = a is not None and ax_s1(a, b) == why
            if not fine:
                errs.append(f"шаг {n}: не {why}")
            continue
        r, i, j = why
        if r not in ok_set or not (1 <= i < n and 1 <= j < n):
            errs.append(f"шаг {n}: {r} недопустимо")
            continue
        (a1, b1, _), (a2, b2, _) = lines[i - 1], lines[j - 1]
        if r in ("R1", "R2", "R3"):
            if a1 is None or a2 is None or a is None:
                errs.append(f"шаг {n}: неверно применено {r}")
                continue
            fine = {"R1": b1 == a2 and a == a1 and b == b2,
                    "R2": a1 == a2 == a and b == C(b1, b2),
                    "R3": a1 == b2 and b1 == a2 and replaceable(a, b, a1, b1) and (a != b or a1 == b1)}[r]
        elif r == "Rd1":
            fine = a is None and a1 is not None and a2 is None and b2 == a1 and b == b1
        elif r == "Rd2":
            fine = a is None and a1 is not None and a2 is None and b2 == N(b1) and b == N(a1)
        elif r == "Rd3":
            fine = a is None and a1 is None and a2 is None and b == C(b1, b2)
        elif r == "Rk1":
            fine = (a is not None and a1 is not None and a2 is None and a1[0] == "conj" and len(a1[1]) == 2
                    and a1[1][0] == a and a1[1][1] == b2 and b1 == b)
        else:
            fine = False
        if not fine:
            errs.append(f"шаг {n}: неверно применено {r}")
    return errs


def why_tex(w):
    if isinstance(w, str):
        if w.startswith("An"):
            return f"$A^n{w[2:]}$"
        if w == "Ad1":
            return "$A^d1$"
        if w == "Ts":
            return "$S^s$"
        return w
    r, i, j = w
    rt = {"Rd1": "$R^d1$", "Rd2": "$R^d2$", "Rd3": "$R^d3$", "Rk1": "$R^k1$"}.get(r, r)
    return f"{rt}: {i}, {j}"


def show(lines):
    return "\n".join(f"{n}. ${ftex(a, b)}$ [{why_tex(w)}]" for n, (a, b, w) in enumerate(lines, 1))


def show_hidden(lines, hide_why, hide_f):
    return "\n".join(f"{n}. {'…' if n in hide_f else '$' + ftex(a, b) + '$'} [{'…' if n in hide_why else why_tex(w)}]"
                     for n, (a, b, w) in enumerate(lines, 1))


if __name__ == "__main__":
    x = V("x")
    T2 = [(N(x), W(NN("x"), QQ("x")), "An1"), (W(NN("x"), QQ("x")), N(x), "An2"), (x, N(N(x)), "A2"),
          (N(N(x)), N(W(NN("x"), QQ("x"))), ("R3", 1, 2)), (x, N(W(NN("x"), QQ("x"))), ("R1", 3, 4)),
          (N(W(NN("x"), QQ("x"))), C(N(NN("x")), N(QQ("x"))), "Ts"), (x, C(N(NN("x")), N(QQ("x"))), ("R1", 5, 6)),
          (C(N(NN("x")), N(QQ("x"))), N(NN("x")), "A3"), (x, N(NN("x")), ("R1", 7, 8))]
    print(check(T2, "Sn"), check(T2, "S1"))
    print(show(T2))
    print([taut3(*an_inst(k, "x")) for k in ("An1", "An2", "An3", "An4", "An5", "An6")], taut3(*an_inst("An7", "x")),
          taut3(*an_inst("An7", "x"), classical=True))
