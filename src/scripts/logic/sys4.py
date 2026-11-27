"""Системы гл. 4 «Комплексной логики»: проверка выводов и шаги для построения выводов.

Формулы — кортежи s1.py / s1w.py: ('v', n), ('neg', A), ('conj', …), ('dis', …) — «:», ('wdis', …) — «∨».
Строка вывода — (посылка, заключение, основание); посылка None — формула вырожденного следования ⊢ x (D1 § 3).
Основание — имя схемы ('A3', 'A12', 'A**12', 'A15', 'Ad1') или правило: ('R1', i, j), ('R2', i, j), ('R3', i, j),
('R*5', i), ('Rd1', i, j), ('Rd2', i, j), ('Rd3', i, j), ('Rk1', i, j) — номера строк с 1, в порядке посылок правила.

Системы (страницы книги):
  S_3  — S₁ (гл. 2, с. 36–37) с ограничением A3: в y входят только элементарные высказывания x (с. 59, 61);
  S_4  — S_3 и A12 x ⊢ x ∨ y (с. 65);
  S_4* — S_4 без A3, A8, A11, с A**12 x ⊢ x(y ∨ ∼y) и правилом R*5 (с. 66);
  S^4  — S¹ (с. 15–17; схемы A1–A11) с ограничением A3 (S³, с. 59) и A15 ∼x ⊢ ∼(xy) (с. 62);
  S^5  — S^s (здесь S₁) и A^d1 ⊢ ∼(∼xx), R^d1, R^d2, R^d3 (с. 67, 70);
  S^6  — S^5 и R^k1: если xz ⊢ y и ⊢ z, то x ⊢ y (с. 70).
"""
from s1 import C, D, N, V, atoms, is_rebracketing, replaceable  # noqa: F401
import s1
import s1w
from s1w import W

W_SCHEMES = ["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9", "A10", "A11"]
SYSTEMS = {
    "S_3": dict(lang="w", schemes=W_SCHEMES, a3="restricted", rules={"R1", "R2", "R3"}),
    "S_1": dict(lang="w", schemes=W_SCHEMES, a3="free", rules={"R1", "R2", "R3"}),
    "S_4": dict(lang="w", schemes=W_SCHEMES + ["A12"], a3="restricted", rules={"R1", "R2", "R3"}),
    "S_4*": dict(lang="w", schemes=["A1", "A2", "A4", "A5", "A6", "A7", "A9", "A10", "A12", "A**12"], a3=None,
                 rules={"R1", "R2", "R3", "R*5"}),
    "S^4": dict(lang="c", schemes=["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9", "A10", "A11", "A15"],
                a3="restricted", rules={"R1", "R2", "R3"}),
    "S^3": dict(lang="c", schemes=["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9", "A10", "A11"],
                a3="restricted", rules={"R1", "R2", "R3"}),
    "S^5": dict(lang="w", schemes=W_SCHEMES + ["Ad1"], a3="free", rules={"R1", "R2", "R3", "Rd1", "Rd2", "Rd3"}),
    "S^6": dict(lang="w", schemes=W_SCHEMES + ["Ad1"], a3="free",
                rules={"R1", "R2", "R3", "Rd1", "Rd2", "Rd3", "Rk1"}),
}


def tex(f, lang="w"):
    return s1w.tex(f) if lang == "w" else s1.tex(f)


def ltex(a, b, lang="w"):
    return f"\\vdash {tex(b, lang)}" if a is None else f"{tex(a, lang)} \\vdash {tex(b, lang)}"


def conj2(f):
    return f[0] == "conj" and len(f[1]) == 2


def a3_shape(a, b):
    return a is not None and conj2(a) and b == a[1][0]


def a3_restricted(a, b, smirnov=False):
    """A3 xy ⊢ x с ограничением S³/S₃ (с. 59): в y только элементарные высказывания x; по Г. А. Смирнову —
    в x и y входят одинаковые элементарные высказывания."""
    if not a3_shape(a, b):
        return False
    x, y = a[1]
    return atoms(x) == atoms(y) if smirnov else atoms(y) <= atoms(x)


def is_w_inst(name, a, b):
    """Пример ли a ⊢ b схемы name системы S₁ (без ограничений)."""
    if a is None:
        return name == "Ad1" and b[0] == "neg" and conj2(b[1]) and b[1][1][0] == N(b[1][1][1])
    if name == "A1":
        return a == N(N(b))
    if name == "A2":
        return b == N(N(a))
    if name == "A3":
        return a3_shape(a, b)
    if name == "A4":
        return conj2(a) and b == C(a[1][1], a[1][0])
    if name == "A5":
        return is_rebracketing(a, b, "conj")
    if name == "A6":
        return is_rebracketing(b, a, "conj")
    if name in ("A7", "A8", "A9", "A10", "A11"):
        return s1w.axiom(a, b) == name
    if name == "A12":
        return b[0] == "wdis" and len(b[1]) == 2 and b[1][0] == a
    if name == "A**12":
        return conj2(b) and b[1][0] == a and b[1][1][0] == "wdis" and len(b[1][1][1]) == 2 and \
            b[1][1][1][1] == N(b[1][1][1][0])
    return False


def is_c_inst(name, a, b):
    """Пример ли a ⊢ b схемы name языка S¹ (A1–A11 по s1.axiom; A15)."""
    if a is None:
        return False
    if name == "A1":
        return b == N(N(a))
    if name == "A2":
        return a == N(N(b))
    if name == "A3":
        return a3_shape(a, b)
    if name == "A4":
        return conj2(a) and b == C(a[1][1], a[1][0])
    if name == "A5":
        return is_rebracketing(a, b, "conj")
    if name == "A6":
        return is_rebracketing(b, a, "conj")
    if name in ("A7", "A8", "A9", "A10", "A11"):
        return s1.axiom(a, b) == name
    if name == "A15":
        return a[0] == "neg" and b[0] == "neg" and conj2(b[1]) and b[1][1][0] == a[1]
    return False


def is_axiom(sysname, name, a, b):
    cfg = SYSTEMS[sysname]
    if name not in cfg["schemes"]:
        return False
    ok = (is_w_inst if cfg["lang"] == "w" else is_c_inst)(name, a, b)
    if ok and name == "A3" and cfg["a3"] == "restricted":
        ok = a3_restricted(a, b)
    return ok


def check(sysname, lines):
    """Список ошибок вывода (пустой — вывод верен)."""
    cfg = SYSTEMS[sysname]
    errs = []
    for n, (a, b, why) in enumerate(lines, 1):
        if isinstance(why, str):
            if not is_axiom(sysname, why, a, b):
                errs.append(f"шаг {n}: не аксиома {why}")
            continue
        r, refs = why[0], why[1:]
        if r not in cfg["rules"]:
            errs.append(f"шаг {n}: правила {r} нет в системе")
            continue
        if not all(1 <= i < n for i in refs):
            errs.append(f"шаг {n}: ссылка вперёд")
            continue
        L = [lines[i - 1] for i in refs]
        ok = False
        if r in ("R1", "R2", "R3"):
            (a1, b1, _), (a2, b2, _) = L
            if a is not None and a1 is not None and a2 is not None:
                ok = {"R1": b1 == a2 and a == a1 and b == b2,
                      "R2": a1 == a2 == a and b == C(b1, b2),
                      "R3": a1 == b2 and b1 == a2 and replaceable(a, b, a1, b1) and (a != b or a1 == b1)}[r]
        elif r == "R*5":
            (a1, b1, _), = L
            ok = (a is not None and a1 is not None and conj2(a) and a[1][0] == a1 and b == b1
                  and atoms(a[1][1]) <= atoms(b1))
        elif r == "Rd1":
            (a1, b1, _), (a2, b2, _) = L
            ok = a is None and a1 is not None and a2 is None and a1 == b2 and b == b1
        elif r == "Rd2":
            (a1, b1, _), (a2, b2, _) = L
            ok = a is None and a1 is not None and a2 is None and b2 == N(b1) and b == N(a1)
        elif r == "Rd3":
            (a1, b1, _), (a2, b2, _) = L
            ok = a is None and a1 is None and a2 is None and b == C(b1, b2)
        elif r == "Rk1":
            (a1, b1, _), (a2, b2, _) = L
            ok = a is not None and a1 is not None and a2 is None and a1 == C(a, b2) and b == b1
        if not ok:
            errs.append(f"шаг {n}: неверно применено {r}")
    return errs


def why_text(w):
    if isinstance(w, str):
        return {"Ad1": "$A^d1$", "A**12": "$A^{**}12$"}.get(w, w)
    name = {"R*5": "$R^*5$", "Rd1": "$R^d1$", "Rd2": "$R^d2$", "Rd3": "$R^d3$", "Rk1": "$R^k1$"}.get(w[0], w[0])
    return f"{name}: " + ", ".join(str(i) for i in w[1:])


def show(lines, lang="w", hide_why=(), hide_f=()):
    return "\n".join(f"{n}. {'…' if n in hide_f else '$' + ltex(a, b, lang) + '$'} "
                     f"[{'…' if n in hide_why else why_text(w)}]" for n, (a, b, w) in enumerate(lines, 1))


# ---------- семантика ----------
def value(f, env):
    return s1w.value(f, env)


def taut_line(a, b):
    if a is None:
        return all(value(b, e) for e in s1w.rows(b))
    return s1w.tautology(a, b)


# ---------- трёхзначные таблицы независимости S_3* (с. 62) ----------
def _t_a3_conj(vs):
    return 2 if 2 in vs else max(vs)


def _t_a3_dis(vs):
    return 2 if 2 in vs else min(vs)


TABLES = {
    # независимость A3 в S_3*: отмечено 1; x ⊢ y неотмеченное только при x ∈ {1, 2}, y = 3
    "A3": dict(conj=_t_a3_conj, wdis=_t_a3_dis, neg=lambda v: 2 if v == 3 else 3,
               ent=lambda a, b: not (a in (1, 2) and b == 3)),
    # независимость A*12: xy = 1 при x = y = 1, иначе 3; x ∨ y = 3 при x = y = 3, иначе 1; ∼x = 4 − x;
    # x ⊢ y равно 1 тогда и только тогда, когда x ≥ y
    "A*12": dict(conj=lambda vs: 1 if all(v == 1 for v in vs) else 3,
                 wdis=lambda vs: 3 if all(v == 3 for v in vs) else 1, neg=lambda v: 4 - v,
                 ent=lambda a, b: a >= b),
    # независимость R*3: xy = max; x ∨ y = 2 при x = y = 2, 3 при x = y = 3, иначе 1; ∼x = 3 при x = 1, иначе 1;
    # x ⊢ y неотмеченное только при x = 1, y ∈ {2, 3}
    "R*3": dict(conj=max, wdis=lambda vs: 2 if all(v == 2 for v in vs) else 3 if all(v == 3 for v in vs) else 1,
                neg=lambda v: 3 if v == 1 else 1, ent=lambda a, b: not (a == 1 and b in (2, 3))),
}


def tval(f, env, t):
    k = f[0]
    if k == "v":
        return env[f[1]]
    if k == "neg":
        return t["neg"](tval(f[1], env, t))
    vs = [tval(a, env, t) for a in f[1]]
    if len(vs) > 2:   # многочленные — попарно слева направо
        acc = vs[0]
        for v in vs[1:]:
            acc = t[k]([acc, v])
        return acc
    return t[k](vs)


def tcheck(a, b, t):
    """(отмеченное ли значение при всех значениях, первый набор с неотмеченным значением)."""
    from itertools import product
    names = sorted(atoms(a) | atoms(b))
    for vs in product((1, 2, 3), repeat=len(names)):
        e = dict(zip(names, vs))
        if not t["ent"](tval(a, e, t), tval(b, e, t)):
            return False, e
    return True, None
