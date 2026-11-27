"""Системы ослабленного следования гл. 3 «Комплексной логики»: S² (§ 1, с. 49), S₂ (§ 4, с. 52), S₂¹ (§ 6, с. 55–58).

Формулы — кортежи s1.py / s1w.py: ('v', n), ('neg', A), ('conj', …), ('dis', …) — «:», ('wdis', …) — «∨».

S² = схемы S¹ (A1–A11, с. 15–17) + A15 ∼x ⊢ ∼(xy); R1 применимо, только если в x, y и z его применения входит
по крайней мере одно одинаковое элементарное высказывание (ограничение Г. А. Смирнова, с. 49).
S₂ = схемы S₁ (A1–A11, с. 36–37) + A12 — в том виде, в каком она применяется в доказательстве на с. 54:
x ⊢ x ∨ y; R1 — с тем же ограничением (с. 52).
Критерий доказуемости в S², S₂ (Sʷ): тавтология и в посылке и заключении есть общее элементарное высказывание
(гл. 3, § 2, MT1, с. 49; § 3, MT4, с. 52).
"""
from itertools import product

import s1
import s1w
from s1 import C, D, N, V, atoms  # noqa: F401
from s1w import W  # noqa: F401


# ---------- значения и критерии ----------
def value(f, env):
    return s1w.value(f, env)


def rows(*fs):
    names = sorted(set().union(*(atoms(f) for f in fs)))
    for v in product((0, 1), repeat=len(names)):
        yield dict(zip(names, v))


def taut(a, b):
    return all(not (value(a, e) and not value(b, e)) for e in rows(a, b))


def is_taut(f):
    return all(value(f, e) for e in rows(f))


def is_contra(f):
    return not any(value(f, e) for e in rows(f))


def counter(a, b):
    for e in rows(a, b):
        if value(a, e) and not value(b, e):
            return e
    return None


def common(a, b):
    return atoms(a) & atoms(b)


def weak(a, b):
    """Доказуемость в Sʷ (S², S₂): тавтология и общее элементарное высказывание."""
    return taut(a, b) and bool(common(a, b))


def strong(a, b):
    """Доказуемость в Sˢ (S¹, S₁): тавтология и в заключении нет новых элементарных высказываний."""
    return taut(a, b) and atoms(b) <= atoms(a)


def env_text(e):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(e.items()))


def letters(s):
    return ", ".join(f"${t}$" for t in sorted(s))


# ---------- схемы ----------
def is_a15(a, b):
    return (a[0] == "neg" and b[0] == "neg" and b[1][0] == "conj" and len(b[1][1]) == 2 and b[1][1][0] == a[1])


def is_a12(a, b):
    return b[0] == "wdis" and len(b[1]) == 2 and b[1][0] == a


def axiom_S2(a, b):
    """Схема S², которой соответствует a ⊢ b (A1–A11 S¹ или A15), или None."""
    if is_a15(a, b):
        return "A15"
    return s1.axiom(a, b)


def axiom_S_2(a, b):
    """Схема S₂ (A1–A11 S₁ или A12 в виде x ⊢ x ∨ y), или None."""
    if is_a12(a, b):
        return "A12"
    return s1w.axiom(a, b)


def check(lines, system="S2", restrict=True):
    """Проверка вывода в S² (system='S2') или S₂ (system='S_2').
    lines: [(посылка, заключение, основание)]; основание — 'A3', ('R1', i, j), ('R2', i, j), ('R3', i, j)
    или 'TW' — ссылка на критерий доказуемости в Sʷ (тавтология + общее элементарное высказывание),
    'TS' — на полноту S¹/S₁ (сильная тавтология). Возвращает список ошибок."""
    ax = axiom_S2 if system == "S2" else axiom_S_2
    errs = []
    for n, (a, b, why) in enumerate(lines, 1):
        if isinstance(why, str):
            if why == "TW":
                if not weak(a, b):
                    errs.append(f"шаг {n}: не теорема Sʷ")
            elif why == "TS":
                if not strong(a, b):
                    errs.append(f"шаг {n}: не сильная тавтология")
            elif ax(a, b) != why:
                errs.append(f"шаг {n}: не аксиома {why}")
            continue
        r, i, j = why
        if not (1 <= i < n and 1 <= j < n):
            errs.append(f"шаг {n}: ссылка вперёд")
            continue
        (a1, b1, _), (a2, b2, _) = lines[i - 1], lines[j - 1]
        ok = {"R1": b1 == a2 and a == a1 and b == b2,
              "R2": a1 == a2 == a and b == C(b1, b2),
              "R3": a1 == b2 and b1 == a2 and s1.replaceable(a, b, a1, b1) and (a != b or a1 == b1)}[r]
        if not ok:
            errs.append(f"шаг {n}: неверно применено {r}")
        elif r == "R1" and restrict and not (atoms(a1) & atoms(b1) & atoms(b2)):
            errs.append(f"шаг {n}: нарушено ограничение R1")
    return errs


def r1_common(lines, n):
    """Общие элементарные высказывания трёх высказываний применения R1 в строке n."""
    a, b, (r, i, j) = lines[n - 1]
    return atoms(lines[i - 1][0]) & atoms(lines[i - 1][1]) & atoms(lines[j - 1][1])


# ---------- S₂¹: ДНФ (с. 56) ----------
def lit(f):
    return f[0] == "v" or (f[0] == "neg" and f[1][0] == "v")


def is_dnf(f):
    """x¹ ∨ … ∨ xⁿ (n ≥ 1), каждое xⁱ — конъюнкция элементарных высказываний и их отрицаний (или одна литера)."""
    ms = f[1] if f[0] == "wdis" else (f,)
    return all(lit(m) or (m[0] == "conj" and all(lit(t) for t in m[1])) for m in ms)


def members(f):
    ms = f[1] if f[0] == "wdis" else (f,)
    return [frozenset(m[1]) if m[0] == "conj" else frozenset([m]) for m in ms]


def s21(a, b):
    """MT1–MT2 § 6 (с. 56–57) для формул в ДНФ: для каждого члена xⁱ найдётся yʲ, все составляющие которого — в xⁱ."""
    assert is_dnf(a) and is_dnf(b)
    xs, ys = members(a), members(b)
    return all(any(yj <= xi for yj in ys) for xi in xs)


def s21_map(a, b):
    """Для каждого xⁱ — номер подходящего yʲ (с 1) или None."""
    xs, ys = members(a), members(b)
    return [next((j for j, yj in enumerate(ys, 1) if yj <= xi), None) for xi in xs]
