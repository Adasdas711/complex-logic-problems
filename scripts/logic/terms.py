"""Термины и высказывания по «Комплексной логике» (1970), Введение, § 4 (с. 5–6).

Выражение строится из узлов; classify() определяет, субъект оно или предикат (или ни то ни другое)
и по какому пункту определений D1 (предикат) и D2 (субъект). latex() и reading() дают запись и чтение.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Atom:
    name: str
    kind: str          # 'S' — простой субъект, 'P' — простой предикат, 'X' — высказывание


@dataclass(frozen=True)
class Op:
    op: str            # neg, opp, conj, disj, each, some, tuple, fact, such, asuch, name
    args: tuple


def S(n): return Atom(n, "S")
def P(n): return Atom(n, "P")
def X(n): return Atom(n, "X")
def neg(a): return Op("neg", (a,))
def opp(a): return Op("opp", (a,))
def conj(*a): return Op("conj", a)
def disj(*a): return Op("disj", a)
def each(*a): return Op("each", a)
def some(*a): return Op("some", a)
def tup(*a): return Op("tuple", a)
def fact(x): return Op("fact", (x,))
def such(x): return Op("such", (x,))
def asuch(a, x): return Op("asuch", (a, x))
def name(a): return Op("name", (a,))


def kinds(e) -> set:
    """Множество из 'S' (субъект), 'P' (предикат), 'X' (высказывание); пустое — не термин."""
    if isinstance(e, Atom):
        return {e.kind}
    k = [kinds(a) for a in e.args]
    o = e.op
    if o in ("neg", "opp"):
        return k[0] & {"S", "P"}
    if o in ("conj", "disj", "each", "some"):
        if len(k) < 2:
            return set()
        return {t for t in ("S", "P") if all(t in x for x in k)}
    if o == "tuple":
        return {"S"} if len(k) >= 2 and all("S" in x for x in k) else set()
    if o == "fact":
        return {"S"} if "X" in k[0] else set()
    if o == "such":
        return {"P"} if "X" in k[0] else set()
    if o == "asuch":
        return (k[0] & {"S", "P"}) if "X" in k[1] else set()
    if o == "name":
        return {"S"} if k[0] else set()
    raise ValueError(o)


# Пункты определений, по которым получается выражение данного вида.
POINT = {"P": {"neg": 2, "opp": 2, "conj": 3, "disj": 3, "each": 4, "some": 4, "such": 5, "asuch": 6},
         "S": {"neg": 2, "opp": 2, "conj": 3, "disj": 3, "each": 4, "some": 4, "tuple": 5, "fact": 6,
               "asuch": 7, "name": 8}}


def verdict(e) -> str:
    k = kinds(e)
    if not k or k == {"X"}:
        return "не термин" if k != {"X"} else "высказывание"
    word = {"S": "субъект", "P": "предикат"}
    return " и ".join(word[t] for t in ("S", "P") if t in k)


def point(e) -> str:
    """Ссылка на пункт определения для верхнего уровня выражения."""
    k = kinds(e)
    if isinstance(e, Atom):
        return {"S": "D2, п. 1", "P": "D1, п. 1", "X": "дано"}[e.kind]
    refs = [f"D{1 if t == 'P' else 2}, п. {POINT[t][e.op]}" for t in ("P", "S") if t in k and e.op in POINT[t]]
    return "; ".join(refs)


def why_not(e) -> str:
    """Почему выражение не термин (для верхнего уровня)."""
    o, k = e.op, [kinds(a) for a in e.args]
    if o in ("conj", "disj", "each", "some"):
        return "члены должны быть все субъектами (D2, п. 3–4) или все предикатами (D1, п. 3–4), а здесь они разного вида или среди них есть не термины"
    if o == "tuple":
        return "в $(a^1, \\dots, a^n)$ все члены должны быть субъектами (D2, п. 5)"
    if o == "fact":
        return "$\\downarrow x$ — субъект, только если $x$ высказывание (D2, п. 6)"
    if o == "such":
        return "$x\\downarrow$ — предикат, только если $x$ высказывание (D1, п. 5)"
    if o == "asuch":
        return "в $a \\downarrow x$ справа должно стоять высказывание, а слева — термин (D1, п. 6; D2, п. 7)"
    if o in ("neg", "opp"):
        return "$\\sim$ и тильда применяются только к терминам (D1, п. 2; D2, п. 2)"
    if o == "name":
        return "в квадратные скобки берётся высказывание, субъект или предикат (D2, п. 8)"
    return ""


def latex(e, top=True) -> str:
    if isinstance(e, Atom):
        return e.name
    a = [latex(x, False) for x in e.args]
    o = e.op
    if o == "neg":
        return f"\\sim {a[0]}"
    if o == "opp":
        return f"\\tilde{{{a[0]}}}" if isinstance(e.args[0], Atom) else f"\\widetilde{{{a[0]}}}"
    if o == "conj":
        return "(" + " \\cdot ".join(a) + ")"
    if o == "disj":
        return "(" + " \\vee ".join(a) + ")"
    if o == "each":
        return "\\cdot\\,(" + ", ".join(a) + ")"
    if o == "some":
        return "\\vee(" + ", ".join(a) + ")"
    if o == "tuple":
        return "(" + ", ".join(a) + ")"
    if o == "fact":
        return f"\\downarrow {a[0]}"
    if o == "such":
        return f"{a[0]} \\downarrow"
    if o == "asuch":
        return f"{a[0]} \\downarrow {a[1]}"
    if o == "name":
        return f"[{a[0]}]"
    raise ValueError(o)


def reading(e) -> str:
    """Чтение по правилам § 4, с. 6 (для простых членов)."""
    if isinstance(e, Atom):
        return f"${e.name}$"
    a = [reading(x) for x in e.args]
    lst = ", ".join(a)
    texts = {
        "neg": lambda: f"предмет, не обозначаемый термином {a[0]}",
        "conj": lambda: f"предмет, обозначаемый каждым из терминов {lst}",
        "disj": lambda: f"предмет, обозначаемый по крайней мере одним из терминов {lst}",
        "each": lambda: f"каждый из предметов {lst}",
        "some": lambda: f"по крайней мере один из предметов {lst}",
        "opp": lambda: f"предмет не-{a[0]} (противоположный {a[0]})",
        "fact": lambda: f"тот факт, что {a[0]}",
        "such": lambda: f"такой, что {a[0]}",
        "asuch": lambda: f"{a[0]}, такой, что {a[1]}",
        "name": lambda: f"термин {a[0]}",
    }
    return texts[e.op]()


def parse_chain(e, depth=0) -> list[str]:
    """Пошаговое обоснование снизу вверх: строки «запись — вывод — пункт»."""
    lines = []
    if isinstance(e, Op):
        for x in e.args:
            lines += parse_chain(x, depth + 1)
    k = verdict(e)
    if isinstance(e, Atom):
        if e.kind != "X":
            lines.append(f"${latex(e)}$ — {k} (дано)")
    else:
        ref = point(e) if kinds(e) - {"X"} else why_not(e)
        lines.append(f"${latex(e)}$ — {k} ({ref})")
    seen, out = set(), []
    for l in lines:
        if l not in seen:
            seen.add(l)
            out.append(l)
    return out
