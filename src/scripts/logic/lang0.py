"""Язык Введения целиком: термины (§ 4, с. 5–6) и высказывания (§ 5, с. 7–8) с взаимной вложенностью.

В отличие от terms.py, где в термин входят только высказывания-буквы, здесь в термин может входить любое
высказывание (↓x, x↓, a↓x, [x]), а в высказывание — составные термины (в кванторной группе и в скобочном
субъекте основного высказывания). Местность (§ 5, с. 7) известна только у простых терминов (ARITY, по умолчанию 1)
и у скобочного субъекта (a¹, …, aⁿ) (n-местный); поэтому в основном высказывании субъект — простой или скобочный,
предикат — простой.

kind(e) — множество видов: 'S' субъект, 'P' предикат, 'X' высказывание; пустое — ни то, ни другое.
parse(e) — разбор снизу вверх: [(выражение, вид, основание)].
"""
from __future__ import annotations

from terms import Atom, Op, S, P, X, neg as tneg, opp, conj as tconj, disj as tdisj, each, some, tup, fact, such, \
    asuch, name  # noqa: F401
from statements import St, basic, neg as sneg, conj as sconj, sdis, wdis, forall, exists, cond  # noqa: F401

ARITY: dict[str, int] = {}

WORD = {"S": "субъект", "P": "предикат", "X": "высказывание"}
TPOINT = {"P": {"neg": 2, "opp": 2, "conj": 3, "disj": 3, "each": 4, "some": 4, "such": 5, "asuch": 6},
          "S": {"neg": 2, "opp": 2, "conj": 3, "disj": 3, "each": 4, "some": 4, "tuple": 5, "fact": 6,
                "asuch": 7, "name": 8}}
SPOINT = {"basic": "§ 5, D1", "neg": "§ 5, D2, п. 2", "conj": "§ 5, D2, п. 3", "sdis": "§ 5, D2, п. 3",
          "wdis": "§ 5, D2, п. 3", "quant": "§ 5, D2, п. 4", "cond": "§ 5, D2, п. 5"}


def arity(t):
    if isinstance(t, Atom) and t.kind in "SP":
        return ARITY.get(t.name, 1)
    if isinstance(t, Op) and t.op == "tuple":
        return len(t.args)
    return None


def kind(e) -> frozenset:
    if isinstance(e, Atom):
        return frozenset(e.kind)
    if isinstance(e, St):
        return frozenset("X") if is_stmt(e) else frozenset()
    k = [kind(a) for a in e.args]
    o = e.op
    if o in ("neg", "opp"):
        return k[0] & {"S", "P"}
    if o in ("conj", "disj", "each", "some"):
        return frozenset(t for t in "SP" if len(k) >= 2 and all(t in x for x in k))
    if o == "tuple":
        return frozenset("S") if len(k) >= 2 and all("S" in x for x in k) else frozenset()
    if o == "fact":
        return frozenset("S") if "X" in k[0] else frozenset()
    if o == "such":
        return frozenset("P") if "X" in k[0] else frozenset()
    if o == "asuch":
        return (k[0] & {"S", "P"}) if "X" in k[1] else frozenset()
    if o == "name":
        return frozenset("S") if k[0] else frozenset()
    raise ValueError(o)


def is_stmt(e) -> bool:
    if isinstance(e, Atom):
        return e.kind == "X"
    if not isinstance(e, St):
        return False
    o = e.op
    if o == "basic":
        a, b = e.args
        return ("S" in kind(a) and "P" in kind(b) and arity(a) is not None and arity(a) == arity(b))
    if o == "neg":
        return is_stmt(e.args[0])
    if o in ("conj", "sdis", "wdis"):
        return len(e.args) >= 2 and all(is_stmt(x) for x in e.args)
    if o == "quant":
        _, a, x = e.args
        return bool(kind(a) & {"S", "P"}) and is_stmt(x)
    if o == "cond":
        return all(is_stmt(x) for x in e.args)
    return False


def tex(e) -> str:
    if isinstance(e, Atom):
        return e.name
    if isinstance(e, Op):
        a = [tex(x) for x in e.args]
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
    o, m = e.op, e.mod
    if o == "basic":
        a, b = e.args
        mid = {"": " \\leftarrow ", "not": " \\urcorner\\!\\leftarrow ", "q": "? \\leftarrow "}[m]
        return f"({tex(a)}{mid}{tex(b)})"
    if o == "neg":
        return f"\\sim {tex(e.args[0])}"
    if o in ("conj", "sdis", "wdis"):
        sep = {"conj": " \\cdot ", "sdis": " : ", "wdis": " \\vee "}[o]
        return "(" + sep.join(tex(x) for x in e.args) + ")"
    if o == "quant":
        q, a, x = e.args
        pre = {"": "", "not": "\\urcorner", "q": "?"}[m]
        return f"({pre}{'\\forall' if q == 'A' else '\\exists'} {tex(a)})\\,{tex(x)}"
    if o == "cond":
        x, y = e.args
        mid = {"": " \\to ", "not": " \\urcorner\\!\\to ", "q": "? \\to "}[m]
        return f"({tex(x)}{mid}{tex(y)})"
    raise ValueError(o)


def verdict(e) -> str:
    k = kind(e)
    if not k:
        return "ни термин, ни высказывание"
    return " и ".join(WORD[t] for t in "SPX" if t in k)


def ref(e) -> str:
    """Пункт определения, по которому получено выражение (верхний уровень)."""
    if isinstance(e, Atom):
        return {"S": "§ 4, D2, п. 1", "P": "§ 4, D1, п. 1", "X": "дано"}[e.kind]
    if isinstance(e, St):
        return SPOINT[e.op]
    k = kind(e)
    return "; ".join(f"§ 4, D{1 if t == 'P' else 2}, п. {TPOINT[t][e.op]}" for t in "PS" if t in k and e.op in TPOINT[t])


def why_not(e) -> str:
    """Почему выражение (части которого уже разобраны) не термин и не высказывание."""
    if isinstance(e, St):
        o = e.op
        if o == "basic":
            a, b = e.args
            if "S" not in kind(a):
                return "слева в основном высказывании должен стоять субъект (§ 5, D1)"
            if "P" not in kind(b):
                return "справа в основном высказывании должен стоять предикат (§ 5, D1)"
            return "местность субъекта и предиката должна совпадать (§ 5, D1)"
        if o == "neg":
            return "$\\sim$ образует высказывание только из высказывания (§ 5, D2, п. 2)"
        if o in ("conj", "sdis", "wdis"):
            return "все члены должны быть высказываниями (§ 5, D2, п. 3)"
        if o == "quant":
            _, a, x = e.args
            if not kind(a) & {"S", "P"}:
                return "в кванторной группе должен стоять термин (§ 5, D2, п. 4)"
            return "после кванторной группы должно стоять высказывание (§ 5, D2, п. 4)"
        if o == "cond":
            return "обе части должны быть высказываниями (§ 5, D2, п. 5)"
    o = e.op
    if o in ("conj", "disj", "each", "some"):
        return "члены должны быть либо все субъектами (§ 4, D2, п. 3–4), либо все предикатами (§ 4, D1, п. 3–4)"
    if o == "tuple":
        return "в $(a^1, \\ldots, a^n)$ все члены должны быть субъектами (§ 4, D2, п. 5)"
    if o == "fact":
        return "$\\downarrow x$ — субъект, только если $x$ — высказывание (§ 4, D2, п. 6)"
    if o == "such":
        return "$x \\downarrow$ — предикат, только если $x$ — высказывание (§ 4, D1, п. 5)"
    if o == "asuch":
        return "в $a \\downarrow x$ слева должен стоять термин, справа — высказывание (§ 4, D1, п. 6; D2, п. 7)"
    if o in ("neg", "opp"):
        return "$\\sim$ и тильда образуют термин только из термина (§ 4, D1, п. 2; D2, п. 2)"
    if o == "name":
        return "в квадратные скобки берётся высказывание, субъект или предикат (§ 4, D2, п. 8)"
    return ""


def children(e):
    if isinstance(e, Atom):
        return []
    if isinstance(e, St) and e.op == "quant":
        return [e.args[1], e.args[2]]
    return list(e.args)


def parse(e, atoms=True) -> list:
    """Разбор снизу вверх без повторов: [(выражение, вердикт, основание)]."""
    out, seen = [], set()

    def go(f):
        for c in children(f):
            go(c)
        if isinstance(f, Atom) and not atoms:
            return
        key = tex(f)
        if key in seen:
            return
        seen.add(key)
        k = kind(f)
        out.append((f, verdict(f), ref(f) if k else why_not(f)))
    go(e)
    return out


def size(e) -> int:
    return 1 + sum(size(c) for c in children(e))


def depth(e) -> int:
    return 1 + max((depth(c) for c in children(e)), default=0)


def ops(e) -> list:
    """Все узлы-операции (с повторами) — для подсчёта вхождений операторов."""
    out = [] if isinstance(e, Atom) else [e]
    for c in children(e):
        out += ops(c)
    return out


def parts(e) -> list:
    """Все подвыражения с повторами (вхождения)."""
    out = [e]
    for c in children(e):
        out += parts(c)
    return out


def occurring(e, what):
    """Различные термины ('T') или высказывания ('X'), входящие в e (§ 7, D1): графические части нужного вида."""
    seen, out = set(), []
    for f in parts(e):
        k = kind(f)
        ok = ("X" in k) if what == "X" else bool(k & {"S", "P"})
        if ok and tex(f) not in seen:
            seen.add(tex(f))
            out.append(f)
    return out


def count_occ(e, f) -> int:
    return sum(1 for g in parts(e) if g == f)


# ---------- формулы следования (§ 8) ----------
class Ent:
    """x ⊢ y (a задан) или ⊢ y (a = None)."""
    __slots__ = ("a", "b")

    def __init__(self, a, b):
        self.a, self.b = a, b

    def __eq__(self, o):
        return isinstance(o, Ent) and self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash(("ent", self.a, self.b))


def etex(f, top=True) -> str:
    if isinstance(f, Ent):
        s = (f"{etex(f.a, False)} \\vdash {etex(f.b, False)}" if f.a is not None else f"\\vdash {etex(f.b, False)}")
        return s if top else f"({s})"
    return tex(f)


def transcribe(f) -> str:
    """Запись по § 4–5 в форме с. 10: x ⊢ y — ([x], [y] ← (⊢)); ⊢ x — ([x] ← (⊢))."""
    if isinstance(f, Ent):
        if f.a is None:
            return f"([{transcribe(f.b)}] \\leftarrow (\\vdash))"
        return f"([{transcribe(f.a)}], [{transcribe(f.b)}] \\leftarrow (\\vdash))"
    return tex(f)


def turnstiles(f) -> int:
    if isinstance(f, Ent):
        return 1 + (turnstiles(f.a) if f.a is not None else 0) + turnstiles(f.b)
    return 0
