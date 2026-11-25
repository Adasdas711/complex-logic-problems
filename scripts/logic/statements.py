"""Высказывания и формулы следования по «Комплексной логике» (1970), Введение, § 5, 7, 8 (с. 7–11).

Термины — из terms.py. Простые субъекты и предикаты имеют заданную местность (по умолчанию 1);
скобочный субъект (a¹,…,aⁿ) — n-местный (§ 5, с. 7). Местность составных терминов книга не определяет,
поэтому в основных высказываниях используются только простые термины и скобочные субъекты.
"""
from __future__ import annotations

from dataclasses import dataclass

from terms import Atom, Op, kinds, latex as tlatex

ARITY: dict[str, int] = {}          # местность простых терминов: имя -> n


@dataclass(frozen=True)
class St:
    op: str      # basic, neg, conj, sdis, wdis, quant, cond
    args: tuple
    mod: str = ""   # для basic/quant/cond: "" | "not" | "q";  для quant: "A"/"E" в args[0]


def basic(a, b, mod=""): return St("basic", (a, b), mod)
def neg(x): return St("neg", (x,))
def conj(*x): return St("conj", x)
def sdis(*x): return St("sdis", x)
def wdis(*x): return St("wdis", x)
def forall(a, x, mod=""): return St("quant", ("A", a, x), mod)
def exists(a, x, mod=""): return St("quant", ("E", a, x), mod)
def cond(x, y, mod=""): return St("cond", (x, y), mod)


def arity(t):
    if isinstance(t, Atom):
        return ARITY.get(t.name, 1)
    if t.op == "tuple":
        return len(t.args)
    return None


def is_stmt(e) -> bool:
    if isinstance(e, Atom):
        return e.kind == "X"
    if not isinstance(e, St):
        return False
    o = e.op
    if o == "basic":
        a, b = e.args
        return "S" in kinds(a) and "P" in kinds(b) and arity(a) is not None and arity(a) == arity(b)
    if o == "neg":
        return is_stmt(e.args[0])
    if o in ("conj", "sdis", "wdis"):
        return len(e.args) >= 2 and all(is_stmt(x) for x in e.args)
    if o == "quant":
        _, a, x = e.args
        return bool(kinds(a) & {"S", "P"}) and is_stmt(x)
    if o == "cond":
        return all(is_stmt(x) for x in e.args)
    return False


def why_not(e) -> str:
    o = e.op
    if o == "basic":
        a, b = e.args
        if "S" not in kinds(a) or "P" not in kinds(b):
            return "в основном высказывании слева должен стоять субъект, справа — предикат (§ 5, D1)"
        return "местность субъекта и предиката должна совпадать (§ 5, D1)"
    if o == "neg":
        return "$\\sim$ ставится перед высказыванием (§ 5, D2, п. 2)"
    if o in ("conj", "sdis", "wdis"):
        return "все члены должны быть высказываниями (§ 5, D2, п. 3)"
    if o == "quant":
        return "в кванторном высказывании после кванторной группы с термином должно стоять высказывание (§ 5, D2, п. 4)"
    if o == "cond":
        return "обе части условного высказывания должны быть высказываниями (§ 5, D2, п. 5)"
    return ""


POINT = {"basic": "D1", "neg": "D2, п. 2", "conj": "D2, п. 3", "sdis": "D2, п. 3", "wdis": "D2, п. 3",
         "quant": "D2, п. 4", "cond": "D2, п. 5"}


def latex(e) -> str:
    if isinstance(e, Atom) or isinstance(e, Op):
        return tlatex(e)
    o, m = e.op, e.mod
    if o == "basic":
        a, b = e.args
        mid = {"": " \\leftarrow ", "not": " \\urcorner\\!\\leftarrow ", "q": "? \\leftarrow "}[m]
        return f"({tlatex(a)}{mid}{tlatex(b)})"
    if o == "neg":
        return f"\\sim {latex(e.args[0])}"
    if o in ("conj", "sdis", "wdis"):
        sep = {"conj": " \\cdot ", "sdis": " : ", "wdis": " \\vee "}[o]
        return "(" + sep.join(latex(x) for x in e.args) + ")"
    if o == "quant":
        q, a, x = e.args
        pre = {"": "", "not": "\\urcorner", "q": "?"}[m]
        return f"({pre}{'\\forall' if q == 'A' else '\\exists'} {tlatex(a)})\\,{latex(x)}"
    if o == "cond":
        x, y = e.args
        mid = {"": " \\to ", "not": " \\urcorner\\!\\to ", "q": "? \\to "}[m]
        return f"({latex(x)}{mid}{latex(y)})"
    raise ValueError(o)


def main_op(e) -> str:
    """Главный оператор по D3 (§ 5, с. 8); None, если высказывание не расчленено (буква)."""
    if isinstance(e, Atom):
        return None
    o = e.op
    if o == "neg" and main_op(e.args[0]) is None:
        return None
    if o == "neg":
        return main_op(e.args[0])
    return {"basic": "\\leftarrow", "conj": "\\cdot", "sdis": ":", "wdis": "\\vee",
            "cond": "\\to"}.get(o) or ("\\forall" if e.args[0] == "A" else "\\exists")


def main_op_point(e) -> str:
    o = e.op
    if o == "neg":
        return main_op_point(e.args[0]) + "; п. 5 (главный в $x$ главен и в $\\sim x$)"
    return {"basic": "п. 1", "conj": "п. 2", "sdis": "п. 2", "wdis": "п. 2", "quant": "п. 3", "cond": "п. 4"}[o]


def reading(e) -> str:
    """Чтение по § 5, с. 7–8 (для высказываний первого уровня с простыми частями)."""
    if isinstance(e, Atom):
        return f"${e.name}$"
    o, m = e.op, e.mod
    if o == "basic":
        a, b = (f"${tlatex(t)}$" for t in e.args)
        return {"": f"{a} имеет {b}", "not": f"{a} не имеет {b}", "q": f"{a} неопределённо имеет {b}"}[m]
    if o == "neg":
        return f"Не-{reading(e.args[0])}"
    parts = [reading(x) for x in e.args] if o in ("conj", "sdis", "wdis") else None
    if o == "conj":
        return " и ".join(parts)
    if o == "sdis":
        return "Либо " + ", либо ".join(parts)
    if o == "wdis":
        return " или ".join(parts)
    if o == "quant":
        q, a, x = e.args
        a, x = f"${tlatex(a)}$", reading(x)
        if m == "q":
            pos = f"({'\\forall' if q == 'A' else '\\exists'} {tlatex(a.strip('$'))})"
            neg_ = f"(\\urcorner{'\\forall' if q == 'A' else '\\exists'} {tlatex(a.strip('$'))})"
            return f"Неопределённо, ${pos}\\,{latex(e.args[2])}$ или ${neg_}\\,{latex(e.args[2])}$"
        return {("A", ""): f"Все {a} таковы, что {x}", ("E", ""): f"Некоторые {a} таковы, что {x}",
                ("A", "not"): f"Не все {a} таковы, что {x}", ("E", "not"): f"Нет таких {a}, что {x}"}[(q, m)]
    if o == "cond":
        x, y = (reading(t) for t in e.args)
        if m == "q":
            return f"Неопределённо, ${latex(cond(*e.args))}$ или ${latex(cond(*e.args, 'not'))}$"
        return {"": f"Если {x}, то {y}", "not": f"Признание {x} не обязывает признать {y}"}[m]
    raise ValueError(o)


def chain(e) -> list[str]:
    """Разбор снизу вверх: какие части — высказывания и по какому пункту."""
    out = []
    if isinstance(e, St):
        subs = [a for a in e.args if isinstance(a, St) or (isinstance(a, Atom) and a.kind == "X")]
        for s in subs:
            out += chain(s)
        if is_stmt(e):
            out.append(f"${latex(e)}$ — высказывание ({POINT[e.op]})")
        else:
            out.append(f"${latex(e)}$ — не высказывание: {why_not(e)}")
    elif isinstance(e, Atom) and e.kind == "X":
        out.append(f"${e.name}$ — высказывание (дано)")
    seen, res = set(), []
    for l in out:
        if l not in seen:
            seen.add(l)
            res.append(l)
    return res


def sub_statements(e) -> list:
    """Все высказывания, входящие в e (§ 7, D1): само e и его части-высказывания."""
    out = [e]
    if isinstance(e, St):
        for a in e.args:
            if isinstance(a, St) or (isinstance(a, Atom) and a.kind == "X"):
                out += sub_statements(a)
    seen, res = set(), []
    for x in out:
        if latex(x) not in seen:
            seen.add(latex(x))
            res.append(x)
    return res


def sub_terms(e) -> list:
    """Простые и составные термины, входящие в высказывание e (верхнего уровня термины и их части)."""
    def tparts(t):
        res = [t]
        if isinstance(t, Op):
            for a in t.args:
                if isinstance(a, Atom) and a.kind == "X":
                    continue
                res += tparts(a)
        return res
    out = []
    if isinstance(e, St):
        if e.op == "basic":
            for t in e.args:
                out += tparts(t)
        elif e.op == "quant":
            out += tparts(e.args[1])
            out += sub_terms(e.args[2])
        else:
            for a in e.args:
                out += sub_terms(a)
    seen, res = set(), []
    for t in out:
        if tlatex(t) not in seen:
            seen.add(tlatex(t))
            res.append(t)
    return res
