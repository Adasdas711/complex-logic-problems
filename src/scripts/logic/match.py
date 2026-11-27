"""Сопоставление формулы в записи TeX со схемой книги.

Метапеременные схемы — строчные буквы x, y, z, v, u, w (высказывания) и a, b, c, d, e (термины). Метапеременная
сопоставляется с последовательностью «единиц» формулы: буква (с индексами), выражение в скобках, функциональная
запись вида E(...), а также всё это с префиксами ~, ⌝, ?, ↓, тильдой или кванторной группой. Одинаковые
метапеременные получают одинаковые значения (с точностью до внешних скобок).

  match(schema, formula) -> dict | None        подстановка, при которой схема даёт формулу
"""
import re

META = set("xyzvuwabcde")
TOK = re.compile(r"\\dashv\\vdash|\\[A-Za-z]+|\\[!,;:]|[A-Za-z](?:\^\{[^}]*\}|\^[0-9a-z*]|_\{[^}]*\}|_[0-9a-z])*|\S")
PREFIX = {"\\sim", "\\urcorner", "?", "\\downarrow", "\\tilde", "\\overline"}
SEP = {"\\vdash", "\\dashv\\vdash"}


def tokens(s):
    s = s.replace("\\!", "").replace("\\,", "").replace("\\;", "")
    s = re.sub(r"\\(left|right)(?=[()\[\]])", "", s)
    return _normalize([t for t in TOK.findall(s) if t not in ("\\!", "\\,", "\\;")])


def _normalize(t):
    """Убрать лишние скобки вокруг единицы: ((x)) → (x), (~x) → ~x, (∀a)(~x) → (∀a)~x."""
    changed = True
    while changed:
        changed = False
        i = 0
        while i < len(t):
            if t[i] == "(":
                e = _group_end(t, i)
                inner = t[i + 1:e - 1] if e else []
                quant = inner[:1] in (["\\forall"], ["\\exists"]) or (len(inner) > 1 and inner[1] in ("\\forall", "\\exists"))
                prev = t[i - 1] if i else ""
                func = re.fullmatch(r"[A-Z]|\\alpha", prev or "-") is not None
                if e and inner and not quant and not func and _unit_end(inner, 0) == len(inner) and (inner[0] == "(" or inner[0] in PREFIX):
                    t = t[:i] + inner + t[e:]
                    changed = True
                    continue
            i += 1
    return t


def _group_end(t, i):
    """Индекс за закрывающей скобкой группы, начинающейся с t[i] == '(' (или '{', '[')."""
    pair = {"(": ")", "{": "}", "[": "]"}[t[i]]
    d = 0
    for j in range(i, len(t)):
        if t[j] == t[i]:
            d += 1
        elif t[j] == pair:
            d -= 1
            if d == 0:
                return j + 1
    return None


def _unit_end(t, i):
    """Конец «единицы», начинающейся в позиции i, или None."""
    if i >= len(t):
        return None
    tok = t[i]
    if tok in PREFIX:
        return _unit_end(t, i + 1)
    if tok == "(":
        e = _group_end(t, i)
        if e is None:
            return None
        inner = t[i + 1:e - 1]
        if inner[:1] in (["\\forall"], ["\\exists"]) or (len(inner) > 1 and inner[0] in ("\\urcorner", "?") and inner[1] in ("\\forall", "\\exists")):
            return _unit_end(t, e)        # кванторная группа: (∀a)x
        return e
    if tok in ("{", "["):
        return _group_end(t, i)
    if re.fullmatch(r"[A-Za-z].*", tok) or tok in ("\\alpha",) or tok.startswith("\\mathrm"):
        j = i + 1
        if j < len(t) and t[j] == "(" and re.fullmatch(r"[A-Z]|\\alpha", tok):
            return _group_end(t, j)
        return j
    if tok.startswith("\\") and tok not in SEP and tok not in ("\\vee", "\\wedge", "\\cdot", "\\rightarrow", "\\to", "\\supset",
                                                            "\\leftarrow", "\\rightharpoonup", "\\rightleftharpoons", "\\Rightarrow",
                                                            "\\in", "\\subset", "\\cup", "\\cap", "\\leq", "\\geq", "\\ldots"):
        return i + 1
    return None


def _strip(seq):
    while len(seq) >= 2 and seq[0] == "(" and _group_end(seq, 0) == len(seq):
        seq = seq[1:-1]
    return tuple(seq)


def _balanced(seq):
    d = 0
    for x in seq:
        d += x in "([{"
        d -= x in ")]}"
        if d < 0:
            return False
    return d == 0


def match(schema, formula, literal=()):
    s, f = tokens(schema), tokens(formula)
    metas = {x for x in s if x in META and x not in literal}
    res = []

    def go(i, j, env):
        if i == len(s):
            if j == len(f):
                res.append(dict(env))
                return True
            return False
        tok = s[i]
        if tok in metas:
            if tok in env:
                for k in range(j + 1, len(f) + 1):
                    if _strip(f[j:k]) == env[tok] and _balanced(f[j:k]) and go(i + 1, k, env):
                        return True
                return False
            k = j
            while True:
                e = _unit_end(f, k)
                if e is None:
                    break
                seg = f[j:e]
                if _balanced(seg) and not (set(seg) & SEP):
                    env[tok] = _strip(seg)
                    if go(i + 1, e, env):
                        return True
                    del env[tok]
                # продолжение последовательности: следующая единица, возможно через бинарную связку
                k = e
                if k < len(f) and f[k] in ("\\vee", "\\wedge", "\\cdot", ":", "\\supset", "\\rightarrow", "\\to", "\\leftarrow"):
                    k += 1
                if k >= len(f):
                    break
            return False
        if j < len(f) and f[j] == tok:
            return go(i + 1, j + 1, env)
        return False

    go(0, 0, {})
    return {k: " ".join(v) for k, v in res[0].items()} if res else None


def tex(seq):
    """Склеить лексемы обратно в TeX."""
    out = ""
    for t in seq.split(" "):
        if out and (re.match(r"\\[A-Za-z]", t) or re.match(r"[A-Za-z]", t) and re.search(r"[A-Za-z]$", out) and out[-1] != " "):
            sep = " " if re.match(r"\\[A-Za-z]", t) or re.search(r"\\[A-Za-z]+$", out) else ""
        else:
            sep = " " if out and re.search(r"\\[A-Za-z]+$", out) and re.match(r"[A-Za-z(]", t) else ""
        if t in ("\\vdash", "\\dashv\\vdash", "\\vee", "\\rightarrow", "\\leftarrow", "\\supset", "\\in", "\\subset", "\\to",
                 "\\rightharpoonup", "\\rightleftharpoons", "\\Rightarrow", ":", "\\wedge", "\\cdot", "\\leq", "\\geq"):
            out = out.rstrip() + " " + t + " "
            continue
        out += sep + t
    return re.sub(r"\s+", " ", out).replace("( ", "(").replace(" )", ")").strip()
