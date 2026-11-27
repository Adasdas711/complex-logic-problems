"""Модель языка теории логических координат («Очерки комплексной логики», § 28, с. 372–375).

Формулы: ('at', 'x'); ('neg', F); ('and'|'or'|'imp', F, G); ('co', F, k) — [F k], где k — переменная для координат:
't1', 't2' (время), 's1', 's2' (пространство), 'u1', 'u2' (условия), 'v', 'v1', 'v2' (любые координаты).
Нормализация переносит координаты к элементарным высказываниям по группе V (V.1–V.4) и упрощает вложенные
координаты одного вида по группе II (II.1, II.2: внутренняя координата сохраняется).
"""

KIND = {"t": "время", "s": "пространство", "u": "условия", "v": "любые"}


def kt(k):
    return k[0] + (f"^{k[1:]}" if k[1:] else "")


def tex(f):
    h = f[0]
    if h == "at":
        return f[1]
    if h == "neg":
        g = f[1]
        return f"\\sim {tex(g)}" if g[0] in ("at", "co", "neg") else f"\\sim({tex(g)})"
    if h == "co":
        return f"[{tex(f[1]) if f[1][0] in ('at', 'co') else '(' + tex(f[1]) + ')'}{kt(f[2])}]"
    op = {"and": "\\wedge", "or": "\\vee", "imp": "\\rightarrow"}[h]
    a, b = f[1], f[2]
    wrap = lambda g: f"({tex(g)})" if g[0] in ("and", "or", "imp") else tex(g)
    return f"{wrap(a)} {op} {wrap(b)}"


AX_V = {"and": "V.1", "or": "V.2", "imp": "V.3", "neg": "V.4"}


def push(f, used):
    """Перенести все координаты к элементарным высказываниям; used — список применённых схем."""
    h = f[0]
    if h == "at":
        return f
    if h == "neg":
        return ("neg", push(f[1], used))
    if h in ("and", "or", "imp"):
        return (h, push(f[1], used), push(f[2], used))
    g, k = f[1], f[2]
    g = push(g, used)
    return attach(g, k, used)


def attach(g, k, used):
    h = g[0]
    if h == "neg":
        used.append("V.4")
        return ("neg", attach(g[1], k, used))
    if h in ("and", "or", "imp"):
        used.append(AX_V[h])
        return (h, attach(g[1], k, used), attach(g[2], k, used))
    if h == "co":
        inner = g[2]
        if inner[0] == k[0] and k[0] in "ts":
            used.append("II.1" if k[0] == "t" else "II.2")
            return g
        return ("co", g, k)
    return ("co", g, k)


def normal(f):
    used = []
    r = push(f, used)
    seen = []
    for a in used:
        if a not in seen:
            seen.append(a)
    return r, seen


AXIOMS = {
    "I.1": "\\vdash (x \\vdash y) \\leftrightarrow ([xv] \\vdash [yv])", "I.2": "\\vdash (x \\vdash y) \\leftrightarrow (\\forall v)(x \\vdash y)",
    "I.3": "\\vdash (\\vdash x) \\leftrightarrow (\\forall v)(\\vdash x)",
    "II.1": "[[xt^1]t^2] \\dashv\\vdash [xt^1]", "II.2": "[[xs^1]s^2] \\dashv\\vdash [xs^1]",
    "II.3": "[[xs]t] \\dashv\\vdash [[xt]s]", "II.4": "[[xv^1]v^2] \\dashv\\vdash [xv^1v^2]",
    "IV.1": "(\\exists a)x \\vdash (\\exists v)[xv]", "IV.2": "(\\forall v)[xv] \\vdash (\\forall a)x",
    "IV.3": "(\\exists v)[xv] \\vdash (\\exists v)x", "IV.4": "(\\forall v)[xv] \\vdash (\\forall v)x",
    "V.1": "[(x \\wedge y)v] \\dashv\\vdash [xv] \\wedge [yv]", "V.2": "[(x \\vee y)v] \\dashv\\vdash [xv] \\vee [yv]",
    "V.3": "[(x \\rightarrow y)v] \\dashv\\vdash [xv] \\rightarrow [yv]", "V.4": "[(\\sim x)v] \\dashv\\vdash \\sim[xv]",
    "VI.1": "(u \\rightarrow x) \\vdash [xu]", "VI.2": "(\\exists \\downarrow u)x \\dashv\\vdash (\\exists s)(\\exists t)x",
    "VI.3": "(\\forall \\downarrow u)x \\dashv\\vdash (\\forall s)(\\forall t)x",
}
