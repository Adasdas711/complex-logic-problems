"""Markdown карточек и формулы $...$ → HTML для сайта.

Формулы набираются символами книги (Unicode) шрифтом STIX Two Text, индексы — <sup>/<sub>,
верхний и нижний индекс вместе — стопкой (<span class="ss">). Библиотеки не нужны.
Неизвестная команда TeX попадает в UNKNOWN: site.py сообщает о ней.
"""
import html
import re

UNKNOWN: set = set()

SYM = {
    "urcorner": "⌝", "sim": "∼", "vdash": "⊢", "dashv": "⊣", "downarrow": "↓", "uparrow": "↑",
    "rightarrow": "→", "to": "→", "leftarrow": "←", "leftrightarrow": "↔", "Rightarrow": "⇒",
    "rightharpoonup": "⇀", "rightleftharpoons": "⇌", "mapsto": "↦",
    "forall": "∀", "exists": "∃", "vee": "∨", "wedge": "∧", "bigvee": "⋁", "bigwedge": "⋀", "cdot": "·",
    "supset": "⊃", "subset": "⊂", "subseteq": "⊆", "supseteq": "⊇", "in": "∈", "notin": "∉",
    "cap": "∩", "cup": "∪", "varnothing": "∅", "emptyset": "∅", "prod": "∏", "sum": "∑",
    "geq": "≥", "leq": "≤", "ge": "≥", "le": "≤", "neq": "≠", "ne": "≠", "equiv": "≡",
    "ldots": "…", "dots": "…", "cdots": "⋯", "times": "×", "neg": "¬", "infty": "∞",
    "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "varepsilon": "ε", "epsilon": "ε",
    "lambda": "λ", "mu": "μ", "pi": "π", "sigma": "σ", "tau": "τ", "varphi": "φ", "phi": "φ", "psi": "ψ",
    "quad": " ", "qquad": "  ",
    "Leftarrow": "⇐", "langle": "⟨", "rangle": "⟩", "mid": "∣", "parallel": "∥", "pm": "±",
    "geqslant": "⩾", "leqslant": "⩽", "square": "□",
}
UPRIGHT = {"min", "max", "lim", "log", "sin", "cos"}
ARG = {"text", "mathrm", "textrm", "operatorname", "mathit", "tilde", "widetilde", "overline", "bar", "hat", "mathbf"}
SPACED = "⊢⊣→←↔⇒⇀⇌↦∨⊃⊂⊆⊇∈∉≥≤≠≡∩∪⇐⩾⩽∣∥"
TIGHT_AFTER = "↓⌝∼∀∃"


def ss(up: str, dn: str) -> str:
    if up and dn:
        return f'<span class="ss"><sup>{up}</sup><sub>{dn}</sub></span>'
    if up:
        return f"<sup>{up}</sup>"
    return f"<sub>{dn}</sub>" if dn else ""


class _Tex:
    def __init__(self, s: str):
        self.s, self.i = s, 0

    def arg(self) -> str:
        """Аргумент: {группа}, команда или один знак."""
        s = self.s
        while self.i < len(s) and s[self.i] == " ":
            self.i += 1
        if self.i >= len(s):
            return ""
        if s[self.i] == "{":
            self.i += 1
            return self.seq("}")
        if s[self.i] == "\\":
            return self.command()
        self.i += 1
        return html.escape(s[self.i - 1], quote=False)

    def raw_group(self) -> str:
        s = self.s
        while self.i < len(s) and s[self.i] == " ":
            self.i += 1
        if self.i < len(s) and s[self.i] == "{":
            depth, j = 0, self.i
            while j < len(s):
                depth += {"{": 1, "}": -1}.get(s[j], 0)
                if depth == 0:
                    break
                j += 1
            text, self.i = s[self.i + 1:j], j + 1
            return text
        return self.arg()

    def command(self) -> str:
        s = self.s
        self.i += 1  # обратная косая
        m = re.match(r"[A-Za-z]+", s[self.i:])
        if not m:
            c = s[self.i] if self.i < len(s) else ""
            self.i += 1
            return {"!": "", ",": " ", ";": " ", ":": " ", " ": " ", "{": "{", "}": "}", "\\": "<br>",
                    "$": "$", "%": "%", "&": "&amp;", "#": "#", "_": "_"}.get(c, html.escape(c))
        name = m[0]
        self.i += len(name)
        if name in SYM:
            return SYM[name]
        if name in UPRIGHT:
            return f'<span class="t">{name}</span>'
        if name in ARG:
            if name in ("text", "mathrm", "textrm", "operatorname"):
                return f'<span class="t">{html.escape(self.raw_group(), quote=False)}</span>'
            inner = self.arg()
            if name in ("mathit",):
                return inner
            if name == "mathbf":
                return f"<b>{inner}</b>"
            if name in ("tilde", "hat") and len(html.unescape(re.sub(r"<[^>]+>", "", inner))) == 1 and "<" not in inner:
                return inner + ("̃" if name == "tilde" else "̂")
            if name in ("tilde", "widetilde"):
                return f'<span class="wt">{inner}</span>'
            return f'<span class="ol">{inner}</span>'
        if name in ("left", "right", "big", "Big", "bigl", "bigr", "displaystyle", "limits"):
            return ""
        UNKNOWN.add(name)
        return html.escape(name)

    def seq(self, stop: str = "") -> str:
        s, out = self.s, []
        while self.i < len(s):
            c = s[self.i]
            if stop and c == stop:
                self.i += 1
                break
            if c == "\\":
                out.append(self.command())
            elif c == "{":
                self.i += 1
                out.append(self.seq("}"))
            elif c in "^_":
                self.i += 1
                a = self.arg()
                up, dn = (a, "") if c == "^" else ("", a)
                j = self.i
                while j < len(s) and s[j] == " ":
                    j += 1
                if j < len(s) and s[j] in "^_" and s[j] != c:
                    self.i = j + 1
                    b = self.arg()
                    up, dn = (up, b) if c == "^" else (b, dn)
                out.append("\x02" + ss(up, dn) + "\x03")
            elif c == "}":
                self.i += 1
            elif c == "~":
                self.i += 1
                out.append(" ")
            else:
                out.append(html.escape(c, quote=False))
                self.i += 1
        return "".join(out)


def _spacing(h: str) -> str:
    parts = re.split(r"(\x02.*?\x03|<[^>]+>)", h)
    for i, p in enumerate(parts):
        if p.startswith("\x02"):
            parts[i] = p[1:-1]
            continue
        if p.startswith("<"):
            continue
        p = re.sub(rf"\s*([{SPACED}])\s*", r" \1 ", p)
        parts[i] = p
    h = re.sub(r"[ \t\n]+", " ", "".join(parts)).replace("⊣ ⊢", "⊣⊢")
    h = re.sub(rf"([{TIGHT_AFTER}]) ", r"\1", h)
    return h.strip()


def tex(s: str) -> str:
    return _spacing(_Tex(s).seq())


def formula(s: str, display: bool = False) -> str:
    cls = "f fd" if display else "f"
    return f'<span class="{cls}">{tex(s)}</span>'


# --- Markdown ---

BOLD = re.compile(r"(?<![\w*])\*\*(?=\S)(.+?)(?<=\S)\*\*(?![\w*])")
ITAL = re.compile(r"(?<![\w*])\*(?=[^\s*])([^*\n]+?)(?<=[^\s*])\*(?![\w*])")
CODE = re.compile(r"`([^`]+)`")
LINE_START = re.compile(r"^(?:[-*•] |\d+[.)] |[а-яa-z]\) |[IVX]+\. )")


def inline(t: str, keep: list) -> str:
    t = html.escape(t, quote=False)
    t = CODE.sub(lambda m: f"<code>{m[1]}</code>", t)
    t = BOLD.sub(r"<b>\1</b>", t)
    t = ITAL.sub(r"<i>\1</i>", t)
    t = t.replace("\\*", "*").replace("&amp;nbsp;", " ")
    return re.sub(r"\x00(\d+)\x01", lambda m: keep[int(m[1])], t)


def _protect(s: str, keep: list) -> str:
    def put(h):
        keep.append(h)
        return f"\x00{len(keep) - 1}\x01"
    s = re.sub(r"\$\$(.+?)\$\$", lambda m: put(formula(m[1], True)), s, flags=re.S)
    return re.sub(r"\$([^$\n]+?)\$", lambda m: put(formula(m[1])), s)


def _table(lines, keep, drop=("LaTeX",)):
    rows = [[c.strip() for c in ln.strip().strip("|").split("|")] for ln in lines]
    head, body = rows[0], [r for r in rows[1:] if not all(re.fullmatch(r":?-+:?", c) for c in r if c)]
    skip = {i for i, c in enumerate(head) if c in drop}
    th = "".join(f'<th scope="col">{inline(c, keep)}</th>' for i, c in enumerate(head) if i not in skip)
    tb = "".join("<tr>" + "".join(f"<td>{inline(c, keep)}</td>" for i, c in enumerate(r) if i not in skip) + "</tr>"
                 for r in body)
    return f'<div class="tw"><table><thead><tr>{th}</tr></thead><tbody>{tb}</tbody></table></div>'


def md(s: str) -> str:
    """Markdown карточки → HTML: абзацы, переносы строк, таблицы, **жирный**, *курсив*, формулы."""
    if not s:
        return ""
    keep: list = []
    s = _protect(s.replace("\r", ""), keep)
    out = []
    for block in re.split(r"\n[ \t]*\n", s.strip()):
        lines = [ln for ln in block.split("\n")]
        if all(ln.lstrip().startswith("|") for ln in lines if ln.strip()):
            out.append(_table([ln for ln in lines if ln.strip()], keep))
            continue
        m = re.match(r"^(#{1,6})\s+(.*)$", lines[0])
        if m and len(lines) == 1:
            lvl = min(len(m[1]) + 1, 6)
            out.append(f"<h{lvl}>{inline(m[2], keep)}</h{lvl}>")
            continue
        if re.fullmatch(r"\s*(-{3,}|\*{3,}|&nbsp;)\s*", block):
            continue
        buf = ""
        for k, ln in enumerate(lines):
            text = ln.rstrip()
            item = text.lstrip()
            if item[:2] in ("- ", "* "):
                item = "• " + item[2:]
            if k == 0:
                buf = item
            elif lines[k - 1].endswith("  ") or LINE_START.match(ln.lstrip()) or ln.startswith("  "):
                buf += "<br>" + item
            else:
                buf += " " + item
        out.append(f"<p>{inline(buf, keep) if '<br>' not in buf else '<br>'.join(inline(x, keep) for x in buf.split('<br>'))}</p>")
    return "".join(out)


# --- Названия: Sᵉ_n, Sᵐ¹_n, S⁵*_if, S₁ ---

SUP = dict(zip("ˢᵉᵐ¹²³⁴⁵⁶⁷⁸⁹⁰ʷʳᶜⁿⁱᵖʰᵏᵗᵈ*", "sem1234567890wrcniphktd*"))
SUB = dict(zip("₀₁₂₃₄₅₆₇₈₉", "0123456789"))
TITLE_RX = re.compile(r"S([" + "".join(SUP) + r"]*)(?:_([a-z0-9]+)|([" + "".join(SUB) + r"]+))?")


def title(t: str) -> str:
    """Название с индексами при S → HTML."""
    out, pos = [], 0
    for m in TITLE_RX.finditer(t):
        up = "".join(SUP[c] for c in m[1])
        dn = m[2] or "".join(SUB[c] for c in (m[3] or ""))
        if not up and not dn:
            continue
        out.append(html.escape(t[pos:m.start()]) + "S" + ss(up, dn))
        pos = m.end()
    out.append(html.escape(t[pos:]))
    return "".join(out)
