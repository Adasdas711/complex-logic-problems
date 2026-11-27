#!/usr/bin/env python3
"""Пересчёт ответов задач «Подставьте в схему …»: одновременная подстановка по отдельным буквам.

  python3 src/scripts/check_subst.py        — список расхождений
"""
import re
import sys

from common import load_problems

TOK = re.compile(r"\\[a-zA-Z]+|\\.|[a-zA-Z]|\s+|.")


def parts(body):
    out, ps = {}, re.split(r"^## (.+)$", body, flags=re.M)
    for t, x in zip(ps[1::2], ps[2::2]):
        out[t.strip()] = x.strip()
    return out


def compound(t):
    return len([x for x in TOK.findall(t) if x.strip()]) > 1


def wrapped(t):
    if not (t.startswith("(") and t.endswith(")")):
        return False
    d = 0
    for i, ch in enumerate(t):
        d += ch == "("
        d -= ch == ")"
        if d == 0 and i < len(t) - 1:
            return False
    return True


def subst(s, mp):
    toks = TOK.findall(s)
    out = []
    for i, tk in enumerate(toks):
        if tk in mp and not (i and toks[i - 1] in ("^", "_")):
            t = mp[tk]
            prev = next((x for x in reversed(toks[:i]) if x.strip()), "")
            nxt = next((x for x in toks[i + 1:] if x.strip()), "")
            letter_adj = re.fullmatch(r"[a-z)]", prev or "-") or re.fullmatch(r"[a-z(]", nxt or "-") or prev == "\\tilde"
            after_op = prev in ("\\downarrow", "K", "\\sim", "\\urcorner")
            if compound(t) and not wrapped(t):
                if t.startswith("\\sim") and not re.fullmatch(r"[a-z(]", nxt or "-") and prev != "\\sim":
                    pass
                elif prev == "K" and t.startswith("\\sim"):
                    pass
                elif letter_adj or after_op or " " in t.strip():
                    if letter_adj or after_op:
                        t = f"({t})"
            if prev == "\\sim" and out and out[-1] == "\\sim" and t.startswith("\\sim"):
                t = " " + t
            out.append(t)
        else:
            out.append(tk)
    return "".join(out)


def norm(s):
    """Без пробелов и скобок: сравниваются буквы и операторы, а не расстановка скобок."""
    s = s.replace("\\widetilde{", "\\tilde{")   # тильда над составным термином: \widetilde{(…)}
    return re.sub(r"[\s(){}]", "", s).replace("\\!", "")


def cases(problems):
    for p in problems:
        pp = parts(p.body)
        c, a = pp.get("Условие", ""), pp.get("Ответ", "")
        m = re.search(r"Подставьте в (?:аксиомную )?схему.*?\(\$(.+?)\$\)", c, re.S)
        if not m:
            continue
        rest = c[m.end():]
        subs = re.findall(r"(?:вместо )?\$([a-zA-Z])\$(?: термин)? — \$([^$]+)\$", rest)
        subs += re.findall(r"(?<![$\w])([A-Z]) — \$([^$]+)\$", rest)  # метазнак квантора: «K — $\exists$»
        if not subs:
            continue
        yield p, m.group(1), dict(subs), a


def extra_problems():
    """Карточки контрольных, входных тестов и планового повторения."""
    from pathlib import Path
    from types import SimpleNamespace
    root = Path(__file__).resolve().parent.parent / "data"
    for d in ("kontrolnye", "vhodnye", "povtorenie"):
        for f in sorted((root / d).glob("*.md")):
            for c in f.read_text(encoding="utf-8").split("\n=====\n"):
                m = re.search(r"^id: (\S+)", c, re.M)
                if m and "## Условие" in c:
                    yield SimpleNamespace(meta={"id": m[1].strip('"')}, body=c[c.index("## Условие"):])


def main():
    bad = 0
    for p, s, mp, a in cases(list(load_problems()) + list(extra_problems())):
        got = subst(s, mp)
        ans = re.fullmatch(r"\$([^$]+)\$\.?", a.strip())
        if not ans:
            continue
        if norm(got) != norm(ans.group(1)):
            bad += 1
            print(f"{p.meta['id']}\n  схема: {s}\n  замена: {mp}\n  ответ: {ans.group(1)}\n  пересчёт: {got}")
    print("расхождений:", bad, file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
