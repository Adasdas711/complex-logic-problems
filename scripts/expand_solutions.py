#!/usr/bin/env python3
"""Расписать по шагам решения, состоящие из одной ссылки на страницу.

Обрабатываются задачи, где ответ дан без пояснений:
  • опознание схем («Каким схемам соответствуют формулы», «Укажите номера теоремных схем» …) — для каждой формулы
    приводится схема книги и подстановка, при которой схема даёт формулу (подстановка находится программой
    scripts/logic/match.py, то есть ответ заодно проверяется);
  • подстановка в схему («Подставьте в схему …», «Запишите пример схемы …») — что на что заменяется;
  • диагностика вида «Студент: F — пример L» — схема L, то, что F из неё не получается, и схема, из которой F получается.

  python3 scripts/expand_solutions.py [файлы карточек …]   — по умолчанию data/zadachi/*.md и data/kontrolnye/*.md
  python3 scripts/expand_solutions.py --dry                  — только отчёт
"""
import contextlib
import importlib.util
import io
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
from match import match, tex  # noqa: E402

PAGE_ONLY = re.compile(r"((С|с)\. [^\n]{0,40}|Гл\. [^\n]{0,40}|Очерки, с\. [^\n]{0,20}|[^\n]{0,12})")
GENS = ["g02_05", "g05_16", "g06_07", "g07_08", "g08_10", "g10_12", "g12_15"]


def registry():
    """[(имя, {метка: схема})] — схемы книги, переписанные в генераторах."""
    reg = []
    for n in GENS:
        spec = importlib.util.spec_from_file_location(f"reg_{n}", ROOT / "scripts" / "gen" / f"{n}.py")
        m = importlib.util.module_from_spec(spec)
        with contextlib.redirect_stdout(io.StringIO()):
            spec.loader.exec_module(m)
        for k, v in vars(m).items():
            if not isinstance(v, dict) or not v:
                continue
            vals = [x[0] if isinstance(x, tuple) and x and isinstance(x[0], str) else x for x in v.values()]
            if all(isinstance(x, str) for x in vals) and sum(("\\vdash" in x or "\\dashv" in x) for x in vals) >= 2:
                reg.append((f"{n}.{k}", {str(a): (b[0] if isinstance(b, tuple) else b) for a, b in v.items()}))
    import coords
    reg.append(("coords.AXIOMS", dict(coords.AXIOMS)))
    return reg


def homes(reg):
    """Где (глава, параграф) встречаются схемы каждого набора — по задачам data/zadachi."""
    from collections import Counter, defaultdict
    from common import load_problems
    texts = defaultdict(str)
    for p in load_problems():
        if p.meta.get("chapter") != 17:
            texts[(p.meta["chapter"], p.meta["section"])] += p.body
    out = {}
    for name, d in reg:
        c = Counter()
        for sch in d.values():
            for key, t in texts.items():
                if sch in t:
                    c[key] += 1
        out[name] = c
    return out


# Глава, к которой относится каждый набор схем (по генератору, где он записан со страниц книги).
CHAPTER = {"g06_07.AX": 6, "g06_07.AQ": 7, "g07_08": 7, "g08_10.AI9": 9, "g08_10.T9": 9, "g08_10.AIII9": 9, "g08_10.AI93": 9,
           "g08_10.T93": 9, "g08_10.AIV9": 9, "g08_10.AK1": 10, "g08_10.TK1": 10, "g08_10.ASK": 10, "g08_10.MODI": 10,
           "g10_12.AE1": 11, "g10_12.DER11": 11, "g10_12.T113": 11, "g10_12.EC": 11, "g10_12.AM1": 12, "g10_12.T123": 12,
           "g10_12.AM0": 12, "g10_12.ALM": 12, "g10_12.T129": 12, "g12_15.AP12": 12, "g12_15.AN": 14, "g12_15.CLN": 14,
           "g12_15": 13, "coords.AXIOMS": 16}


def chapter_of(name):
    return CHAPTER.get(name, CHAPTER.get(name.split(".")[0]))


def ordered(reg, home, ch, sec):
    """Наборы схем для задачи параграфа (ch, sec): только наборы этой главы, сначала встречающиеся в этом параграфе.
    Для смешанных наборов (гл. 17) — все наборы."""
    if ch == 17:
        return reg
    mine = [r for r in reg if chapter_of(r[0]) == ch]
    return sorted(mine, key=lambda r: -home[r[0]].get((ch, sec), 0))


def label_keys(label):
    label = label.strip().strip("$").replace("^", "").replace("{", "").replace("}", "")
    out = [label]
    m = re.fullmatch(r"([A-Za-z*]*)\s*\.?\s*([0-9IVX.]+\*?)(?: \(.*\))?", label)
    if m:
        out.append(m.group(1) + m.group(2))
        if m.group(1) in ("", "T"):      # теоремы в наборах записаны номерами
            out.append(m.group(2))
    m = re.fullmatch(r"(?:схема )?(\d+)", label)
    if m:
        out.append(m.group(1))
    return list(dict.fromkeys(out))


def show(v):
    t = tex(v)
    return f"({t})" if re.search(r" (\\vee|\\rightarrow|\\leftarrow|\\supset|:|\\in|\\to|\\wedge|\\cdot|\\Rightarrow|\\rightharpoonup) ", t) \
        and not (t.startswith("(") and t.endswith(")")) else t


def subst_text(env):
    pairs = [(k, show(v)) for k, v in sorted(env.items()) if tex(v) != k]
    if not pairs:
        return "без замены букв"
    return "при " + ", ".join(f"${k}$ — ${v}$" for k, v in pairs)


def apply(schema, env):
    """Подставить значения метапеременных в запись схемы (одновременно, по лексемам; индексы не трогаются).
    Составное значение берётся в скобки, если стоит вплотную к другому выражению или после оператора."""
    toks = re.findall(r"\\[A-Za-z]+|.", schema)
    out = []
    for i, t in enumerate(toks):
        if t not in env or (i and toks[i - 1] in "^_"):
            out.append(t)
            continue
        v = tex(env[t])
        prev = next((x for x in reversed(toks[:i]) if x.strip()), "")
        nxt = next((x for x in toks[i + 1:] if x.strip()), "")
        simple = re.fullmatch(r"[a-z]", v) or (v.startswith("(") and v.endswith(")") and _balanced_str(v[1:-1]))
        tight = re.fullmatch(r"[A-Za-z)?]", prev or "-") or re.fullmatch(r"[a-z(\\]", nxt[:1] or "-") or prev in (
            "\\sim", "\\downarrow", "\\urcorner", "\\tilde")
        out.append(v if simple or not tight else f"({v})")
    return "".join(out)


def _balanced_str(v):
    d = 0
    for ch in v:
        d += (ch == "(") - (ch == ")")
        if d < 0:
            return False
    return d == 0


def wrap(t):
    """Взять в скобки выражение с бинарным оператором верхнего уровня (как в записи книги)."""
    return f"({t})" if re.search(r" (\\vee|\\rightarrow|\\leftarrow|\\supset|:|\\in|\\to|\\wedge|\\Rightarrow|\\rightharpoonup) ", t) \
        and not (t.startswith("(") and t.endswith(")") and _balanced_str(t[1:-1])) else t


def find(reg, label, formula):
    for name, d in reg:
        for k in label_keys(label):
            if k in d:
                env = match(d[k], formula)
                if env is not None:
                    return d[k], env
    return None


def find_any(reg, formula):
    for name, d in reg:
        for k, s in d.items():
            env = match(s, formula)
            if env is not None:
                return k, s, env
    return None


def parts(body):
    out, ps = {}, re.split(r"^## (.+)$", body, flags=re.M)
    for t, x in zip(ps[1::2], ps[2::2]):
        out[t.strip()] = x.strip()
    return out


def page_of(sol, src):
    m = re.search(r"[сС]\. [\d–, ]+\d", sol) or re.search(r"с\. [\d–, ]+\d", src or "")
    return m.group(0).replace("С.", "с.") if m else None


def expand(card, reg_all, home):
    """Новое решение или None."""
    ch = int(re.search(r"^chapter: (\d+)", card, re.M).group(1))
    sec = int(re.search(r"^section: (\d+)", card, re.M).group(1))
    reg = ordered(reg_all, home, ch, sec)
    pp = parts(card)
    cond, ans, sol = pp.get("Условие", ""), pp.get("Ответ", ""), pp.get("Решение", "")
    core = re.sub(r"\n\nИсточник:.*", "", sol).strip()
    if not PAGE_ONLY.fullmatch(core):
        return None
    src = (re.search(r'^source: "?(.*?)"?$', card, re.M) or [None, ""])[1]
    page = page_of(core, src)
    ref = f" ({page})" if page else ""

    # 1. Опознание схем
    if re.search(r"(схемам[^?]*соответствуют|номера (теоремных схем|следствий)|Укажите схемы|теоремные схемы .* записаны|"
                 r"Укажите аксиомные \(A\) или теоремные \(T\) схемы)", cond):
        its = re.findall(r"^([а-е])\) \$(.+)\$\s*$", cond, re.M)
        labs = dict(re.findall(r"([а-е])\) ([^;]+)", ans))
        lines, ok = [], 0
        for L, f in its:
            lab = labs.get(L, "").strip().rstrip(".")
            hit = find(reg, lab, f) if lab else None
            if hit:
                s, env = hit
                ok += 1
                lines.append(f"{L}) Схема {lab.strip('$')}: ${s}$. Формула получается из неё {subst_text(env)}.")
            else:
                lines.append(f"{L}) {lab.strip('$')}.")
        if ok * 2 >= len(its) and its:
            return ("Для каждой формулы ищем схему, из которой она получается заменой метапеременных (одинаковые буквы схемы — "
                    "одинаковыми выражениями).\n\n" + "\n".join(lines) + f"\n\nСхемы — {page or 'по указанной странице'}.")

    # 2. Подстановка в схему
    m = re.search(r"Подставьте в (?:аксиомную )?схему.*?\(\$(.+?)\$\)(.*)", cond, re.S)
    if m and re.fullmatch(r"\$[^$]+\$\.?", ans.strip()):
        subs = re.findall(r"(?:вместо )?\$([a-zA-Z])\$(?: термин)? — \$([^$]+)\$", m.group(2))
        subs += re.findall(r"(?<![$\w])([A-Z]) — \$([^$]+)\$", m.group(2))
        schema = m.group(1)
        used = [(v, t) for v, t in subs if re.search(rf"(?<![\\A-Za-z]){v}|{v}(?![a-z])", re.sub(r"\\[A-Za-z]+", "", schema))]
        if used:
            res = ans.strip().rstrip(".")
            return (f"1. Схема{ref}: ${schema}$; её буквы — метапеременные.\n"
                    "2. Одновременно заменяем каждое вхождение: " + "; ".join(f"${v}$ → ${t}$" for v, t in used) +
                    ". Составное выражение, стоящее рядом с другим выражением или после оператора, берём в скобки, "
                    "чтобы не изменилось строение формулы.\n"
                    f"3. Получаем {res}.")

    # 3. «Запишите пример схемы … при x = …»
    m = re.search(r"Запишите пример схемы \$([^$]+)\$[^(]*\(\$(.+?)\$, \$y\$ — из \$x\$ заменой \$(\w)\$ на \$(\w)\$.*?при \$x = (.+?)\$", cond, re.S)
    if m and re.fullmatch(r"\$[^$]+\$\.?", ans.strip()):
        name, schema, a, b, x = m.groups()
        return (f"1. Схема ${name}${ref}: ${schema}$, где $y$ получается из $x$ заменой ${a}$ на ${b}$ во всех вхождениях "
                f"(в том числе в $K{a}$).\n2. $x = {x}$; заменяем ${a}$ на ${b}$ и получаем $y$.\n"
                f"3. Подставляем $x$ и $y$ в схему: {ans.strip().rstrip('.')}.")

    # 4. Диагностика «Студент: F — пример L» / «L: F»
    m = (re.search(r"Студент: \$(.+?)\$ — (?:пример|это) ([A-Z][A-Za-z*^.0-9IV]*)", cond) or
         re.search(r"Студент: «([A-Z][A-Za-z*^.0-9IV]*): \$(.+?)\$»", cond))
    if m and m.re.pattern.startswith("Студент: «"):
        lab, f = m.group(1), m.group(2)
    elif m:
        f, lab = m.group(1), m.group(2).rstrip(".:")
    if m and ch != 17:
        own = None
        for name, d in reg:
            for k in label_keys(lab):
                if k in d and own is None:
                    own = d[k]
        side = None
        if own and ", где" in own:
            own, side = own.split(", где", 1)
            side = "где" + side
        if own and side and match(own, f) is not None:
            reason = re.sub(r"^Неверно:\s*", "", ans.strip()).rstrip(".")
            return (f"1. Схема {lab}{ref}: ${own}$, {side}.\n2. По виду формула подходит под схему {subst_text(match(own, f))}.\n"
                    f"3. Проверяем условие схемы: {reason}.\n4. Условие не выполнено, значит, формула — не пример схемы {lab}.")
        if own and match(own, f) is None and "\\vdash" in own and "\\vdash" in f and "\\dashv" not in own:
            sp0, sc0 = own.split("\\vdash", 1)
            env_r = match(f"{sc0.strip()} \\vdash {sp0.strip()}", f)
            if env_r is not None:
                return (f"1. Схема {lab}{ref}: ${own}$.\n2. Формула студента получается из схемы, если поменять местами посылку и "
                        f"заключение ({subst_text(env_r)}): это обращение схемы, а не её пример.\n"
                        f"3. Обращение схемы схемой не является; значит, формула — не пример схемы {lab}.")
        if own and match(own, f) is None and "\\vdash" in own and "\\vdash" in f:
            sp, sc = own.split("\\vdash", 1)
            fp, fc = f.split("\\vdash", 1)
            env_p, env_c = match(sp, fp), match(sc, fc)
            if env_p is not None:
                why = (f"2. Посылка формулы подходит под схему {subst_text(env_p)}. Тогда по схеме заключение должно быть "
                       f"${wrap(apply(sc, env_p).strip())}$, а у студента — ${fc.strip()}$.")
            elif env_c is not None:
                why = (f"2. Заключение формулы подходит под схему {subst_text(env_c)}. Тогда по схеме посылка должна быть "
                       f"${wrap(apply(sp, env_c).strip())}$, а у студента — ${fp.strip()}$.")
            else:
                why = "2. Ни посылка, ни заключение формулы не имеют строения, которого требует схема."
            other = find_any(reg, f)
            step3 = (f"\n3. Формула студента получается из схемы {other[0]}: ${other[1]}$ {subst_text(other[2])}." if other else "")
            return f"1. Схема {lab}{ref}: ${own}$.\n{why}{step3}\n{len(step3) and 4 or 3}. Значит, формула — не пример схемы {lab}."
    return None


def run(files, dry=False):
    reg = registry()
    home = homes(reg)
    total = 0
    for f in files:
        text = f.read_text(encoding="utf-8")
        chunks = text.split("\n=====\n")
        n = 0
        for i, c in enumerate(chunks):
            if "## Решение" not in c:
                continue
            new = expand(c, reg, home)
            if not new:
                continue
            a = c.index("## Решение")
            tail = c[len(c.rstrip()):]
            chunks[i] = c[:a] + "## Решение\n\n" + new + tail
            n += 1
        if n and not dry:
            f.write_text("\n=====\n".join(chunks), encoding="utf-8")
        total += n
        print(f"{f.relative_to(ROOT)}: {n}")
    print("всего:", total)


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    files = [Path(a).resolve() for a in args] or sorted((ROOT / "data" / "zadachi").glob("*.md")) + sorted((ROOT / "data" / "kontrolnye").glob("*.md"))
    run(files, dry="--dry" in sys.argv)
