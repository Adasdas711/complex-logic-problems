#!/usr/bin/env python3
"""Пересчёт ответов программой (помимо подстановок в схемы — их проверяет check_subst.py).

Разбор формул здесь свой, независимый от генераторов: TeX-запись карточки переводится
в дерево и вычисляется по главной интерпретации (с. 22) и критериям систем (гл. 5, § 2, с. 72–73).

Проверяется:
  1. строки выводов «N. $x \\vdash y$ [основание]» в решениях глав об общей теории дедукции:
     формула должна быть тавтологией, а в $S^1$, $S_1$ и $S^s$ — ещё и без элементарных
     высказываний заключения, отсутствующих в посылке (MT1 § 4 и MT1 § 5 гл. 1);
     если основание — одна аксиомная схема $S^1$ (A1–A11, гл. 1), строка должна быть её примером;
  2. ответы «а) да; б) нет; …» на вопросы о тавтологичности, условии на элементарные
     высказывания и доказуемости в одной из систем $S^s$, $S^w$, $S^m$, $S^c$, $S^6$, $S^1$, $S_1$, $S^2$, $S_2$;
  3. ответы вида «$S^s$ — нет; $S^w$ — да; …» по одной формуле условия.

Формулы с операторами вне общей теории дедукции (←, ↓, →, кванторы, модальности) пропускаются.

Запуск: python3 scripts/check_answers.py [-v]   (код возврата 1 при расхождениях)
"""
import glob
import re
import signal
import sys
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent / "logic"))
import s1  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent


class Skip(Exception):
    pass


# ---------------------------------------------------------------- разбор
TOK = re.compile(r"\\[A-Za-z]+|[():]|[a-z](?:\^\{?\d+\}?|_\{?\d+\}?)?|\S")


def tokens(s):
    s = re.sub(r"\\[,!;]|\\left|\\right|\\cdot|\\ ", " ", s)
    s = s.replace("\\lnot", "\\sim").replace("\\neg", "\\sim")
    out = TOK.findall(s)
    for t in out:
        if not (t in ("\\sim", "\\vee", "\\supset", "\\vdash", "(", ")", ":") or re.fullmatch(r"[a-z].*", t)):
            raise Skip(t)
    return out


class P:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, x=None):
        t = self.peek()
        if x is not None and t != x:
            raise Skip(f"ожидалось {x}")
        self.i += 1
        return t

    def expr(self):
        a = self.disj()
        if self.peek() == "\\supset":
            self.eat()
            b = self.disj()
            return ("imp", a, b)
        return a

    def disj(self):
        parts, op = [self.conj()], None
        while self.peek() in (":", "\\vee"):
            o = self.eat()
            if op and o != op:
                raise Skip("смешаны : и ∨")
            op = o
            parts.append(self.conj())
        if op is None:
            return parts[0]
        return ("dis" if op == ":" else "wdis", tuple(parts))

    def conj(self):
        parts = [self.fac()]
        while self.peek() is not None and (self.peek() in ("\\sim", "(") or re.fullmatch(r"[a-z].*", self.peek())):
            parts.append(self.fac())
        return parts[0] if len(parts) == 1 else ("conj", tuple(parts))

    def fac(self):
        t = self.peek()
        if t == "\\sim":
            self.eat()
            return ("neg", self.fac())
        if t == "(":
            self.eat()
            e = self.expr()
            self.eat(")")
            return e
        if t is not None and re.fullmatch(r"[a-z].*", t):
            self.eat()
            return ("v", re.sub(r"[{}]", "", t))
        raise Skip(f"не формула: {t}")


OPQ = ("\\leftarrow", "\\rightarrow", "\\downarrow", "\\in", "\\rightharpoonup", "\\Rightarrow")


def opaque(s):
    """Составные части вне общей теории дедукции — (a ← b), N(↓x), ?M(↓x), (x → y) — заменяются
    элементарными высказываниями «@k» (одинаковая запись — одна буква)."""
    toks = [t for t in GTOK.findall(re.sub(r"\\[,!;]|\\left|\\right|\\ ", "", s)) if t not in ("{", "}")]
    out, i, names = [], 0, {}

    def group_end(j):
        d = 0
        for k in range(j, len(toks)):
            d += (toks[k] == "(") - (toks[k] == ")")
            if d == 0:
                return k
        raise Skip("скобки")

    while i < len(toks):
        t = toks[i]
        j = i
        while j < len(toks) and (toks[j] in ("?", "\\urcorner") or re.fullmatch(r"[A-Z]", toks[j])):
            j += 1
        if j > i and j < len(toks) and toks[j] == "(" and re.fullmatch(r"[A-Z]", toks[j - 1]):
            e = group_end(j)
        elif t == "(":
            e = group_end(i)
            if not any(x in OPQ for x in toks[i:e + 1]):
                out.append(t)
                i += 1
                continue
            if any(x in ("\\forall", "\\exists") for x in toks[i:e + 1]):
                raise Skip("кванторы")
        else:
            if t in ("\\forall", "\\exists") or t in OPQ:
                raise Skip(t)
            out.append(t)
            i += 1
            continue
        key = "".join(toks[i:e + 1])
        names.setdefault(key, f"q^{{{len(names) + 1}}}")
        out.append(names[key])
        i = e + 1
    return " ".join(out)


def formula(s):
    p = P(tokens(s))
    e = p.expr()
    if p.peek() is not None:
        raise Skip("хвост")
    return e


def entail(s):
    """'x \\vdash y' → (x, y); '\\vdash y' → (None, y)."""
    s = s.strip().strip("$").strip()
    if "\\dashv" in s or s.count("\\vdash") != 1:
        raise Skip("не формула следования")
    a, b = s.split("\\vdash")
    return (formula(a) if a.strip() else None), formula(b)


# ---------------------------------------------------------------- семантика (с. 22; гл. 2, с. 36)
def val(f, e, tab=None):
    """Значение по главной интерпретации; tab — особая двузначная таблица § 8 гл. 1:
    {'neg': 'x' | '0' | '1', 'dis': 'or' | 'and'}."""
    tab = tab or {}
    k = f[0]
    if k == "v":
        return e[f[1]]
    if k == "neg":
        if tab.get("neg") == "x":
            return val(f[1], e, tab)
        if tab.get("neg") in ("0", "1"):
            return int(tab["neg"])
        return 1 - val(f[1], e, tab)
    if k == "dis" and tab.get("dis") == "or":
        return int(any(val(a, e, tab) for a in f[1]))
    if k == "dis" and tab.get("dis") == "and":
        return int(all(val(a, e, tab) for a in f[1]))
    if k == "conj":
        return int(all(val(a, e, tab) for a in f[1]))
    if k == "dis":
        return int(sum(val(a, e, tab) for a in f[1]) == 1)
    if k == "wdis":
        return int(any(val(a, e, tab) for a in f[1]))
    if k == "imp":
        return int(not val(f[1], e, tab) or val(f[2], e, tab))
    raise ValueError(k)


def at(f):
    if f is None:
        return set()
    if f[0] == "v":
        return {f[1]}
    if f[0] == "neg":
        return at(f[1])
    if f[0] == "imp":
        return at(f[1]) | at(f[2])
    return set().union(*(at(a) for a in f[1]))


def taut(a, b):
    vs = sorted(at(a) | at(b))
    for bits in product((0, 1), repeat=len(vs)):
        e = dict(zip(vs, bits))
        if (a is None or val(a, e)) and not val(b, e):
            return False
    return True


def cond(k, a, b):
    A, B = at(a), at(b)
    return {"s": B <= A, "w": bool(A & B), "m": A == B, "c": A <= B, "q": True}[k]


def prov(k, a, b):
    if a is None:          # ⊢ y в системах с A^d (гл. 4): доказуемы тавтологии (MT4 § 3 гл. 4)
        return taut(a, b)
    return taut(a, b) and cond(k, a, b)


# ---------------------------------------------------------------- карточки
def cards():
    files = sorted(glob.glob(str(ROOT / "data/zadachi/*.md")))
    for d in ("kontrolnye", "vhodnye", "povtorenie"):
        files += sorted(glob.glob(str(ROOT / f"data/{d}/*.md")))
    for f in files:
        for c in open(f, encoding="utf-8").read().split("\n=====\n"):
            m = re.search(r'^id: "?([^"\s]+)', c, re.M)
            chm = re.search(r"^chapter: (\d+)", c, re.M)
            if not m or "## Условие" not in c:
                continue
            cond_, rest = c.split("## Условие", 1)[1].split("## Ответ", 1)
            ans, sol = rest.split("## Решение", 1) if "## Решение" in rest else (rest, "")
            typ = re.search(r"^type: (\S+)", c, re.M)
            cid = m[1] if re.match(r"\d\d\.", m[1]) else f"{int(chm[1]):02d}:{m[1]}" if chm else m[1]
            yield cid, (typ[1] if typ else ""), cond_.strip(), ans.strip(), sol.strip()


SYS = [(r"S\^\{?s\}?(?![_\w])", "s"), (r"S\^\{?1\}?(?![_\w])", "s"), (r"S_\{?1\}?(?!\^)", "s"),
       (r"S\^\{?w\}?", "w"), (r"S\^\{?2\}?(?![_\w])", "w"), (r"S_\{?2\}?(?!\^)", "w"),
       (r"S\^\{?m\}?(?![\w{])", "m"), (r"S\^\{?c\}?(?![\w{])", "c"), (r"S\^\{?6\}?", "q"), (r"S\^\{?5\}?(?![_\w])", "s")]
LET = "абвгдеж"


def systems_in(text):
    found = set()
    for rx, k in SYS:
        if re.search(rx, text):
            found.add(k)
    return found


def predicate(q):
    """Что спрашивается в серии а), б), …: ('taut',) | ('cond', k) | ('prov', k) | None."""
    ql = q.lower()
    if re.search(r"таблиц|интерпретаци|значени[яй] 1, 2|трёхзнач|четырёхзнач|контрольн", ql):
        return None          # тавтологичность в особой таблице или иной процедуре — не главная интерпретация
    ks = systems_in(q)
    if "тавтолог" in ql and not re.search(r"доказу|теорем|следовани|услови", ql):
        return ("taut",)
    if len(ks) != 1:
        return None
    k = ks.pop()
    if "тавтологичность здесь не проверяйте" in ql:
        return ("cond", k)
    if re.search(r"услови\w* на элементар|условие \$?s|выполнено ли условие|выполнено условие", ql) and "тавтолог" not in ql:
        return ("cond", k)
    if re.search(r"доказу|теорем|следованием в смысле|следование в смысле", ql):
        return ("prov", k)
    return None


def items(cond_):
    out = {}
    for m in re.finditer(r"^([а-ж])\) \$([^$]+)\$\s*$", cond_, re.M):
        out[m[1]] = m[2]
    return out


def yesno(ans):
    out = {}
    for m in re.finditer(r"([а-ж])\) (да|нет)", ans):
        out[m[1]] = m[2] == "да"
    return out


AX_CH1 = {"01", "17"}

# ---------------------------------------------------------------- опознание схем
GTOK = re.compile(r"\\[A-Za-z]+|[A-Za-z]|\d|[^\s]")


def gtoks(s):
    s = re.sub(r"\\[,!;]|\\left|\\right|\\ ", "", s)
    return [t for t in GTOK.findall(s) if t not in ("{", "}")]


def strip(span):
    while len(span) >= 2 and span[0] == "(" and span[-1] == ")":
        d = 0
        for i, t in enumerate(span):
            d += (t == "(") - (t == ")")
            if d == 0 and i < len(span) - 1:
                return span
        span = span[1:-1]
    return span


def balanced(span):
    d = 0
    for t in span:
        d += (t == "(") - (t == ")")
        if d < 0:
            return False
    return d == 0


def gmatch(sch, f, meta, env=None, i=0, j=0):
    """Есть ли замена метапеременных схемы (одинаковые — одинаково), дающая f (с точностью до внешних скобок)."""
    env = dict(env or {})
    if i == len(sch):
        return j == len(f)
    s = sch[i]
    if s in meta:
        if s in env:
            for k in range(j + 1, len(f) + 1):
                if strip(f[j:k]) == env[s] and gmatch(sch, f, meta, env, i + 1, k):
                    return True
            return False
        for k in range(j + 1, len(f) + 1):
            span = f[j:k]
            if balanced(span) and span[0] not in (")", "\\vdash"):
                env[s] = strip(span)
                if gmatch(sch, f, meta, env, i + 1, k):
                    return True
        return False
    return j < len(f) and f[j] == s and gmatch(sch, f, meta, env, i + 1, j + 1)


SCHEMAS = {}


def main():
    verbose = "-v" in sys.argv
    bad, n_lines, n_items, n_five, n_schema, n_val = [], 0, 0, 0, 0, 0
    for cid, typ, cond_, ans, sol in cards():
        ch = cid[:2]
        # 1. строки выводов
        if ch in ("01", "02", "03", "04", "05", "17") and typ != "E":
            ks = systems_in(cond_ + sol)
            strong = ch in ("01", "02") or (ks <= {"s"} and ch != "03")
            if re.search(r"\[(дано|допущ|посылк|предполож)", sol):
                continue     # вывод из допущений: строки после допущения — не теоремы
            for m in re.finditer(r"^\s*(\d+)\. \$([^$]+)\$ \[([^\]]+)\]", sol + "\n" + ans, re.M):
                num, fx, why = m[1], m[2], m[3]
                if re.search(r"дано|допущ|посылк|предполож|гипотез|…|\.\.\.", why):
                    continue
                try:
                    a, b = entail(fx)
                except Skip:
                    continue
                n_lines += 1
                if not taut(a, b):
                    bad.append(f"{cid}: строка {num} ${fx}$ — не тавтология")
                elif strong and a is not None and not cond("s", a, b):
                    bad.append(f"{cid}: строка {num} ${fx}$ — в заключении новое элементарное высказывание")
                elif ch in AX_CH1 and re.fullmatch(r"A(?:[1-9]|1[01])", why.strip()) and a is not None \
                        and "wdis" not in repr((a, b)) and "imp" not in repr((a, b)):
                    got = s1.axiom(a, b)
                    if got != why.strip() and not (why.strip() in ("A5", "A6", "A11") and got in ("A5", "A6", "A11")):
                        bad.append(f"{cid}: строка {num} ${fx}$ — указана {why.strip()}, программа: {got}")
        its, yn = items(cond_), yesno(ans)
        # 1а. шаги «[$S^s$]», «[A3 $S^1$]» в выводах любых глав: составные части иных теорий — как элементарные
        if typ != "E" and ch not in ("01", "02", "03", "04", "05"):
            for m in re.finditer(r"^\s*(\d+)\. \$([^$]+)\$ \[([^\]]*(?:S\^s|S\^1|S\^\{s\})[^\]]*)\]", sol, re.M):
                if re.search(r"[:,]\s*\d|R\d", m[3]):
                    continue     # шаг из предыдущих строк, а не теорема S^s сама по себе
                try:
                    lhs, rhs = m[2].split("\\vdash") if m[2].count("\\vdash") == 1 else (None, None)
                    if lhs is None or not lhs.strip():
                        continue
                    both = opaque(lhs + " \\vdash " + rhs)
                    a, b = entail(both.replace("\\\\", "\\"))
                except Skip:
                    continue
                n_lines += 1
                if not (taut(a, b) and cond("s", a, b)):
                    bad.append(f"{cid}: строка {m[1]} ${m[2]}$ [{m[3]}] — не сильная тавтология")
        # 2. серии а) да; б) нет
        if its and yn and set(yn) == set(its):
            pred = predicate(cond_.split("\n\nа)")[0] if "\n\nа)" in cond_ else cond_)
            if pred and typ != "E":
                for L, fx in its.items():
                    if L not in yn:
                        continue
                    try:
                        if "\\vdash" in fx:
                            a, b = entail(fx)
                        else:
                            a, b = None, formula(fx)
                    except Skip:
                        continue
                    if pred[0] == "taut":
                        got = taut(a, b)
                    elif a is None:
                        continue
                    elif pred[0] == "cond":
                        got = cond(pred[1], a, b)
                    else:
                        got = prov(pred[1], a, b)
                    n_items += 1
                    if got != yn[L]:
                        bad.append(f"{cid}: {L}) ${fx}$ — в ответе «{'да' if yn[L] else 'нет'}», программа: "
                                   f"«{'да' if got else 'нет'}» ({' '.join(pred)})")
        # 3. «S^s — нет; S^w — да; …»
        five = re.findall(r"\$S\^\{?(s|w|m|c|6)\}?\$ — (да|нет)", ans)
        if len(five) >= 3 and typ != "E":
            fs = re.findall(r"\$([^$]*\\vdash[^$]*)\$", cond_)
            if len(set(fs)) == 1:
                try:
                    a, b = entail(fs[0])
                except Skip:
                    a = b = None
                if b is not None and a is not None:
                    n_five += 1
                    for k, v in five:
                        k = "q" if k == "6" else k
                        got = prov(k, a, b)
                        if got != (v == "да"):
                            bad.append(f"{cid}: {k} — в ответе «{v}», программа: «{'да' if got else 'нет'}»")
        # 5. значения при главной интерпретации: «при $x = 0$, $y = 1$» и ответ «а) 0; б) 1; …»
        tab = None
        if "Таблица" in cond_:
            m = re.search(r"отмеченное значение 1; (.*?); остальные операторы", cond_, re.S)
            tab = {}
            if m:
                neg = re.search(r"\\sim x = (x|0|1)\$", m[1])
                dis = re.search(r"x\^n = x\^1 (\\vee|\\cdot)", m[1])
                if neg:
                    tab["neg"] = neg[1]
                if dis:
                    tab["dis"] = "or" if dis[1] == "\\vee" else "and"
            if not m or set(re.findall(r"\$([^$]*=[^$]*)\$", m[1])) - {neg[0][:-1] if neg else "", ""} and not dis:
                tab = "skip"
        if re.fullmatch(r"(?:[а-ж]\) [01][;.]?\s*)+", ans) and typ != "E" and "интерпретации" in cond_ + "Таблица" \
                and tab != "skip" and ("главной интерпретации" in cond_ or tab):
            env = {k: int(v) for k, v in re.findall(r"\$([a-z]) = ([01])\$", cond_)}
            got_ans = dict(re.findall(r"([а-ж])\) ([01])", ans))
            for L, fx in its.items():
                try:
                    f = formula(fx)
                    v = val(f, env, tab or None)
                except (Skip, KeyError):
                    continue
                n_val += 1
                if str(v) != got_ans.get(L):
                    bad.append(f"{cid}: {L}) ${fx}$ — в ответе {got_ans.get(L)}, программа: {v}")
        # 4. «а) A2; б) A5» по схемам, приведённым в решении; одна метка — одна схема во всех карточках
        lab = dict(re.findall(r"([а-ж])\) \$?(A\d+)\$?(?=[;\s.]|$)", ans))
        sysm = re.search(r"схем\w* (\$[^$]+\$)", cond_)
        if lab and its and set(lab) == set(its) and typ != "E" and sysm:
            quoted = {}
            for m in re.finditer(r"(A\d+)(?: \$\S+\$)?[: ]+\$([^$]+\\vdash[^$]+)\$", sol):
                quoted.setdefault(m[1], m[2])
            meta = set("".join(re.findall(r"\$([a-z](?:, ?[a-z])*)\$ —", cond_)).replace(",", "").replace(" ", ""))
            for L, A in lab.items():
                if A not in quoted:
                    continue
                key = (sysm[1], A)
                norm = "".join(gtoks(quoted[A]))
                SCHEMAS.setdefault(key, {}).setdefault(norm, cid)
                n_schema += 1
                if not gmatch(gtoks(quoted[A]), gtoks(its[L]), meta or set("xyzvuw")):
                    bad.append(f"{cid}: {L}) ${its[L]}$ не получается из {A} ${quoted[A]}$")
    for (sy, A), forms in SCHEMAS.items():
        if len(forms) > 1:
            bad.append(f"{sy} {A}: разные записи схемы в карточках " + ", ".join(sorted(forms.values())))
    print(f"Проверено строк выводов: {n_lines}; пунктов «да/нет»: {n_items}; ответов по пяти системам: {n_five}; "
          f"опознаний схем: {n_schema}; значений: {n_val}; расхождений: {len(bad)}")
    for b in bad:
        print("  " + b)
    if verbose:
        pass
    return 1 if bad else 0


if __name__ == "__main__":
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    sys.exit(main())
