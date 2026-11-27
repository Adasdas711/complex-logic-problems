"""Общие средства для усложнённых задач Введения (hard00.py): случайные выражения по § 4–5 с явными границами,
разбор, порча строк разбора, сопоставление с образцом, запись карточек.
Модель — src/scripts/logic/lang0.py.
"""
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts"))
import lang0 as G  # noqa: E402
from lang0 import (Atom, Op, St, S, P, X, tex, kind, parse, verdict, ref, why_not, is_stmt)  # noqa: E402,F401
from open_form import test_like  # noqa: E402,F401

G.ARITY["r"] = 2
rnd = random.Random(1970_0)
s, t, u = S("s"), S("t"), S("u")
p, q, r = P("p"), P("q"), P("r")
x, y, z = X("x"), X("y"), X("z")
SUBJ, PRED1, LET = [s, t, u], [p, q], [x, y, z]
L = "абвгдежз"
CONV4 = "Обозначения: $s, t, u$ — простые субъекты; $p, q, r$ — простые предикаты; $x, y, z$ — высказывания."
CONV5 = ("Обозначения: $s, t, u$ — простые субъекты; $p, q$ — одноместные простые предикаты, $r$ — двухместный "
         "простой предикат; $x, y, z$ — высказывания.")


def set_seed(n):
    rnd.seed(n)


# ---------- явные границы (обозначения: ∼, тильда и ↓ — только перед выражениями с явными границами) ----------
def t_bounded(e):
    """Термин можно поставить после ∼ и слева от ↓."""
    return isinstance(e, Atom) or (isinstance(e, Op) and e.op in ("conj", "disj", "tuple", "each", "some", "name", "opp"))


def t_member(e):
    """Член записи $(a \\cdot b)$, $(a \\vee b)$."""
    return isinstance(e, Atom) or (isinstance(e, Op) and e.op in ("conj", "disj", "tuple", "name", "opp"))


def t_tilde(e):
    """Под тильду — только простой член или короткая запись в скобках."""
    return isinstance(e, Atom) or (isinstance(e, Op) and e.op in ("name", "conj", "disj") and len(tex(e)) <= 16)


def s_arrow(e):
    """Высказывание рядом с ↓ — буква или запись в скобках."""
    return isinstance(e, Atom) or (isinstance(e, St) and e.op in ("basic", "conj", "sdis", "wdis", "cond"))


def s_bounded(e):
    """Высказывание можно поставить после ↓, перед ↓, членом (x·y), после ∼, в [ ]."""
    if isinstance(e, Atom):
        return True
    if isinstance(e, St):
        if e.op in ("basic", "conj", "sdis", "wdis", "cond"):
            return True
        if e.op == "neg":
            return s_bounded(e.args[0])
    return False


# ---------- случайные выражения ----------
def r_subject(d, full):
    if d <= 0 or rnd.random() < 0.18:
        return rnd.choice(SUBJ)
    k = rnd.choice(["neg", "opp", "conj", "disj", "each", "some", "tuple", "fact", "asuch", "name", "name", "fact"])
    return r_build(k, "S", d, full)


def r_predicate(d, full):
    if d <= 0 or rnd.random() < 0.18:
        return rnd.choice([p, q, r])
    k = rnd.choice(["neg", "opp", "conj", "disj", "each", "some", "such", "asuch", "such", "asuch"])
    return r_build(k, "P", d, full)


def r_term(d, full):
    return r_subject(d, full) if rnd.random() < 0.55 else r_predicate(d, full)


def r_bt(gen, d, full):
    for _ in range(50):
        e = gen(d, full)
        if t_bounded(e):
            return e
    return gen(0, full)


def r_bs(d, full, ok=None):
    ok = ok or s_bounded
    for _ in range(50):
        e = r_statement(d, full)
        if ok(e):
            return e
    return rnd.choice(LET)


def r_with(gen, d, full, ok):
    for _ in range(50):
        e = gen(d, full)
        if ok(e):
            return e
    return gen(0, full)


def r_build(k, want, d, full):
    gen = r_subject if want == "S" else r_predicate
    if k == "neg":
        return G.tneg(r_bt(gen, d - 1, full))
    if k == "opp":
        return G.opp(r_with(gen, d - 1, full, t_tilde))
    if k in ("conj", "disj"):
        a, b = r_with(gen, d - 1, full, t_member), r_with(gen, d - 2, full, t_member)
        if a == b:
            b = rnd.choice(SUBJ if want == "S" else PRED1)
        return (G.tconj if k == "conj" else G.tdisj)(a, b) if a != b else a
    if k in ("each", "some", "tuple"):
        a, b = gen(d - 1, full), gen(d - 2, full)
        if a == b:
            return a
        return {"each": G.each, "some": G.some, "tuple": G.tup}[k](a, b)
    if k == "fact":
        return G.fact(r_bs(d - 1, full, s_arrow))
    if k == "such":
        return G.such(r_bs(d - 1, full, s_arrow))
    if k == "asuch":
        return G.asuch(r_bt(gen, d - 1, full), r_bs(d - 2, full, s_arrow))
    if k == "name":
        c = rnd.random()
        inner = r_subject(d - 1, full) if c < .4 else r_predicate(d - 1, full) if c < .7 else r_statement(d - 1, full)
        return G.name(inner)
    raise ValueError(k)


def r_basic():
    m = rnd.choice(["", "", "not", "q"])
    if rnd.random() < 0.5:
        return G.basic(rnd.choice(SUBJ), rnd.choice(PRED1), m)
    return G.basic(G.tup(*rnd.sample(SUBJ, 2)), r, m)


def r_basic_full(d):
    """Основное высказывание; в скобочном субъекте — составные субъекты."""
    m = rnd.choice(["", "", "not", "q"])
    if rnd.random() < 0.45 or d <= 0:
        return r_basic()
    a, b = r_subject(d - 1, True), r_subject(d - 2, True)
    if a == b:
        return r_basic()
    return G.basic(G.tup(a, b), r, m)


def r_statement(d, full):
    """full=False — только буквы (для § 4: составные высказывания ещё не изучены)."""
    if not full:
        return rnd.choice(LET)
    if d <= 0 or rnd.random() < 0.15:
        return rnd.choice(LET + [r_basic()])
    k = rnd.choice(["basic", "basic", "neg", "conj", "sdis", "wdis", "quant", "cond", "conj", "cond"])
    if k == "basic":
        return r_basic_full(d)
    if k == "neg":
        return G.sneg(r_bs(d - 1, full))
    if k in ("conj", "sdis", "wdis"):
        n = 3 if rnd.random() < 0.2 else 2
        mem = [r_bs(d - 1 - (i > 0), full) for i in range(n)]
        if len({tex(m) for m in mem}) < n:
            return mem[0]
        return {"conj": G.sconj, "sdis": G.sdis, "wdis": G.wdis}[k](*mem)
    if k == "quant":
        a = r_term(d - 2, full) if rnd.random() < .6 else rnd.choice(SUBJ + PRED1)
        body = r_statement(d - 1, full)
        if not (s_bounded(body) or (isinstance(body, St) and body.op == "quant")):
            body = r_bs(d - 1, full)
        return rnd.choice([G.forall, G.exists])(a, body, rnd.choice(["", "not", "q"]))
    a, b = r_bs(d - 1, full), r_statement(d - 2, full)
    return G.cond(a, b, rnd.choice(["", "not", "q"]))


def lines_of(e, atoms=True):
    return parse(e, atoms)


def plen(e, atoms=True):
    return len(parse(e, atoms))


def pick(gen, ok, tries=4000):
    for _ in range(tries):
        e = gen()
        if ok(e):
            return e
    raise RuntimeError("не найдено выражение")


SEEN = set()


def fresh(gen, ok, tries=4000):
    def ok2(e):
        return tex(e) not in SEEN and ok(e)
    e = pick(gen, ok2, tries)
    SEEN.add(tex(e))
    return e


# ---------- запись разбора ----------
def row(n, e, v, rf, hide_e=False, hide_r=False):
    left = "…" if hide_e else f"${tex(e)}$"
    right = "… (…)" if hide_r else f"{v} ({rf})"
    return f"{n}. {left} — {right}"


def show(rows, hide_e=(), hide_r=()):
    return "\n".join(row(n, e, v, rf, n in hide_e, n in hide_r) for n, (e, v, rf) in enumerate(rows, 1))


# ---------- порча строки разбора (правдоподобные ошибки) ----------
def corrupt(e, v, rf, mode):
    """Неверная запись строки и пояснение ошибки; None, если правдоподобной порчи нет."""
    if isinstance(e, Op):
        o, k = e.op, kind(e)
        if o in ("conj", "disj") and k:
            w = next(iter(k))
            D = "D1" if w == "P" else "D2"
            return (v, f"§ 4, {D}, п. 4",
                    f"$({'a^1 \\cdot \\ldots \\cdot a^n' if o == 'conj' else 'a^1 \\vee \\ldots \\vee a^n'})$ строится по п. 3 {D} § 4 "
                    f"(с. 5–6), а п. 4 — это ${'\\cdot' if o == 'conj' else '\\vee'}\\,(a^1, \\ldots, a^n)$")
        if o in ("each", "some") and k:
            w = next(iter(k))
            D = "D1" if w == "P" else "D2"
            return (v, f"§ 4, {D}, п. 3",
                    f"${'\\cdot' if o == 'each' else '\\vee'}\\,(a^1, \\ldots, a^n)$ — п. 4 {D} § 4 (с. 5–6), а п. 3 — "
                    f"запись с ${'\\cdot' if o == 'each' else '\\vee'}$ между членами")
        if o == "fact":
            return ("предикат", "§ 4, D1, п. 5",
                    "$\\downarrow x$ (стрелка перед высказыванием) — субъект по D2, п. 6 § 4 (с. 6); предикат по D1, п. 5 — "
                    "$x \\downarrow$ (стрелка после высказывания)")
        if o == "such":
            return ("субъект", "§ 4, D2, п. 6",
                    "$x \\downarrow$ — предикат по D1, п. 5 § 4 (с. 6); субъект по D2, п. 6 — $\\downarrow x$")
        if o == "asuch" and "S" in k:
            return (v, "§ 4, D2, п. 6",
                    "$a \\downarrow x$ при субъекте $a$ — субъект по D2, п. 7 § 4 (с. 6); п. 6 D2 — это $\\downarrow x$")
        if o == "asuch" and "P" in k:
            return ("субъект", "§ 4, D2, п. 7",
                    "в $a \\downarrow x$ вид определяется термином $a$ слева: $a$ — предикат, значит, и $a \\downarrow x$ — "
                    "предикат по D1, п. 6 § 4 (с. 6)")
        if o == "name":
            inner = e.args[0]
            if "P" in kind(inner):
                return ("предикат", "§ 4, D1, п. 2",
                        "$[a]$ — всегда субъект по D2, п. 8 § 4 (с. 6), даже если $a$ — предикат")
            return (v, "§ 4, D2, п. 2", "квадратные скобки $[a]$ дают субъект по D2, п. 8 § 4 (с. 6), а не по п. 2")
        if o == "tuple":
            return ("предикат", "§ 4, D1, п. 4",
                    "$(a^1, \\ldots, a^n)$ без знака перед скобкой — субъект по D2, п. 5 § 4 (с. 6); таких предикатов нет")
        if o in ("neg", "opp") and k:
            w = next(iter(k))
            other = "предикат" if w == "S" else "субъект"
            return (other, f"§ 4, D{2 if w == 'P' else 1}, п. 2",
                    "$\\sim a$ и $\\tilde a$ — термин того же вида, что и $a$ (D1, п. 2; D2, п. 2 § 4, с. 5–6)")
    if isinstance(e, St) and mode == 5:
        o = e.op
        if o == "basic":
            return (v, "§ 5, D2, п. 1",
                    "основное высказывание $(a \\leftarrow b)$, $(a \\urcorner\\!\\leftarrow b)$, $(a? \\leftarrow b)$ "
                    "получается по D1 § 5 (с. 7); п. 1 D2 лишь говорит, что основные высказывания — высказывания")
        if o == "quant":
            return (v, "§ 5, D2, п. 5",
                    "высказывания с кванторами — по D2, п. 4 § 5 (с. 7); п. 5 — высказывания с $\\to$")
        if o == "cond":
            return (v, "§ 5, D2, п. 4",
                    "высказывания с $\\to$ — по D2, п. 5 § 5 (с. 8); п. 4 — высказывания с кванторами")
        if o in ("conj", "sdis", "wdis"):
            return (v, "§ 5, D2, п. 2", "$(x^1 \\cdot \\ldots \\cdot x^n)$, $(x^1 : \\ldots : x^n)$, $(x^1 \\vee \\ldots \\vee x^n)$ — "
                    "по D2, п. 3 § 5 (с. 7); п. 2 — отрицание $\\sim x$")
        if o == "neg":
            return ("предикат", "§ 4, D1, п. 2",
                    "$\\sim$ перед высказыванием образует высказывание по D2, п. 2 § 5 (с. 7); D1, п. 2 § 4 относится к "
                    "$\\sim a$ для предиката $a$")
    return None


# ---------- карточки ----------
def render(cid, c, ch=0):
    sec = int(cid.split(".")[1].split("-")[0])
    sysl = f'system: "{c["system"]}"\n' if c.get("system") else ""
    return (f'---\nid: "{cid}"\nchapter: {ch}\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\n'
            f'step: {c["step"]}\ncondition: {c.get("condition", "def")}\nform: {c["form"]}\nanswer: {c["answer"]}\n'
            f'source: "{c["source"]}"\n{sysl}generated: true\ntags: [{c["tags"]}]\n---\n\n'
            f'## Условие\n\n{c["cond"]}\n\n## Ответ\n\n{c["ans"]}\n\n## Решение\n\n{c["sol"]}\n')


def replace_cards(path, cards, ch=0):
    """Заменяет карточки файла главы с теми же номерами. cards: {id: card}."""
    parts = re.split(r"(\n=====\n)", path.read_text(encoding="utf-8"))
    done = set()
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "([\d.]+-\d{3})"', chunk, re.M)
        if m and m.group(1) in cards:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            parts[i] = lead + render(m.group(1), cards[m.group(1)], ch).rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
            done.add(m.group(1))
    path.write_text("".join(parts), encoding="utf-8")
    missing = set(cards) - done
    assert not missing, f"нет карточек: {sorted(missing)}"
    return len(done)
