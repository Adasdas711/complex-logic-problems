#!/usr/bin/env python3
"""Серии для занятий 12–15: гл. 1, § 4–9 (непарадоксальность, главная интерпретация, непротиворечивость,
полнота и канонические формы, независимость, подстановка). Ответы вычисляются моделями s1.py и indep.py.
Пишет drafts/01.04-09-gen.md.
"""
import importlib.util
import random
import sys
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import indep as I  # noqa: E402
from s1 import (C, D, IMP, N, OR, V, atoms, counterexample, ftex, new_atoms, strong_tautology,  # noqa: E402
                tautology, tex, value)


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / "scripts" / "gen" / f"{name}.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


G2 = load("g01_02")
card, verdict_text, env_text = G2.card, G2.verdict_text, G2.env_text
CONV = G2.CONV
CRIT = G2.CRIT
L = "абвгдежз"
rnd = random.Random(1970_33)
a, b, c, x, y, z = (V(n) for n in "abcxyz")
DEDUP = set()


def rand_stmt(names, depth):
    if depth == 0 or rnd.random() < 0.25:
        v = V(rnd.choice(names))
        return N(v) if rnd.random() < 0.35 else v
    k = rnd.choice(["neg", "conj", "conj", "dis", "dis"])
    if k == "neg":
        s = rand_stmt(names, depth - 1)
        return N(s) if s[0] != "neg" else s
    n = 2 if rnd.random() < 0.8 else 3
    args = tuple(rand_stmt(names, depth - 1) for _ in range(n))
    if len(set(args)) < n:
        return rand_stmt(names, depth)
    return (k, args)


def fresh(gen, ok=lambda *a: True, tries=500):
    for _ in range(tries):
        f = gen()
        key = repr(f)
        if key not in DEDUP and ok(f):
            DEDUP.add(key)
            return f
    raise RuntimeError("не удалось подобрать")


def is_contr(f):
    names = sorted(atoms(f))
    return all(value(f, dict(zip(names, v))) == 0 for v in product((0, 1), repeat=len(names)))


def is_taut(f):
    names = sorted(atoms(f))
    return all(value(f, dict(zip(names, v))) == 1 for v in product((0, 1), repeat=len(names)))


def kind(f):
    return "тавтология" if is_taut(f) else ("противоречие" if is_contr(f) else "ни то ни другое")


# ---------- канонические формы (§ 7, D2, D3) ----------
def canon(f, names=None):
    names = sorted(names or atoms(f))
    rows = [env for env in (dict(zip(names, v)) for v in product((1, 0), repeat=len(names))) if value(f, env)]
    mem = []
    for env in rows:
        lits = [V(n) if env[n] else N(V(n)) for n in names]
        mem.append(lits[0] if len(lits) == 1 else C(*lits))
    return mem[0] if len(mem) == 1 else D(*mem)


def lit(f):
    return f[0] == "v" or (f[0] == "neg" and f[1][0] == "v")


def canon_violation(f):
    """None, если f в канонической форме по D2 (с. 25–26), иначе пункт 'а', 'b' или 'c'."""
    mem = list(f[1]) if f[0] == "dis" else [f]
    if len(mem) == 2 and mem[1] == N(mem[0]):
        return None                                   # п. 1: x : ~x
    for m in mem:
        ls = list(m[1]) if m[0] == "conj" else [m]
        if not all(lit(q) for q in ls):
            return "а"
        key = [(q[1] if q[0] == "v" else q[1][1], q[0] == "neg") for q in ls]
        if len(set(key)) < len(key) or key != sorted(key):
            return "b"
    if len(set(mem)) < len(mem):
        return "c"
    return None


# ---------------- § 4 ----------------
def sec4():
    out, SRC = [], "с. 21–22, гл. 1, § 4"
    its = []
    for _ in range(5):
        p, q = fresh(lambda: (rand_stmt("xyz", 2), rand_stmt("xyzu", 2)), lambda f: True)
        its.append((p, q))
    ans = "; ".join(f"{L[k]}) " + (", ".join(f"${t}$" for t in sorted(new_atoms(p, q))) or "нет")
                    for k, (p, q) in enumerate(its))
    body = (f"## Условие\n\n{CONV.replace('x, y, z, u, w', 'x, y, z, u')} Для каждой формулы выпишите элементарные "
            "высказывания, которые входят в заключение, но не входят в посылку.\n\n" +
            "\n".join(f"{L[k]}) ${ftex(p, q)}$" for k, (p, q) in enumerate(its)) +
            f"\n\n## Ответ\n\n{ans}\n\n## Решение\n\nПо § 4, MT1 (с. 21) формулы, где такие высказывания есть, "
            "недоказуемы в $S^1$.")
    out.append(card(4, 2, "D", "iso", "sym", "short", "S1, непарадоксальность", body, "новые-в-заключении", SRC))
    # ступень 3, диагностика: обращение MT1
    its = []
    while len(its) < 4:
        p = rand_stmt("xy", 2)
        q = rand_stmt("xy", 2)
        if new_atoms(p, q) or repr((p, q)) in DEDUP:
            continue
        if len([1 for P, Q in its if strong_tautology(P, Q)]) >= 2 and strong_tautology(p, q):
            continue
        DEDUP.add(repr((p, q)))
        its.append((p, q))
    if all(strong_tautology(p, q) for p, q in its):
        its[-1] = (x, N(x))
    bad = [k for k, (p, q) in enumerate(its) if not strong_tautology(p, q)]
    body = (f"## Условие\n\n{CONV} Студент рассуждает: «В заключение каждой из этих формул не входят элементарные "
            "высказывания, отсутствующие в посылке. Значит, по § 4, MT1 все они доказуемы в $S^1$». Найдите ошибку и "
            "укажите, какие формулы на самом деле недоказуемы.\n\n" +
            "\n".join(f"{L[k]}) ${ftex(p, q)}$" for k, (p, q) in enumerate(its)) +
            "\n\n## Ответ\n\nMT1 — необходимое условие доказуемости, а не достаточное. Недоказуемы: " +
            ", ".join(f"{L[k]})" for k in bad) + ".\n\n## Решение\n\nMT1 (с. 21): если $x \\vdash y$ — теорема, то в $y$ "
            "нет новых элементарных высказываний; обратное не утверждается. Недоказуемые формулы не тавтологии "
            "(§ 5, MT1, с. 22):\n" + "\n".join(f"- {L[k]}) при {env_text(counterexample(*its[k]))} посылка — 1, "
                                               "заключение — 0." for k in bad))
    out.append(card(4, 3, "E", "iso", "sym", "short", "S1, непарадоксальность, диагностика", body, None, SRC))
    # ступень 5: MT2
    its = []
    for kind_ in rnd.sample(["diff", "diff", "eq", "neq", "eq"], 5):
        while True:
            p = rand_stmt("xyz", 2)
            q = rand_stmt("xyz", 2)
            same = atoms(p) == atoms(q)
            eq = same and tautology(p, q) and tautology(q, p)
            if {"diff": not same, "eq": eq, "neq": same and not eq}[kind_] and repr((p, q)) not in DEDUP:
                DEDUP.add(repr((p, q)))
                its.append((p, q, kind_))
                break
    ans = "; ".join(f"{L[k]}) " + {"diff": "нет (MT2)", "eq": "да", "neq": "нет (не равнозначны)"}[kd]
                    for k, (_, _, kd) in enumerate(its))
    sol = []
    for k, (p, q, kd) in enumerate(its):
        if kd == "diff":
            sol.append(f"{L[k]}) множества элементарных высказываний различны — по § 4, MT2 (с. 21) обе формулы "
                       "теоремами быть не могут.")
        elif kd == "eq":
            sol.append(f"{L[k]}) элементарные высказывания одни и те же, значения совпадают при всех комбинациях — "
                       "обе формулы сильные тавтологии и по § 7, MT6 (с. 32) доказуемы.")
        else:
            pp, qq = (p, q) if not tautology(p, q) else (q, p)
            sol.append(f"{L[k]}) MT2 не мешает, но ${ftex(pp, qq)}$ не тавтология (при "
                       f"{env_text(counterexample(pp, qq))}), по § 5, MT1 (с. 22) она не теорема.")
    body = (f"## Условие\n\n{CONV} Для каждой пары высказываний ответьте: могут ли обе формулы $A \\vdash B$ и "
            f"$B \\vdash A$ быть теоремами $S^1$? {CRIT}\n\n" +
            "\n".join(f"{L[k]}) $A$ — ${tex(p)}$, $B$ — ${tex(q)}$" for k, (p, q, _) in enumerate(its)) +
            f"\n\n## Ответ\n\n{ans}\n\n## Решение\n\n" + "\n".join(sol))
    out.append(card(4, 5, "C", "iso", "sym", "short", "S1, MT2", body, "MT2", "с. 21–22, 32, гл. 1, § 4–7"))
    return out


# ---------------- § 5 ----------------
SRC5 = "с. 22–24, гл. 1, § 5"


def value_card(level=2, typ="D"):
    names = "xyz"
    env = {n: rnd.randint(0, 1) for n in names}
    its = [fresh(lambda: rand_stmt(names, 3), lambda f: f[0] != "v") for _ in range(5)]
    body = (f"## Условие\n\n{CONV} Вычислите при главной интерпретации значения высказываний при {env_text(env)}.\n\n" +
            "\n".join(f"{L[k]}) ${tex(f)}$" for k, f in enumerate(its)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[k]}) {value(f, env)}" for k, f in enumerate(its)) +
            "\n\n## Решение\n\nПункты 2–4 главной интерпретации (с. 22): $\\sim$ меняет значение; конъюнкция имеет "
            "значение 1, когда все члены — 1; $x^1 : \\ldots : x^n$ — когда одно и только одно из $x^i$ имеет "
            "значение 1. Значения вычисляются от элементарных высказываний к целому.")
    return card(5, level, typ, "iso", "sym", "short", "S1, интерпретация", body, "значения", SRC5)


def taut_card(level=3, n=4):
    its = []
    while len(its) < n:
        p = rand_stmt("xyz", 2)
        q = rand_stmt("xyz", 2)
        if repr((p, q)) in DEDUP or new_atoms(p, q) and rnd.random() < 0.5:
            continue
        if sum(tautology(P, Q) for P, Q in its) >= n // 2 + 1 and tautology(p, q):
            continue
        DEDUP.add(repr((p, q)))
        its.append((p, q))
    ans = "; ".join(f"{L[k]}) " + ("да" if tautology(p, q) else "нет") for k, (p, q) in enumerate(its))
    sol = "\n".join(f"{L[k]}) " + ("ни при каких значениях посылка не имеет значения 1 при заключении 0 — "
                                   "тавтология (D1, с. 22)." if tautology(p, q) else
                                   f"при {env_text(counterexample(p, q))} посылка — 1, заключение — 0; формула имеет "
                                   "значение 0 (п. 5, с. 22).") for k, (p, q) in enumerate(its))
    body = (f"## Условие\n\n{CONV} Какие из формул следования — тавтологии при главной интерпретации (§ 5, D1)? Для "
            "остальных укажите значения элементарных высказываний, при которых формула имеет значение 0.\n\n" +
            "\n".join(f"{L[k]}) ${ftex(p, q)}$" for k, (p, q) in enumerate(its)) +
            f"\n\n## Ответ\n\n{ans}\n\n## Решение\n\n{sol}")
    return card(5, level, "C", "iso", "sym", "short", "S1, тавтологии", body, "тавтология-ли", SRC5)


def kind_card(level, sec=5, src=SRC5, series="тавтология-противоречие"):
    its = []
    want = ["тавтология", "противоречие", "ни то ни другое", rnd.choice(["тавтология", "противоречие"]),
            "ни то ни другое"]
    rnd.shuffle(want)
    for w in want:
        its.append(fresh(lambda: rand_stmt("xy", 3), lambda f: kind(f) == w and f[0] != "v"))
    body = (f"## Условие\n\n{CONV} Определите для каждого высказывания: тавтология (§ 5, D2), противоречие (§ 5, D3) "
            "или ни то ни другое.\n\n" + "\n".join(f"{L[k]}) ${tex(f)}$" for k, f in enumerate(its)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[k]}) {kind(f)}" for k, f in enumerate(its)) +
            "\n\n## Решение\n\nПеребираем 4 комбинации значений $x$, $y$ (с. 22). Тавтология — значение 1 при всех "
            "комбинациях; противоречие — высказывание, отрицание которого тавтология, то есть значение 0 при всех "
            "комбинациях.")
    return card(sec, level, "C", "iso", "sym", "short", "S1, тавтологии", body, series, src)


def wrong_value_card(level=2):
    env = {n: rnd.randint(0, 1) for n in "xyz"}
    f = fresh(lambda: rand_stmt("xyz", 3), lambda f: f[0] == "dis" and len(f[1]) >= 2)
    v = value(f, env)
    body = (f"## Условие\n\n{CONV} Студент вычисляет значение ${tex(f)}$ при {env_text(env)} и получает {1 - v}: "
            "«дизъюнкция истинна, если истинен хотя бы один член». Найдите ошибку и вычислите верно.\n\n## Ответ\n\n"
            f"Верно — {v}: $x^1 : \\ldots : x^n$ имеет значение 1, когда одно и только одно из $x^i$ имеет значение 1 "
            f"(главная интерпретация, п. 4, с. 22).\n\n## Решение\n\nЗначения членов: " +
            ", ".join(f"${tex(m)}$ = {value(m, env)}" for m in f[1]) + ". Студент читает «$:$» как соединительную "
            "дизъюнкцию $\\vee$ («по крайней мере одно из», § 3, с. 20).")
    if sum(value(m, env) for m in f[1]) < 2 and v == 1 or sum(value(m, env) for m in f[1]) == 0:
        return None
    return card(5, level, "E", "iso", "sym", "short", "S1, интерпретация, диагностика", body, None, SRC5)


def sec5():
    out = []
    # ступень 1
    items = [(N(V("x")), "2"), (C(x, y), "3"), (D(x, y, z), "4"), (None, "5"), (V("x"), "1")]
    rnd.shuffle(items)
    txt = lambda f: "$x \\vdash y$" if f is None else (f"элементарное высказывание ${tex(f)}$" if f[0] == "v"
                                                         else f"${tex(f)}$")
    body = (f"## Условие\n\n{CONV} Какой пункт главной интерпретации (с. 22) задаёт значение каждого выражения?\n\n" +
            "\n".join(f"{L[k]}) {txt(f)}" for k, (f, _) in enumerate(items)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[k]}) п. {p}" for k, (_, p) in enumerate(items)) +
            "\n\n## Решение\n\nС. 22: п. 1 — элементарные высказывания (значения 1 и 0); п. 2 — отрицание; п. 3 — "
            "конъюнкция; п. 4 — сильная дизъюнкция; п. 5 — формула следования.")
    out.append(card(5, 1, "R", "iso", "sym", "short", "S1, интерпретация", body, None, SRC5))
    out.append(kind_card(1).replace("level: 1", "level: 1", 1))
    for _ in range(4):
        out.append(value_card())
    w = None
    while not w:
        w = wrong_value_card()
    out.append(w)
    for _ in range(7):
        out.append(taut_card())
    # ступень 3, диагностика: строка таблицы
    for _ in range(2):
        p, q = fresh(lambda: (rand_stmt("xy", 2), rand_stmt("xy", 2)), lambda f: not tautology(*f) and
                     not new_atoms(*f))
        env = counterexample(p, q)
        body = (f"## Условие\n\n{CONV} Студент проверил формулу ${ftex(p, q)}$: «при {env_text(env)} посылка "
                f"имеет значение {value(p, env)}, заключение — {value(q, env)}, значит, формула имеет значение 1; так "
                "при всех значениях — тавтология». Найдите ошибку.\n\n## Ответ\n\nПри этих значениях формула имеет "
                "значение 0 (посылка 1, заключение 0), поэтому она не тавтология.\n\n## Решение\n\nГлавная "
                "интерпретация, п. 5 (с. 22): $x \\vdash y$ имеет значение 0 тогда и только тогда, когда $x$ имеет "
                "значение 1, а $y$ — 0. D1 (с. 22): тавтология — значение 1 при любых значениях.")
        out.append(card(5, 3, "E", "iso", "sym", "short", "S1, интерпретация, диагностика", body, None, SRC5))
    # ступень 4: дополнение таблицы (2) + диагностика (1)
    for _ in range(2):
        f = fresh(lambda: rand_stmt("xy", 2), lambda f: f[0] in ("dis", "conj") and len(atoms(f)) == 2)
        rows = [dict(x=p, y=q) for p, q in product((1, 0), repeat=2)]
        hide = sorted(rnd.sample(range(4), 2))
        tab = "\n".join(f"| {r['x']} | {r['y']} | {'?' if i in hide else value(f, r)} |" for i, r in enumerate(rows))
        body = (f"## Условие\n\n{CONV} Заполните пропуски в таблице значений высказывания ${tex(f)}$.\n\n"
                f"| $x$ | $y$ | значение |\n|---|---|---|\n{tab}\n\n## Ответ\n\n" +
                "; ".join(f"при $x = {rows[i]['x']}$, $y = {rows[i]['y']}$ — {value(f, rows[i])}" for i in hide) +
                "\n\n## Решение\n\nПункты 2–4 главной интерпретации (с. 22).")
        out.append(card(5, 4, "D", "complete", "sym", "short", "S1, интерпретация", body, "таблица", SRC5))
    f = D(x, y, z)
    body = (f"## Условие\n\n{CONV} Студент составил таблицу для $x : y : z$ и в строке $x = y = z = 1$ записал 1: "
            "«$x : y$ даёт 0, а $0 : 1$ даёт 1». Найдите ошибку.\n\n## Ответ\n\nВерно — 0: по п. 4 главной "
            "интерпретации $x^1 : \\ldots : x^n$ имеет значение 1, только когда одно и только одно из $x^i$ имеет "
            "значение 1.\n\n## Решение\n\nСтудент вычислил $(x : y) : z$, а это другое высказывание: в $S^1$ "
            "$x : y : z$ — дизъюнкция трёх членов (с. 15, 22).")
    out.append(card(5, 4, "E", "complete", "sym", "short", "S1, интерпретация, диагностика", body, None, SRC5))
    # ступень 6: открытый исход (3 генерированных)
    for _ in range(3):
        out.append(kind_card(6))
    return out


# ---------------- § 6 ----------------
SRC6 = "с. 22, 25, гл. 1, § 5–6"


def sec6():
    out = [kind_card(3, 6, SRC6, "противоречие-ли")]
    its = []
    for want in rnd.sample([True, True, False, False], 4):
        p = fresh(lambda: rand_stmt("xy", 2), lambda f: is_contr(f) == want and f[0] != "v")
        q = rnd.choice([y, x, N(x)])
        its.append((p, q))
    ans = "; ".join(f"{L[k]}) " + ("да" if strong_tautology(p, C(N(q), q)) else "нет") for k, (p, q) in enumerate(its))
    sol = "\n".join(f"{L[k]}) " + (f"${tex(p)}$ — противоречие, в заключение не входят новые элементарные высказывания: "
                                   "сильная тавтология, по § 7, MT6 (с. 32) — теорема." if strong_tautology(p, C(N(q), q))
                                   else (f"${tex(p)}$ не противоречие, по § 6, MT2 (с. 25) формула не теорема."
                                         if not is_contr(p) else "в заключение входит элементарное высказывание, "
                                         "которого нет в посылке (§ 4, MT1, с. 21).")) for k, (p, q) in enumerate(its))
    body = (f"## Условие\n\n{CONV} Доказуемы ли в $S^1$ формулы? {CRIT}\n\n" +
            "\n".join(f"{L[k]}) ${ftex(p, C(N(q), q))}$" for k, (p, q) in enumerate(its)) +
            f"\n\n## Ответ\n\n{ans}\n\n## Решение\n\n{sol}")
    out.append(card(6, 6, "C", "open", "sym", "short", "S1, непротиворечивость", body, "x-следует-противоречие",
                    "с. 21, 25, 32, гл. 1, § 4–7"))
    return out


# ---------------- § 7 ----------------
SRC7 = "с. 25–32, гл. 1, § 7"


def classify_card(level, n=4):
    its, kinds = [], ["сильная", "сильная", "только", "не"]
    rnd.shuffle(kinds)
    for kd in kinds[:n]:
        def ok(f):
            p, q = f
            return {"сильная": strong_tautology(p, q), "только": tautology(p, q) and not strong_tautology(p, q),
                    "не": not tautology(p, q)}[kd]
        its.append(fresh(lambda: (rand_stmt("xy", 2), rand_stmt("xyz", 2)), ok))
    lab = lambda p, q: ("сильная тавтология" if strong_tautology(p, q) else
                        "тавтология, но не сильная" if tautology(p, q) else "не тавтология")
    body = (f"## Условие\n\n{CONV} Для каждой формулы определите: сильная тавтология (§ 7, D1), тавтология, но не "
            "сильная, или не тавтология.\n\n" + "\n".join(f"{L[k]}) ${ftex(p, q)}$" for k, (p, q) in enumerate(its)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[k]}) {lab(p, q)}" for k, (p, q) in enumerate(its)) +
            "\n\n## Решение\n\nD1 § 7 (с. 25): сильная тавтология — тавтология (§ 5, D1), в заключение которой не "
            "входят элементарные высказывания, отсутствующие в посылке.\n" +
            "\n".join(f"{L[k]}) " + (f"новые в заключении: " + ", ".join(f"${t}$" for t in sorted(new_atoms(p, q))) + "."
                                     if tautology(p, q) and new_atoms(p, q) else
                                     (f"при {env_text(counterexample(p, q))} формула имеет значение 0."
                                      if not tautology(p, q) else "тавтология без новых элементарных высказываний."))
                      for k, (p, q) in enumerate(its)))
    return card(7, level, "C", "iso", "sym", "short", "S1, сильная тавтология", body, "сильная-ли", SRC7)


def canon_candidates():
    good = [canon(rand_stmt("ab", 2)) for _ in range(3)]
    bad = [D(C(a, b), C(b, N(a))), D(C(N(a), b), C(N(a), b)), D(C(a, N(b)), N(C(a, b))), C(b, a),
           D(C(a, N(a)), C(N(b), b)), D(a, C(a, b)), D(C(a, a), N(a)), D(C(a, b), C(b, c))]
    return good, bad


def canon_check_card(level=3, typ="R"):
    good, bad = canon_candidates()
    its = [g for g in good if not is_contr(g)][:2] + rnd.sample(bad, 3)
    its = [i for i in its if repr(i) not in DEDUP][:5]
    for i in its:
        DEDUP.add(repr(i))
    rnd.shuffle(its)
    ans = "; ".join(f"{L[k]}) " + ("да" if canon_violation(f) is None else f"нет, нарушен п. 2{canon_violation(f)}")
                    for k, f in enumerate(its))
    body = (f"## Условие\n\nБуквы $a, b, c$ — элементарные высказывания в алфавитном порядке $a, b, c$. Находится ли "
            "высказывание в канонической форме (§ 7, D2)? Если нет — какое условие нарушено?\n\n" +
            "\n".join(f"{L[k]}) ${tex(f)}$" for k, f in enumerate(its)) +
            f"\n\n## Ответ\n\n{ans}\n\n## Решение\n\nD2 (с. 25–26), п. 2: а) каждый член — конъюнкция элементарных "
            "высказываний с отрицанием или без; b) в каждом члене элементарные высказывания различны как пары "
            "«высказывание с отрицанием/без» и идут в алфавитном порядке, а если высказывание одно и то же, сначала "
            "без отрицания; c) все члены попарно различны. Порядок самих членов D2 не задаёт.")
    return card(7, level, typ, "iso", "sym", "short", "S1, каноническая форма", body, "канон-ли", SRC7)


def canon_build_card(level=4):
    f = fresh(lambda: rand_stmt("ab", 3), lambda f: not is_contr(f) and atoms(f) == {"a", "b"} and f[0] != "v"
              and canon(f) != f and len(canon(f)[1]) < 4)
    cf = canon(f)
    rows = [dict(a=p, b=q) for p, q in product((1, 0), repeat=2)]
    body = (f"## Условие\n\nБуквы $a, b$ — элементарные высказывания. Найдите каноническую форму (§ 7, D2, D3) "
            f"высказывания ${tex(f)}$.\n\n## Ответ\n\n${tex(cf)}$ (порядок членов может быть любым)\n\n## Решение\n\n"
            "Значения (главная интерпретация, с. 22):\n\n| $a$ | $b$ | значение |\n|---|---|---|\n" +
            "\n".join(f"| {r['a']} | {r['b']} | {value(f, r)} |" for r in rows) +
            "\n\nКаждой строке со значением 1 соответствует член — конъюнкция $a$, $b$ с отрицаниями там, где значение 0. "
            "Полученное высказывание в канонической форме (D2), равнозначно исходному и содержит те же элементарные "
            "высказывания; поэтому обе формулы следования между ними — сильные тавтологии и по MT6 (с. 32) теоремы, "
            "что и требует D3 (с. 26).")
    return card(7, level, "D", "iso", "sym", "short", "S1, каноническая форма", body, "канон-построить", SRC7)


def canon_wrong_card(level=4):
    f = fresh(lambda: rand_stmt("ab", 3), lambda f: not is_contr(f) and atoms(f) == {"a", "b"} and f[0] != "v"
              and 2 <= len(canon(f)[1] if canon(f)[0] == "dis" else [1]) <= 3)
    cf = canon(f)
    mem = list(cf[1])
    kind_ = rnd.choice(["miss", "order", "extra"])
    if kind_ == "miss":
        wrong = D(*mem[:-1]) if len(mem) > 2 else mem[0]
        why = f"пропущен член ${tex(mem[-1])}$: при соответствующих значениях исходное высказывание имеет значение 1"
    elif kind_ == "order":
        m = mem[0]
        wrong = D(C(m[1][1], m[1][0]), *mem[1:])
        why = "в первом члене нарушен алфавитный порядок (D2, п. 2b)"
    else:
        allm = [C(a, b), C(a, N(b)), C(N(a), b), C(N(a), N(b))]
        ex = [m for m in allm if m not in mem][0]
        wrong = D(*mem, ex)
        why = f"лишний член ${tex(ex)}$: при соответствующих значениях исходное высказывание имеет значение 0"
    body = (f"## Условие\n\nБуквы $a, b$ — элементарные высказывания. Студент нашёл каноническую форму "
            f"${tex(f)}$: ${tex(wrong)}$. Найдите ошибку.\n\n## Ответ\n\nОшибка: {why}. Верно: ${tex(cf)}$.\n\n"
            "## Решение\n\nD2, D3 (с. 25–26): каноническая форма должна быть в канонической форме и равнозначна "
            "исходному высказыванию (обе формулы следования — теоремы, а значит, тавтологии по § 5, MT1).")
    return card(7, level, "E", "iso", "sym", "short", "S1, каноническая форма, диагностика", body, None, SRC7)


def d5_card(level=5):
    while True:
        p = rand_stmt("ab", 2)
        q = rand_stmt("a", 2) if rnd.random() < 0.5 else rand_stmt("b", 2)
        if (atoms(p) == {"a", "b"} and not is_contr(p) and strong_tautology(p, q) and not is_taut(q)
                and repr((p, q)) not in DEDUP):
            DEDUP.add(repr((p, q)))
            break
    xs, ys, yss = canon(p), canon(q), canon(q, atoms(p))
    v = sorted(atoms(p) - atoms(q))
    body = (f"## Условие\n\nБуквы $a, b$ — элементарные высказывания. Формула ${ftex(p, q)}$ — сильная тавтология. "
            "Найдите её каноническую форму $x^* \\vdash y^{**}$ по D5 § 7.\n\n## Ответ\n\n"
            f"${ftex(xs, yss)}$\n\n## Решение\n\nD5 (с. 26). $x^*$ — каноническая форма посылки: ${tex(xs)}$. $y^*$ — "
            f"каноническая форма заключения: ${tex(ys)}$. Высказываний вида $\\sim aa$ в $x^*$ нет, поэтому $z$ пусто. "
            f"$v$ — элементарные высказывания $x^*$, не входящие в $y^*$: ${', '.join(v)}$. $y^{{**}}$ — каноническая "
            f"форма для $y^*({v[0]} : \\sim {v[0]})$; это ${tex(yss)}$: члены — строки со значением 1 по $a$ и $b$.")
    return card(7, level, "D", "vary", "sym", "short", "S1, каноническая форма", body, "D5", SRC7)


def prov_card(level=6, sec=7, src="с. 20–32, гл. 1, § 3–7"):
    while True:
        p = rand_stmt("xy", 1)
        q = rand_stmt("xy", 1)
        kind_ = rnd.choice(["imp", "or", "imp2"])
        if kind_ == "imp":
            pr, co = p, IMP(q, p)
            txt = f"{tex(p)} \\vdash {tex(q)} \\supset {tex(p)}"
        elif kind_ == "or":
            pr, co = C(p, q), OR(p, q)
            txt = f"{tex(C(p, q))} \\vdash {tex(p)} \\vee {tex(q)}"
        else:
            pr, co = C(p, IMP(p, q)), q
            txt = f"{tex(p)}({tex(p)} \\supset {tex(q)}) \\vdash {tex(q)}"
        if repr((pr, co)) not in DEDUP and p != q:
            DEDUP.add(repr((pr, co)))
            break
    v, why = verdict_text(pr, co)
    body = (f"## Условие\n\n{CONV} Доказуема ли в $S^1$ формула ${txt}$? Сокращения — по § 3 (с. 20). {CRIT}\n\n"
            f"## Ответ\n\n{v}\n\n## Решение\n\nРаскрываем сокращения: ${ftex(pr, co)}$. " +
            ("Это сильная тавтология (§ 7, D1), по MT6 (с. 32) — теорема." if v == "доказуема" else why[0].upper() +
             why[1:] + "."))
    return card(sec, level, "C", "open", "sym", "short", "S1, доказуемость", body, "доказуемость-сокращения", src)


def sec7():
    out = [classify_card(2).replace("level: 2", "level: 2")]
    out[0] = out[0].replace("type: C", "type: R")
    out += [classify_card(3), classify_card(3), canon_check_card(3)]
    # ступень 3, диагностика
    p, q = fresh(lambda: (rand_stmt("x", 2), rand_stmt("xy", 2)), lambda f: tautology(*f) and new_atoms(*f))
    body = (f"## Условие\n\n{CONV} Студент: «${ftex(p, q)}$ — тавтология, значит, сильная тавтология и по MT6 — "
            "теорема $S^1$». Найдите ошибку.\n\n## Ответ\n\nНе сильная тавтология: в заключение входит " +
            ", ".join(f"${t}$" for t in sorted(new_atoms(p, q))) + ", отсутствующее в посылке.\n\n## Решение\n\n"
            "§ 7, D1 (с. 25); формула недоказуема по § 4, MT1 (с. 21).")
    out.append(card(7, 3, "E", "iso", "sym", "short", "S1, сильная тавтология, диагностика", body, None, SRC7))
    # ступень 4
    for _ in range(3):
        out.append(canon_build_card())
    out.append(canon_check_card(4, "C"))
    for _ in range(2):
        out.append(canon_wrong_card())
    # ступень 5
    for _ in range(2):
        out.append(d5_card())
    # ступень 6
    for _ in range(4):
        out.append(prov_card())
    return out


# ---------------- § 8 ----------------
SRC8 = "с. 33–35, гл. 1, § 8"
TBL_TEXT = {k: t["note"] for k, t in I.TABLES.items() if t["note"]}


def tbl_intro(k):
    return (f"Таблица для {k} (§ 8, с. 33): значения 1 и 0, отмеченное значение 1; {TBL_TEXT[k]}; остальные операторы "
            "и $\\vdash$ — как при главной интерпретации (§ 5).")


def tval_card(level=2):
    k = rnd.choice(["A1", "A3", "A4", "A9"])
    env = {n: rnd.randint(0, 1) for n in "xyz"}
    its = [fresh(lambda: rand_stmt("xyz", 2), lambda f: f[0] != "v") for _ in range(5)]
    t = I.TABLES[k]
    body = (f"## Условие\n\n{CONV} {tbl_intro(k)} Вычислите в этой таблице значения высказываний при {env_text(env)}."
            "\n\n" + "\n".join(f"{L[i]}) ${tex(f)}$" for i, f in enumerate(its)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[i]}) {I.val(f, env, t)}" for i, f in enumerate(its)) +
            "\n\n## Решение\n\nЗначения вычисляются от элементарных высказываний к целому, но по таблице, а не по главной "
            "интерпретации.")
    return card(8, level, "D", "iso", "sym", "short", "S1, независимость, таблицы", body, "таблица-значения", SRC8)


def fails_card(level, k):
    t = I.TABLES[k]
    p, q = I.SAMPLES[k][0]
    ok, env = I.valid(p, q, t)
    assert not ok
    intro = tbl_intro(k) if k in TBL_TEXT else table_text(k)
    body = (f"## Условие\n\n{CONV} {intro} Покажите, что формула ${ftex(p, q)}$ (пример схемы {k}) в этой таблице не "
            "тавтологична: найдите значения, при которых она принимает неотмеченное значение.\n\n## Ответ\n\n"
            f"Например, при {env_text(env)}: посылка — {I.val(p, env, t)}, заключение — {I.val(q, env, t)}, формула — "
            f"{I.fval(p, q, env, t)}.\n\n## Решение\n\nВычисление по таблице (с. 33–34). Так как остальные аксиомные "
            "схемы в этой таблице тавтологичны, а правила сохраняют тавтологичность, схема " + k + " не выводима из "
            "остальных.")
    return card(8, level, "D", "iso", "sym", "short", "S1, независимость", body, "опровергнуть-аксиому", SRC8)


def table_text(k):
    return {
        "A5": "Трёхзначная таблица с единственным отмеченным значением 0 (с. 33): $\\sim x = 1$ при $x = 1$, $\\sim x = 2$ "
              "при $x = 0$, $\\sim x = 0$ при $x = 2$; $xy = 0$ тогда и только тогда, когда $x = 0$ и $y = 0$, иначе 1; "
              "$x^1 : \\ldots : x^n = 1$; $(x \\vdash y) = 2$, если $x = 0$, а $y = 1$ или $y = 2$, иначе 0; конъюнкция "
              "более чем двух членов $x^1 \\cdot \\ldots \\cdot x^n = 0$ ($n > 2$).",
        "A6": "Та же трёхзначная таблица, что для A5 (с. 33), но конъюнкция более чем двух членов "
              "$x^1 \\cdot \\ldots \\cdot x^n = 1$ ($n > 2$).",
        "A8": "Трёхзначная таблица с отмеченными значениями 0 и 1 (с. 34): $\\sim x = 1$ при $x = 1$, $\\sim x = 2$ при "
              "$x = 0$, $\\sim x = 0$ при $x = 2$; $(x \\vdash y) = 2$, если $x = 0$ или $x = 1$, а $y = 2$, иначе 0; "
              "$xy = 2$ тогда и только тогда, когда $x = 2$ или $y = 2$, иначе 0; $x^1 : \\ldots : x^n = 0$, если одно "
              "и только одно $x^i$ равно 0, а остальные равны 2; $= 2$, если все $x^i$ равны 2; $= 1$ в остальных "
              "случаях.",
        "A13": "Трёхзначная таблица с отмеченными значениями 0 и 1 (с. 34): $\\sim$ и $\\vdash$ — как в таблице для A8; "
               "$xy = 2$ тогда и только тогда, когда $x = 2$ или $y = 2$, иначе 1; $x^1 : \\ldots : x^n = 1$.",
        "A14": "Четырёхзначная таблица с отмеченным значением 0 (с. 34): $\\sim x = x$ при $x = 1$ или $2$, "
               "$\\sim x = 3$ при $x = 0$, $\\sim x = 0$ при $x = 3$; $xy = 0$ тогда и только тогда, когда $x = y = 0$, "
               "иначе 1; $(x \\vdash y) = 2$ тогда и только тогда, когда $x = 0$, а $y$ равно 1, 2 или 3, иначе 0; "
               "$x^1 : \\ldots : x^n = 1$, если хотя бы одно $x^i$ равно 1, иначе 0.",
    }[k]


def cross_card(level=6):
    k = rnd.choice(["A1", "A3", "A4", "A7", "A9", "A10"])
    t = I.TABLES[k]
    names = rnd.sample([n for n in I.SAMPLES if n not in ("A11*", "A12", "A5", "A6")], 4)
    if k not in names:
        names[0] = k
    rnd.shuffle(names)
    res = {n: I.valid(*I.SAMPLES[n][0], t) for n in names}
    body = (f"## Условие\n\n{CONV} {tbl_intro(k)} Какие из формул тавтологичны в этой таблице (принимают значение 1 при "
            "любых значениях элементарных высказываний)?\n\n" +
            "\n".join(f"{L[i]}) ${ftex(*I.SAMPLES[n][0])}$" for i, n in enumerate(names)) +
            "\n\n## Ответ\n\n" + "; ".join(f"{L[i]}) " + ("да" if res[n][0] else "нет") for i, n in enumerate(names)) +
            "\n\n## Решение\n\n" + "\n".join(f"{L[i]}) пример {n}: " + ("тавтологична." if res[n][0] else
                                                                     f"при {env_text(res[n][1])} — значение 0.")
                                            for i, n in enumerate(names)) +
            f"\n\nТаблица построена так, что не тавтологичен только пример {k} (с. 33).")
    return card(8, level, "C", "open", "sym", "short", "S1, независимость", body, "чужая-таблица", SRC8)


def theorems_needing(level=9):
    """Какие аксиомы нужны для вывода теоремной схемы: таблицы, где она не тавтологична."""
    th = {"T2": (x, x), "T3": (x, C(x, x)), "T6": (D(x, y), D(y, x)), "T9": (C(D(x, y), z), D(C(x, z), C(y, z))),
          "T13": (x, D(x, C(x, N(x)))), "T22": (C(D(x, y), x), N(y))}
    name = rnd.choice([n for n in th if repr(n) not in DEDUP])
    DEDUP.add(repr(name))
    p, q = th[name]
    keys = ["A1", "A2", "A3", "A4", "A7", "A9", "A10", "R1", "R2"]
    fail = [k for k in keys if not I.valid(p, q, I.TABLES[k])[0]]
    body = (f"## Условие\n\n{CONV} Теоремная схема {name} (§ 2, с. 18–20): ${ftex(p, q)}$. Пользуясь таблицами § 8 "
            "(с. 33–35), выясните, без каких аксиомных схем или правил её нельзя вывести. Обоснуйте метод.\n\n"
            "## Ответ\n\n" + (", ".join(fail) if fail else "таблицы § 8 ничего не показывают") + "\n\n## Решение\n\n"
            "Если в таблице для $A_k$ (или $R_k$) все остальные аксиомы тавтологичны и правила сохраняют "
            "тавтологичность, а данная формула не тавтологична, то её нельзя вывести без $A_k$ ($R_k$). Проверка: "
            + "; ".join(f"в таблице для {k} " + ("не тавтологична" if k in fail else "тавтологична") for k in keys) +
            ". Взяты двухзначные таблицы: в них правила R1–R3 сохраняют тавтологичность (для таблиц R1 и R2 — кроме "
            "самого опровергаемого правила, с. 34–35).")
    return card(8, level, "M", "transfer", "meta", "proof", "S1, независимость", body, "T-нужны", SRC8)


def sec8():
    out = [tval_card()]
    k = rnd.choice(["A3", "A4"])
    out.append(fails_card(3, k))
    # ступень 3 E: студент ошибочно считает, что в таблице для Ak нарушена Aj
    k, j = "A3", "A4"
    t = I.TABLES[k]
    p, q = I.SAMPLES[j][0]
    body = (f"## Условие\n\n{CONV} {tbl_intro(k)} Студент: «В этой таблице $xy = 1$ при любых $x, y$, поэтому "
            f"${ftex(p, q)}$ (A4) тоже не тавтологична». Проверьте.\n\n## Ответ\n\nНеверно: обе части равны 1, и формула "
            "имеет значение 1 при любых значениях.\n\n## Решение\n\nПо таблице $xy = yx = 1$, а $1 \\vdash 1$ имеет "
            "значение 1 (п. 5 главной интерпретации). Не тавтологична в этой таблице только A3: при $x = 0$ посылка "
            "$xy = 1$, заключение $x = 0$.")
    assert I.valid(p, q, t)[0]
    out.append(card(8, 3, "E", "iso", "sym", "short", "S1, независимость, диагностика", body, None, SRC8))
    # ступень 4: дополнение таблицы (3) + E (2)
    for k in ("A1", "A4", "A9"):
        t = I.TABLES[k]
        p, q = I.SAMPLES[k][0]
        names = sorted(atoms(p) | atoms(q))
        rows = [dict(zip(names, v)) for v in product((1, 0), repeat=len(names))]
        hide = sorted(rnd.sample(range(len(rows)), 2))
        head = " | ".join(f"${n}$" for n in names)
        tab = "\n".join("| " + " | ".join(str(r[n]) for n in names) + f" | {I.val(p, r, t)} | " +
                        ("?" if i in hide else str(I.val(q, r, t))) + " | " + ("?" if i in hide else
                                                                              str(I.fval(p, q, r, t))) + " |"
                        for i, r in enumerate(rows))
        body = (f"## Условие\n\n{CONV} {tbl_intro(k)} Заполните пропуски в таблице для ${ftex(p, q)}$ и скажите, "
                f"тавтологична ли формула.\n\n| {head} | посылка | заключение | формула |\n|" + "---|" * (len(names) + 3) +
                f"\n{tab}\n\n## Ответ\n\n" + "; ".join(f"строка {i + 1}: заключение {I.val(q, rows[i], t)}, формула "
                                                      f"{I.fval(p, q, rows[i], t)}" for i in hide) +
                "; формула не тавтологична.\n\n## Решение\n\nТаблица для " + k + " (с. 33). Достаточно одной строки со "
                "значением 0.")
        out.append(card(8, 4, "D", "complete", "sym", "short", "S1, независимость", body, "дополнить-таблицу", SRC8))
    body = (f"## Условие\n\n{CONV} {tbl_intro('A1')} Студент: «В этой таблице $\\sim x = 0$, поэтому $\\sim\\sim x = 1$, и "
            "$x \\vdash \\sim\\sim x$ — тавтология». Найдите ошибку.\n\n## Ответ\n\n$\\sim\\sim x$ — это $\\sim$ от "
            "$\\sim x$, а по таблице $\\sim$ от чего угодно равно 0: $\\sim\\sim x = 0$. При $x = 1$ формула имеет "
            "значение 0.\n\n## Решение\n\nС. 33, п. 1. Студент применил главную интерпретацию к внешнему $\\sim$.")
    out.append(card(8, 4, "E", "complete", "sym", "short", "S1, независимость, диагностика", body, None, SRC8))
    body = (f"## Условие\n\n{CONV} {tbl_intro('A9')} Студент проверяет A9 ($\\sim(x : y) \\vdash xy : \\sim x\\sim y$) "
            "при $x = 1$, $y = 0$: «$x : y = 1$, $\\sim(x : y) = 0$, формула — 1». Найдите ошибку.\n\n## Ответ\n\n"
            "В этой таблице $\\sim x = x$: $\\sim(x : y) = x : y = 1$. Заключение: $xy = 0$, $\\sim x\\sim y = xy = 0$, "
            "$0 : 0 = 0$. Формула имеет значение 0.\n\n## Решение\n\nС. 33, п. 6: $\\sim x = x$, "
            "$x^1 : \\ldots : x^n = x^1 \\vee \\ldots \\vee x^n$.")
    t = I.TABLES["A9"]
    assert I.fval(*I.SAMPLES["A9"][0], {"x": 1, "y": 0}, t) == 0
    out.append(card(8, 4, "E", "complete", "sym", "short", "S1, независимость, диагностика", body, None, SRC8))
    # ступень 5: трёхзначные (2) + E (1)
    for k in ("A5", "A8"):
        out.append(fails_card(5, k).replace("type: D", "type: D"))
    t = I.TABLES["A5"]
    p, q = I.SAMPLES["A6"][0]
    ok, _ = I.valid(p, q, t)
    assert ok
    body = (f"## Условие\n\n{CONV} {table_text('A5')} Студент: «A6 ($(xy)z \\vdash xyz$) здесь не тавтологична: при "
            "$x = y = z = 1$ формула равна 0, а 0 — это "
            "“ложно”». Найдите ошибку.\n\n## Ответ\n\nВ этой таблице отмеченное значение — 0, а не 1: значение 0 у "
            "формулы следования как раз «хорошее». A6 здесь тавтологична.\n\n## Решение\n\nС. 33: «трёхзначные таблицы "
            "с 0 в качестве единственного отмеченного значения». Формула имеет значение 2 только при посылке 0 и "
            "заключении 1 или 2; посылка $(xy)z$ равна 0 лишь при $xy = 0$ и $z = 0$, то есть при $x = y = z = 0$, и "
            "тогда $xyz = 1$ — значение формулы 0? Нет: $xyz$ — конъюнкция трёх членов, равная 1 по таблице для A6, "
            "но в таблице для A5 она равна 0, и формула имеет значение 0.")
    body = body.replace("тогда $xyz = 1$ — значение формулы 0? Нет: $xyz$ — конъюнкция трёх членов, равная 1 по таблице "
                        "для A6, но в таблице для A5 она равна 0, и формула имеет значение 0.",
                        "тогда $xyz = 0$ (конъюнкция трёх членов в этой таблице равна 0), и формула имеет значение 0.")
    out.append(card(8, 5, "E", "vary", "sym", "short", "S1, независимость, диагностика", body, None, SRC8))
    # ступень 6
    for _ in range(3):
        out.append(cross_card())
    # ступень 9: какие аксиомы нужны (2)
    for _ in range(2):
        out.append(theorems_needing())
    return out


# ---------------- § 9 ----------------
SRC9 = "с. 35, гл. 1, § 9"
THMS = [("A3", C(x, y), x), ("A4", C(x, y), C(y, x)), ("T1", C(x, y), y), ("T6", D(x, y), D(y, x)),
        ("T22", C(D(x, y), x), N(y)), ("A9", N(D(x, y)), D(C(x, y), C(N(x), N(y)))), ("T3", x, C(x, x))]


def subst(f, var, s):
    if f[0] == "v":
        return s if f[1] == var else f
    if f[0] == "neg":
        return N(subst(f[1], var, s))
    return (f[0], tuple(subst(g, var, s) for g in f[1]))


def sec9():
    out = []
    nm, p, q = rnd.choice(THMS)
    s = rnd.choice([D(z, N(z)), C(N(y), z), N(D(y, z))])
    var = rnd.choice(sorted(atoms(p)))
    p2, q2 = subst(p, var, s), subst(q, var, s)
    body = (f"## Условие\n\n{CONV} ${ftex(p, q)}$ — теорема $S^1$ ({nm}). Подставьте ${tex(s)}$ вместо ${var}$ по § 9, "
            "MT1 и запишите полученную теорему.\n\n## Ответ\n\n$" + ftex(p2, q2) + "$\n\n## Решение\n\nMT1 § 9 (с. 35): "
            "подстановка высказывания на место элементарного высказывания везде, где оно входит в формулу, "
            "сохраняет доказуемость.")
    out.append(card(9, 3, "D", "iso", "sym", "short", "S1, подстановка", body, "подстановка", SRC9))
    nm, p, q = rnd.choice([t for t in THMS if t[0] != nm])
    var = sorted(atoms(p))[0]
    s = rnd.choice([C(z, N(y)), D(N(z), y)])
    p2, q2 = subst(p, var, s), subst(q, var, s)
    body = (f"## Условие\n\n{CONV} Какой подстановкой в теорему ${ftex(p, q)}$ ({nm}) получена формула ${ftex(p2, q2)}$? "
            "Доказуема ли она?\n\n## Ответ\n\n" + f"${tex(s)}$ вместо ${var}$; доказуема.\n\n## Решение\n\n§ 9, MT1 "
            "(с. 35): подстановка сделана везде, где входит $" + var + "$.")
    out.append(card(9, 4, "D", "iso", "sym", "short", "S1, подстановка", body, "какая-подстановка", SRC9))
    # ступень 4 E: подстановка не везде
    body = (f"## Условие\n\n{CONV} Студент: «$xy \\vdash x$ — теорема (A3). Подставлю $z$ вместо $x$ в заключении — "
            "получу теорему $xy \\vdash z$». Найдите ошибку.\n\n## Ответ\n\nMT1 § 9 требует подстановки везде, где "
            "элементарное высказывание входит в формулу; $xy \\vdash z$ недоказуема.\n\n## Решение\n\nС. 35. Формула "
            "$xy \\vdash z$ вводит в заключение $z$, которого нет в посылке (§ 4, MT1, с. 21). Верная подстановка даёт "
            "$zy \\vdash z$.")
    out.append(card(9, 4, "E", "iso", "sym", "short", "S1, подстановка, диагностика", body, None, SRC9))
    # ступень 6: открытый исход (2)
    for _ in range(2):
        nm, p, q = rnd.choice(THMS)
        var = sorted(atoms(p))[-1]
        s = rnd.choice([N(z), C(z, x), D(z, N(x))])
        if rnd.random() < 0.5:
            p2, q2 = subst(p, var, s), subst(q, var, s)
            how = "везде"
        else:
            p2, q2 = subst(p, var, s), q
            how = "только в посылке"
        if repr((p2, q2)) in DEDUP:
            continue
        DEDUP.add(repr((p2, q2)))
        v, why = verdict_text(p2, q2)
        body = (f"## Условие\n\n{CONV} Получается ли ${ftex(p2, q2)}$ из теоремы ${ftex(p, q)}$ ({nm}) подстановкой "
                f"по § 9, MT1? Доказуема ли она? {CRIT}\n\n## Ответ\n\n" +
                ("получается; доказуема" if how == "везде" else f"не получается (замена сделана только в посылке); {v}") +
                "\n\n## Решение\n\n" + (f"Подстановка ${tex(s)}$ вместо ${var}$ везде — MT1 § 9 (с. 35)."
                                        if how == "везде" else
                                        f"${var}$ заменено на ${tex(s)}$ только в посылке, MT1 § 9 неприменима. Формула "
                                        + ("всё же доказуема: сильная тавтология (§ 7, MT6)." if v == "доказуема"
                                           else f"{v}: {why}.")))
        out.append(card(9, 6, "C", "open", "sym", "short", "S1, подстановка", body, "подстановка-ли", SRC9))
    return out


def main():
    (ROOT / "drafts").mkdir(exist_ok=True)
    parts = [sec4(), sec5(), sec6(), sec7(), sec8(), sec9()]
    cards = [c for p in parts for c in p]
    (ROOT / "drafts" / "01.04-09-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print([len(p) for p in parts], len(cards))


if __name__ == "__main__":
    main()
