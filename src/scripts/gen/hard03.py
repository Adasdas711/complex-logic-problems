#!/usr/bin/env python3
"""Усложнение гл. 3 «Ослабленное следование» (занятия 20–25) по образцу занятия 10.

Заменяет в src/data/zadachi/03.md генерированные карточки (серии «доказуема ли по критерию» ступеней 1–6) трудными:
  § 1–3 — выводы в S² (схемы S¹ + A15, R1 с ограничением Г. А. Смирнова) в 8–12 строк с проверкой ограничения,
          дополнение длинных выводов, выводы с двумя неверными основаниями (A1/A2 — нумерация S¹ и S₁ обратна,
          A15/A12, R1/R2), «выводы» парадоксов с нарушенным ограничением R1, составные замены и почти-примеры A15,
          серии длинных формул с обоснованием значениями, цепочки x ⊢ y, y ⊢ z и ограничение R1,
          построения «постройте или докажите, что нельзя»;
  § 4–5 — то же для S₂ (схемы S₁ + A12, с. 52–54), перевод S₂ → S² (D2 § 3 гл. 1), сравнение Sˢ и Sʷ, перевод
          рассуждений обычного языка; вручную — A15 и A12 друг через друга, непарадоксальность S₂ по образцу MT1,
          транзитивность и контрапозиция в Sʷ;
  § 6 — S₂¹ (с. 55–58): критерий MT1–MT2 для формул в ДНФ, сравнение с Sʷ, R2 и R3 S₂¹, R*6, шаг доказательства
        MT3, пример Аккермана (с. 55); вручную — построения и метатеоремы ступеней 8–9.
Все выводы проверяются logic/weak3.check (с ограничением R1), доказуемость — критериями Sʷ, Sˢ и S₂¹.

Запуск: python3 src/scripts/gen/hard03.py
"""
import random
import re
import sys
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts"))
import s1  # noqa: E402
import s1w  # noqa: E402
import weak3 as K  # noqa: E402
from s1 import C, D, N, V, atoms  # noqa: E402
from s1w import W  # noqa: E402
from open_form import test_like  # noqa: E402

rnd = random.Random(1970_0300)
x, y, z, u, w = (V(c) for c in "xyzuw")
L = "абвгдежз"

S2, S_2 = "S2", "S_2"
NAME = {S2: "$S^2$", S_2: "$S_2$"}
CONV = {S2: ("Буквы $x, y, z, u, w$ — элементарные высказывания; «$:$» — сильная дизъюнкция («одно и только одно из»); "
             "конъюнкция пишется без знака и связывает сильнее дизъюнкции, обе — сильнее знака следования (с. 15)."),
        S_2: ("Буквы $x, y, z, u, w$ — элементарные высказывания; $\\vee$ — соединительная дизъюнкция («по крайней мере "
              "одно из», с. 36); конъюнкция пишется без знака и связывает сильнее дизъюнкции (с. 15).")}
RESTR = ("R1 применимо, только если в трёх высказываниях $x$, $y$, $z$ его применения (из $x \\vdash y$ и $y \\vdash z$ — "
         "$x \\vdash z$) входит по крайней мере одно одинаковое элементарное высказывание (ограничение Г. А. Смирнова, с. 49)")
SCH = {S2: ("Система $S^2$ (гл. 3, § 1, с. 49) — схемы $S^1$ (с. 15–17): A1 $x \\vdash \\sim\\sim x$; A2 $\\sim\\sim x \\vdash x$; "
            "A3 $xy \\vdash x$; A4 $xy \\vdash yx$; A5, A6 — расстановка и снятие скобок в конъюнкции; "
            "A7 $\\sim(xy) \\vdash \\sim xy : x\\sim y : \\sim x\\sim y$; A8 — обратная к A7; "
            "A9 $\\sim(x : y) \\vdash xy : \\sim x\\sim y$; A10 — обратная к A9; и A15 $\\sim x \\vdash \\sim(xy)$. "
            "Правила: R1 — из $x \\vdash y$ и $y \\vdash z$ получаем $x \\vdash z$; R2 — из $x \\vdash y$ и $x \\vdash z$ "
            f"получаем $x \\vdash yz$ (с. 17). {RESTR}."),
       S_2: ("Система $S_2$ (гл. 3, § 4, с. 52) — схемы $S_1$ (с. 36–37): A1 $\\sim\\sim x \\vdash x$; A2 $x \\vdash \\sim\\sim x$; "
             "A3 $xy \\vdash x$; A4 $xy \\vdash yx$; A5, A6 — расстановка и снятие скобок в конъюнкции; "
             "A7 $(x \\vee y)z \\vdash xz \\vee y$; A8 $xz \\vee yz \\vdash (x \\vee y)z$; "
             "A9 $\\sim(x^1 \\ldots x^n) \\vdash \\sim x^1 \\vee \\ldots \\vee \\sim x^n$; A10 — обратная к A9; "
             "A11 $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$; и A12 — дополнительная схема $S_2$, которая в "
             "доказательстве на с. 54 применяется в виде $x \\vdash x \\vee y$ (в этом виде её и применяйте). Правила R1, R2 — "
             f"как в $S^2$; {RESTR.replace('(ограничение Г. А. Смирнова, с. 49)', '(как в $S^2$, с. 49, 52)')}.")}
CRIT_W = ("Критерий: формула $x \\vdash y$ доказуема в $S^2$ (и в эквивалентной ей $S_2$, то есть в $S^w$) тогда и только тогда, "
          "когда она — тавтология и в $x$ и $y$ входит по крайней мере одно одинаковое элементарное высказывание "
          "(гл. 3, § 2, MT1, с. 49; § 3, MT4, с. 52; § 4–5, с. 53).")
CRIT_S = ("$S^s$ — сильное следование ($S^1$, $S_1$ и эквивалентные им системы): формула доказуема в $S^s$ тогда и только "
          "тогда, когда она — тавтология и в заключение не входят элементарные высказывания, отсутствующие в посылке "
          "(гл. 1, § 7, MT6, с. 32; гл. 2, § 2, MT5, с. 43; § 5, с. 45).")
SRC = {1: "с. 49, гл. 3, § 1", 2: "с. 49–50, гл. 3, § 1–2", 3: "с. 49–52, гл. 3, § 2–3", 4: "с. 52–54, гл. 3, § 4",
       5: "с. 53–54, гл. 3, § 4–5", 6: "с. 55–58, гл. 3, § 6"}


def tx(f, sy=S2):
    return s1.tex(f) if sy == S2 else s1w.tex(f)


def ft(a, b, sy=S2):
    return f"{tx(a, sy)} \\vdash {tx(b, sy)}"


def anytex(f):
    return s1w.tex(f) if "wdis" in repr(f) else s1.tex(f)


def aft(a, b):
    return f"{anytex(a)} \\vdash {anytex(b)}"


def size(f):
    return len(anytex(f))


def why_text(wh):
    if isinstance(wh, str):
        return {"TW": "MT4 § 3", "TS": "теорема $S^s$"}.get(wh, wh)
    return f"{wh[0]}: {wh[1]}, {wh[2]}"


def show(lines, sy=S2):
    return "\n".join(f"{n}. ${ft(a, b, sy)}$ [{why_text(wh)}]" for n, (a, b, wh) in enumerate(lines, 1))


def show_hidden(lines, sy, hide_why, hide_f):
    return "\n".join(f"{n}. {'…' if n in hide_f else '$' + ft(a, b, sy) + '$'} [{'…' if n in hide_why else why_text(wh)}]"
                     for n, (a, b, wh) in enumerate(lines, 1))


def r1_note(lines):
    out = []
    for n, (a, b, wh) in enumerate(lines, 1):
        if isinstance(wh, tuple) and wh[0] == "R1":
            out.append(f"шаг {n} — {K.letters(K.r1_common(lines, n))}")
    return "Ограничение R1 соблюдено (общее элементарное высказывание трёх высказываний): " + "; ".join(out) + "."


def ob(st, case="nom"):
    """«общее $x$» / «общие $x$, $y$»; case='ins' — «общим $x$» / «общими $x$, $y$»."""
    one = len(st) == 1
    w_ = {"nom": ("общее", "общие"), "ins": ("общим", "общими")}[case][0 if one else 1]
    return f"{w_} {K.letters(st)}"


def newp(st, what="которого нет в посылке"):
    """«входит $u$, которого нет в посылке» / «входят $y$, $z$, которых нет в посылке»."""
    if len(st) > 1:
        return f"входят {K.letters(st)}, {what.replace('которого', 'которых')}"
    return f"входит {K.letters(st)}, {what}"


def sub(p, q):
    return p == q or (q[0] == "neg" and sub(p, q[1])) or (q[0] in ("conj", "wdis", "dis") and any(sub(p, c) for c in q[1]))


def card(level, typ, step, ans_kind, src, tags, cond, ans, sol, form="sym", system="S^2"):
    return dict(level=level, type=typ, step=step, form=form, answer=ans_kind, source=src, tags=tags, cond=cond,
                ans=ans, sol=sol, system=system)


SYSF = {S2: "S^2", S_2: "S_2"}


# ---------- шаги выводов ----------
FRESH = [x, y, z, u, N(x), N(y), N(z), N(u)]


def moves(q, sy):
    out = []
    if sy == S2:
        if q[0] == "neg" and q[1][0] == "neg":
            out.append(("A2", q[1][1]))
        if q[0] in ("v", "neg") and size(q) < 7:
            out.append(("A1", N(N(q))))
    else:
        if q[0] == "neg" and q[1][0] == "neg":
            out.append(("A1", q[1][1]))
        if q[0] in ("v", "neg") and size(q) < 7:
            out.append(("A2", N(N(q))))
    if q[0] == "conj" and len(q[1]) == 2:
        a, b = q[1]
        out += [("A3", a), ("A4", C(b, a))]
        if a[0] == "conj" and len(a[1]) == 2 and all(t[0] != "conj" for t in a[1]) and b[0] != "conj":
            out.append(("A6", C(a[1][0], a[1][1], b)))
        if b[0] == "conj" and len(b[1]) == 2 and all(t[0] != "conj" for t in b[1]) and a[0] != "conj":
            out.append(("A6", C(a, b[1][0], b[1][1])))
        if sy == S_2 and a[0] == "wdis" and len(a[1]) == 2:
            out.append(("A7", W(C(a[1][0], b), a[1][1])))
    if q[0] == "conj" and len(q[1]) == 3 and all(t[0] != "conj" for t in q[1]):
        a, b, c = q[1]
        out += [("A5", C(C(a, b), c)), ("A5", C(a, C(b, c)))]
    if sy == S2:
        if q[0] == "neg" and q[1][0] == "conj" and len(q[1][1]) == 2 and size(q) < 12:
            a, b = q[1][1]
            out.append(("A7", D(C(N(a), b), C(a, N(b)), C(N(a), N(b)))))
        if q[0] == "dis" and len(q[1]) == 3 and s1.axiom(q, N(C(*q[1][1][1]))) == "A8":
            out.append(("A8", N(C(*q[1][1][1]))))
        if q[0] == "neg" and q[1][0] == "dis" and len(q[1][1]) == 2:
            a, b = q[1][1]
            out.append(("A9", D(C(a, b), C(N(a), N(b)))))
        if q[0] == "dis" and len(q[1]) == 2 and q[1][0][0] == "conj" and len(q[1][0][1]) == 2:
            a, b = q[1][0][1]
            if q[1][1] == C(N(a), N(b)):
                out.append(("A10", N(D(a, b))))
        if q[0] == "neg" and size(q) < 14 and not (q[1][0] == "conj" and any(t[0] == "conj" for t in q[1][1])):
            for Y in rnd.sample(FRESH, 3):
                if Y != q[1]:
                    out.append(("A15", N(C(q[1], Y))))
    else:
        if q[0] == "neg" and q[1][0] == "conj":
            out.append(("A9", W(*(N(t) for t in q[1][1]))))
        if q[0] == "wdis" and all(t[0] == "neg" for t in q[1]):
            out.append(("A10", N(C(*(t[1] for t in q[1])))))
        if q[0] == "wdis" and len(q[1]) == 2:
            a, b = q[1]
            if a[0] == "conj" and b[0] == "conj" and len(a[1]) == 2 and len(b[1]) == 2 and a[1][1] == b[1][1]:
                out.append(("A8", C(W(a[1][0], b[1][0]), a[1][1])))
            if a[0] == "conj" and len(a[1]) == 2 and size(q) < 14:
                out.append(("A11", C(q, W(a[1][1], N(a[1][1])))))
        if size(q) < 14 and q[0] != "wdis" and not (q[0] == "neg" and q[1][0] == "conj" and any(t[0] == "conj" for t in q[1][1])):
            for Y in rnd.sample(FRESH, 3):
                if not sub(Y, q):
                    out.append(("A12", W(q, Y)))
    ax = K.axiom_S2 if sy == S2 else K.axiom_S_2
    for n, r in out:
        assert ax(q, r) == n, (sy, n, anytex(q), anytex(r), ax(q, r))
    return out


def build(P, want, sy):
    for _ in range(60):
        lines, facts = [], []
        first = moves(P, sy)
        if not first:
            return None
        name, r = rnd.choice(first)
        lines.append((P, r, name))
        facts.append((r, 1))
        used_r2, tries = 0, 0
        while len(lines) < want and tries < 90:
            tries += 1
            if len(facts) >= 2 and rnd.random() < 0.28:
                (q1, i), (q2, j) = rnd.sample(facts, 2)
                if size(C(q1, q2)) > 30 or C(q1, q2) in [f for f, _ in facts] or sub(q1, q2) or sub(q2, q1):
                    continue
                lines.append((P, C(q1, q2), ("R2", i, j)))
                facts.append((C(q1, q2), len(lines)))
                used_r2 += 1
                continue
            q, i = rnd.choice(facts)
            opts = [(n, r) for n, r in moves(q, sy) if size(r) <= 34 and r not in [f for f, _ in facts] and r != P]
            if not opts:
                continue
            usedn = {wh for *_, wh in lines if isinstance(wh, str)}
            name, r = rnd.choices(opts, weights=[1 if n in usedn else 4 for n, _ in opts])[0]
            if not (atoms(P) & atoms(q) & atoms(r)):
                continue
            lines.append((q, r, name))
            lines.append((P, r, ("R1", i, len(lines))))
            facts.append((r, len(lines)))
        a, b = lines[-1][0], lines[-1][1]
        if (a == P and used_r2 and sum(1 for *_, wh in lines if isinstance(wh, tuple)) >= 3
                and not K.check(lines, sy) and K.weak(a, b) and 10 <= size(b) <= 34):
            return lines
    return None


def prune(lines):
    need, stack = set(), [len(lines)]
    while stack:
        n = stack.pop()
        if n in need:
            continue
        need.add(n)
        wh = lines[n - 1][2]
        if isinstance(wh, tuple):
            stack += [wh[1], wh[2]]
    keep = sorted(need)
    new = {old: i for i, old in enumerate(keep, 1)}
    return [(a, b, wh if isinstance(wh, str) else (wh[0], new[wh[1]], new[wh[2]])) for a, b, wh in
            (lines[o - 1] for o in keep)]


def premises(sy):
    X, Y, Z = rnd.sample([x, y, z, N(x), N(y), u], 3)
    if sy == S2:
        return rnd.choice([N(C(X, Y)), C(N(X), Y), N(D(X, Y)), C(N(N(X)), Y), C(X, N(C(Y, Z))), C(N(X), N(Y)),
                           C(N(D(X, Y)), Z), N(C(X, Y, Z))])
    return rnd.choice([C(W(X, Y), Z), N(C(X, Y)), W(N(X), N(Y)), C(N(N(X)), Y), W(C(X, Y), Z), C(X, Y, Z),
                       W(C(X, Z), C(Y, Z)), C(X, W(Y, Z)), N(C(X, Y, Z)), C(N(X), Y)])


SEEN = set()
NEWNAME = {S2: "A15", S_2: "A12"}


def build_ok(want, least, sy, need_new=True):
    for _ in range(4000):
        lines = build(premises(sy), want + 4, sy)
        if lines:
            lines = prune(lines)
            a, b = lines[-1][0], lines[-1][1]
            key = ft(a, b, sy)
            used = any(wh == NEWNAME[sy] for *_, wh in lines)
            names = {wh for *_, wh in lines if isinstance(wh, str)}
            r2 = any(isinstance(wh, tuple) and wh[0] == "R2" for *_, wh in lines)
            n_new = sum(wh == NEWNAME[sy] for *_, wh in lines)
            if (len(lines) >= least and r2 and len(names) >= 4 and n_new <= 2 and not K.check(lines, sy) and key not in SEEN
                    and (not need_new or (used and atoms(b) - atoms(a)))):
                SEEN.add(key)
                return lines
    raise RuntimeError("вывод не построен")




# ---------- выводы ----------
def c_deriv(sy, src, level=7, step="open"):
    lines = build_ok(rnd.choice([9, 10, 11]), least=8, sy=sy)
    a, b = lines[-1][0], lines[-1][1]
    new = atoms(b) - atoms(a)
    cond = (f"{CONV[sy]} {SCH[sy]}\n\nВыведите в {NAME[sy]} формулу ${ft(a, b, sy)}$, пользуясь аксиомными схемами и "
            f"правилами R1, R2; при каждом применении R1 укажите общее элементарное высказывание трёх высказываний. "
            f"Объясните, почему эта формула недоказуема в {'$S^1$' if sy == S2 else '$S_1$'}.")
    ans = (f"Например, вывод в {len(lines)} строк (см. решение); без {NEWNAME[sy]} не обойтись: в заключение "
           f"{newp(new)}.")
    sol = (show(lines, sy) + "\n\n" + r1_note(lines) + "\n\n" +
           f"Формула недоказуема в {'$S^1$' if sy == S2 else '$S_1$'}: в заключение {newp(new)}, а теоремы {'$S^1$' if sy == S2 else '$S_1$'} таких формул не содержат "
           f"(непарадоксальность, {'гл. 1, § 4, с. 21' if sy == S2 else 'гл. 2, § 1, с. 37'}); "
           f"в {NAME[sy]} это даёт схема {NEWNAME[sy]} ({'с. 49' if sy == S2 else 'с. 52–54'}).")
    return card(level, "D", step, "proof", src, f"{'S2' if sy == S2 else 'S2w'}, вывод, ограничение R1", cond, ans, sol,
                system=SYSF[sy])


def c_complete(sy, src, level=5, step="complete"):
    lines = build_ok(rnd.choice([10, 11]), least=9, sy=sy)
    sl = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, str)]
    rl = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, tuple)]
    hide_f = set(rnd.sample(sl[1:] or sl, min(2, max(1, len(sl) - 1))))
    hide_why = set(rnd.sample([n for n in sl if n not in hide_f], min(2, len(sl) - len(hide_f))))
    hide_why |= set(rnd.sample(rl[:-1], min(2, len(rl) - 1)))
    hide_f |= set(rnd.sample([n for n in rl[:-1] if n not in hide_why], 1)) if len(rl) > 3 else set()
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV[sy]} {SCH[sy]}\n\nВ выводе в {NAME[sy]} формулы ${ft(a, b, sy)}$ пропущены основания некоторых шагов и "
            f"формулы некоторых строк («…»). Восстановите их и проверьте, что при каждом применении R1 ограничение "
            f"соблюдено.\n\n{show_hidden(lines, sy, hide_why, hide_f)}")
    parts = []
    for n in sorted(hide_why | hide_f):
        la, lb, wh = lines[n - 1]
        parts.append(f"{n} — " + (f"${ft(la, lb, sy)}$ " if n in hide_f else "") + (f"[{why_text(wh)}]" if n in hide_why else ""))
    sol = ("Формулу строки восстанавливаем по соседним: в R1 заключение одной строки — посылка другой, в R2 обе строки "
           "имеют общую посылку; основание — по виду формулы.\n\n" + show(lines, sy) + "\n\n" + r1_note(lines))
    return card(level, "D", step, "build", src, f"{'S2' if sy == S2 else 'S2w'}, вывод, дополнение", cond,
                "; ".join(p.strip() for p in parts), sol, system=SYSF[sy])


WRONG = {S2: {"A1": "A2", "A2": "A1", "A3": "A4", "A4": "A3", "A7": "A8", "A8": "A7", "A9": "A10", "A10": "A9",
              "A5": "A6", "A6": "A5", "A15": "A12"},
         S_2: {"A1": "A2", "A2": "A1", "A3": "A4", "A4": "A3", "A7": "A8", "A8": "A7", "A9": "A10", "A10": "A9",
               "A5": "A6", "A6": "A5", "A11": "A7", "A12": "A15"}}


def wrong_why(sy, right, wrong):
    if sy == S2:
        d = {"A1": "в $S^1$ (и в $S^2$) A1 — $x \\vdash \\sim\\sim x$, а A2 — $\\sim\\sim x \\vdash x$ (с. 15); "
                   "обратная нумерация — у $S_1$ (с. 36)",
             "A2": "в $S^1$ (и в $S^2$) A2 — $\\sim\\sim x \\vdash x$, а A1 — $x \\vdash \\sim\\sim x$ (с. 15); "
                   "обратная нумерация — у $S_1$ (с. 36)",
             "A15": "дополнительная схема $S^2$ — A15 $\\sim x \\vdash \\sim(xy)$ (с. 49); номер A12 имеет "
                    "дополнительная схема $S_2$ (с. 52), а в $S^1$ A12 — схема для сильной дизъюнкции (с. 16)"}
    else:
        d = {"A1": "в $S_1$ (и в $S_2$) A1 — $\\sim\\sim x \\vdash x$, а A2 — $x \\vdash \\sim\\sim x$ (с. 36); "
                   "в $S^1$ нумерация обратная (с. 15)",
             "A2": "в $S_1$ (и в $S_2$) A2 — $x \\vdash \\sim\\sim x$, а A1 — $\\sim\\sim x \\vdash x$ (с. 36); "
                   "в $S^1$ нумерация обратная (с. 15)",
             "A12": "дополнительная схема $S_2$ имеет номер A12 (с. 52; в виде $x \\vdash x \\vee y$ — с. 54); "
                    "A15 — номер дополнительной схемы $S^2$ (с. 49)",
             "A11": "A11 — $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$, а A7 — $(x \\vee y)z \\vdash xz \\vee y$ "
                    "(с. 36–37)"}
    gen = {"A3": "A3 оставляет первый член конъюнкции, A4 переставляет члены",
           "A4": "A4 переставляет члены конъюнкции, A3 оставляет первый член",
           "A5": "A5 расставляет скобки в конъюнкции без скобок, A6 снимает их",
           "A6": "A6 снимает скобки в конъюнкции, A5 расставляет их",
           "A7": ("A7 раскрывает отрицание конъюнкции в сильную дизъюнкцию, A8 — обратный переход" if sy == S2 else
                  "A7 — $(x \\vee y)z \\vdash xz \\vee y$, A8 — $xz \\vee yz \\vdash (x \\vee y)z$"),
           "A8": ("A8 собирает сильную дизъюнкцию в отрицание конъюнкции, A7 — обратный переход" if sy == S2 else
                  "A8 — $xz \\vee yz \\vdash (x \\vee y)z$, A7 — $(x \\vee y)z \\vdash xz \\vee y$"),
           "A9": ("A9 — $\\sim(x : y) \\vdash xy : \\sim x\\sim y$, A10 — обратная" if sy == S2 else
                  "A9 раскрывает отрицание конъюнкции в дизъюнкцию отрицаний, A10 — обратный переход"),
           "A10": ("A10 — $xy : \\sim x\\sim y \\vdash \\sim(x : y)$, A9 — обратная" if sy == S2 else
                   "A10 собирает дизъюнкцию отрицаний в отрицание конъюнкции, A9 — обратный переход")}
    pg = "с. 15–16" if sy == S2 else "с. 36–37"
    return d.get(right) or f"{gen[right]} ({pg})"


def c_diag(sy, src, level=6, step="vary"):
    for _ in range(400):
        lines = build_ok(rnd.choice([8, 9, 10]), least=8, sy=sy)
        cand = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, str) and wh in WRONG[sy]]
        rs = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, tuple) and wh[0] == "R1"]
        if not cand or not rs:
            continue
        pri = [i for i in cand if lines[i][2] in ("A1", "A2", NEWNAME[sy])] or cand
        i, j = rnd.choice(pri), rnd.choice(rs)
        bad = list(lines)
        a, b, wh = bad[i]
        bad[i] = (a, b, WRONG[sy][wh])
        a2, b2, wh2 = bad[j]
        bad[j] = (a2, b2, ("R2", wh2[1], wh2[2]))
        errs = K.check(bad, sy)
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        if steps == sorted([i + 1, j + 1]):
            break
    else:
        raise RuntimeError("нет вывода для диагностики")
    p, q = sorted([i, j])
    fix = {i: lines[i][2], j: lines[j][2]}
    cond = (f"{CONV[sy]} {SCH[sy]}\n\nВ выводе в {NAME[sy]} формулы ${ft(lines[-1][0], lines[-1][1], sy)}$ ровно два "
            f"основания указаны неверно. Найдите их, назовите нарушенные схемы или правила с номерами и страницами и "
            f"исправьте вывод.\n\n{show(bad, sy)}")
    ans = f"Шаг {p + 1}: [{why_text(fix[p])}]; шаг {q + 1}: [{why_text(fix[q])}]."
    exp = []
    for k in (p, q):
        a, b, _ = lines[k]
        if k == i:
            exp.append(f"Шаг {k + 1}: ${ft(a, b, sy)}$ — пример {fix[k]}, а не {WRONG[sy][fix[k]]}: "
                       f"{wrong_why(sy, fix[k], WRONG[sy][fix[k]])}.")
        else:
            exp.append(f"Шаг {k + 1}: R2 соединяет в конъюнкцию заключения двух строк с общей посылкой (с. 17), а здесь "
                       f"заключение строки {fix[k][1]} — посылка строки {fix[k][2]}: это R1, и ограничение R1 (с. 49) "
                       f"соблюдено — {ob(K.r1_common(lines, k + 1))}.")
    sol = "\n".join(exp) + "\n\nИсправленный вывод:\n\n" + show(lines, sy)
    return card(level, "E", step, "text", src, f"{'S2' if sy == S2 else 'S2w'}, вывод, диагностика", cond, ans, sol,
                system=SYSF[sy])


# ---------- «выводы» парадоксов с нарушенным ограничением R1 ----------
def compound(names, sy):
    a, b = rnd.sample(names, 2)
    A, B = V(a), V(b)
    opts = [A, N(A), C(A, N(B)), C(N(A), B), N(C(A, B))]
    opts.append(D(A, B) if sy == S2 else W(A, B))
    opts.append(N(D(A, B)) if sy == S2 else W(N(A), B))
    return rnd.choice(opts)


def paradox_lines(sy, X, Y):
    P = C(X, N(X))
    if sy == S2:
        return [(P, X, "A3"), (P, C(N(X), X), "A4"), (C(N(X), X), N(X), "A3"), (P, N(X), ("R1", 2, 3)),
                (N(X), N(C(X, N(Y))), "A15"), (P, N(C(X, N(Y))), ("R1", 4, 5)), (P, C(X, N(C(X, N(Y)))), ("R2", 1, 6)),
                (C(X, N(C(X, N(Y)))), Y, "TW"), (P, Y, ("R1", 7, 8))]
    M = W(N(X), Y)
    return [(P, X, "A3"), (P, C(N(X), X), "A4"), (C(N(X), X), N(X), "A3"), (P, N(X), ("R1", 2, 3)),
            (N(X), M, "A12"), (P, M, ("R1", 4, 5)), (P, C(X, M), ("R2", 1, 6)), (C(X, M), C(M, X), "A4"),
            (P, C(M, X), ("R1", 7, 8)), (C(M, X), W(C(N(X), X), Y), "A7"), (P, W(C(N(X), X), Y), ("R1", 9, 10)),
            (W(C(N(X), X), Y), Y, "TW"), (P, Y, ("R1", 11, 12))]


def c_paradox(sy, src, level=7, step="vary"):
    for _ in range(500):
        X = compound(["x", "z"], sy)
        Y = compound(["y", "u"], sy)
        lines = paradox_lines(sy, X, Y)
        last = len(lines)
        errs = K.check(lines, sy)
        assert [int(re.match(r"шаг (\d+)", e).group(1)) for e in errs] == [last], (errs, show(lines, sy))
        assert "ограничение" in errs[0] and K.taut(lines[-1][0], lines[-1][1]) and not K.weak(lines[-1][0], lines[-1][1])
        cand = [k for k, (*_, wh) in enumerate(lines[:-1]) if isinstance(wh, str) and wh in WRONG[sy]]
        rr = [k for k, (*_, wh) in enumerate(lines[:-1]) if isinstance(wh, tuple) and wh[0] == "R2"]
        k = rnd.choice(cand + rr)
        bad = list(lines)
        a, b, wh = bad[k]
        bad[k] = (a, b, WRONG[sy][wh] if isinstance(wh, str) else ("R1", wh[1], wh[2]))
        e2 = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in K.check(bad, sy)})
        if e2 == sorted([k + 1, last]) and size(lines[-1][0]) <= 16:
            break
    P, Yf = lines[-1][0], lines[-1][1]
    pre = lines[last - 2][0]
    ex = (f"Шаг {k + 1}: ${ft(lines[k][0], lines[k][1], sy)}$ — " +
          (f"пример {lines[k][2]}, а не {WRONG[sy][lines[k][2]]}: {wrong_why(sy, lines[k][2], WRONG[sy][lines[k][2]])}."
           if isinstance(lines[k][2], str) else
           "R2 (из $x \\vdash y$ и $x \\vdash z$ — $x \\vdash yz$, с. 17): обе строки имеют общую посылку, а R1 требует, "
           "чтобы заключение одной строки было посылкой другой."))
    ex2 = (f"Шаг {last}: R1 применено к ${tx(P, sy)}$, ${tx(pre, sy)}$ и ${tx(Yf, sy)}$, но общего элементарного "
           f"высказывания у всех трёх нет: в ${tx(P, sy)}$ — только {K.letters(atoms(P))}, в ${tx(Yf, sy)}$ — только "
           f"{K.letters(atoms(Yf))}. Ограничение R1 (с. 49{', 52' if sy == S_2 else ''}) нарушено.")
    why8 = ("Строка со ссылкой на MT4 § 3 верна: формула — тавтология, и в посылке и заключении есть "
            f"{ob(K.common(lines[last - 2][0], lines[last - 2][1]))} (с. 52).")
    cond = (f"{CONV[sy]} {SCH[sy]} Ссылка «MT4 § 3» означает: строка доказуема в {NAME[sy]}, потому что она — тавтология "
            f"с общим элементарным высказыванием посылки и заключения (гл. 3, § 3, MT4, с. 52{'; § 4, с. 53' if sy == S_2 else ''}).\n\n"
            f"Студент «вывел» в {NAME[sy]} формулу ${ft(P, Yf, sy)}$. В выводе две ошибки. Найдите их, назовите "
            f"нарушенные схемы и правила с номерами и страницами и выясните, можно ли исправить вывод.\n\n{show(bad, sy)}")
    ans = (f"Шаг {k + 1}: должно быть [{why_text(lines[k][2])}]; шаг {last}: нарушено ограничение R1 (с. 49) — у "
           f"${tx(P, sy)}$ и ${tx(Yf, sy)}$ нет общего элементарного высказывания. Исправить нельзя: формула недоказуема "
           "(MT1 § 2, с. 49).")
    sol = (ex + "\n\n" + ex2 + "\n\n" + why8 + "\n\n" +
           f"Исправить вывод нельзя: ${ft(P, Yf, sy)}$ — тавтология (посылка ложна при всех значениях), но общих "
           f"элементарных высказываний у посылки и заключения нет, и по MT1 § 2 (с. 49{'; эквивалентность $S^2$ и $S_2$ — с. 53' if sy == S_2 else ''}) "
           f"формула недоказуема в {NAME[sy]}. Без ограничения R1 система была бы парадоксальной: так выводилась бы "
           "формула «из противоречия — что угодно».")
    return card(level, "E", step, "text", src, f"{'S2' if sy == S2 else 'S2w'}, парадоксы, ограничение R1, диагностика",
                cond, ans, sol, system=SYSF[sy])




# ---------- случайные формулы ----------
def rf(names, depth, sy):
    if depth == 0 or rnd.random() < 0.22:
        v = V(rnd.choice(names))
        return N(v) if rnd.random() < 0.35 else v
    k = rnd.random()
    if k < 0.18:
        return N(rf(names, depth - 1, sy))
    op = C if k < 0.58 else (D if sy == S2 else W)
    a, b = rf(names, depth - 1, sy), rf(names, depth - 1, sy)
    return op(a, b) if a != b else a


def contra(names, sy):
    X = rf(names, 1, sy)
    if rnd.random() < 0.3 and len(names) >= 2:
        A, B = (V(t) for t in rnd.sample(names, 2))
        return C(D(A, B) if sy == S2 else W(A, B), N(A), N(B))
    return rnd.choice([C(X, N(X)), C(N(X), X)])


def tauto(names, sy):
    X = rf(names, 1, sy)
    return D(X, N(X)) if sy == S2 else W(X, N(X))


def item(kind, sy, lim=40):
    for _ in range(20000):
        A = rnd.sample(["x", "y", "z"], 2)
        if kind in ("yes", "yes_new", "yes_strong") and rnd.random() < 0.4:
            ls = build_ok(5, least=4, sy=sy, need_new=(kind == "yes_new"))
            a, b = ls[-1][0], ls[-1][1]
        elif kind == "nocommon":
            B = [t for t in "xyzu" if t not in A]
            B = rnd.sample(B, rnd.choice([1, 2]))
            a, b = (contra(A, sy), rf(B, 2, sy)) if rnd.random() < 0.5 else (rf(A, 2, sy), tauto(B, sy))
        else:
            extra = ["u"] if kind == "yes_new" or rnd.random() < 0.4 else []
            a, b = rf(A, 2, sy), rf(A + extra, 2, sy)
        cat = ("nontaut" if not K.taut(a, b) else "nocommon" if not K.common(a, b) else
               "yes_strong" if K.strong(a, b) else "yes_new")
        ok = cat == kind or (kind == "yes" and cat.startswith("yes"))
        if ok and a != b and 12 <= size(a) + size(b) <= lim and not (K.is_contra(a) and kind != "nocommon"):
            return a, b
    raise RuntimeError(kind)


def reason_w(a, b, sy):
    """Обоснование доказуемости в S^w значениями и элементарными высказываниями."""
    if not K.taut(a, b):
        return False, (f"при {K.env_text(K.counter(a, b))} посылка — 1, заключение — 0: не тавтология; теоремы {NAME[sy]} — "
                       f"тавтологии (непротиворечивость $S^2$, § 1, с. 49{'; эквивалентность $S^2$ и $S_2$, с. 53' if sy == S_2 else ''}), "
                       "формула недоказуема")
    if not K.common(a, b):
        why = ("посылка ложна при всех значениях" if K.is_contra(a) else "заключение истинно при всех значениях")
        return False, (f"тавтология ({why}), но в посылке только {K.letters(atoms(a))}, в заключении только "
                       f"{K.letters(atoms(b))}: общих элементарных высказываний нет, по MT1 § 2 (с. 49) недоказуема")
    return True, (f"тавтология (нет набора значений, при котором посылка — 1, а заключение — 0), "
                  f"{ob(K.common(a, b))}: по MT4 § 3 (с. 52) доказуема")


def c_series(sy, src, level=6, kinds=None, step="open"):
    kinds = kinds or ["yes_new", "nocommon", "nontaut", rnd.choice(["yes", "yes_new", "nocommon"])]
    its = []
    while len(its) < 4:
        a, b = item(kinds[len(its)], sy)
        if (a, b) not in its:
            its.append((a, b))
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (a, b) in enumerate(its):
        ok, why = reason_w(a, b, sy)
        ans.append(f"{L[k]}) {'доказуема' if ok else 'недоказуема'}")
        sol.append(f"{L[k]}) {why[0].upper() + why[1:]}.")
    cond = (f"{CONV[sy]} Исследуйте доказуемость в {NAME[sy]} каждой формулы и обоснуйте значениями: для недоказуемой — "
            "набор значений, при котором посылка — 1, а заключение — 0, или отсутствие общих элементарных высказываний "
            f"(тогда покажите, что формула всё же тавтология). {CRIT_W}\n\n"
            + "\n".join(f"{L[k]}) ${ft(a, b, sy)}$" for k, (a, b) in enumerate(its)))
    return card(level, "C", step, "short", src, f"{'S2' if sy == S2 else 'S2w'}, доказуемость, критерий", cond,
                "; ".join(ans), "\n".join(sol), system=SYSF[sy])


def c_series_diag(sy, src, level=6, step="vary"):
    kinds = ["yes_new", "nocommon", "nontaut", rnd.choice(["yes_new", "nocommon", "yes_strong"])]
    its = []
    while len(its) < 4:
        a, b = item(kinds[len(its)], sy, lim=36)
        if (a, b) not in its:
            its.append((a, b))
    order = list(range(4))
    rnd.shuffle(order)
    its = [its[i] for i in order]
    kinds = [kinds[i] for i in order]
    cats = rnd.sample(["yes_new", "nocommon", "nontaut"], 2)
    wrong = [kinds.index(c) for c in cats]
    body, ans, sol = [], [], []
    for k, (a, b) in enumerate(its):
        ok, why = reason_w(a, b, sy)
        kd = kinds[k]
        if k in wrong:
            if kd == "yes_new":
                na = K.letters(atoms(b) - atoms(a))
                claim = f"недоказуема: в заключение {newp(atoms(b) - atoms(a))}"
                ans.append(f"{k + 1}: доказуема (MT4 § 3, с. 52)")
                sol.append(f"{k + 1}. Неверно: студент применил условие сильного следования $S^s$. В {NAME[sy]} новые "
                           f"элементарные высказывания в заключении допустимы ({NEWNAME[sy]}, "
                           f"{'с. 49' if sy == S2 else 'с. 52–54'}): {why}.")
            elif kd == "nocommon":
                claim = "доказуема: это тавтология"
                ans.append(f"{k + 1}: недоказуема (MT1 § 2, с. 49)")
                sol.append(f"{k + 1}. Неверно: тавтологии мало — {why}.")
            else:
                claim = f"доказуема: есть {ob(K.common(a, b))}"
                ans.append(f"{k + 1}: недоказуема (не тавтология)")
                sol.append(f"{k + 1}. Неверно: общего элементарного высказывания мало — {why}.")
        else:
            claim = ("доказуема: тавтология с " + ob(K.common(a, b), "ins") if ok else
                     "недоказуема: тавтология, но общих элементарных высказываний нет" if K.taut(a, b) else
                     f"недоказуема: при {K.env_text(K.counter(a, b))} посылка 1, заключение 0")
        body.append(f"{k + 1}. ${ft(a, b, sy)}$ — {claim}.")
    cond = (f"{CONV[sy]} Студент исследовал доказуемость четырёх формул в {NAME[sy]}:\n\n" + "\n".join(body) +
            f"\n\nРовно два вывода неверны. Найдите их, назовите метатеорему или схему книги, которую нарушил студент, и "
            f"дайте верный ответ с обоснованием значениями. {CRIT_W}")
    return card(level, "E", step, "text", src, f"{'S2' if sy == S2 else 'S2w'}, доказуемость, диагностика", cond,
                "; ".join(ans), "\n".join(sol) + "\n\nОстальные выводы верны.", system=SYSF[sy])


def c_ss_sw(sy, src, level=7, step="transfer"):
    kinds = ["yes_strong", "yes_new", "nocommon", rnd.choice(["nontaut", "yes_new"])]
    its = []
    while len(its) < 4:
        a, b = item(kinds[len(its)], sy, lim=36)
        if (a, b) not in its:
            its.append((a, b))
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (a, b) in enumerate(its):
        s_, w_ = K.strong(a, b), K.weak(a, b)
        ans.append(f"{L[k]}) $S^s$ — {'да' if s_ else 'нет'}, $S^w$ — {'да' if w_ else 'нет'}")
        if not K.taut(a, b):
            t = f"при {K.env_text(K.counter(a, b))} посылка — 1, заключение — 0: не тавтология, недоказуема в обеих."
        elif s_:
            t = ("тавтология, новых элементарных высказываний в заключении нет — доказуема в $S^s$; "
                 f"{ob(K.common(a, b))} есть — доказуема и в $S^w$.")
        elif w_:
            t = (f"тавтология с {ob(K.common(a, b), 'ins')} — доказуема в $S^w$; но в заключение "
                 f"{newp(atoms(b) - atoms(a))}, — в $S^s$ недоказуема. Вывести её в "
                 f"{NAME[sy]} можно только с {NEWNAME[sy]}: это единственная схема, допускающая в заключении элементарные "
                 f"высказывания, отсутствующие в посылке ({'с. 49' if sy == S2 else 'с. 53'}).")
        else:
            t = (f"тавтология, но общих элементарных высказываний нет ({K.letters(atoms(a))} и {K.letters(atoms(b))}): "
                 "недоказуема в $S^w$ (MT1 § 2, с. 49); в $S^s$ тоже — в заключение входят элементарные высказывания, "
                 "отсутствующие в посылке.")
        sol.append(f"{L[k]}) {t[0].upper() + t[1:]}")
    cond = (f"{CONV[sy]} Исследуйте доказуемость каждой формулы в $S^s$ и в $S^w$, обоснуйте значениями и составом "
            f"элементарных высказываний; для формул, разделяющих системы, укажите схему {NAME[sy]}, без которой их не "
            f"вывести. {CRIT_S} {CRIT_W}\n\n" + "\n".join(f"{L[k]}) ${ft(a, b, sy)}$" for k, (a, b) in enumerate(its)))
    return card(level, "S", step, "short", src, "Ss, Sw, сравнение систем", cond, "; ".join(ans), "\n".join(sol),
                system="S^w")


# ---------- цепочки x ⊢ y, y ⊢ z и ограничение R1 ----------
def chain(cat, sy):
    for _ in range(40000):
        names = ["x", "y", "z"]
        r = rnd.random()
        X = contra(rnd.sample(names, 2), sy) if cat != "A" and r < 0.5 else rf(rnd.sample(names, 2), 2, sy)
        Y = rf(names, 2, sy)
        Z = tauto(rnd.sample(names, 2), sy) if cat != "A" and r >= 0.5 else rf(rnd.sample(names, 2), 2, sy)
        if not (K.weak(X, Y) and K.weak(Y, Z)) or X == Y or Y == Z or X == Z:
            continue
        tri = atoms(X) & atoms(Y) & atoms(Z)
        got = "A" if tri else ("B" if K.common(X, Z) else "C")
        if got == cat and size(X) + size(Y) + size(Z) <= 34 and size(X) >= 3:
            assert K.taut(X, Z)
            return X, Y, Z
    raise RuntimeError(cat)


def chain_text(cat, X, Y, Z, sy):
    tri = atoms(X) & atoms(Y) & atoms(Z)
    head = (f"${ft(X, Y, sy)}$ и ${ft(Y, Z, sy)}$ доказуемы (тавтологии с {ob(K.common(X, Y), 'ins')} и "
            f"{ob(K.common(Y, Z), 'ins')}; MT4 § 3, с. 52). ")
    if cat == "A":
        return head + f"R1 применимо: {ob(tri)} у всех трёх; ${ft(X, Z, sy)}$ доказуема по R1."
    if cat == "B":
        return head + (f"R1 неприменимо: у ${tx(X, sy)}$, ${tx(Y, sy)}$, ${tx(Z, sy)}$ нет общего элементарного "
                       f"высказывания (с. 49). Но ${ft(X, Z, sy)}$ — тавтология (так как обе формулы — тавтологии) с "
                       f"{ob(K.common(X, Z), 'ins')}, поэтому доказуема по MT4 § 3 (с. 52) — другим выводом.")
    return head + (f"R1 неприменимо: общего элементарного высказывания у трёх нет. ${ft(X, Z, sy)}$ — тавтология, но у "
                   f"посылки ({K.letters(atoms(X))}) и заключения ({K.letters(atoms(Z))}) общих нет: по MT1 § 2 (с. 49) "
                   "недоказуема — никаким выводом.")


CHAIN_ANS = {"A": "R1 применимо, $p \\vdash r$ доказуема", "B": "R1 неприменимо, но $p \\vdash r$ доказуема",
             "C": "R1 неприменимо, $p \\vdash r$ недоказуема"}


def c_chain(sy, src, level=7, step="open"):
    cats = ["A", "B", "C", rnd.choice(["B", "C"])]
    rnd.shuffle(cats)
    its = [chain(c, sy) for c in cats]
    body = "\n".join(f"{L[k]}) $p$ = ${tx(X, sy)}$, $q$ = ${tx(Y, sy)}$, $r$ = ${tx(Z, sy)}$"
                     for k, (X, Y, Z) in enumerate(its))
    cond = (f"{CONV[sy]} {RESTR}. {CRIT_W}\n\nДля каждой тройки высказываний $p$, $q$, $r$ проверьте, что "
            f"$p \\vdash q$ и $q \\vdash r$ доказуемы в {NAME[sy]}, выясните, применимо ли к ним R1, и исследуйте "
            f"доказуемость $p \\vdash r$.\n\n{body}")
    ans = "; ".join(f"{L[k]}) {CHAIN_ANS[c]}" for k, c in enumerate(cats))
    sol = "\n".join(f"{L[k]}) {chain_text(c, *its[k], sy)}" for k, c in enumerate(cats))
    return card(level, "C" if src in (SRC[2], SRC[3]) else "P", step, "short", src,
                f"{'S2' if sy == S2 else 'S2w'}, ограничение R1, непарадоксальность",
                cond, ans, sol, system=SYSF[sy])


def c_chain_diag(sy, src, level=7, step="vary"):
    cats = ["A", "B", "C", rnd.choice(["A", "B", "C"])]
    rnd.shuffle(cats)
    its = [chain(c, sy) for c in cats]
    wrong = rnd.sample([k for k, c in enumerate(cats) if c in ("B", "C")], 1)
    wrong += rnd.sample([k for k in range(4) if cats[k] != cats[wrong[0]]], 1)
    body, ans, sol = [], [], []
    for k, (c, (X, Y, Z)) in enumerate(zip(cats, its)):
        f = f"$p$ = ${tx(X, sy)}$, $q$ = ${tx(Y, sy)}$, $r$ = ${tx(Z, sy)}$"
        if k in wrong:
            if c == "C":
                claim = "$p \\vdash q$ и $q \\vdash r$ доказуемы, значит, по R1 доказуема и $p \\vdash r$"
                ans.append(f"{k + 1}: R1 неприменимо (ограничение, с. 49), $p \\vdash r$ недоказуема (MT1 § 2)")
            elif c == "B":
                claim = "R1 неприменимо из-за ограничения, значит, $p \\vdash r$ недоказуема"
                ans.append(f"{k + 1}: $p \\vdash r$ доказуема (MT4 § 3, с. 52), хотя R1 к этой тройке неприменимо")
            else:
                na = atoms(Z) - atoms(X)
                claim = (f"$p \\vdash r$ недоказуема: в $r$ {newp(na, 'которого нет в $p$')}" if na else
                         "R1 неприменимо: общего элементарного высказывания у трёх нет")
                ans.append(f"{k + 1}: R1 применимо ({ob(atoms(X) & atoms(Y) & atoms(Z))}), $p \\vdash r$ доказуема")
            sol.append(f"{k + 1}. Неверно. {chain_text(c, X, Y, Z, sy)}")
        else:
            claim = {"A": "R1 применимо, $p \\vdash r$ доказуема",
                     "B": "R1 неприменимо, но $p \\vdash r$ доказуема по MT4 § 3",
                     "C": "R1 неприменимо, а $p \\vdash r$ недоказуема по MT1 § 2"}[c]
        body.append(f"{k + 1}. {f}: {claim}.")
    cond = (f"{CONV[sy]} {RESTR}. {CRIT_W}\n\nВо всех тройках ниже $p \\vdash q$ и $q \\vdash r$ доказуемы в {NAME[sy]}. "
            f"Студент рассуждал о формуле $p \\vdash r$:\n\n" + "\n".join(body) +
            "\n\nРовно два рассуждения неверны. Найдите их, назовите нарушенное правило или метатеорему с номером и "
            "страницей и дайте верный ответ.")
    return card(level, "E", step, "text", src, f"{'S2' if sy == S2 else 'S2w'}, ограничение R1, диагностика", cond,
                "; ".join(ans), "\n".join(sol) + "\n\nОстальные рассуждения верны.", system=SYSF[sy])


# ---------- составные замены и почти-примеры A15 / A12 ----------
def cmp2(sy):
    pool = [C(x, N(y)), N(C(y, z)), C(N(x), z), N(N(u)), N(y), C(u, w)]
    pool += [D(x, N(z)), N(D(y, z))] if sy == S2 else [W(x, N(z)), W(N(y), u)]
    return pool


def near_items(sy):
    """(посылка, заключение, вид, вывод или None)."""
    for _ in range(200):
        X, Y, Z = rnd.sample(cmp2(sy), 3)
        if X[0] != "neg" and len(atoms(X) & atoms(Y)) == 0:
            break
    out = []
    if sy == S2:
        out.append((N(X), N(C(X, Y)), "inst", f"$x$ := ${tx(X)}$, $y$ := ${tx(Y)}$"))
        out.append((N(N(X)), N(C(N(X), Y)), "inst", f"$x$ := ${tx(N(X))}$, $y$ := ${tx(Y)}$"))
        out.append((N(X), N(C(Y, X)), "der", [(N(X), N(C(X, Y)), "A15"), (C(X, Y), C(Y, X), "A4"),
                                               (C(Y, X), C(X, Y), "A4"), (N(C(X, Y)), N(C(Y, X)), ("R3", 2, 3)),
                                               (N(X), N(C(Y, X)), ("R1", 1, 4))]))
        out.append((X, N(C(N(X), Y)), "der", [(X, N(N(X)), "A1"), (N(N(X)), N(C(N(X), Y)), "A15"),
                                             (X, N(C(N(X), Y)), ("R1", 1, 2))]))
        out.append((N(X), C(N(X), N(Y)), "no", None))
        out.append((N(C(X, Y)), N(X), "no", None))
        out.append((N(X), N(D(X, Y)), "no", None))
    else:
        out.append((X, W(X, Y), "inst", f"$x$ := ${tx(X, sy)}$, $y$ := ${tx(Y, sy)}$"))
        out.append((W(X, Z), W(W(X, Z), Y), "inst", f"$x$ := ${tx(W(X, Z), sy)}$, $y$ := ${tx(Y, sy)}$"))
        out.append((C(X, Z), W(X, Y), "der", [(C(X, Z), X, "A3"), (X, W(X, Y), "A12"), (C(X, Z), W(X, Y), ("R1", 1, 2))]))
        out.append((N(N(X)), W(X, Y), "der", [(N(N(X)), X, "A1"), (X, W(X, Y), "A12"), (N(N(X)), W(X, Y), ("R1", 1, 2))]))
        out.append((X, W(W(X, Y), Z), "der", [(X, W(X, Y), "A12"), (W(X, Y), W(W(X, Y), Z), "A12"),
                                             (X, W(W(X, Y), Z), ("R1", 1, 2))]))
        out.append((X, W(Y, X), "crit", None))
        out.append((X, C(X, Y), "no", None))
        out.append((W(X, Y), X, "no", None))
    for a, b, kd, extra in out:
        isin = (K.axiom_S2 if sy == S2 else K.axiom_S_2)(a, b) == NEWNAME[sy]
        assert isin == (kd == "inst"), (kd, ft(a, b, sy))
        if kd == "der":
            assert not K.check(extra, sy), (K.check(extra, sy), show(extra, sy))
            assert extra[-1][0] == a and extra[-1][1] == b
        if kd in ("der", "crit", "inst"):
            assert K.weak(a, b)
        if kd == "no":
            assert not K.taut(a, b)
    return out


NEAR_WHY = {S2: "схема A15 требует, чтобы посылка была отрицанием $\\sim X$, а заключение — отрицанием конъюнкции $\\sim(XY)$ "
                "с тем же $X$ первым членом",
            S_2: "схема A12 (в виде $x \\vdash x \\vee y$) требует, чтобы заключение было двучленной дизъюнкцией, первый "
                 "член которой совпадает с посылкой"}


def near_sol(a, b, kd, extra, sy):
    if kd == "inst":
        return f"пример {NEWNAME[sy]}: {extra}."
    base = f"не пример {NEWNAME[sy]} ({NEAR_WHY[sy]}); "
    if kd == "der":
        return (base + "доказуема:\n\n" + show(extra, sy) + "\n\n" + r1_note(extra))
    if kd == "crit":
        return base + (f"доказуема: тавтология с {ob(K.common(a, b), 'ins')} (MT4 § 3, с. 52; эквивалентность "
                       "$S^2$ и $S_2$ — с. 53).")
    return base + f"недоказуема: при {K.env_text(K.counter(a, b))} посылка — 1, заключение — 0, это не тавтология (с. 49)."


def near_ans(kd, sy):
    return {"inst": f"пример {NEWNAME[sy]}", "der": f"не пример {NEWNAME[sy]}, доказуема",
            "crit": f"не пример {NEWNAME[sy]}, доказуема", "no": f"не пример {NEWNAME[sy]}, недоказуема"}[kd]


def c_near(sy, src, level=6, step="vary"):
    pool = near_items(sy)
    insts = [t for t in pool if t[2] == "inst"]
    ders = [t for t in pool if t[2] in ("der", "crit")]
    nos = [t for t in pool if t[2] == "no"]
    its = [rnd.choice(insts)] + rnd.sample(ders, 2 if len(ders) > 1 else 1) + rnd.sample(nos, 1)
    rnd.shuffle(its)
    sch = ("A15 $\\sim x \\vdash \\sim(xy)$" if sy == S2 else "A12 (в виде $x \\vdash x \\vee y$, с. 54)")
    r3 = (" R3 (с. 17): если $x \\vdash y$ и $y \\vdash x$, то $z \\vdash v$, где $v$ получается из $z$ заменой вхождений "
          "$x$ на $y$." if sy == S2 else "")
    cond = (f"{CONV[sy]} {SCH[sy]}{r3}\n\nДля каждой формулы установите, получается ли она из схемы {sch} заменой букв "
            f"высказываниями (одинаковые буквы — одинаковыми); если получается — укажите замену, если нет — исследуйте "
            f"доказуемость формулы в {NAME[sy]}: выведите её (соблюдая ограничение R1) или опровергните значениями. "
            f"{CRIT_W}\n\n" + "\n".join(f"{L[k]}) ${ft(a, b, sy)}$" for k, (a, b, _, _) in enumerate(its)))
    ans = "; ".join(f"{L[k]}) {near_ans(kd, sy)}" for k, (_, _, kd, _) in enumerate(its))
    sol = "\n\n".join(f"{L[k]}) " + near_sol(a, b, kd, ex, sy) for k, (a, b, kd, ex) in enumerate(its))
    return card(level, "A", step, "short", src, f"{'S2' if sy == S2 else 'S2w'}, схемы, почти-примеры", cond, ans, sol,
                system=SYSF[sy])


def c_near_diag(sy, src, level=6, step="vary"):
    pool = near_items(sy)
    insts = [t for t in pool if t[2] == "inst"]
    ders = [t for t in pool if t[2] == "der"]
    nos = [t for t in pool if t[2] == "no"]
    its = [rnd.choice(insts), rnd.choice(ders), rnd.choice(nos), rnd.choice([t for t in ders + insts if t not in []])]
    while its[3] in its[:3]:
        its[3] = rnd.choice(ders + insts + nos)
    rnd.shuffle(its)
    wrong = [k for k, t in enumerate(its) if t[2] == "no"][:1]
    wrong += rnd.sample([k for k, t in enumerate(its) if t[2] in ("der", "inst") and k not in wrong], 1)
    body, ans, sol = [], [], []
    for k, (a, b, kd, ex) in enumerate(its):
        if k in wrong:
            if kd == "no":
                claim = f"пример {NEWNAME[sy]}, значит, доказуема"
                ans.append(f"{k + 1}: не пример {NEWNAME[sy]} и недоказуема (не тавтология)")
            elif kd == "inst":
                claim = f"не пример {NEWNAME[sy]}: посылка и заключение начинаются по-разному, значит, недоказуема"
                ans.append(f"{k + 1}: пример {NEWNAME[sy]} ({ex}), доказуема")
            else:
                claim = f"не пример {NEWNAME[sy]}, значит, недоказуема"
                ans.append(f"{k + 1}: не пример {NEWNAME[sy]}, но доказуема (вывод из {len(ex)} строк)")
            sol.append(f"{k + 1}. Неверно: " + near_sol(a, b, kd, ex, sy))
        else:
            claim = {"inst": f"пример {NEWNAME[sy]}", "der": f"не пример {NEWNAME[sy]}, но доказуема",
                     "no": f"не пример {NEWNAME[sy]} и недоказуема"}[kd]
        body.append(f"{k + 1}. ${ft(a, b, sy)}$ — {claim}.")
    sch = ("A15 $\\sim x \\vdash \\sim(xy)$ (с. 49)" if sy == S2 else "A12 в виде $x \\vdash x \\vee y$ (с. 52, 54)")
    cond = (f"{CONV[sy]} {SCH[sy]}{' R3 — как в $S^1$ (с. 17).' if sy == S2 else ''}\n\nСтудент сравнил четыре формулы со "
            f"схемой {sch} и сделал выводы о доказуемости в {NAME[sy]}:\n\n" + "\n".join(body) +
            "\n\nРовно два вывода неверны. Найдите их, объясните ошибку со ссылкой на схему, правило или метатеорему и "
            f"страницу и дайте верный ответ. {CRIT_W}")
    return card(level, "E", step, "text", src, f"{'S2' if sy == S2 else 'S2w'}, схемы, почти-примеры, диагностика", cond,
                "; ".join(ans), "\n\n".join(sol) + "\n\nОстальные выводы верны.", system=SYSF[sy])


# ---------- A15 и теоремы S¹ ----------
def c_a15_transfer(src, level=7, step="transfer"):
    pool = cmp2(S2)
    its = []
    while len(its) < 4:
        X, Y = rnd.sample(pool, 2)
        if X[0] == "neg" and X[1][0] == "v":
            continue
        want_strong = len(its) in (0, 2) and False or len(its) == 1
        if want_strong:
            lit_ = rnd.choice(sorted(atoms(X)))
            Y = rnd.choice([V(lit_), N(V(lit_)), N(X)])
        a, b = N(X), N(C(X, Y))
        if (a, b) not in its and K.taut(a, b) and (K.strong(a, b) == want_strong):
            its.append((a, b))
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (a, b) in enumerate(its):
        st = K.strong(a, b)
        ans.append(f"{L[k]}) {'теорема' if st else 'не теорема'} $S^1$")
        X, Y = a[1], b[1][1][1]
        t = (f"{L[k]}) Пример A15 ($x$ := ${tx(X)}$, $y$ := ${tx(Y)}$). Тавтология: если посылка ${tx(a)}$ — 1, то "
             f"${tx(X)}$ = 0, конъюнкция ${tx(b[1])}$ = 0 и заключение — 1 (при любых значениях ${tx(Y)}$). ")
        if st:
            t += ("Элементарные высказывания заключения все входят в посылку: сильная тавтология, по MT6 § 7 гл. 1 (с. 32) — "
                  "теорема уже $S^1$.")
        else:
            t += (f"В заключение {newp(atoms(b) - atoms(a))}: в $S^1$ такие формулы "
                  "недоказуемы (непарадоксальность, гл. 1, § 4, с. 21); теорема только $S^2$.")
        sol.append(t)
    cond = (f"{CONV[S2]} Схема A15 системы $S^2$: $\\sim x \\vdash \\sim(xy)$ (с. 49). Каждая формула ниже — пример A15 с "
            "составными заменами. Найдите замену, проверьте значениями, что формула — тавтология (так обосновывается "
            "непротиворечивость $S^2$, с. 49), и исследуйте, доказуема ли она уже в $S^1$. Формула доказуема в $S^1$ тогда и "
            "только тогда, когда она — сильная тавтология: тавтология, в заключение которой не входят элементарные "
            "высказывания, отсутствующие в посылке (гл. 1, § 4, с. 21; § 7, MT6, с. 32).\n\n"
            + "\n".join(f"{L[k]}) ${ft(a, b)}$" for k, (a, b) in enumerate(its)))
    return card(level, "S", step, "short", src, "S2, A15, непротиворечивость, S1", cond, "; ".join(ans), "\n".join(sol))




# ---------- «постройте или докажите, что нельзя» ----------
def facts(a, b, sy):
    out = []
    if K.taut(a, b):
        out.append("формула — тавтология (нет набора значений, при котором посылка — 1, а заключение — 0)")
    else:
        out.append(f"при {K.env_text(K.counter(a, b))} посылка — 1, заключение — 0: не тавтология")
    cm = K.common(a, b)
    out.append(f"{ob(cm)} элементарн{'ое высказывание' if len(cm) == 1 else 'ые высказывания'}" if cm else "общих элементарных высказываний нет")
    out.append(f"в заключение {newp(atoms(b) - atoms(a))}" if atoms(b) - atoms(a) else
               "все элементарные высказывания заключения входят в посылку")
    out.append("посылка ложна при всех значениях (противоречие)" if K.is_contra(a) else
               f"посылка — не противоречие (равна 1 при {K.env_text(next(e for e in K.rows(a) if K.value(a, e)))})")
    out.append("заключение истинно при всех значениях (тавтология)" if K.is_taut(b) else
               f"заключение — не тавтология (равно 0 при {K.env_text(next(e for e in K.rows(b) if not K.value(b, e)))})")
    out.append(f"в $S^w$ {'доказуема' if K.weak(a, b) else 'недоказуема'} (MT1 § 2, MT4 § 3), в $S^s$ "
               f"{'доказуема' if K.strong(a, b) else 'недоказуема'}")
    return "; ".join(out) + "."


def poss(sy):
    dis = D if sy == S2 else W
    return [
        ("доказуема в $S^w$, недоказуема в $S^s$, посылка — не противоречие, заключение — не тавтология, и в заключение "
         "входит ровно одно элементарное высказывание, отсутствующее в посылке",
         lambda a, b: K.weak(a, b) and not K.strong(a, b) and not K.is_contra(a) and not K.is_taut(b)
         and len(atoms(b) - atoms(a)) == 1, None),
        ("доказуема в $S^w$ и недоказуема в $S^s$, а формула $\\sim y \\vdash \\sim x$, где $x$ — посылка и $y$ — "
         "заключение, доказуема в $S^s$",
         lambda a, b: K.weak(a, b) and not K.strong(a, b) and K.strong(N(b), N(a)), None),
        ("вместе с обратной ей формулой $y \\vdash x$ доказуема в $S^w$, хотя множества элементарных высказываний посылки "
         "и заключения различны",
         lambda a, b: K.weak(a, b) and K.weak(b, a) and atoms(a) != atoms(b),
         lambda: (lambda X, Y: (X, C(X, dis(Y, N(Y)))))(*rnd.sample([x, N(y), C(x, z), N(C(x, y))], 1),
                                                         rnd.choice([u, z, N(u)]))),
        ("доказуема в $S^w$, посылка — противоречие (ложна при всех значениях), заключение — не тавтология, и в "
         "заключение входят элементарные высказывания, отсутствующие в посылке",
         lambda a, b: K.weak(a, b) and K.is_contra(a) and not K.is_taut(b) and atoms(b) - atoms(a), None),
        (f"пример схемы {'A15' if sy == S2 else 'A12 (в виде $x \\vdash x \\vee y$)'}, доказуемый уже в "
         f"{'$S^1$' if sy == S2 else '$S_1$'}",
         lambda a, b: (K.is_a15(a, b) if sy == S2 else K.is_a12(a, b)) and K.strong(a, b),
         lambda: (lambda X: (N(X), N(C(X, rnd.choice([N(X), X])))) if sy == S2 else (X, W(X, N(X))))(
             rnd.choice([C(x, N(y)), dis(x, z), N(C(y, z))]))),
    ]


IMPOSS = [
    ("доказуема в $S^w$, обратная ей формула $y \\vdash x$ — тавтология, но недоказуема в $S^w$, хотя множества "
     "элементарных высказываний посылки и заключения совпадают",
     "Множества элементарных высказываний $x$ и $y$ совпадают и непусты (в каждом высказывании есть элементарное, D2 § 1 "
     "гл. 1, с. 15), поэтому у $y$ и $x$ есть общее элементарное высказывание. Формула $y \\vdash x$ — тавтология с общим "
     "элементарным высказыванием и по MT4 § 3 (с. 52) доказуема в $S^w$. Противоречие."),
    ("недоказуема в $S^w$, хотя заключение — тавтология и в посылке и заключении есть общее элементарное высказывание",
     "Если заключение истинно при всех значениях, то набора, при котором посылка — 1, а заключение — 0, нет: формула — "
     "тавтология. Общее элементарное высказывание есть, и по MT4 § 3 (с. 52) формула доказуема в $S^w$. Противоречие."),
    ("пример схемы {sch}, не являющийся тавтологией",
     "{why} Значит, все примеры схемы — тавтологии (на этом основана непротиворечивость, с. 49{p})."),
]


def find_ex(pred, gen, sy):
    if gen:
        for _ in range(200):
            a, b = gen()
            if pred(a, b):
                return a, b
    for _ in range(60000):
        A = rnd.sample(["x", "y", "z"], 2)
        r = rnd.random()
        a = contra(A, sy) if r < 0.25 else rf(A, 2, sy)
        b = rf(A + ["u"], 2, sy) if r < 0.85 else tauto(A + ["u"], sy)
        if a != b and size(a) + size(b) <= 26 and pred(a, b):
            return a, b
    raise RuntimeError("пример не найден")


def c_build(sy, src, level=7, step="open"):
    pd, pred, gen = rnd.choice(poss(sy))
    a, b = find_ex(pred, gen, sy)
    idesc, iproof = rnd.choice(IMPOSS)
    sch = "A15 $\\sim x \\vdash \\sim(xy)$" if sy == S2 else "A12 в виде $x \\vdash x \\vee y$"
    why = ("Пример A15 имеет вид $\\sim X \\vdash \\sim(XY)$. Если $\\sim X = 1$, то $X = 0$, конъюнкция $XY = 0$ и "
           "$\\sim(XY) = 1$." if sy == S2 else
           "Пример A12 имеет вид $X \\vdash X \\vee Y$. Если $X = 1$, то $X \\vee Y = 1$ («по крайней мере одно из», с. 36).")
    idesc = idesc.replace("{sch}", sch)
    iproof = iproof.replace("{why}", why).replace("{p}", "" if sy == S2 else ", 52")
    items = [("p", pd), ("i", idesc)]
    rnd.shuffle(items)
    cond = (f"{CONV[sy]} {CRIT_W} {CRIT_S}\n\nДля каждого пункта постройте формулу следования $x \\vdash y$ в языке "
            f"{NAME[sy]} с указанными свойствами и проверьте их значениями — или докажите, что такой формулы нет.\n\n"
            + "\n".join(f"{L[k]}) {d[0].upper() + d[1:]}." for k, (_, d) in enumerate(items)))
    ans, sol = [], []
    for k, (t, _) in enumerate(items):
        if t == "p":
            ans.append(f"{L[k]}) например, ${ft(a, b, sy)}$")
            sol.append(f"{L[k]}) ${ft(a, b, sy)}$: {facts(a, b, sy)}" +
                       (f" Обратная формула ${ft(b, a, sy)}$: {facts(b, a, sy)}" if "обратной" in pd else "") +
                       (f" Формула ${ft(N(b), N(a), sy)}$: {facts(N(b), N(a), sy)}" if "\\sim y \\vdash" in pd else ""))
        else:
            ans.append(f"{L[k]}) такой формулы нет")
            sol.append(f"{L[k]}) Такой формулы нет. {iproof}")
    return card(level, "K" if src in (SRC[2], SRC[3]) else "S", step, "build", src,
                f"{'S2' if sy == S2 else 'S2w'}, построение, Ss, Sw", cond,
                "; ".join(ans), "\n\n".join(sol), system="S^w")


# ---------- перевод S₂ → S² (D2 § 3 гл. 1) ----------
def to_s1(f):
    k = f[0]
    if k == "v":
        return f
    if k == "neg":
        return N(to_s1(f[1]))
    if k == "conj":
        return C(*(to_s1(t) for t in f[1]))
    if len(f[1]) == 2:
        a, b = f[1]
        return N(C(N(to_s1(a)), N(to_s1(b))))
    return N(C(*(N(to_s1(t)) for t in f[1])))


def c_translate(src, level=6, step="transfer"):
    for _ in range(20000):
        A = rnd.sample("xyz", 2)
        kind = rnd.choice(["yes_new", "yes_new", "nocommon", "yes_strong", "nontaut"])
        a, b = item(kind, S_2, lim=28)
        if repr((a, b)).count("wdis") >= 1 and size(to_s1(a)) + size(to_s1(b)) <= 46:
            break
    A_, B_ = to_s1(a), to_s1(b)
    for e in K.rows(a, b):
        assert K.value(a, e) == K.value(A_, e) and K.value(b, e) == K.value(B_, e)
    ok, why = reason_w(a, b, S_2)
    assert ok == K.weak(A_, B_)
    cond = (f"{CONV[S_2]} Переведите формулу $S_2$ ${ft(a, b, S_2)}$ на язык $S^2$, раскрыв каждое $x \\vee y$ по D2 § 3 гл. 1 "
            "($x \\vee y$ есть сокращение для $\\sim(\\sim x\\sim y)$, с. 20), проверьте значениями, что перевод не меняет "
            "значений посылки и заключения, и исследуйте доказуемость формулы в $S_2$ и её перевода в $S^2$ "
            f"(эквивалентность $S^2$ и $S_2$, с. 53). {CRIT_W}")
    ans = f"${ft(A_, B_)}$; в обеих системах {'доказуема' if ok else 'недоказуема'}."
    sol = (f"1. Раскрываем $\\vee$ изнутри: ${tx(a, S_2)}$ → ${tx(A_)}$; ${tx(b, S_2)}$ → ${tx(B_)}$.\n"
           "2. «Не оба члена ложны» — то же, что «по крайней мере один истинен» (с. 20, 36): при каждом наборе значений "
           "перевод посылки и заключения имеет то же значение (проверяется перебором наборов), а элементарные высказывания "
           "не меняются.\n"
           f"3. {why[0].upper() + why[1:]} — и для исходной формулы, и для перевода. Множества теорем $S^2$ и $S_2$ "
           "совпадают (из полноты обеих систем, с. 53).")
    return card(level, "T", step, "short", src, "S2, S2w, перевод, эквивалентность", cond, ans, sol, system="S^w")


# ---------- рассуждения обычного языка ----------
VOC = [
    {"x": ("идёт дождь", "дождь не идёт"), "y": ("дует ветер", "ветер не дует"), "z": ("холодно", "не холодно"),
     "u": ("светит солнце", "солнце не светит")},
    {"x": ("цепь замкнута", "цепь не замкнута"), "y": ("ток течёт", "ток не течёт"), "z": ("лампа горит", "лампа не горит"),
     "u": ("предохранитель цел", "предохранитель не цел")},
    {"x": ("свидетель говорит правду", "свидетель не говорит правду"), "y": ("алиби подтверждено", "алиби не подтверждено"),
     "z": ("подсудимый виновен", "подсудимый не виновен"), "u": ("улик достаточно", "улик недостаточно")},
    {"x": ("число делится на 2", "число не делится на 2"), "y": ("число делится на 3", "число не делится на 3"),
     "z": ("число больше 10", "число не больше 10"), "u": ("число простое", "число не простое")},
    {"x": ("поезд опоздал", "поезд не опоздал"), "y": ("рейс отменён", "рейс не отменён"),
     "z": ("встреча перенесена", "встреча не перенесена"), "u": ("билеты проданы", "билеты не проданы")},
]


def lit_t(f, voc):
    return voc[f[1]][0] if f[0] == "v" else voc[f[1][1]][1]


def verb(f, voc):
    """Высказывание обычного языка для формул ограниченного вида (литеры и одна-две связки)."""
    if K.lit(f):
        return lit_t(f, voc)
    k = f[0]
    if k == "conj" and all(K.lit(t) for t in f[1]):
        ps = [lit_t(t, voc) for t in f[1]]
        return ", ".join(ps[:-1]) + " и " + ps[-1]
    if k == "wdis" and all(K.lit(t) for t in f[1]) and len(f[1]) == 2:
        return f"{lit_t(f[1][0], voc)} или {lit_t(f[1][1], voc)}"
    if k == "neg" and f[1][0] in ("conj", "wdis") and all(K.lit(t) for t in f[1][1]) and len(f[1][1]) == 2:
        return f"неверно, что {verb(f[1], voc)}"
    if k == "conj" and len(f[1]) == 2 and f[1][0][0] == "wdis" and K.lit(f[1][1]):
        return f"{lit_t(f[1][1], voc)}, и при этом {verb(f[1][0], voc)}"
    if k == "conj" and len(f[1]) == 2 and K.lit(f[1][0]) and f[1][1][0] == "neg":
        return f"{lit_t(f[1][0], voc)}, но {verb(f[1][1], voc)}"
    if k == "wdis" and len(f[1]) == 2 and f[1][0][0] == "conj" and K.lit(f[1][1]):
        return f"«{verb(f[1][0], voc)}» или «{lit_t(f[1][1], voc)}»"
    if k == "wdis" and len(f[1]) == 2 and all(t[0] == "conj" for t in f[1]):
        return f"«{verb(f[1][0], voc)}» или «{verb(f[1][1], voc)}»"
    raise ValueError(anytex(f))


def nat_shape(names):
    l_ = lambda: (lambda v: N(v) if rnd.random() < 0.35 else v)(V(rnd.choice(names)))
    k = rnd.randrange(8)
    for _ in range(200):
        a, b, c = l_(), l_(), l_()
        if len({list(atoms(t))[0] for t in (a, b, c)}) == min(3, len(names)) and c not in (a, b) and a != b:
            break
    return [a, C(a, b), W(a, b), N(C(a, b)), N(W(a, b)), C(W(a, b), c), C(a, N(C(b, c))), W(C(a, b), c)][k]


NAT_NOTE = ("«Или» означает «по крайней мере одно из» ($\\vee$, с. 36); «неверно, что …» относится ко всему, что "
            "стоит после него; кавычки «…» показывают группировку.")


def c_nat(src, level=6, step="vary"):
    want = rnd.choice(["yes_new", "yes_new", "nocommon", "yes_strong", "nontaut"])
    for _ in range(50000):
        voc = rnd.choice(VOC)
        A = rnd.sample("xyzu", 3)
        a, b = nat_shape(A[:2]), nat_shape(A)
        if want == "nocommon":
            b = nat_shape([t for t in "xyzu" if t not in A[:2]])
        cat = ("nontaut" if not K.taut(a, b) else "nocommon" if not K.common(a, b) else
               "yes_strong" if K.strong(a, b) else "yes_new")
        if cat == want and a != b and size(a) + size(b) >= 9:
            try:
                pa, pb = verb(a, voc), verb(b, voc)
            except ValueError:
                continue
            break
    ok, why = reason_w(a, b, S_2)
    s_ = K.strong(a, b)
    letters_ = ", ".join(f"${k}$ — «{voc[k][0]}»" for k in sorted(atoms(a) | atoms(b)))
    cond = (f"Запишите рассуждение формулой следования в языке $S_2$ и исследуйте, будет ли оно следованием в смысле "
            f"$S^w$ и в смысле $S^s$: «{pa[0].upper() + pa[1:]}; следовательно, {pb}». Обозначения: {letters_}. "
            f"{NAT_NOTE} {CRIT_W} {CRIT_S}")
    ans = (f"${ft(a, b, S_2)}$; $S^w$ — {'да' if ok else 'нет'}, $S^s$ — {'да' if s_ else 'нет'}.")
    sol = (f"1. Формула: ${ft(a, b, S_2)}$.\n2. $S^w$: {why}.\n3. $S^s$: " +
           ("тавтология, и все элементарные высказывания заключения входят в посылку — доказуема." if s_ else
            "недоказуема: " + ("не тавтология." if not K.taut(a, b) else f"в заключение {newp(atoms(b) - atoms(a))}.")))
    return card(level, "F", step, "short", src, "Sw, Ss, обычный язык", cond, ans, sol, form="nat", system="S^w")


def c_nat_chain(src, kind, level=7, step="transfer"):
    voc = rnd.choice(VOC)
    a_, b_ = rnd.sample("xyzu", 2)
    p_ = V(a_) if rnd.random() < 0.6 else N(V(a_))
    q_ = V(b_) if rnd.random() < 0.6 else N(V(b_))
    np_ = N(p_) if p_[0] == "v" else p_[1]
    if kind == "lewis":
        X, M, Y = C(p_, np_), C(W(np_, q_), p_), q_
        steps = [(X, M), (M, Y), (X, Y)]
        words = [f"{lit_t(p_, voc)} и {lit_t(np_, voc)}", f"{lit_t(p_, voc)}, и при этом {lit_t(np_, voc)} или "
                 f"{lit_t(q_, voc)}", lit_t(q_, voc)]
    else:
        X, M1, M2, Y = C(np_, p_), W(C(np_, p_), C(np_, q_)), C(np_, W(p_, q_)), q_
        steps = [(X, M1), (M1, M2), (M2, Y), (X, Y)]
        words = [f"{lit_t(np_, voc)} и {lit_t(p_, voc)}",
                 f"«{lit_t(np_, voc)} и {lit_t(p_, voc)}» или «{lit_t(np_, voc)} и {lit_t(q_, voc)}»",
                 f"{lit_t(np_, voc)}, и при этом {lit_t(p_, voc)} или {lit_t(q_, voc)}", lit_t(q_, voc)]
    idx = [(0, 1), (1, 2), (0, 2)] if kind == "lewis" else [(0, 1), (1, 2), (2, 3), (0, 3)]
    rs = "\n".join(f"{n + 1}) «{words[i][0].upper() + words[i][1:]}; следовательно, {words[j]}»." for n, (i, j) in enumerate(idx))
    for n, (a, b) in enumerate(steps):
        assert K.weak(a, b) == (n < len(steps) - 1), (n, aft(a, b))
    mid = steps[-2][0]
    assert not (atoms(X) & atoms(mid) & atoms(Y))
    letters_ = ", ".join(f"${k}$ — «{voc[k][0]}»" for k in sorted(atoms(Y) | atoms(X)))
    extra = (" Сравните с системой Аккермана, где, по книге (с. 55), третья формула недоказуема." if kind == "akk" else "")
    cond = (f"Запишите рассуждения формулами в языке $S_2$ и исследуйте каждое как следование в смысле $S^w$; затем "
            f"выясните, можно ли получить последнее из предыдущих по транзитивности (R1 с ограничением). Обозначения: "
            f"{letters_}. {NAT_NOTE} {RESTR}. {CRIT_W}{extra}\n\n{rs}")
    ans = ("; ".join(f"{n + 1}) ${ft(a, b, S_2)}$ — {'доказуема' if n < len(steps) - 1 else 'недоказуема'}"
                     for n, (a, b) in enumerate(steps)) +
           "; последнее по R1 не получить: у трёх высказываний нет общего элементарного (с. 49)")
    sol = []
    for n, (a, b) in enumerate(steps):
        ok, why = reason_w(a, b, S_2)
        sol.append(f"{n + 1}) ${ft(a, b, S_2)}$: {why}.")
    sol.append(f"Транзитивность: {'R1 к первым двум формулам применимо (общее ' + K.letters(atoms(X) & atoms(steps[0][1]) & atoms(steps[1][1])) + '), получаем ' + '$' + ft(X, steps[1][1], S_2) + '$; ' if kind == 'akk' else ''}"
               f"применить R1 к ${ft(X, mid, S_2)}$ и ${ft(mid, Y, S_2)}$ нельзя: у ${tx(X, S_2)}$, ${tx(mid, S_2)}$ и "
               f"${tx(Y, S_2)}$ нет общего элементарного высказывания (ограничение, с. 49). Это и спасает $S^w$ от "
               "«парадокса» «из противоречия — что угодно»: последняя формула недоказуема по MT1 § 2.")
    if kind == "akk":
        sol.append("В системе Аккермана, по книге (с. 55), парадокс исключён иначе: недоказуема уже третья формула, хотя она "
                   "удовлетворяет критерию $S^w$; поэтому система Аккермана неполна в смысле полноты $S^w$.")
    return card(level, "C" if src in (SRC[2], SRC[3]) else "P", step, "short", src,
                "Sw, парадоксы, ограничение R1, обычный язык", cond, ans,
                "\n".join(sol), form="nat", system="S^w")


# ---------- § 6: система S₂¹ ----------
DNF_DEF = ("По с. 56: $x^1 \\vee \\ldots \\vee x^n$ ($n \\geq 1$) находится в дизъюнктивной нормальной форме (ДНФ), если каждое "
           "$x^i$ — конъюнкция, образованная из элементарных высказываний и их отрицаний; эти элементарные высказывания и "
           "отрицания — конъюнктивные составляющие $x^i$.")
CRIT21 = ("Критерий (MT1–MT2 § 6, с. 56–57): если $x^1 \\vee \\ldots \\vee x^n$ и $y^1 \\vee \\ldots \\vee y^m$ — ДНФ посылки и "
          "заключения, то $x \\vdash y$ доказуема в $S_2^1$ тогда и только тогда, когда для каждого $x^i$ найдётся $y^j$, "
          "все конъюнктивные составляющие которого входят в $x^i$ (тогда $x^i \\vdash y^j$ — тавтология).")
S21_SYS = ("Система $S_2^1$ Е. А. Сидоренко (с. 55–56): схемы A1–A10 системы $S_1$ и правила R1 (если $x \\vdash y$, то "
           "$\\sim y \\vdash \\sim x$), R2 (если $x \\vdash y$ и $y \\vdash z$, то $x \\vdash z$), R3 (если $x \\vdash y$ и "
           "$z \\vdash v$, то $x \\vee z \\vdash y \\vee v$).")
CONV6 = ("Буквы $x, y, z, u$ — элементарные высказывания; $\\vee$ — соединительная дизъюнкция («по крайней мере одно из»); "
         "в многочленных дизъюнкциях скобки опускаем, как в доказательстве MT2 (с. 57).")


def L_(atom, neg):
    return N(V(atom)) if neg else V(atom)


def mem(names, k, allow_contra=False):
    if allow_contra and rnd.random() < 0.25:
        a = rnd.choice(names)
        rest = [L_(t, rnd.random() < 0.4) for t in rnd.sample([t for t in names if t != a], min(k - 2, len(names) - 1))] if k > 2 else []
        return frozenset([V(a), N(V(a))] + rest)
    ats = rnd.sample(names, min(k, len(names)))
    return frozenset(L_(t, rnd.random() < 0.4) for t in ats)


def mform(ms):
    def one(m):
        ls = sorted(m, key=lambda l: ("xyzuw".index(list(atoms(l))[0]), l[0] == "neg"))
        return ls[0] if len(ls) == 1 else C(*ls)
    ms = list(ms)
    return one(ms[0]) if len(ms) == 1 else W(*(one(m) for m in ms))


def mtex(m):
    return s1w.tex(mform([m]))


def dnf_pair(want, names=("x", "y", "z"), maxs=34):
    names = list(names)
    for _ in range(5000):
        xs = []
        while len(xs) < rnd.choice([2, 3]):
            m = mem(names, rnd.choice([1, 2, 2, 3]), allow_contra=True)
            if m not in xs:
                xs.append(m)
        ys = []
        if want:
            for xi in xs:
                if rnd.random() < 0.7 or not ys:
                    sub_ = frozenset(rnd.sample(sorted(xi, key=repr), rnd.randint(1, len(xi))))
                    if sub_ not in ys:
                        ys.append(sub_)
        while len(ys) < rnd.choice([2, 3]):
            m = mem(names + (["u"] if rnd.random() < 0.3 else []), rnd.choice([1, 2, 2]))
            if m not in ys:
                ys.append(m)
        rnd.shuffle(ys)
        a, b = mform(xs), mform(ys)
        if K.s21(a, b) == want and a != b and 8 <= size(a) + size(b) <= maxs:
            return a, b
    raise RuntimeError("ДНФ")


def s21_text(a, b):
    xs, ys = K.members(a), K.members(b)
    mp = K.s21_map(a, b)
    if all(mp):
        return "доказуема: " + "; ".join(f"$x^{i}$ = ${mtex(xs[i - 1])}$ содержит все составляющие $y^{j}$ = ${mtex(ys[j - 1])}$"
                                          for i, j in enumerate(mp, 1)) + " (MT2, с. 56–57)"
    i = mp.index(None) + 1
    xi = xs[i - 1]
    det = ", ".join(f"в $y^{j}$ = ${mtex(yj)}$ есть ${s1w.tex(sorted(yj - xi, key=repr)[0])}$" for j, yj in enumerate(ys, 1))
    return (f"недоказуема: для члена $x^{i}$ = ${mtex(xi)}$ нет $y^j$, все составляющие которого входят в него ({det}, "
            f"а в $x^{i}$ этого нет); по MT1 (с. 56) формула недоказуема")


def c21_series(src, level=6, step="iso"):
    want = [True, False, rnd.choice([True, False]), rnd.choice([True, False])]
    its = []
    while len(its) < 4:
        p_ = dnf_pair(want[len(its)])
        if p_ not in its:
            its.append(p_)
    rnd.shuffle(its)
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21}\n\nКаждая формула записана в ДНФ (члены посылки — $x^1, x^2, \\ldots$, "
            "члены заключения — $y^1, y^2, \\ldots$ по порядку). Исследуйте её доказуемость в $S_2^1$: для доказуемой укажите "
            "для каждого $x^i$ подходящий $y^j$, для недоказуемой — член $x^i$, которому никакой $y^j$ не подходит, и почему.\n\n"
            + "\n".join(f"{L[k]}) ${ft(a, b, S_2)}$" for k, (a, b) in enumerate(its)))
    ans = "; ".join(f"{L[k]}) {'доказуема' if K.s21(a, b) else 'недоказуема'} в $S_2^1$" for k, (a, b) in enumerate(its))
    sol = "\n".join(f"{L[k]}) {s21_text(a, b)[0].upper() + s21_text(a, b)[1:]}." for k, (a, b) in enumerate(its))
    return card(level, "C", step, "short", src, "S21, ДНФ, критерий", cond, ans, sol, system="S_2^1")


def c21_vs_w(src, level=7, step="transfer"):
    kinds = ["both", "w_only", "w_only", rnd.choice(["none", "both", "w_only"])]
    its = []
    for kd in kinds:
        for _ in range(20000):
            a, b = dnf_pair(kd == "both")
            w_ = K.weak(a, b)
            if (kd == "both" and w_) or (kd == "w_only" and w_ and not K.s21(a, b)) or (kd == "none" and not w_):
                if (a, b) not in its:
                    its.append((a, b))
                    break
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (a, b) in enumerate(its):
        w_, s_ = K.weak(a, b), K.s21(a, b)
        assert not s_ or w_
        ans.append(f"{L[k]}) $S^w$ — {'да' if w_ else 'нет'}, $S_2^1$ — {'да' if s_ else 'нет'}")
        _, why = reason_w(a, b, S_2)
        sol.append(f"{L[k]}) $S^w$: {why}. $S_2^1$: {s21_text(a, b)}.")
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21} {CRIT_W}\n\nИсследуйте доказуемость каждой формулы в $S^w$ и в $S_2^1$ "
            "(обоснуйте значениями и составом членов ДНФ) и объясните, что показывают формулы, доказуемые в $S^w$, но не в "
            "$S_2^1$, о полноте $S_2^1$ в смысле $S^w$ (с. 55).\n\n"
            + "\n".join(f"{L[k]}) ${ft(a, b, S_2)}$" for k, (a, b) in enumerate(its)))
    sol.append("Формулы, доказуемые в $S^w$, но не в $S_2^1$, показывают, что $S_2^1$ не полна в смысле полноты $S^w$; по книге "
               "(с. 55) она полна в другом смысле — в смысле MT3 § 6 (с. 57).")
    return card(level, "S", step, "short", src, "S21, Sw, сравнение систем", cond, "; ".join(ans), "\n".join(sol),
                system="S_2^1")


def stud_rev(a, b):
    """Ошибка: для каждого yʲ ищется xⁱ, в который он входит."""
    xs, ys = K.members(a), K.members(b)
    return all(any(yj <= xi for xi in xs) for yj in ys)


def stud_some(a, b):
    xs, ys = K.members(a), K.members(b)
    return any(yj <= xs[0] for yj in ys)


def stud_noneg(a, b):
    strip = lambda m: frozenset(t if t[0] == "v" else t[1] for t in m)
    xs, ys = [strip(m) for m in K.members(a)], [strip(m) for m in K.members(b)]
    return all(any(yj <= xi for yj in ys) for xi in xs)


STUD = {"rev": (stud_rev, "для каждого члена заключения нашёлся член посылки, в который входят все его составляющие"),
        "some": (stud_some, "для первого члена посылки нашёлся подходящий член заключения"),
        "noneg": (stud_noneg, "если не обращать внимания на знаки отрицания, каждому члену посылки подходит член заключения"),
        "taut": (K.taut, "формула — тавтология")}


def c21_diag(src, level=6, step="vary"):
    its, errs = [], []
    kinds = rnd.sample(list(STUD), 2)
    for kd in kinds:
        f, _ = STUD[kd]
        for _ in range(20000):
            a, b = dnf_pair(rnd.choice([True, False]))
            if f(a, b) != K.s21(a, b) and (a, b) not in its:
                its.append((a, b))
                errs.append(kd)
                break
    while len(its) < 4:
        a, b = dnf_pair(rnd.choice([True, False]))
        if (a, b) not in its:
            its.append((a, b))
            errs.append(None)
    order = list(range(4))
    rnd.shuffle(order)
    its, errs = [its[i] for i in order], [errs[i] for i in order]
    body, ans, sol = [], [], []
    for k, ((a, b), e) in enumerate(zip(its, errs)):
        r = K.s21(a, b)
        if e:
            f, txt = STUD[e]
            v = f(a, b)
            body.append(f"{k + 1}. ${ft(a, b, S_2)}$ — {'доказуема' if v else 'недоказуема'}: "
                        f"{txt if v else 'не выполнено: ' + txt}.")
            ans.append(f"{k + 1}: {'доказуема' if r else 'недоказуема'} в $S_2^1$ (MT1–MT2, с. 56–57)")
            how = {"rev": "студент перевернул критерий: подходящий член заключения нужно искать для каждого члена посылки",
                   "some": "проверять нужно каждый член посылки, а не один",
                   "noneg": "$\\sim a$ и $a$ — разные конъюнктивные составляющие (с. 56)",
                   "taut": "тавтологии мало — это критерий $S^w$, а в $S_2^1$ нужен подходящий член заключения для каждого "
                           "члена посылки"}[e]
            sol.append(f"{k + 1}. Неверно: {how}. Верно: {s21_text(a, b)}.")
        else:
            body.append(f"{k + 1}. ${ft(a, b, S_2)}$ — {'доказуема' if r else 'недоказуема'} по критерию MT1–MT2.")
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21}\n\nСтудент исследовал доказуемость в $S_2^1$ четырёх формул в ДНФ:\n\n"
            + "\n".join(body) + "\n\nРовно два вывода неверны. Найдите их, объясните, какое условие MT1–MT2 нарушено, и дайте "
            "верный ответ.")
    return card(level, "E", step, "text", src, "S21, ДНФ, критерий, диагностика", cond, "; ".join(ans),
                "\n".join(sol) + "\n\nОстальные выводы верны.", system="S_2^1")


def flat(a, c):
    return mform(K.members(a) + [m for m in K.members(c) if m not in K.members(a)])


def c21_r3(src, level=6, step="open"):
    for _ in range(5000):
        a, b = dnf_pair(True, ("x", "y"), 18)
        c, d = dnf_pair(True, ("y", "z"), 18)
        ac, bd = flat(a, c), flat(b, d)
        if len(K.members(ac)) == len(K.members(a)) + len(K.members(c)) and len(K.members(bd)) == len(K.members(b)) + len(K.members(d)):
            ms = []
            for m in K.members(bd):
                sm = frozenset(rnd.sample(sorted(m, key=repr), rnd.randint(1, len(m))))
                if sm not in ms:
                    ms.append(sm)
            if rnd.random() < 0.5:
                ms.append(mem(["x", "z", "u"], 1))
            rnd.shuffle(ms)
            e = mform(ms)
            if K.s21(bd, e) and K.s21(ac, bd) and size(ac) + size(e) <= 40 and e != bd:
                break
    else:
        raise RuntimeError("R3")
    assert K.s21(ac, e) and K.taut(ac, e)
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21}\n\nДаны формулы (1) ${ft(a, b, S_2)}$, (2) ${ft(c, d, S_2)}$, "
            f"(3) ${ft(bd, e, S_2)}$. Проверьте критерием, что они доказуемы в $S_2^1$, получите из (1) и (2) по R3 формулу (4), "
            "из (4) и (3) по R2 — формулу (5), и проверьте критерием MT1–MT2 и значениями, что (5) доказуема.")
    ans = f"(4) ${ft(ac, bd, S_2)}$; (5) ${ft(ac, e, S_2)}$ — доказуема в $S_2^1$."
    sol = (f"(1) {s21_text(a, b)}.\n(2) {s21_text(c, d)}.\n(3) {s21_text(bd, e)}.\n"
           f"(4) По R3 (с. 56): из $x \\vdash y$ и $z \\vdash v$ — $x \\vee z \\vdash y \\vee v$: ${ft(ac, bd, S_2)}$.\n"
           f"(5) По R2 из (4) и (3): ${ft(ac, e, S_2)}$. Проверка: {s21_text(ac, e)}; формула — тавтология (нет набора "
           "значений, при котором посылка — 1, а заключение — 0).")
    return card(level, "D", step, "proof", src, "S21, R2, R3, ДНФ", cond, ans, sol, system="S_2^1")


def c21_r2(src, level=5, step="iso"):
    for _ in range(5000):
        a, b = dnf_pair(True)
        cs = []
        for m in K.members(b):
            sm = frozenset(rnd.sample(sorted(m, key=repr), max(1, len(m) - 1)))
            if sm not in cs:
                cs.append(sm)
        cs.append(mem(["x", "y", "z", "u"], 1))
        rnd.shuffle(cs)
        c = mform(cs)
        if (K.s21(b, c) and c != b and len(set(cs)) == len(cs) and len(K.members(b)) >= 2
                and any(len(m) > 1 for m in K.members(b)) and size(a) + size(c) <= 30):
            break
    mp1, mp2 = K.s21_map(a, b), K.s21_map(b, c)
    tri = [(i, j, mp2[j - 1]) for i, j in enumerate(mp1, 1)]
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21}\n\nДаны доказуемые в $S_2^1$ формулы ${ft(a, b, S_2)}$ и ${ft(b, c, S_2)}$. "
            "Получите по R2 третью формулу и проверьте её критерием: для каждого члена $x^i$ её посылки укажите цепочку "
            "$x^i \\to y^j \\to z^k$ (члены заключений первой и второй формул) и объясните, почему $z^k$ подходит к $x^i$. "
            f"Затем проверьте, применимо ли к тем же формулам R1 системы $S^2$ с ограничением ({RESTR}).")
    cm = atoms(a) & atoms(b) & atoms(c)
    ans = f"${ft(a, c, S_2)}$; цепочки: " + "; ".join(f"$x^{i} \\to y^{j} \\to z^{k}$" for i, j, k in tri) + \
          f"; ограничение R1 выполнено ({ob(cm)})."
    xs, ys, zs = K.members(a), K.members(b), K.members(c)
    sol = (f"По R2 (с. 56): ${ft(a, c, S_2)}$.\n" + "\n".join(
        f"$x^{i}$ = ${mtex(xs[i - 1])}$, $y^{j}$ = ${mtex(ys[j - 1])}$, $z^{k}$ = ${mtex(zs[k - 1])}$: составляющие $z^{k}$ "
        f"входят в $y^{j}$, а те — в $x^{i}$." for i, j, k in tri) +
        f"\nКритерий выполнен (MT2, с. 56–57). У посылки первой формулы, её заключения и заключения второй формулы есть "
        f"{ob(cm)} — ограничение R1 (с. 49) здесь выполнено.")
    assert K.s21(a, c) and cm
    return card(level, "D", step, "short", src, "S21, R2, ДНФ, ограничение R1", cond, ans, sol, system="S_2^1")




POSS21 = [
    ("доказуема в $S_2^1$, хотя в заключение входит элементарное высказывание, отсутствующее в посылке",
     lambda a, b: K.s21(a, b) and atoms(b) - atoms(a)),
    ("недоказуема в $S_2^1$, хотя она тавтология и каждая конъюнктивная составляющая заключения входит в посылку",
     lambda a, b: not K.s21(a, b) and K.taut(a, b) and set().union(*K.members(b)) <= set().union(*K.members(a))),
    ("доказуема в $S_2^1$, причём в посылке есть член, не совпадающий ни с одним членом заключения, а в заключении — член, "
     "не совпадающий ни с одним членом посылки",
     lambda a, b: K.s21(a, b) and set(K.members(a)) - set(K.members(b)) and set(K.members(b)) - set(K.members(a))),
    ("вместе с обратной формулой $y \\vdash x$ доказуема в $S_2^1$, хотя ДНФ $x$ и $y$ состоят из разных наборов членов",
     lambda a, b: K.s21(a, b) and K.s21(b, a) and set(K.members(a)) != set(K.members(b))),
    ("доказуема в $S^s$ (сильная тавтология), но недоказуема в $S_2^1$",
     lambda a, b: K.strong(a, b) and not K.s21(a, b)),
    ("доказуема в $S_2^1$, заключение — тавтология, а посылка — не противоречие",
     lambda a, b: K.s21(a, b) and K.is_taut(b) and not K.is_contra(a)),
]
IMP21 = [
    ("доказуема в $S_2^1$, хотя посылка — $x\\sim x$, а $x$ в заключение не входит",
     "Посылка $x\\sim x$ — один член с составляющими $x$ и $\\sim x$. По MT1 (с. 56) найдётся член заключения, все "
     "составляющие которого входят в $x\\sim x$, то есть это $x$, $\\sim x$ или $x\\sim x$; в каждом случае $x$ входит в "
     "заключение. Противоречие."),
    ("доказуема в $S_2^1$, хотя в посылке и заключении нет ни одного общего элементарного высказывания",
     "По MT1 (с. 56) для члена $x^1$ посылки найдётся член $y^j$ заключения, все составляющие которого входят в $x^1$. В "
     "$y^j$ есть хотя бы одна составляющая (элементарное высказывание или его отрицание), и её элементарное высказывание "
     "входит и в посылку, и в заключение. Противоречие."),
    ("доказуема в $S_2^1$, хотя не является тавтологией",
     "По MT1 (с. 56) для каждого $x^i$ найдётся $y^j$, все составляющие которого входят в $x^i$. Если посылка равна 1, то "
     "равен 1 какой-то её член $x^i$, а с ним — все его составляющие, в том числе все составляющие $y^j$; значит, $y^j = 1$ "
     "и заключение равно 1. Формула — тавтология. Противоречие."),
]


def subm(m):
    return frozenset(rnd.sample(sorted(m, key=repr), rnd.randint(1, len(m))))


def build21(k):
    """Построение-кандидат для пункта k списка POSS21."""
    p_, q_ = rnd.sample(["x", "y", "z"], 2)
    xs = [mem(["x", "y", "z"], rnd.choice([1, 2])) for _ in range(rnd.choice([1, 2]))]
    xs = list(dict.fromkeys(xs))
    if k == 0:
        return mform(xs), mform(list(dict.fromkeys([subm(m) for m in xs] + [frozenset([L_("u", rnd.random() < 0.4)])])))
    if k in (1, 4):
        m = mem([t for t in "xyz" if t != p_], 2)
        if k == 4 and rnd.random() < 0.5:
            return (mform([frozenset([V(p_)]), frozenset([V(q_), N(V(q_))])]),
                    mform([frozenset([V(p_), V(q_)]), frozenset([V(p_), N(V(q_))])]))
        return mform([frozenset([V(p_), N(V(p_))]), m]), mform([subm(m)])
    if k == 5:
        return mform(xs), mform(list(dict.fromkeys([subm(m) for m in xs] + [frozenset([V(p_)]), frozenset([N(V(p_))])])))
    return dnf_pair(True, maxs=20)


def c21_build(src, level=7, step="open"):
    k_ = rnd.randrange(len(POSS21))
    pd, pred = POSS21[k_]
    for _ in range(20000):
        a, b = build21(k_)
        if a != b and pred(a, b) and size(a) + size(b) <= 26:
            break
    else:
        raise RuntimeError(pd)
    idesc, iproof = rnd.choice(IMP21)
    items = [("p", pd), ("i", idesc)]
    rnd.shuffle(items)
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21} {CRIT_S}\n\nДля каждого пункта постройте формулу $x \\vdash y$, посылка и "
            "заключение которой записаны в ДНФ, с указанными свойствами и проверьте их — или докажите, что такой формулы нет.\n\n"
            + "\n".join(f"{L[k]}) {d[0].upper() + d[1:]}." for k, (_, d) in enumerate(items)))
    ans, sol = [], []
    for k, (t, _) in enumerate(items):
        if t == "p":
            ans.append(f"{L[k]}) например, ${ft(a, b, S_2)}$")
            extra = (f" Обратная формула: {s21_text(b, a)}." if "обратной" in pd else "")
            ss = (f" В $S^s$: {'тавтология, новых элементарных высказываний в заключении нет — доказуема' if K.strong(a, b) else 'недоказуема'}."
                  if "S^s" in pd else "")
            tt = (" Формула — тавтология (нет набора значений, при котором посылка — 1, а заключение — 0)." if K.taut(a, b) else "")
            cc = (f" Заключение истинно при всех значениях; посылка равна 1 при "
                  f"{K.env_text(next(e for e in K.rows(a) if K.value(a, e)))}." if "противоречие" in pd else "")
            nw = (f" В заключение {newp(atoms(b) - atoms(a))}." if atoms(b) - atoms(a) else "")
            sol.append(f"{L[k]}) ${ft(a, b, S_2)}$: {s21_text(a, b)}.{extra}{tt}{ss}{cc}{nw}")
        else:
            ans.append(f"{L[k]}) такой формулы нет")
            sol.append(f"{L[k]}) Такой формулы нет. {iproof}")
    return card(level, "C", step, "build", src, "S21, ДНФ, построение", cond, "; ".join(ans), "\n\n".join(sol),
                system="S_2^1")


def mt3_text(a, b):
    xs, ys = K.members(a), K.members(b)
    mp = K.s21_map(a, b)
    bad = [i for i, j in enumerate(mp, 1) if j is None]
    i = bad[0]
    det = "; ".join(f"$y^{j}$ = ${mtex(yj)}$ — ${s1w.tex(sorted(yj - xs[i - 1], key=repr)[0])}$" for j, yj in enumerate(ys, 1))
    return bad, i, det


def c21_mt3(src, level=6, step="vary"):
    its = []
    while len(its) < 3:
        p_ = dnf_pair(False)
        mixed = any(K.s21_map(*p_)) or len(its) == 2
        if p_ not in its and len(K.members(p_[0])) >= 2 and mixed:
            its.append(p_)
    ans, sol = [], []
    for k, (a, b) in enumerate(its):
        bad, i, det = mt3_text(a, b)
        ans.append(f"{L[k]}) " + ", ".join(f"$x^{t}$" for t in bad) + f"; для $x^{i}$: {det}")
        sol.append(f"{L[k]}) " + "; ".join(
            f"$x^{t}$ = ${mtex(K.members(a)[t - 1])}$ — " + ("подходящего $y^j$ нет" if t in bad else
                                                             f"подходит $y^{K.s21_map(a, b)[t - 1]}$")
            for t in range(1, len(K.members(a)) + 1)) + f". Для $x^{i}$ в каждом $y^j$ есть составляющая, отсутствующая в "
            f"$x^{i}$: {det}. В доказательстве MT3 вместо таких составляющих по R*6 подставляется высказывание (в книге — $z$) "
            "с элементарными высказываниями, отсутствующими в формуле, после чего по A3 из каждого $y^j$ следует это "
            "высказывание (с. 57–58).")
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21}\n\nВ доказательстве MT3 (с. 57–58) для недоказуемой формулы в ДНФ берётся "
            "член $x^i$ посылки, для которого среди $y^1, \\ldots, y^m$ нет такого, все составляющие которого входят в $x^i$; "
            "тогда в каждое $y^j$ входит составляющая, отсутствующая в $x^i$. Для каждой формулы найдите все такие члены $x^i$ "
            "и для первого из них укажите в каждом $y^j$ составляющую, отсутствующую в $x^i$.\n\n"
            + "\n".join(f"{L[k]}) ${ft(a, b, S_2)}$" for k, (a, b) in enumerate(its)))
    return card(level, "M", step, "short", src, "S21, MT3, ДНФ", cond, "; ".join(ans), "\n".join(sol), system="S_2^1")


def c21_mt3_diag(src, level=6, step="vary"):
    its = []
    while len(its) < 4:
        p_ = dnf_pair(len(its) == 3)
        if p_ not in its and len(K.members(p_[0])) >= 2:
            its.append(p_)
    rnd.shuffle(its)
    wrong = rnd.sample(range(4), 2)
    body, ans, sol = [], [], []
    for k, (a, b) in enumerate(its):
        mp = K.s21_map(a, b)
        ok_i = [i for i, j in enumerate(mp, 1) if j is not None]
        bad_i = [i for i, j in enumerate(mp, 1) if j is None]
        if k in wrong:
            if ok_i:
                t = rnd.choice(ok_i)
                claim = f"взять $x^{t}$: ни один $y^j$ к нему не подходит"
                right = (f"к $x^{t}$ подходит $y^{mp[t - 1]}$; " +
                         (f"нужный член — {', '.join(f'$x^{q}$' for q in bad_i)}" if bad_i else "формула доказуема — "
                          "MT3 к ней не применяется"))
            else:
                claim = "формула доказуема, MT3 не применяется"
                right = f"формула недоказуема: ни один $y^j$ не подходит к $x^{bad_i[0]}$"
            ans.append(f"{k + 1}: {right}")
            sol.append(f"{k + 1}. Неверно: {s21_text(a, b)}.")
        else:
            claim = (f"взять $x^{rnd.choice(bad_i)}$: ни один $y^j$ к нему не подходит" if bad_i else
                     "формула доказуема, MT3 не применяется")
        body.append(f"{k + 1}. ${ft(a, b, S_2)}$ — {claim}.")
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21}\n\nДоказательство MT3 (с. 57–58) начинается с недоказуемой формулы и её члена "
            "$x^i$, к которому не подходит ни один член заключения. Студент выбрал такие члены для четырёх формул:\n\n"
            + "\n".join(body) + "\n\nРовно два выбора неверны. Найдите их, объясните со ссылкой на MT1–MT2 (с. 56–57) и "
            "исправьте.")
    return card(level, "E", step, "text", src, "S21, MT3, диагностика", cond, "; ".join(ans),
                "\n".join(sol) + "\n\nОстальные выборы верны.", system="S_2^1")


def subst_lit(f, sig):
    if K.lit(f):
        return sig.get(f, f)
    if f[0] == "neg":
        return N(subst_lit(f[1], sig))
    return (f[0], tuple(subst_lit(t, sig) for t in f[1]))


def c21_rstar6(src, level=5, step="iso"):
    for _ in range(5000):
        p_, q_ = rnd.sample(["x", "y"], 2)
        xs = [frozenset([V(p_), L_(q_, rnd.random() < 0.5)]), frozenset([N(V(p_))] + ([V(q_)] if rnd.random() < 0.5 else []))]
        ys = list(dict.fromkeys([subm(m) for m in xs] + ([frozenset([L_(q_, rnd.random() < 0.5)])] if rnd.random() < 0.5 else [])))
        rnd.shuffle(ys)
        a, b = mform(xs), mform(ys)
        if not K.s21(a, b) or a == b:
            continue
        lits = sorted(set().union(*K.members(a), *K.members(b)), key=repr)
        pos = [l for l in lits if l[0] == "v"]
        negs = [l for l in lits if l[0] == "neg"]
        if not (pos and negs and any(N(p_) in negs for p_ in pos)):
            continue
        pool = [C(z, u), W(z, N(u)), N(z), u, C(N(u), w), W(u, w)]
        vals = rnd.sample(pool, len(lits))
        sig = dict(zip(lits, vals))
        a2, b2 = subst_lit(a, sig), subst_lit(b, sig)
        if K.taut(a2, b2) and size(a2) + size(b2) <= 44:
            break
    else:
        raise RuntimeError("R*6")
    st = ", ".join(f"${s1w.tex(l)}$ := ${s1w.tex(v)}$" for l, v in sig.items())
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21} Производное правило R*6 (с. 57): если $x \\vdash y$, где $x$ и $y$ в ДНФ, то "
            "$x^* \\vdash y^*$, которая получается из $x \\vdash y$ подстановкой на место конъюнктивных составляющих любых "
            "высказываний, причём вместо элементарного высказывания и его отрицания могут быть подставлены разные "
            f"высказывания.\n\nПроверьте критерием, что ${ft(a, b, S_2)}$ доказуема в $S_2^1$, примените к ней R*6 с подстановкой "
            f"{st} и проверьте значениями, что полученная формула — тавтология.")
    ans = f"${ft(a2, b2, S_2)}$"
    sol = (f"1. {s21_text(a, b)[0].upper() + s21_text(a, b)[1:]}.\n2. Подставляем вместо каждой составляющей её высказывание: "
           f"${ft(a2, b2, S_2)}$ (теорема $S_2^1$ по R*6, с. 57).\n3. Значения: каждый член посылки после подстановки — "
           "конъюнкция высказываний, среди которых есть все высказывания некоторого члена заключения (подстановка сохраняет "
           "вхождение составляющих), поэтому если посылка равна 1, то равен 1 и этот член заключения; перебор наборов "
           "значений подтверждает: набора, при котором посылка — 1, а заключение — 0, нет.")
    return card(level, "D", step, "short", src, "S21, R*6, подстановка", cond, ans, sol, system="S_2^1")




def check21(lines):
    """Проверка вывода в S₂¹: основание 'MT2' (критерий для формул в ДНФ) или ('R1', i), ('R2', i, j), ('R3', i, j)."""
    errs = []
    for n, (a, b, wh) in enumerate(lines, 1):
        if wh == "MT2":
            ok = K.is_dnf(a) and K.is_dnf(b) and K.s21(a, b)
        elif wh[0] == "R1":
            a1, b1, _ = lines[wh[1] - 1]
            ok = a == N(b1) and b == N(a1)
        elif wh[0] == "R2":
            (a1, b1, _), (a2, b2, _) = lines[wh[1] - 1], lines[wh[2] - 1]
            ok = b1 == a2 and a == a1 and b == b2
        else:
            (a1, b1, _), (a2, b2, _) = lines[wh[1] - 1], lines[wh[2] - 1]
            ok = a == flat(a1, a2) and b == flat(b1, b2)
        if not ok:
            errs.append(n)
    return errs


def wt21(wh):
    return wh if isinstance(wh, str) else f"{wh[0]}: " + ", ".join(str(t) for t in wh[1:])


def small_thm(names):
    for _ in range(1000):
        xs = list(dict.fromkeys(mem(list(names), rnd.choice([1, 2])) for _ in range(2)))
        ys = list(dict.fromkeys([subm(m) for m in xs] + ([mem(list(names), 1)] if rnd.random() < 0.5 else [])))
        rnd.shuffle(ys)
        a, b = mform(xs), mform(ys)
        if a != b and K.s21(a, b):
            return a, b
    raise RuntimeError("small")


def c21_rules_diag(src, level=6, step="vary"):
    for _ in range(3000):
        a, b = small_thm(("x", "y"))
        c, d = small_thm(("y", "z"))
        ac, bd = flat(a, c), flat(b, d)
        if len(K.members(ac)) != len(K.members(a)) + len(K.members(c)) or len(K.members(bd)) != len(K.members(b)) + len(K.members(d)):
            continue
        ms = list(dict.fromkeys(subm(m) for m in K.members(bd)))
        e = mform(ms)
        if K.s21(bd, e) and e != bd and size(ac) + size(e) <= 40:
            break
    else:
        raise RuntimeError("R-diag")
    good = [(a, b, "MT2"), (c, d, "MT2"), (ac, bd, ("R3", 1, 2)), (N(b), N(a), ("R1", 1)), (bd, e, "MT2"),
            (ac, e, ("R2", 3, 5)), (N(e), N(ac), ("R1", 6))]
    leaf_ok = (flat(c, a), flat(d, b), ("R3", 2, 1))
    leaf_bad = rnd.choice([(C(a, c), C(b, d), ("R3", 1, 2)), (a, e, ("R2", 1, 5))])
    assert not check21(good + [leaf_ok])
    pick = rnd.choice([(4, 8), (7, 8)])
    bad = list(good) + [leaf_bad if 8 in pick else leaf_ok]
    for k in pick:
        if k in (4, 7):
            a1, b1, wh = bad[k - 1]
            bad[k - 1] = (N(good[k - 1][1][1]), N(good[k - 1][0][1]), wh)
    assert sorted(check21(bad)) == sorted(pick), (check21(bad), pick)
    body = "\n".join(f"{n}. ${ft(p_, q_, S_2)}$ [{wt21(wh)}]" for n, (p_, q_, wh) in enumerate(bad, 1))
    exp = []
    for k in sorted(pick):
        p_, q_, wh = bad[k - 1]
        if wh[0] == "R1":
            g = good[k - 1]
            exp.append(f"Шаг {k}: R1 $S_2^1$ (с. 56) из $x \\vdash y$ даёт $\\sim y \\vdash \\sim x$ — отрицание заключения "
                       f"становится посылкой. Из строки {wh[1]} получается ${ft(g[0], g[1], S_2)}$, а записано обращение.")
        elif wh[0] == "R3":
            exp.append(f"Шаг {k}: R3 (с. 56) из $x \\vdash y$ и $z \\vdash v$ даёт $x \\vee z \\vdash y \\vee v$ — "
                       f"дизъюнкции, а не конъюнкции. Верно: ${ft(ac, bd, S_2)}$ (как в строке 3).")
        else:
            exp.append(f"Шаг {k}: R2 (с. 56) требует, чтобы заключение первой формулы было посылкой второй, а заключение "
                       f"строки 1 — ${tx(b, S_2)}$, посылка строки 5 — ${tx(bd, S_2)}$. Так получить ${ft(a, e, S_2)}$ нельзя "
                       f"(сама формула {'доказуема по критерию, но другим путём' if K.s21(a, e) else 'и недоказуема: ' + s21_text(a, e)}).")
    cond = (f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21} Основание «MT2» означает: формула в ДНФ доказуема по критерию.\n\n"
            "В выводе в $S_2^1$ ровно два шага неверны. Найдите их, назовите нарушенное правило с номером и страницей и "
            f"исправьте.\n\n{body}")
    ans = "; ".join(f"шаг {k}: неверно применено {bad[k - 1][2][0]} (с. 56)" for k in sorted(pick))
    sol = ("\n".join(exp) + "\n\nСтроки с основанием MT2 проверяются критерием: " +
           "; ".join(f"строка {n}: {s21_text(p_, q_)}" for n, (p_, q_, wh) in enumerate(good, 1) if wh == "MT2") + ".")
    return card(level, "E", step, "text", src, "S21, R1, R2, R3, диагностика", cond, ans, sol, system="S_2^1")


def akk_lines(p_, q_):
    np_ = N(p_) if p_[0] == "v" else p_[1]
    X, M1, M2 = C(np_, p_), W(C(np_, p_), C(np_, q_) if K.lit(q_) else C(np_, *q_[1])), C(np_, W(p_, q_))
    return np_, X, M1, M2, q_


def c_akk(src, level=7, step="transfer"):
    p_ = rnd.choice([x, y, z])
    q_ = rnd.choice([u, N(u), C(u, w), C(N(u), w), N(w)])
    np_, X, M1, M2, Y = akk_lines(p_, q_)
    fs = [(X, M1), (M1, M2), (M2, Y), (X, Y)]
    for n, (a, b) in enumerate(fs):
        assert K.weak(a, b) == (n < 3)
    assert K.s21(X, M1) and not K.s21(X, Y)
    cond = (f"{CONV6} {RESTR}. {CRIT_W} {DNF_DEF} {CRIT21}\n\nНа с. 55 книга показывает неполноту системы Аккермана "
            "формулами такого вида (подставлено $x$ := " + f"${tx(p_, S_2)}$, $y$ := ${tx(q_, S_2)}$):\n\n"
            + "\n".join(f"({n + 1}) ${ft(a, b, S_2)}$" for n, (a, b) in enumerate(fs)) +
            "\n\nИсследуйте каждую формулу в $S^w$ (значениями), а формулы (1) и (4), записанные в ДНФ, — ещё и в $S_2^1$. "
            "Выясните, где по транзитивности (R1 с ограничением) получается следующая формула, а где — нет, и объясните, "
            "как $S^w$, система Аккермана и $S_2^1$ избегают «парадокса» (4).")
    ans = ("(1)–(3) доказуемы в $S^w$, (4) — нет; (1) доказуема и в $S_2^1$, (4) — нет; R1 даёт из (1), (2) формулу "
           f"${ft(X, M2, S_2)}$, но к ней и (3) R1 неприменимо.")
    sol = [f"({n + 1}) {reason_w(a, b, S_2)[1]}." for n, (a, b) in enumerate(fs)]
    sol.append(f"В $S_2^1$: (1) {s21_text(X, M1)}; (4) {s21_text(X, Y)}.")
    sol.append(f"R1 к (1) и (2): у ${tx(X, S_2)}$, ${tx(M1, S_2)}$, ${tx(M2, S_2)}$ есть "
               f"{ob(atoms(X) & atoms(M1) & atoms(M2))} — получаем ${ft(X, M2, S_2)}$. R1 к ней и (3): у ${tx(X, S_2)}$ и "
               f"${tx(Y, S_2)}$ общих элементарных высказываний нет — ограничение (с. 49) не выполнено.")
    sol.append("Итак, $S^w$ избегает (4) ограничением R1, сохраняя (3); в системе Аккермана, по книге (с. 55), недоказуема "
               "уже (3), и потому она неполна в смысле полноты $S^w$; в $S_2^1$ (4) отсекается критерием MT1: члену "
               f"${tx(X, S_2)}$ посылки не подходит ни один член заключения.")
    return card(level, "P", step, "short", src, "Sw, Аккерман, S21, ограничение R1", cond, ans, "\n".join(sol),
                system="S^w")


def c_akk_diag(src, level=7, step="vary"):
    p_ = rnd.choice([x, y, z])
    q_ = rnd.choice([u, N(u), C(u, w), N(w)])
    np_, X, M1, M2, Y = akk_lines(p_, q_)
    right = {"r1": f"(1) ${ft(X, M1, S_2)}$ доказуема в $S^w$: тавтология с {ob(K.common(X, M1), 'ins')}.",
             "r3": f"(3) ${ft(M2, Y, S_2)}$ доказуема в $S^w$: тавтология с {ob(K.common(M2, Y), 'ins')}.",
             "rR": f"Из (1) и (2) по R1 получается ${ft(X, M2, S_2)}$: у трёх высказываний есть "
                   f"{ob(atoms(X) & atoms(M1) & atoms(M2))}.",
             "r4": f"(4) ${ft(X, Y, S_2)}$ недоказуема в $S^w$: общих элементарных высказываний нет (MT1 § 2)."}
    wrongs = {"r3": (f"(3) ${ft(M2, Y, S_2)}$ недоказуема в $S^w$ — так же, как в системе Аккермана.",
                     "(3) доказуема в $S^w$: тавтология с общим элементарным высказыванием, MT4 § 3 (с. 52); недоказуема "
                     "она в системе Аккермана, и это по книге (с. 55) показывает неполноту той системы в смысле $S^w$"),
              "r4": (f"(4) доказуема в $S^w$: R1 применимо к ${ft(X, M2, S_2)}$ и (3), ведь у каждой из двух формул посылка "
                     "и заключение имеют общее элементарное высказывание.",
                     "ограничение R1 (с. 49) требует общего элементарного высказывания у всех трёх высказываний, а у "
                     f"${tx(X, S_2)}$ и ${tx(Y, S_2)}$ его нет; (4) недоказуема по MT1 § 2 (с. 49)"),
              "r1": ("(1) недоказуема в $S^w$: в заключение входят элементарные высказывания, которых нет в посылке.",
                     "это условие сильного следования $S^s$; в $S^w$ новые элементарные высказывания допустимы (A12, "
                     "с. 52–54), (1) — тавтология с общим элементарным высказыванием, доказуема по MT4 § 3 (с. 52)"),
              "ak": ("Система Аккермана полна в смысле полноты $S^w$: в ней, как и в $S^w$, (4) недоказуема.",
                     "по книге (с. 55) система Аккермана не полна в смысле полноты $S^w$: в ней недоказуема (3), "
                     "удовлетворяющая критерию $S^w$")}
    wk = rnd.sample(list(wrongs), 2)
    w2 = [wrongs[k] for k in wk]
    r2 = [right[k] for k in rnd.sample([k for k in right if k not in wk], 2)]
    claims = [(t, None) for t in r2] + list(w2)
    rnd.shuffle(claims)
    fs = [(X, M1), (M1, M2), (M2, Y), (X, Y)]
    cond = (f"{CONV6} {RESTR}. {CRIT_W}\n\nФормулы вида, которым книга (с. 55) показывает неполноту системы Аккермана "
            f"(подставлено $x$ := ${tx(p_, S_2)}$, $y$ := ${tx(q_, S_2)}$):\n\n"
            + "\n".join(f"({n + 1}) ${ft(a, b, S_2)}$" for n, (a, b) in enumerate(fs)) +
            "\n\nСтудент утверждает:\n\n" + "\n".join(f"{k + 1}. {t}" for k, (t, _) in enumerate(claims)) +
            "\n\nРовно два утверждения неверны. Найдите их, назовите нарушенное правило или метатеорему с номером и страницей "
            "и исправьте.")
    bad = [k + 1 for k, (_, w_) in enumerate(claims) if w_]
    ans = "; ".join(f"{k}: неверно — {claims[k - 1][1].split(';')[0]}" for k in bad)
    sol = "\n".join(f"{k}. Неверно: {claims[k - 1][1]}." for k in bad) + "\n\nОстальные утверждения верны: " + \
        "; ".join(reason_w(a, b, S_2)[1] for a, b in fs) + "."
    return card(level, "E", step, "text", src, "Sw, Аккерман, ограничение R1, диагностика", cond, ans, sol, system="S^w")


# ---------- вручную: задачи ступеней 8–9 (все формулы проверяются программой) ----------
def hand():
    H = {}
    # 03.04-029: A15 и A12 друг через друга
    la = [(x, N(N(x)), "A1"), (N(N(x)), N(C(N(x), N(y))), "A15"), (x, N(C(N(x), N(y))), ("R1", 1, 2))]
    lb = [(N(x), W(N(x), N(y)), "A12"), (W(N(x), N(y)), N(C(x, y)), "A10"), (N(x), N(C(x, y)), ("R1", 1, 2))]
    assert not K.check(la, S2) and not K.check(lb, S_2)
    H["03.04-029"] = card(
        8, "M", "transfer", "proof", "с. 20, 49, 52–54, гл. 1, § 3; гл. 3, § 1, 4", "S2, S2w, A15, A12, эквивалентность",
        f"{CONV[S2]} {SCH[S2]}\n\n{SCH[S_2]}\n\nКнига говорит, что $S_2$ получается из $S_1$ так же, как $S^2$ из $S^1$ (с. 52). "
        "Проверьте это прямо: а) выведите в $S^2$ формулу $x \\vdash \\sim(\\sim x\\sim y)$ — запись формулы "
        "$x \\vdash x \\vee y$ (вида, в котором A12 применяется на с. 54) по D2 § 3 гл. 1 ($x \\vee y$ есть сокращение для "
        "$\\sim(\\sim x\\sim y)$, с. 20); б) выведите в $S_2$ схему A15 $\\sim x \\vdash \\sim(xy)$; в) объясните, почему в "
        "обоих выводах не обойтись без дополнительной схемы и почему ограничение R1 не мешает, и как результат связан с "
        "эквивалентностью $S^2$ и $S_2$ (с. 53).",
        "а) $x \\vdash \\sim\\sim x$ [A1], $\\sim\\sim x \\vdash \\sim(\\sim x\\sim y)$ [A15], R1; б) $\\sim x \\vdash \\sim x \\vee \\sim y$ "
        "[A12], $\\sim x \\vee \\sim y \\vdash \\sim(xy)$ [A10], R1; общее $x$ в обоих применениях R1.",
        "а) Вывод в $S^2$:\n\n" + show(la, S2) + "\n\n(A1 $S^1$: $x \\vdash \\sim\\sim x$, с. 15; A15 с заменой $x$ := $\\sim x$, "
        "$y$ := $\\sim y$, с. 49.)\n\nб) Вывод в $S_2$:\n\n" + show(lb, S_2) + "\n\n(A12 в виде $x \\vdash x \\vee y$ с заменой "
        "$x$ := $\\sim x$, $y$ := $\\sim y$, с. 54; A10 $S_1$, с. 36.)\n\n"
        "в) В обеих формулах в заключение входит $y$, которого нет в посылке. Без A15 (соответственно A12) такие формулы не "
        "выводятся: A15 — единственная схема $S^2$, допускающая в заключении элементарные высказывания, отсутствующие в "
        "посылке (с. 49), A12 — единственная такая схема $S_2$ (с. 53). Ограничение R1 соблюдено: в трёх высказываниях "
        "каждого применения R1 есть $x$. Итак, каждая дополнительная схема одной системы выводится в другой из её "
        "дополнительной схемы и схем $S^1$ (соответственно $S_1$) — в этом и состоит «так же». Это согласуется с "
        "эквивалентностью $S^2$ и $S_2$, которую книга выводит из полноты обеих систем (с. 53): перевод одной "
        "дополнительной схемы в язык другой системы оказывается её теоремой.")
    # 03.04-030: непарадоксальность S₂ по образцу MT1 § 2
    for nm in ["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10", "A11"]:
        a_, b_ = s1w.instance(nm, x, y, z)
        assert atoms(b_) <= atoms(a_), nm
    H["03.04-030"] = card(
        8, "M", "transfer", "proof", "с. 36–37, 49–50, 52–54, гл. 2, § 1; гл. 3, § 2, 4", "S2w, непарадоксальность, MT1",
        f"{SCH[S_2]} R3 — как в $S^1$ (с. 17): если $x \\vdash y$ и $y \\vdash x$, то $z \\vdash v$, где $v$ получается из $z$ "
        "заменой вхождений $x$ на $y$.\n\nПо образцу доказательства MT1 § 2 (с. 49–50: четыре случая — аксиома, R1, R2, "
        "R3) докажите прямо для $S_2$, не ссылаясь на эквивалентность с $S^2$: если $x \\vdash y$ доказуема в $S_2$, то в $x$ "
        "и $y$ входит по крайней мере одно одинаковое элементарное высказывание. Отдельно разберите, какие аксиомные схемы "
        "дают общее элементарное высказывание «с запасом» и где без ограничения R1 доказательство бы не прошло.",
        "Индукция по выводу. Аксиомы: у A1–A11 $S_1$ все элементарные высказывания заключения входят в посылку, у A12 "
        "$x \\vdash x \\vee y$ посылка входит в заключение; R1 — по ограничению; R2 и R3 — общее высказывание переходит от "
        "посылок правила к заключению.",
        "1. Случай аксиомы. Схемы $S_1$ (с. 36–37): A1 $\\sim\\sim x \\vdash x$, A2 $x \\vdash \\sim\\sim x$, A3 $xy \\vdash x$, "
        "A4 $xy \\vdash yx$, A5, A6 (скобки в конъюнкции), A7 $(x \\vee y)z \\vdash xz \\vee y$, A8 $xz \\vee yz \\vdash (x \\vee y)z$, "
        "A9, A10 (отрицание конъюнкции и дизъюнкция отрицаний), A11 $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$: в каждой "
        "все элементарные высказывания заключения входят в посылку (проверяется просмотром схем). В заключении есть хотя бы "
        "одно элементарное высказывание (D2 § 1 гл. 1, с. 15) — оно общее. A12 в виде $x \\vdash x \\vee y$ (с. 54): посылка "
        "$x$ входит в заключение, общие — все элементарные высказывания $x$. Это схема «без запаса»: в заключении есть и "
        "новые высказывания (из $y$), но общее всё равно есть.\n"
        "2. Случай R1: $x \\vdash y$ получена из $x \\vdash z$ и $z \\vdash y$. По ограничению (с. 49, 52) в $x$, $z$, $y$ есть "
        "одно и то же элементарное высказывание — оно общее для $x$ и $y$. Без ограничения предположение индукции дало бы "
        "лишь общее высказывание у $x$ и $z$ и, может быть, другое — у $z$ и $y$: так «выводился» бы парадокс "
        "$x\\sim x \\vdash y$ (см. задачи этого параграфа).\n"
        "3. Случай R2: $x \\vdash vz$ из $x \\vdash v$ и $x \\vdash z$. По предположению у $x$ и $v$ есть общее элементарное "
        "высказывание; оно входит в $vz$.\n"
        "4. Случай R3: $y$ получено из $x$ заменой вхождения $z$ на $v$, причём $z \\vdash v$ и $v \\vdash z$ доказуемы. По "
        "предположению у $z$ и $v$ есть общее элементарное высказывание $a$; $a$ входит в $x$ (через $z$) и в $y$ (через $v$).\n"
        "По индукции свойство есть у всех теорем $S_2$ — это MT1 § 2, перенесённая на $S_2$ (ср. с. 49–50).")
    # 03.05-016: транзитивность в S^w
    P1, Q1, R1_ = C(x, z), C(x, W(y, N(y))), W(W(y, N(y)), z)
    P2, Q2, R2_ = C(x, N(x)), C(x, W(N(x), y)), y
    assert K.weak(P1, Q1) and K.weak(Q1, R1_) and not (atoms(P1) & atoms(Q1) & atoms(R1_)) and K.weak(P1, R1_)
    assert K.weak(P2, Q2) and K.weak(Q2, R2_) and not K.weak(P2, R2_) and K.taut(P2, R2_)
    H["03.05-016"] = card(
        9, "M", "transfer", "proof", "с. 49–53, гл. 3, § 1–5", "Sw, ограничение R1, транзитивность",
        f"{CONV[S_2]} {RESTR}. {CRIT_W}\n\nДокажите: если $p \\vdash q$ и $q \\vdash r$ доказуемы в $S^w$, то $p \\vdash r$ "
        "доказуема в $S^w$ тогда и только тогда, когда в $p$ и $r$ есть общее элементарное высказывание, — даже если R1 к "
        "тройке $p$, $q$, $r$ неприменимо. Постройте пример такой тройки, где R1 неприменимо из-за ограничения, а $p \\vdash r$ "
        "всё же доказуема, и пример, где $p \\vdash r$ недоказуема. Объясните, почему ограничение R1 не сужает множества "
        "теорем, которое задаёт критерий.",
        f"Тавтологичность переходит по цепочке, остаётся условие на общее высказывание. Примеры: $p$ = ${tx(P1, S_2)}$, "
        f"$q$ = ${tx(Q1, S_2)}$, $r$ = ${tx(R1_, S_2)}$ (R1 неприменимо, $p \\vdash r$ доказуема); $p$ = ${tx(P2, S_2)}$, "
        f"$q$ = ${tx(Q2, S_2)}$, $r$ = ${tx(R2_, S_2)}$ ($p \\vdash r$ недоказуема).",
        "1. $p \\vdash q$ и $q \\vdash r$ — тавтологии (теоремы $S^w$ — тавтологии: непротиворечивость, § 1, с. 49). Если бы "
        "при некоторых значениях $p = 1$ и $r = 0$, то $q = 1$ (из первой) и $r = 1$ (из второй) — противоречие. Значит, "
        "$p \\vdash r$ — тавтология.\n"
        "2. Если в $p$ и $r$ есть общее элементарное высказывание, то по MT4 § 3 (с. 52) $p \\vdash r$ доказуема — каким-то "
        "выводом, не обязательно применением R1 к данной тройке. Если общего нет, то по MT1 § 2 (с. 49) она недоказуема.\n"
        f"3. Пример 1: ${ft(P1, Q1, S_2)}$ — тавтология с общим $x$; ${ft(Q1, R1_, S_2)}$ — тавтология (заключение истинно при "
        f"всех значениях) с общим $y$. В $p$, $q$, $r$ общего нет ($x$, $z$; $x$, $y$; $y$, $z$) — R1 неприменимо. Но "
        f"${ft(P1, R1_, S_2)}$ — тавтология с общим $z$, доказуема по MT4.\n"
        f"4. Пример 2: ${ft(P2, Q2, S_2)}$ — тавтология (посылка ложна всегда) с общим $x$; ${ft(Q2, R2_, S_2)}$ — тавтология "
        f"(если $x = 1$ и $\\sim x \\vee y = 1$, то $y = 1$) с общим $y$. ${ft(P2, R2_, S_2)}$ — тавтология без общих "
        "элементарных высказываний, недоказуема.\n"
        "5. Итак, ограничение R1 отсекает только переходы к формулам без общего элементарного высказывания посылки и "
        "заключения; все тавтологии с общим высказыванием остаются теоремами (MT4) — ограничение не сужает множества, "
        "заданного критерием, а лишь не даёт выйти за его пределы.")
    # 03.05-030: контрапозиция
    assert K.strong(C(x, y), x) and not K.strong(N(x), N(C(x, y))) and K.weak(N(x), N(C(x, y)))
    assert K.is_a15(N(x), N(C(x, y)))
    H["03.05-030"] = card(
        9, "M", "transfer", "proof", "с. 32, 49, 52, 56, гл. 1, § 7; гл. 3, § 1–3, 6", "Sw, Ss, контрапозиция",
        f"{CONV[S_2]} {CRIT_W} {CRIT_S}\n\nВ $S_2^1$ контрапозиция — основное правило R1: если $x \\vdash y$, то "
        "$\\sim y \\vdash \\sim x$ (с. 56). Докажите, что множество теорем $S^w$ замкнуто относительно этого правила, а "
        "множество теорем $S^s$ — нет: постройте теорему $S^s$, контрапозиция которой в $S^s$ недоказуема, и найдите условие "
        "на элементарные высказывания, при котором контрапозиция теоремы $S^s$ остаётся теоремой $S^s$. Сравните полученное "
        "с MT8 § 7 гл. 1 (с. 32).",
        "$S^w$: контрапозиция тавтологии — тавтология, множества элементарных высказываний частей те же. $S^s$: $xy \\vdash x$ "
        "(A3) — теорема, а $\\sim x \\vdash \\sim(xy)$ — нет (это A15). Условие: множества элементарных высказываний посылки и "
        "заключения совпадают.",
        "1. Пусть $x \\vdash y$ доказуема в $S^w$: тавтология с общим элементарным высказыванием. Если бы при некоторых "
        "значениях $\\sim y = 1$ и $\\sim x = 0$, то $y = 0$ и $x = 1$, и $x \\vdash y$ не была бы тавтологией. Значит, "
        "$\\sim y \\vdash \\sim x$ — тавтология. Элементарные высказывания $\\sim y$ — те же, что у $y$, у $\\sim x$ — те же, что "
        "у $x$: общее высказывание сохраняется. По MT4 § 3 (с. 52) $\\sim y \\vdash \\sim x$ доказуема в $S^w$.\n"
        "2. $S^s$: $xy \\vdash x$ — пример A3, теорема $S^1$. Её контрапозиция $\\sim x \\vdash \\sim(xy)$ — тавтология, но в "
        "заключение входит $y$, которого нет в посылке: в $S^s$ недоказуема (гл. 1, § 4, с. 21). Это в точности схема A15, "
        "которую $S^2$ добавляет к $S^1$ (с. 49).\n"
        "3. Пусть $x \\vdash y$ — теорема $S^s$: тавтология, элементарные высказывания $y$ входят в $x$. Контрапозиция — "
        "тавтология (п. 1); она теорема $S^s$ тогда и только тогда, когда элементарные высказывания $\\sim x$ (то есть $x$) "
        "входят в $\\sim y$ (то есть в $y$). Вместе с условием теоремы это значит: множества элементарных высказываний $x$ и "
        "$y$ совпадают.\n"
        "4. Это согласуется с MT8 § 7 гл. 1 (с. 32): если $x \\vdash y$ доказуема в $S^1$ и в $x$ и $y$ входят одинаковые "
        "элементарные высказывания, то $\\sim y \\vdash \\sim x$ доказуема в $S^1$. Для $S^w$ такого условия не нужно — "
        "контрапозиция в ней допустима всегда.")
    # 03.06-018: пример Аккермана в общем виде
    for X_, Y_ in [(x, y), (C(x, N(z)), W(u, y)), (W(x, z), C(N(u), y))]:
        nX = N(X_)
        ch = [(C(nX, X_), W(C(nX, X_), C(nX, Y_))), (W(C(nX, X_), C(nX, Y_)), C(nX, W(X_, Y_))), (C(nX, W(X_, Y_)), Y_)]
        assert all(K.weak(a_, b_) for a_, b_ in ch) and not K.weak(C(nX, X_), Y_) and K.taut(C(nX, X_), Y_)
    T1a, T1b, T1c = x, C(x, W(y, N(y))), W(y, N(y))
    assert K.weak(T1a, T1b) and K.weak(T1b, T1c) and not K.weak(T1a, T1c) and K.taut(T1a, T1c)
    H["03.06-018"] = card(
        8, "P", "transfer", "proof", "с. 49–52, 55, гл. 3, § 1–3, 6", "Sw, Аккерман, непарадоксальность",
        f"{CONV[S_2]} {RESTR}. {CRIT_W}\n\nНа с. 55 неполнота системы Аккермана показана формулами (стрелка там — знак "
        "сильного следования; здесь — $\\vdash$): $\\sim xx \\vdash \\sim xx \\vee \\sim xy$, "
        "$\\sim xx \\vee \\sim xy \\vdash \\sim x(x \\vee y)$, $\\sim x(x \\vee y) \\vdash y$; по транзитивности из них получилась бы "
        "парадоксальная $\\sim xx \\vdash y$. По образцу этого рассуждения: а) докажите, что для любых высказываний $a$ и $b$ "
        "без общих элементарных высказываний первые три формулы с $a$ вместо $x$ и $b$ вместо $y$ доказуемы в $S^w$, а "
        "$\\sim aa \\vdash b$ — нет; б) укажите, какое применение R1 здесь запрещено и почему разрешено предыдущее; в) постройте "
        "аналогичную цепочку из двух доказуемых в $S^w$ формул, ведущую к «парадоксу» другого вида — с тавтологией в "
        "заключении.",
        "а) Все три — тавтологии с общими элементарными высказываниями (высказывания $a$; $a$ и $b$; $b$); $\\sim aa \\vdash b$ — "
        "тавтология без общих. б) Запрещено R1 к $\\sim aa$, $\\sim a(a \\vee b)$, $b$. в) Например, $x \\vdash x(y \\vee \\sim y)$ и "
        "$x(y \\vee \\sim y) \\vdash y \\vee \\sim y$, а $x \\vdash y \\vee \\sim y$ недоказуема.",
        "а) Пусть $A$ — элементарные высказывания $a$, $B$ — $b$, $A$ и $B$ не пересекаются.\n"
        "(1) $\\sim aa \\vdash \\sim aa \\vee \\sim ab$: если посылка — 1, то 1 и первый член заключения; тавтология, общие — "
        "высказывания $A$.\n"
        "(2) $\\sim aa \\vee \\sim ab \\vdash \\sim a(a \\vee b)$: если $\\sim aa = 1$ или $\\sim ab = 1$, то $\\sim a = 1$ и $a = 1$ или "
        "$b = 1$, то есть заключение — 1; общие — $A$ и $B$.\n"
        "(3) $\\sim a(a \\vee b) \\vdash b$: если $\\sim a = 1$ и $a \\vee b = 1$, то $a = 0$ и $b = 1$; общие — $B$.\n"
        "По MT4 § 3 (с. 52) все три доказуемы. $\\sim aa \\vdash b$ — тавтология (посылка ложна всегда), но общих "
        "элементарных высказываний нет — по MT1 § 2 (с. 49) недоказуема. (Программа проверила это, например, для $a$ = $x$, "
        "$b$ = $y$; $a$ = $x\\sim z$, $b$ = $u \\vee y$; $a$ = $x \\vee z$, $b$ = $\\sim uy$.)\n"
        "б) R1 к (1) и (2) разрешено: в $\\sim aa$, $\\sim aa \\vee \\sim ab$, $\\sim a(a \\vee b)$ есть высказывания $A$; получаем "
        "$\\sim aa \\vdash \\sim a(a \\vee b)$. R1 к ней и (3) запрещено: в $\\sim aa$ — только $A$, в $b$ — только $B$, общего "
        "у трёх высказываний нет (с. 49). В системе Аккермана, по книге (с. 55), парадокс исключён иначе — недоказуемостью "
        "(3), и потому выпадает целый класс формул, удовлетворяющих теореме непарадоксальности $S^w$.\n"
        f"в) ${ft(T1a, T1b, S_2)}$ — тавтология с общим $x$; ${ft(T1b, T1c, S_2)}$ — тавтология (заключение истинно всегда) с "
        f"общим $y$; R1 к ним неприменимо (у $x$ и $y \\vee \\sim y$ общего нет), и ${ft(T1a, T1c, S_2)}$ недоказуема по MT1 — "
        "это «парадокс» вида $x \\vdash y \\vee \\sim y$, названный на с. 50.")
    # 03.06-048: S₂¹ и S^w
    for a_, b_ in [(x, W(C(x, y), C(x, N(y)))), (N(z), W(C(N(z), u), C(N(z), N(u))))]:
        assert K.weak(a_, b_) and not K.s21(a_, b_) and not K.is_contra(a_) and not K.is_taut(b_)
    for _ in range(300):
        a_, b_ = dnf_pair(True)
        assert K.weak(a_, b_)
    H["03.06-048"] = card(
        9, "M", "transfer", "proof", "с. 49–52, 55–57, гл. 3, § 2–3, 6", "S21, Sw, полнота, непарадоксальность",
        f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21} {CRIT_W}\n\nДокажите, что каждая формула в ДНФ, доказуемая в $S_2^1$, "
        "доказуема в $S^w$, — в частности, в теоремах $S_2^1$ такого вида у посылки и заключения всегда есть общее "
        "элементарное высказывание. Затем докажите, что для любых двух различных элементарных высказываний $a$ и $b$ формула "
        "$a \\vdash ab \\vee a\\sim b$ доказуема в $S^w$, но не в $S_2^1$, хотя её посылка — не противоречие, а заключение — не "
        "тавтология. Объясните, почему этот пример сильнее примеров с членом-противоречием вроде $x\\sim x$.",
        "Если для каждого $x^i$ есть $y^j$ со всеми составляющими в $x^i$, то формула — тавтология и составляющие $y^j$ дают "
        "общее элементарное высказывание; по MT4 § 3 она в $S^w$. $a \\vdash ab \\vee a\\sim b$: тавтология с общим $a$, но к "
        "члену $a$ не подходит ни $ab$, ни $a\\sim b$.",
        "1. Пусть $x \\vdash y$ в ДНФ доказуема в $S_2^1$. По MT1 (с. 56) для каждого $x^i$ есть $y^j$, все составляющие "
        "которого входят в $x^i$. Если посылка равна 1, то равен 1 некоторый $x^i$, а значит, все его составляющие, в том "
        "числе все составляющие $y^j$; тогда $y^j = 1$ и заключение равно 1. Формула — тавтология.\n"
        "2. Возьмём $x^1$ и подходящий ему $y^j$. В $y^j$ есть хотя бы одна составляющая — элементарное высказывание или его "
        "отрицание; её элементарное высказывание входит и в $x^1$, и в $y$. Общее элементарное высказывание есть.\n"
        "3. По MT4 § 3 (с. 52) формула доказуема в $S^w$. (Программа подтвердила это на 300 случайных теоремах $S_2^1$ в "
        "ДНФ.)\n"
        "4. $a \\vdash ab \\vee a\\sim b$: если $a = 1$, то при $b = 1$ истинен $ab$, при $b = 0$ — $a\\sim b$; тавтология, общее "
        "$a$, — доказуема в $S^w$. Посылка — один член $a$; члены заключения $ab$ и $a\\sim b$ содержат составляющие $b$ и "
        "$\\sim b$, которых в $a$ нет. По MT1 (с. 56) формула недоказуема в $S_2^1$. Посылка равна 1 при $a = 1$ — не "
        "противоречие; заключение равно 0 при $a = 0$ — не тавтология.\n"
        "5. В примерах вроде $x(\\sim x \\vee y) \\vdash y$ или цепочки Аккермана (с. 55) недоказуемость в $S_2^1$ вызвана "
        "членом-противоречием $x\\sim x$, то есть «парадоксальной» частью. Здесь противоречий нет вовсе: $S_2^1$ не "
        "доказывает даже «разбор случаев» $a \\vdash ab \\vee a\\sim b$, и её неполнота в смысле $S^w$ не сводится к отбрасыванию "
        "парадоксов.")
    # 03.06-049: R2 и R3 S₂¹ без ограничения
    ak1, ak2 = (C(N(x), x), W(C(N(x), x), C(N(x), y))), (W(C(N(x), x), C(N(x), y)), y)
    assert K.s21(*ak1) and not K.s21(*ak2) and K.weak(*ak2)
    for _ in range(300):
        a_, b_ = dnf_pair(True)
        cs = list(dict.fromkeys(subm(m) for m in K.members(b_)))
        c_ = mform(cs)
        assert K.s21(b_, c_) and K.s21(a_, c_) and atoms(a_) & atoms(b_) & atoms(c_)
    H["03.06-049"] = card(
        9, "M", "transfer", "proof", "с. 49, 55–57, гл. 3, § 1, 6", "S21, R2, R3, ограничение R1",
        f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21} {RESTR}.\n\nПравило R2 системы $S_2^1$ (транзитивность) не имеет ограничения, "
        "подобного ограничению R1 в $S^2$. Докажите, что для формул в ДНФ это не ведёт к парадоксам: если $x \\vdash y$ и "
        "$y \\vdash z$ удовлетворяют критерию MT1–MT2, то ему удовлетворяет и $x \\vdash z$, причём в $x$, $y$ и $z$ всегда есть "
        "общее элементарное высказывание, — ограничение Смирнова выполняется само собой. Докажите то же для R3. Затем покажите "
        "на формулах $\\sim xx \\vdash \\sim xx \\vee \\sim xy$ и $\\sim xx \\vee \\sim xy \\vdash y$, где обрывается в $S_2^1$ "
        "цепочка, подобная цепочке Аккермана (с. 55).",
        "Подходящие члены соединяются в цепочку $x^i \\to y^j \\to z^k$: составляющие $z^k$ входят в $y^j$, а те — в $x^i$; "
        "элементарное высказывание любой составляющей $z^k$ общее для трёх. Для R3 члены $x \\vee z$ — члены $x$ или $z$. "
        "Первая формула удовлетворяет критерию, вторая — нет (члену $\\sim xx$ не подходит $y$).",
        "1. R2. Пусть для $x \\vdash y$ и $y \\vdash z$ (в ДНФ) выполнен критерий MT1–MT2 (с. 56–57). Возьмём член $x^i$; ему "
        "подходит $y^j$ (все составляющие $y^j$ входят в $x^i$), а $y^j$ — член $z^k$ (все составляющие $z^k$ входят в $y^j$). "
        "Тогда все составляющие $z^k$ входят в $x^i$: $z^k$ подходит к $x^i$. Критерий для $x \\vdash z$ выполнен.\n"
        "2. В $z^k$ есть составляющая; её элементарное высказывание входит в $z$, в $y$ (через $y^j$) и в $x$ (через $x^i$). "
        "Это и есть общее элементарное высказывание трёх высказываний, которого требует ограничение R1 в $S^2$ (с. 49). "
        "(Программа подтвердила оба утверждения на 300 случайных цепочках.)\n"
        "3. R3: из $x \\vdash y$ и $z \\vdash v$ — $x \\vee z \\vdash y \\vee v$ (с. 56). Члены ДНФ $x \\vee z$ — члены $x$ и члены "
        "$z$; члену $x$ подходит член $y$, члену $z$ — член $v$, и оба — члены $y \\vee v$. Критерий выполнен.\n"
        "4. $\\sim xx \\vdash \\sim xx \\vee \\sim xy$: единственному члену посылки $\\sim xx$ подходит член $\\sim xx$ заключения — "
        "доказуема. $\\sim xx \\vee \\sim xy \\vdash y$: члену $\\sim xx$ не подходит $y$ ($y$ в него не входит) — по MT1 "
        "недоказуема, хотя это тавтология с общим $y$, то есть теорема $S^w$. В $S_2^1$ цепочка обрывается уже на втором "
        "шаге: критерий, замкнутый относительно R2, сам не пропускает формул, ведущих к парадоксу, и ограничение на "
        "транзитивность не нужно.")
    # 03.06-050: R*6 нельзя принять в S^w
    th = (x, W(C(x, y), C(x, N(y))))
    sig = {y: z, N(y): u}
    bad_ = (subst_lit(th[0], sig), subst_lit(th[1], sig))
    assert K.weak(*th) and not K.taut(*bad_) and K.counter(*bad_)
    for _ in range(200):
        a_, b_ = dnf_pair(True, ("x", "y"), 20)
        lits = sorted(set().union(*K.members(a_), *K.members(b_)), key=repr)
        sg = dict(zip(lits, rnd.choices([C(z, u), W(z, N(u)), N(z), u, W(u, w)], k=len(lits))))
        assert K.taut(subst_lit(a_, sg), subst_lit(b_, sg))
    H["03.06-050"] = card(
        9, "M", "transfer", "proof", "с. 49–52, 56–57, гл. 3, § 2–3, 6", "S21, Sw, R*6, непротиворечивость",
        f"{CONV6} {S21_SYS} {DNF_DEF} {CRIT21} {CRIT_W} Производное правило $S_2^1$ R*6 (с. 57): если $x \\vdash y$, где $x$ и "
        "$y$ в ДНФ, то $x^* \\vdash y^*$, которая получается подстановкой на место конъюнктивных составляющих любых "
        "высказываний, причём вместо элементарного высказывания и его отрицания могут быть подставлены разные "
        "высказывания.\n\nДокажите, что R*6 нельзя присоединить к $S^w$ как правило, применяемое к её теоремам в ДНФ: "
        "постройте теорему $S^w$ в ДНФ, из которой R*6 даёт формулу, не являющуюся тавтологией (а теоремы $S^w$ — тавтологии, "
        "с. 49). Затем докажите, что к теоремам $S_2^1$ в ДНФ R*6 всегда даёт тавтологии, и объясните, какое свойство критерия "
        "MT1–MT2 это обеспечивает.",
        f"Например, ${ft(*th, S_2)}$ (теорема $S^w$) при $y$ := $z$, $\\sim y$ := $u$ даёт ${ft(*bad_, S_2)}$ — не тавтология "
        f"({K.env_text(K.counter(*bad_))}). В $S_2^1$ подстановка сохраняет вхождение составляющих подходящего $y^j$ в $x^i$.",
        f"1. ${ft(*th, S_2)}$ — тавтология с общим $x$, теорема $S^w$ (MT4 § 3, с. 52); обе части в ДНФ (с. 56).\n"
        f"2. R*6 разрешает подставить вместо $y$ и $\\sim y$ разные высказывания: $y$ := $z$, $\\sim y$ := $u$. Получаем "
        f"${ft(*bad_, S_2)}$. При {K.env_text(K.counter(*bad_))} посылка — 1, заключение — 0: не тавтология. Присоединив R*6 к "
        "$S^w$, мы получили бы теорему, ложную при главной интерпретации, и потеряли бы непротиворечивость (с. 49).\n"
        "3. Пусть $x \\vdash y$ в ДНФ доказуема в $S_2^1$: для каждого $x^i$ есть $y^j$, все составляющие которого входят в $x^i$ "
        "(MT1, с. 56). Подстановка R*6 заменяет каждую составляющую одним и тем же высказыванием везде, где она встречается; "
        "поэтому после подстановки $x^{i*}$ — конъюнкция высказываний, среди которых есть все высказывания $y^{j*}$. Если "
        "посылка $x^*$ равна 1, то равен 1 некоторый $x^{i*}$, с ним — $y^{j*}$, и заключение равно 1: $x^* \\vdash y^*$ — "
        "тавтология. (Программа проверила это на 200 случайных теоремах $S_2^1$ и подстановках.)\n"
        "4. Решает то, что критерий $S_2^1$ — синтаксический: он требует вхождения составляющих, а не значений. В пункте 2 "
        "тавтологичность держалась на том, что $y$ и $\\sim y$ — отрицания друг друга (член $x$ не содержит ни $y$, ни "
        "$\\sim y$), а R*6 эту связь разрывает. Поэтому в $S_2^1$ R*6 производное (с. 57), а в $S^w$ — недопустимо.")
    for cid, c in H.items():
        assert not test_like(c["cond"]), cid
    return H


# ---------- распределение по номерам ----------
def plan():
    s1_ = [lambda: c_complete(S2, SRC[1]), lambda: c_complete(S2, SRC[1], step="iso"), lambda: c_near(S2, SRC[1]),
           lambda: c_diag(S2, SRC[1]), lambda: c_series(S2, SRC[1]), lambda: c_near(S2, SRC[1], step="iso"),
           lambda: c_diag(S2, SRC[1], step="iso"), lambda: c_deriv(S2, SRC[1]), lambda: c_deriv(S2, SRC[1], step="iso"),
           lambda: c_paradox(S2, SRC[1]), lambda: c_build(S2, SRC[1]), lambda: c_a15_transfer(SRC[1])]
    s2_ = [lambda: c_series(S2, SRC[2], kinds=["nocommon", "nocommon", "yes_new", "nontaut"]),
           lambda: c_series_diag(S2, SRC[2]), lambda: c_paradox(S2, SRC[2]),
           lambda: c_series(S2, SRC[2], kinds=["nocommon", "yes_new", "yes_new", "nocommon"], step="iso"),
           lambda: c_paradox(S2, SRC[2], step="iso"), lambda: c_chain(S2, SRC[2]), lambda: c_chain_diag(S2, SRC[2]),
           lambda: c_build(S2, SRC[2]), lambda: c_chain(S2, SRC[2], step="iso"),
           lambda: c_nat_chain(SRC[2], "lewis")]
    s3_ = [lambda: c_series(S2, SRC[3]), lambda: c_series_diag(S2, SRC[3]), lambda: c_series_diag(S2, SRC[3], step="iso"),
           lambda: c_deriv(S2, SRC[3]), lambda: c_chain_diag(S2, SRC[3]), lambda: c_build(S2, SRC[3]),
           lambda: c_ss_sw(S2, SRC[3])]
    s4_ = ([lambda: c_complete(S_2, SRC[4])] + [lambda: c_complete(S_2, SRC[4], step="iso")] * 3 +
           [lambda: c_near(S_2, SRC[4]), lambda: c_series(S_2, SRC[4]), lambda: c_diag(S_2, SRC[4])] +
           [lambda: c_diag(S_2, SRC[4], step="iso")] * 3 +
           [lambda: c_near(S_2, SRC[4], step="iso"), lambda: c_series(S_2, SRC[4], step="iso"),
            lambda: c_series_diag(S_2, SRC[4]), lambda: c_deriv(S_2, SRC[4])] +
           [lambda: c_deriv(S_2, SRC[4], step="iso")] * 3 +
           [lambda: c_paradox(S_2, SRC[4]), lambda: c_paradox(S_2, SRC[4], step="iso"), lambda: c_chain(S_2, SRC[4]),
            lambda: c_chain_diag(S_2, SRC[4]), lambda: c_build(S_2, SRC[4]), lambda: c_build(S_2, SRC[4], step="iso"),
            lambda: c_nat(SRC[4]), lambda: c_ss_sw(S_2, SRC[4]), lambda: c_translate(SRC[4])] +
           [lambda: c_translate(SRC[4], step="iso")] * 2)
    s5_ = ([lambda: c_complete(S_2, SRC[5]), lambda: c_complete(S_2, SRC[5], step="iso"), lambda: c_near(S_2, SRC[5]),
            lambda: c_series(S_2, SRC[5])] + [lambda: c_series(S_2, SRC[5], step="iso")] * 2 +
           [lambda: c_diag(S_2, SRC[5]), lambda: c_diag(S_2, SRC[5], step="iso"), lambda: c_near_diag(S_2, SRC[5]),
            lambda: c_series_diag(S_2, SRC[5]), lambda: c_series_diag(S_2, SRC[5], step="iso"),
            lambda: c_nat(SRC[5]), lambda: c_deriv(S_2, SRC[5]), lambda: c_chain(S_2, SRC[5]),
            lambda: c_deriv(S_2, SRC[5], step="iso"), lambda: c_chain(S_2, SRC[5], step="iso"),
            lambda: c_chain_diag(S_2, SRC[5]), lambda: c_chain_diag(S_2, SRC[5], step="iso"),
            lambda: c_paradox(S_2, SRC[5]), lambda: c_nat(SRC[5], step="iso"), lambda: c_nat(SRC[5], step="iso"),
            lambda: c_build(S_2, SRC[5])] + [lambda: c_build(S_2, SRC[5], step="iso")] * 2 +
           [lambda: c_ss_sw(S_2, SRC[5]), lambda: c_ss_sw(S_2, SRC[5], step="iso"), lambda: c_translate(SRC[5]),
            lambda: c_translate(SRC[5], step="iso")])
    S6 = SRC[6]
    s6_ = ([lambda: c21_r2(S6)] + [lambda: c21_r2(S6, step="iso")] * 2 + [lambda: c21_rstar6(S6)] +
           [lambda: c21_rstar6(S6, step="iso")] * 2 + [lambda: c21_series(S6)] + [lambda: c21_series(S6, step="iso")] * 4 +
           [lambda: c21_diag(S6)] + [lambda: c21_diag(S6, step="iso")] * 5 +
           [lambda: c21_mt3(S6)] + [lambda: c21_mt3(S6, step="iso")] * 3 +
           [lambda: c21_mt3_diag(S6), lambda: c21_mt3_diag(S6, step="iso"), lambda: c21_rules_diag(S6),
            lambda: c21_rules_diag(S6, step="iso"), lambda: c21_r3(S6)] + [lambda: c21_r3(S6, step="iso")] * 3 +
           [lambda: c21_build(S6)] + [lambda: c21_build(S6, step="iso")] * 3 +
           [lambda: c_akk_diag(S6)] + [lambda: c_akk_diag(S6, step="iso")] * 2 +
           [lambda: c21_vs_w(S6)] + [lambda: c21_vs_w(S6, step="iso")] * 4 +
           [lambda: c_akk(S6)] + [lambda: c_akk(S6, step="iso")] * 2 +
           [lambda: c_nat_chain(S6, "akk"), lambda: c_nat_chain(S6, "akk", step="iso")])
    ids = {1: ["03.01-%03d" % n for n in range(1, 13)], 2: ["03.02-%03d" % n for n in range(1, 11)],
           3: ["03.03-%03d" % n for n in range(1, 8)], 4: ["03.04-%03d" % n for n in range(1, 29)],
           5: ["03.05-%03d" % n for n in range(1, 31) if n not in (16, 30)],
           6: ["03.06-%03d" % n for n in range(1, 51) if n not in (18, 48, 49, 50)]}
    out = {}
    for sec, ks in zip(range(1, 7), [s1_, s2_, s3_, s4_, s5_, s6_]):
        assert len(ids[sec]) == len(ks), (sec, len(ids[sec]), len(ks))
        out.update(zip(ids[sec], ks))
    return out


def render(cid, c):
    sec = int(cid.split(".")[1].split("-")[0])
    sysl = f'system: "{c["system"]}"\n' if c.get("system") else ""
    return (f'---\nid: "{cid}"\nchapter: 3\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\n'
            f'step: {c["step"]}\ncondition: def\nform: {c["form"]}\nanswer: {c["answer"]}\nsource: "{c["source"]}"\n'
            f'{sysl}generated: true\ntags: [{c["tags"]}]\n---\n\n## Условие\n\n{c["cond"]}\n\n## Ответ\n\n{c["ans"]}\n\n'
            f'## Решение\n\n{c["sol"]}\n')


def main():
    cards = {cid: fn() for cid, fn in plan().items()}
    cards.update(hand())
    for cid, c in cards.items():
        assert not test_like(c["cond"]), (cid, c["cond"][:160])
    path = ROOT / "data" / "zadachi" / "03.md"
    parts = re.split(r"(\n=====\n)", path.read_text(encoding="utf-8"))
    done = set()
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(03\.\d\d-\d{3})"', chunk, re.M)
        if m and m.group(1) in cards:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            parts[i] = lead + render(m.group(1), cards[m.group(1)]).rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
            done.add(m.group(1))
    assert done == set(cards), sorted(set(cards) - done)
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {len(done)}")


if __name__ == "__main__":
    main()
