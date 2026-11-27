"""Общие средства генератора hard06.py (гл. 6): построение выводов в системах условных высказываний,
дополнение, диагностика, серии с обоснованием значениями."""
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts"))
import if6 as F  # noqa: E402
from if6 import C, IF, IFN, IFQ, IMP, N, V, W, ftex, tex  # noqa: E402

rnd = random.Random(1970_0600)
x, y, z, v, u = (V(c) for c in "xyzvu")
L = "абвгдежз"

CV = ("Буквы $x, y, z, v, u$ — высказывания; $\\rightarrow$ — оператор условности «если, то» (гл. 6, § 1, с. 82); "
      "$\\supset$ — материальная импликация.")
SYSNAME = {"s": "S^s_{if}", "w": "S^w_{if}", "5": "S^5_{if}", "5s": "S^{5*}_{if}", "n": "S^s + A^n1\\text{–}A^n6",
           "n7": "S^5 + A^n1\\text{–}A^n7"}
RULES = ("Правила общей теории дедукции (с. 17): R1 — если $x \\vdash y$ и $y \\vdash z$, то $x \\vdash z$; R2 — если "
         "$x \\vdash y$ и $x \\vdash z$, то $x \\vdash yz$; R3 — если $x \\vdash y$ и $y \\vdash x$, то $z \\vdash v$, где $v$ "
         "получается из $z$ заменой вхождений $x$ на $y$. Основание «$S^s$» — теорема общей теории дедукции: формула, "
         "которая становится сильной тавтологией, если условные высказывания считать элементарными (гл. 2, § 2, MT5; "
         "аксиомы заданы схемами, с. 97).")
SCH_S = ("Схемы $S^s_{if}$ (с. 90): A1 $(x \\rightarrow y)x \\vdash y$; A2 $(x \\rightarrow y) \\vdash (\\sim y \\rightarrow "
         "\\sim x)$; A3 $(x \\rightarrow y)(y \\rightarrow z) \\vdash (x \\rightarrow z)$; A4 $(x \\rightarrow yz) \\vdash "
         "(x \\rightarrow y)(x \\rightarrow z)$; A5 $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$; A6 "
         "$(x \\rightarrow (y \\rightarrow z)) \\vdash (xy \\rightarrow z)$; A7 $(x \\rightarrow y)(z \\rightarrow v) \\vdash "
         "(xz \\rightarrow yv)$; A8 $(x \\rightarrow y) \\vee (z \\rightarrow v) \\vdash (xz \\rightarrow y \\vee v)$.")
SCH_W = SCH_S.replace("Схемы $S^s_{if}$ (с. 90)", "Схемы $S^w_{if}$ (с. 90–91)")[:-1] + \
    "; A9 $(x \\rightarrow y) \\vdash (xz \\rightarrow y)$."
S5_RULES = ("$S^5_{if}$ — $S^s_{if}$ и $S^5$ (гл. 4, § 3, с. 67–69) с правилом R1 § 8: если $x \\vdash y$, то "
            "$\\vdash (x \\rightarrow y)$ (с. 91). Из $S^5$: $R^d1$ — если $x \\vdash y$ и $\\vdash x$, то $\\vdash y$; "
            "MT6 гл. 4 — если $\\vdash x$ и $\\vdash y$, то $\\vdash xy$; основание «$S^5$» — $\\vdash x$, где $x$ — "
            "тавтология, если условные высказывания считать элементарными (MT4 § 3 гл. 4, с. 69).")
SCH_5S = ("$S^{5*}_{if}$ — $S^5$ (гл. 4, § 3) с аксиомными схемами (с. 93) A1 $(x \\rightarrow y)x \\vdash y$; A2 "
          "$(x \\rightarrow y)\\sim y \\vdash \\sim x$; A3 $\\vdash ((xy \\rightarrow z) \\rightarrow (x \\rightarrow "
          "(y \\rightarrow z)))$ и правилом R1: если $x \\vdash y$, то $\\vdash (x \\rightarrow y)$. Из $S^5$: $R^d1$ — если "
          "$x \\vdash y$ и $\\vdash x$, то $\\vdash y$; MT6 гл. 4 — если $\\vdash x$ и $\\vdash y$, то $\\vdash xy$.")
SCH_N = ("Схемы § 5 (с. 89): $A^n1$ $(x \\rightarrow y) \\vdash \\sim(x \\urcorner\\!\\rightarrow y)\\sim(x? \\rightarrow y)$; "
         "$A^n2$ — обратная к $A^n1$; $A^n3$ $(x \\urcorner\\!\\rightarrow y) \\vdash \\sim(x \\rightarrow y)\\sim(x? "
         "\\rightarrow y)$; $A^n4$ — обратная к $A^n3$; $A^n5$ $(x? \\rightarrow y) \\vdash \\sim(x \\rightarrow y)\\sim(x "
         "\\urcorner\\!\\rightarrow y)$; $A^n6$ — обратная к $A^n5$.")


def sys_phrase(sysk):
    return "системе $S^s$ со схемами $A^n1$–$A^n6$" if sysk == "n" else f"${SYSNAME[sysk]}$"


def sys_text(sysk):
    return {"s": SCH_S + " " + RULES, "w": SCH_W + " " + RULES, "5": SCH_S + " " + S5_RULES + " " + RULES,
            "5s": SCH_5S + " " + RULES, "n": SCH_N + " " + RULES}[sysk]


def card(level, typ, step, ans_kind, src, tags, cond, ans, sol, form="sym", system=None, condition="def"):
    return dict(level=level, type=typ, step=step, form=form, answer=ans_kind, source=src, tags=tags, cond=cond,
                ans=ans, sol=sol, system=system, condition=condition)


# ---------------------------------------------------------------- построение выводов
def size(f):
    return F.size(f)


def contains(a, b):
    return a == b or any(g == a for g in F.subs(b))


def r3_options(q):
    """Равнозначные замены внутри условных высказываний: снятие ∼∼, законы де Моргана (через R3)."""
    out = []
    if q[0] not in F.COND and q[0] != "conj":
        return out
    for g in F.subs(q):
        if g[0] == "neg" and g[1][0] == "neg":
            out.append((g, g[1][1]))
        if g[0] == "neg" and g[1][0] == "wdis" and len(g[1][1]) == 2:
            out.append((g, C(N(g[1][1][0]), N(g[1][1][1]))))
        if g[0] == "neg" and g[1][0] == "conj" and len(g[1][1]) == 2:
            out.append((g, W(N(g[1][1][0]), N(g[1][1][1]))))
    res = []
    for a, b in out:
        q2 = replace_all(q, a, b)
        if q2 != q:
            res.append((a, b, q2))
    return res


def replace_all(f, a, b):
    if f == a:
        return b
    k = f[0]
    if k == "v":
        return f
    if k == "neg":
        return N(replace_all(f[1], a, b))
    if k in F.COND or k == "imp":
        return (k, replace_all(f[1], a, b), replace_all(f[2], a, b))
    return (k, tuple(replace_all(t, a, b) for t in f[1]))


def unary(q, sysk, letters):
    out = []
    if sysk in ("s", "w", "5") and q[0] == "if":
        X, Y = q[1], q[2]
        out.append(("A2", IF(N(Y), N(X))))
        if Y[0] == "conj" and len(Y[1]) == 2:
            out.append(("A4", C(IF(X, Y[1][0]), IF(X, Y[1][1]))))
        if X[0] == "conj" and len(X[1]) == 2:
            out.append(("A5", IF(X[1][0], IF(X[1][1], Y))))
        if Y[0] == "if":
            out.append(("A6", IF(C(X, Y[1]), Y[2])))
        if sysk == "w":
            Z = rnd.choice(letters)
            if not contains(Z, X):
                out.append(("A9", IF(C(X, Z), Y)))
    if sysk in ("s", "w", "5") and q[0] == "wdis" and len(q[1]) == 2 and all(t[0] == "if" for t in q[1]):
        (a, b), (c, d) = (q[1][0][1], q[1][0][2]), (q[1][1][1], q[1][1][2])
        out.append(("A8", IF(C(a, c), W(b, d))))
    return out


def binary(q1, q2, sysk):
    out = []
    if q1[0] == "if":
        X, Y = q1[1], q1[2]
        if sysk in ("s", "w", "5"):
            if q2 == X:
                out.append(("A1", Y))
            if q2[0] == "if" and q2[1] == Y:
                out.append(("A3", IF(X, q2[2])))
            if q2[0] == "if" and q2 != q1 and size(q1) + size(q2) < 26:
                out.append(("A7", IF(C(X, q2[1]), C(Y, q2[2]))))
        if sysk == "5s":
            if q2 == X:
                out.append(("B1", Y))
            if q2 == N(Y):
                out.append(("B2", N(X)))
    return out


WEIGHT = {"A1": 3, "A3": 4, "B1": 3, "B2": 3, "A4": 3, "A5": 2, "A6": 2, "A8": 3, "A2": 1.2, "A7": 1, "A9": 2,
          "nn": 6, "dm": 2}


def build(P, sysk, want, letters):
    lines = []
    facts = [(P, 0)]
    if P[0] == "conj":
        facts = []
        for t in P[1]:
            lines.append((P, t, "Ss"))
            facts.append((t, len(lines)))
    tries = 0
    while len(lines) < want and tries < 60:
        tries += 1
        known = [f for f, _ in facts]
        moves = []
        for (q1, i) in facts:
            for (q2, j) in facts:
                if q1 is q2 and i == j:
                    continue
                for n, res in binary(q1, q2, sysk):
                    if res in known or size(res) > 30:
                        continue
                    if n == "A7" and (F.atoms(q1[1]) & F.atoms(q2[1]) or F.atoms(q1[2]) & F.atoms(q2[2])
                                      or (F.atoms(q1[1]) | F.atoms(q2[1])) & (F.atoms(q1[2]) | F.atoms(q2[2]))):
                        continue
                    if dup(res):
                        continue
                    moves.append((WEIGHT[n], ("bin", n, q1, i, q2, j, res)))
            for a, b, q2 in r3_options(q1):
                if q2 not in known:
                    moves.append((WEIGHT["nn" if a[1][0] == "neg" else "dm"], ("r3", a, b, q1, i, q2)))
            for n, res in unary(q1, sysk, letters):
                if res not in known and size(res) <= 30 and not dup(res):
                    moves.append((WEIGHT[n], ("un", n, q1, i, res)))
        if not moves:
            break
        tot = sum(wt for wt, _ in moves)
        r = rnd.random() * tot
        for wt, mv in moves:
            r -= wt
            if r <= 0:
                break
        if mv[0] == "bin":
            _, n, q1, i, q2, j, res = mv
            prem = C(q1, q2)
            if prem == P:
                lines.append((P, res, n))
            else:
                if i == 0 or j == 0:
                    continue
                lines.append((P, prem, ("R2", i, j)))
                k = len(lines)
                lines.append((prem, res, n))
                lines.append((P, res, ("R1", k, k + 1)))
            facts.append((res, len(lines)))
        elif mv[0] == "r3":
            _, a, b, q, i, q2 = mv
            lines.append((a, b, "Ss"))
            lines.append((b, a, "Ss"))
            k = len(lines)
            lines.append((q, q2, ("R3", k - 1, k)))
            if i != 0:
                lines.append((P, q2, ("R1", i, len(lines))))
            facts.append((q2, len(lines)))
        else:
            _, n, q, i, res = mv
            lines.append((q, res, n))
            if i != 0:
                lines.append((P, res, ("R1", i, len(lines))))
            facts.append((res, len(lines)))
    return lines


def dup(f):
    return any(g[0] in ("conj", "wdis") and len(set(g[1])) < len(g[1]) for g in F.subs(f))


def clean(f):
    for g in F.subs(f):
        if g[0] == "neg" and g[1][0] != "v":
            return False
        if g[0] in ("conj", "wdis") and any(t[0] == g[0] for t in g[1]):
            return False
    return True


def has_nn(f):
    return any(g[0] == "neg" and g[1][0] == "neg" for g in F.subs(f))


def axioms_used(lines):
    return {wh for _, _, wh in lines if isinstance(wh, str) and wh not in ("Ss", "S5")}


SEEN = set()


def neg(t):
    return t[1] if t[0] == "neg" else N(t)


def premise(sysk, need=frozenset()):
    X, Y, Z, Vv, U = (N(t) if rnd.random() < 0.25 else t for t in rnd.sample([x, y, z, v, u], 5))
    if sysk == "5s":
        pool = [C(IF(X, Y), IF(Y, Z), X), C(IF(X, Y), IF(Y, Z), neg(Z)), C(IF(X, Y), IF(Z, Vv), X, Z),
                C(IF(X, IF(Y, Z)), X, Y), C(IF(C(X, Y), Z), X, Y), C(IF(X, Y), IF(Y, neg(Z)), Z),
                C(IF(X, W(Y, Z)), X, neg(Y)), C(IF(X, C(Y, Z)), X)]
        return rnd.choice(pool)
    T = {
        "A1": [C(IF(X, Y), IF(Y, Z), X), C(IF(X, IF(Y, Z)), X, Y), C(IF(C(X, Y), Z), neg(Z), X),
               C(IF(X, C(Y, Z)), IF(Y, Vv), X), C(W(IF(X, Y), IF(Z, Vv)), X, Z), C(IF(C(X, Y), Z), X)],
        "A2": [C(IF(X, Y), IF(Y, Z), neg(Z)), C(IF(C(X, Y), Z), neg(Z), X), C(IF(X, W(Y, Z)), neg(Y)),
               C(IF(X, C(Y, Z)), neg(Z))],
        "A3": [C(IF(X, C(Y, Z)), IF(Z, Vv)), C(IF(C(X, Y), Z), IF(Z, Vv)), C(IF(X, Y), IF(C(Y, Z), Vv)),
               C(IF(X, IF(Y, Z)), IF(Z, Vv)), C(IF(W(X, Y), Z), IF(Vv, X))],
        "A4": [IF(X, C(Y, Z)), C(IF(X, C(Y, Z)), IF(Z, Vv)), C(IF(X, C(Y, Z)), X), IF(X, C(Y, IF(Z, Vv))),
               IF(C(X, Y), C(Z, Vv)), IF(W(X, Y), C(Z, Vv))],
        "A5": [C(IF(C(X, Y), Z), X), C(IF(C(X, Y), Z), IF(Z, Vv)), IF(C(X, Y), C(Z, Vv))],
        "A6": [C(IF(X, IF(Y, Z)), IF(Z, Vv)), C(IF(X, IF(Y, Z)), IF(Vv, X))],
        "A7": [C(IF(X, Y), IF(Z, Vv)), C(IF(X, Y), IF(Z, Vv), IF(C(Y, Vv), U)), C(IF(X, Z), IF(Y, Vv), X)],
        "A8": [C(W(IF(X, Y), IF(Z, Vv)), IF(W(Y, Vv), U)), C(W(IF(X, Y), IF(Z, Vv)), X, Z)],
        "A9": [C(IF(X, Y), IF(Y, Z)), C(IF(X, C(Y, Z)), X), IF(X, Y), C(IF(X, Y), neg(Y))],
    }
    keys = sorted(need) or sorted(T)
    pool = []
    for k in keys:
        pool += T.get(k, [])
    return rnd.choice(pool or T["A3"])


def good_final(lines, P, sysk):
    a, b, _ = lines[-1]
    if a != P or b in (P[1] if P[0] == "conj" else (P,)) or not clean(b):
        return False
    if b[0] == "conj" and not all(t[0] == "if" for t in b[1]):
        return False
    if any(F.atoms(g[1]) & F.atoms(g[2]) for g in F.conds(b)):
        return False
    if b[0] == "conj" and len(b[1]) > 2:
        return False
    if sysk in ("s", "w", "5") and not F.has(b):
        return len(axioms_used(lines)) >= 3
    return F.has(b) or sysk == "5s"


NEEDS = {"s": [{"A4"}, {"A1"}, {"A8"}, {"A2", "A1"}, {"A7"}, {"A6", "A3"}, {"A4", "A3"}, {"A2", "A3"}, {"A5", "A1"}],
         "w": [{"A9", "A1"}, {"A9", "A4"}, {"A9", "A3"}, {"A9", "A2"}, {"A9", "A7"}, {"A9"}],
         "5s": [set()]}
NEED_I = {"s": 0, "w": 0, "5s": 0}


def derivation(sysk="s", lo=8, hi=12, minax=3, P=None, letters=None, need=None):
    if need is None:
        lst = NEEDS[sysk]
        need = lst[NEED_I[sysk] % len(lst)]
        NEED_I[sysk] += 1
    for it in range(6000):
        if it == 3000:
            need = set()
        PP = P or premise(sysk, need)
        lets = letters or [x, y, z, v, u, N(x)]
        lines = build(PP, sysk, hi + 6, lets)
        if not lines:
            continue
        # выбрать конечную строку с посылкой P
        cands = [k for k, (a, _, _) in enumerate(lines) if a == PP]
        rnd.shuffle(cands)
        for k in cands:
            ls = F.prune(lines[:k + 1])
            if lo <= len(ls) <= hi and len(axioms_used(ls)) >= minax and need <= axioms_used(ls) \
                    and good_final(ls, PP, sysk) \
                    and not F.check(ls, sysk):
                key = ftex(ls[-1][0], ls[-1][1])
                if key in SEEN or size(ls[-1][1]) > 32:
                    continue
                SEEN.add(key)
                return ls
    raise RuntimeError(f"нет вывода {sysk} {lo}-{hi}")


# ---------------------------------------------------------------- S⁵_if и S⁵*_if: выводы ⊢-формул
def mp(lines, i_imp, i_ant):
    """Модус поненс по доказательству MT3 § 8: (F → G)F ⊢ G [A1], ⊢ (F → G)F [MT6], ⊢ G [Rᵈ1]."""
    fg = lines[i_imp - 1][1]
    f_ = lines[i_ant - 1][1]
    assert fg[0] == "if" and fg[1] == f_
    name = "B1" if MODE5S[0] else "A1"
    lines.append((C(fg, f_), fg[2], name))
    k = len(lines)
    lines.append((None, C(fg, f_), ("MT6", i_imp, i_ant)))
    lines.append((None, fg[2], ("Rd1", k, k + 1)))
    return len(lines)


MODE5S = [False]


def s5_curry(lines, sysk):
    """После вывода P ⊢ Q с P = C(P1, P2): ⊢ (P → Q) [R1 § 8], далее ⊢ (P1 → (P2 → Q))."""
    P, Q, _ = lines[-1]
    n = len(lines)
    lines.append((None, IF(P, Q), ("Rif", n)))
    k = len(lines)
    if P[0] == "conj" and len(P[1]) == 2:
        P1, P2 = P[1]
        if sysk == "5":
            lines.append((IF(P, Q), IF(P1, IF(P2, Q)), "A5"))
            lines.append((None, IF(P1, IF(P2, Q)), ("Rd1", k + 1, k)))
        else:
            MODE5S[0] = True
            lines.append((None, IF(IF(P, Q), IF(P1, IF(P2, Q))), "B3"))
            mp(lines, k + 1, k)
            MODE5S[0] = False
    return lines


def derive_goal(P, Q, sysk, tries=400):
    for _ in range(tries):
        lines = build(P, sysk, 14, [x, y, z, v, u])
        for k, (a, b, _) in enumerate(lines):
            if a == P and b == Q:
                ls = F.prune(lines[:k + 1])
                if not F.check(ls, sysk):
                    return ls
    return None


def goal_5s():
    X, Y, Z, Vv = (N(t) if rnd.random() < 0.25 else t for t in rnd.sample([x, y, z, v, u], 4))
    return rnd.choice([(C(IF(X, Y), IF(Y, Z), X), Z), (C(IF(X, Y), IF(Y, Z), neg(Z)), neg(X)),
                       (C(IF(X, IF(Y, Z)), X, Y), Z), (C(IF(X, Y), IF(Z, Vv), X, Z), C(Y, Vv)),
                       (C(IF(X, C(Y, Z)), X), Z), (C(IF(X, W(Y, Z)), X, neg(Y)), Z), (C(IF(X, Y), neg(Y)), neg(X)),
                       (C(IF(X, Y), IF(Y, Z), X), C(Y, Z))])


def s5_deriv(sysk="5", lo=8, hi=14):
    for _ in range(3000):
        if sysk == "5":
            inner = derivation("s", 4, 8, 2)
        else:
            P0, Q0 = goal_5s()
            inner = derive_goal(P0, Q0, "5s", 60)
            if not inner:
                continue
        P = inner[-1][0]
        if not (P[0] == "conj" and len(P[1]) >= 2):
            continue
        # переписать посылку как двучлен: (P1)(P2), где P2 — последний член
        P1 = C(*P[1][:-1]) if len(P[1]) > 2 else P[1][0]
        P2 = P[1][-1]
        if sysk == "5s" and F.has(P2):
            continue
        Pb = C(P1, P2)
        if Pb != P:
            lines = [(P if a == P else a, b, wh) for a, b, wh in inner]
            # заменить посылку на двучленную форму во всех строках, где она стоит
            lines = [(Pb if a == P else a, Pb if b == P else b, wh) for a, b, wh in lines]
            if F.check(lines, "s" if sysk == "5" else "5s"):
                continue
        else:
            lines = list(inner)
        if not all(any(a == Pb and b == t for a, b, _ in lines) for t in P[1]):
            continue
        lines = s5_curry(lines, sysk)
        if lo <= len(lines) <= hi and not F.check(lines, sysk):
            key = tex(lines[-1][1])
            if key in SEEN:
                continue
            SEEN.add(key)
            return lines
    raise RuntimeError("нет вывода S5")


def discharge(P, Q, aux_letters):
    """⊢ (P → Q) при тавтологичном P ⊢ Q с новыми буквами: вспомогательная тавтология A = (n ∨ ∼n)…"""
    parts = [W(V(n), N(V(n))) for n in aux_letters]
    A = parts[0] if len(parts) == 1 else C(*parts)
    lines = [(C(A, P), Q, "Ss"), (None, IF(C(A, P), Q), ("Rif", 1)), (IF(C(A, P), Q), IF(A, IF(P, Q)), "A5"),
             (None, IF(A, IF(P, Q)), ("Rd1", 3, 2)), (None, A, "S5")]
    mp(lines, 4, 5)
    assert not F.check(lines, "5"), F.check(lines, "5")
    return lines


# ---------------------------------------------------------------- карточки: вывод, дополнение, две ошибки
def goal_text(lines):
    a, b, _ = lines[-1]
    return ftex(a, b)


def c_deriv(sysk="s", src="с. 90–91, гл. 6, § 6", lo=8, hi=12, lines=None, extra=""):
    lines = lines or derivation(sysk, lo, hi)
    sname = SYSNAME[sysk]
    cond = (f"{CV} Выведите в {sys_phrase(sysk)} формулу ${goal_text(lines)}$.{extra} {sys_text(sysk)}")
    ans = (f"Например, вывод из {len(lines)} строк (см. решение); схемы: "
           f"{', '.join(sorted(F.LABEL[a] for a in axioms_used(lines)))}.")
    sol = F.show(lines, sysk) + "\n\nКаждая строка проверена: пример схемы, теорема общей теории дедукции или применение правила."
    lvl = 7 if len(lines) >= 10 else 6
    return card(lvl, "D", "open", "proof", src, "условность, вывод", cond, ans, sol, system=sname.replace("{", "").replace("}", ""))


def show_hidden(lines, hide_why, hide_f, sysk):
    out = []
    for n, (a, b, wh) in enumerate(lines, 1):
        f_ = "…" if n in hide_f else f"${ftex(a, b)}$"
        w_ = "…" if n in hide_why else F.why_text(wh, sysk)
        out.append(f"{n}. {f_} [{w_}]")
    return "\n".join(out)


def c_complete(sysk="s", src="с. 90–91, гл. 6, § 6", lines=None):
    lines = lines or derivation(sysk, 9, 12)
    ax = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, str)]
    rl = [n for n, (*_, wh) in enumerate(lines, 1) if not isinstance(wh, str)]
    hide_f = set(rnd.sample(ax[1:] or ax, min(2, max(1, len(ax) - 1))))
    rest = [n for n in ax if n not in hide_f]
    hide_why = set(rnd.sample(rest, min(2, len(rest))))
    hide_why |= set(rnd.sample(rl[:-1], min(2, max(0, len(rl) - 1))))
    sname = SYSNAME[sysk]
    cond = (f"{CV} В выводе в {sys_phrase(sysk)} формулы ${goal_text(lines)}$ пропущены формулы некоторых строк и основания "
            f"некоторых шагов («…»). Восстановите их. {sys_text(sysk)}\n\n{show_hidden(lines, hide_why, hide_f, sysk)}")
    parts = []
    for n in sorted(hide_why | hide_f):
        a, b, wh = lines[n - 1]
        parts.append(f"{n} — " + (f"${ftex(a, b)}$ " if n in hide_f else "") +
                     (f"[{F.why_text(wh, sysk)}]" if n in hide_why else ""))
    sol = ("Формулу строки восстанавливаем по соседним строкам: в R1 заключение одной строки — посылка другой; в R2 обе "
           "строки имеют общую посылку; в R3 две строки — взаимно выводимые высказывания; основание — по виду формулы.\n\n"
           + F.show(lines, sysk))
    return card(5, "D", "complete", "build", src, "условность, вывод, дополнение", cond,
                "; ".join(p.strip() for p in parts) + ".", sol, system=sname.replace("{", "").replace("}", ""))


WRONG = {"A1": "A3", "A2": "A4", "A3": "A7", "A4": "A2", "A5": "A6", "A6": "A5", "A7": "A3", "A8": "A7", "A9": "A5",
         "B1": "B2", "B2": "B1", "B3": "B1", "N1": "N2", "N2": "N1", "N3": "N4", "N4": "N3", "N5": "N6", "N6": "N5"}
WHY_AX = {
    "A1": "это A1 $(x \\rightarrow y)x \\vdash y$: из условного высказывания и его антецедента — консеквент",
    "A2": "это A2 $(x \\rightarrow y) \\vdash (\\sim y \\rightarrow \\sim x)$ — контрапозиция",
    "A3": "это A3 $(x \\rightarrow y)(y \\rightarrow z) \\vdash (x \\rightarrow z)$: консеквент первого — антецедент второго",
    "A4": "это A4 $(x \\rightarrow yz) \\vdash (x \\rightarrow y)(x \\rightarrow z)$ — расщепление консеквента-конъюнкции",
    "A5": "это A5 $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$: конъюнкция в антецеденте "
          "переходит во вложенное условное высказывание",
    "A6": "это A6 $(x \\rightarrow (y \\rightarrow z)) \\vdash (xy \\rightarrow z)$ — обратный к A5 переход",
    "A7": "это A7 $(x \\rightarrow y)(z \\rightarrow v) \\vdash (xz \\rightarrow yv)$: антецеденты и консеквенты "
          "соединяются конъюнкцией",
    "A8": "это A8 $(x \\rightarrow y) \\vee (z \\rightarrow v) \\vdash (xz \\rightarrow y \\vee v)$",
    "A9": "это A9 $(x \\rightarrow y) \\vdash (xz \\rightarrow y)$ — усиление антецедента (только в $S^w_{if}$)",
    "B1": "это A1 § 9 $(x \\rightarrow y)x \\vdash y$",
    "B2": "это A2 § 9 $(x \\rightarrow y)\\sim y \\vdash \\sim x$",
    "B3": "это A3 § 9 $\\vdash ((xy \\rightarrow z) \\rightarrow (x \\rightarrow (y \\rightarrow z)))$",
    "N1": "это $A^n1$: из $x \\rightarrow y$ — отрицания двух других", "N2": "это $A^n2$ — обратная к $A^n1$",
    "N3": "это $A^n3$: из $x \\urcorner\\!\\rightarrow y$ — отрицания двух других", "N4": "это $A^n4$ — обратная к $A^n3$",
    "N5": "это $A^n5$: из $x? \\rightarrow y$ — отрицания двух других", "N6": "это $A^n6$ — обратная к $A^n5$",
}
PAGE = {"s": "с. 90", "w": "с. 90–91", "5": "с. 90–91", "5s": "с. 93", "n": "с. 89"}


def corrupt(lines, sysk, kinds):
    """Две ошибки разных видов; возвращает (испорченный вывод, [(номер, вид, верное основание)])."""
    bad = list(lines)
    errs = []
    used = set()
    for kind in kinds:
        if kind == "ax":
            cand = [i for i, (*_, wh) in enumerate(bad) if isinstance(wh, str) and wh in WRONG and i not in used]
        elif kind == "ss":
            cand = [i for i, (a, b, wh) in enumerate(bad) if isinstance(wh, str) and wh in WRONG and i not in used
                    and a is not None and not F.s_step(a, b)]
        elif kind == "r12":
            cand = [i for i, (*_, wh) in enumerate(bad) if not isinstance(wh, str) and wh[0] == "R1" and i not in used]
        elif kind == "rd":
            cand = [i for i, (*_, wh) in enumerate(bad) if not isinstance(wh, str) and wh[0] == "Rd1" and i not in used]
        else:
            cand = []
        if not cand:
            return None
        i = rnd.choice(cand)
        used.add(i)
        a, b, wh = bad[i]
        if kind == "ax":
            bad[i] = (a, b, WRONG[wh])
        elif kind == "ss":
            bad[i] = (a, b, "Ss")
        elif kind == "r12":
            bad[i] = (a, b, ("R2",) + tuple(wh[1:]))
        elif kind == "rd":
            bad[i] = (a, b, ("MT6",) + tuple(wh[1:]))
        errs.append((i + 1, kind, wh))
    found = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in F.check(bad, sysk)})
    if found != sorted(n for n, _, _ in errs):
        return None
    return bad, sorted(errs)


def explain(n, kind, wh, lines, sysk):
    a, b, _ = lines[n - 1]
    pg = PAGE[sysk]
    if kind == "ax":
        return (f"Шаг {n}: основание {F.LABEL[WRONG[wh]]} неверно — {WHY_AX[wh]} ({pg}); формула строки — пример "
                f"{F.LABEL[wh]}.")
    if kind == "ss":
        ce = F.s_counter(a, b)
        tail = ""
        if ce:
            e, tab = ce
            tail = " (если считать условные высказывания элементарными, при " + ", ".join(
                f"${tex(tab[k]) if k in tab else k} = {vv}$" for k, vv in sorted(e.items())) + \
                " посылка истинна, а заключение ложно)"
        return (f"Шаг {n}: это не теорема общей теории дедукции{tail}; шаг опирается на свойства оператора условности — "
                f"{WHY_AX[wh]} ({pg}).")
    if kind == "r12":
        return (f"Шаг {n}: R2 соединяет конъюнкцией заключения двух строк с общей посылкой, а здесь заключение строки "
                f"{wh[1]} — посылка строки {wh[2]}: это R1 «если $x \\vdash y$ и $y \\vdash z$, то $x \\vdash z$» (с. 17).")
    if kind == "rd":
        return (f"Шаг {n}: MT6 гл. 4 соединяет две формулы $\\vdash x$, $\\vdash y$ в $\\vdash xy$, а здесь строка {wh[1]} — "
                f"формула следования $x \\vdash y$, строка {wh[2]} — $\\vdash x$: это $R^d1$ (с. 67).")
    raise ValueError(kind)


def c_diag(sysk="s", src="с. 90–91, гл. 6, § 6", lines_fn=None, kinds_pool=None):
    kinds_pool = kinds_pool or [("ax", "r12"), ("ax", "ss"), ("ss", "r12"), ("ax", "ax")]
    for _ in range(400):
        lines = lines_fn() if lines_fn else derivation(sysk, 8, 11)
        res = corrupt(lines, sysk, rnd.choice(kinds_pool))
        if res:
            break
    else:
        raise RuntimeError("нет диагностики")
    bad, errs = res
    sname = SYSNAME[sysk]
    cond = (f"{CV} В выводе в {sys_phrase(sysk)} формулы ${goal_text(lines)}$ ровно два основания указаны неверно (формулы строк "
            f"верны). Найдите оба, назовите нарушенное правило или схему и исправьте. {sys_text(sysk)}\n\n"
            f"{F.show(bad, sysk)}")
    ans = "; ".join(f"шаг {n}: [{F.why_text(wh, sysk)}]" for n, _, wh in errs) + "."
    sol = "\n".join(explain(n, k, wh, lines, sysk) for n, k, wh in errs) + "\n\nИсправленный вывод:\n\n" + F.show(lines, sysk)
    return card(6, "E", "vary", "text", src, "условность, вывод, диагностика", cond, ans, sol,
                system=sname.replace("{", "").replace("}", ""))
