"""Задачи гл. 7, § 8–9, для hard07.py: базисные формулы и полнота S^s_cq (§ 8), контрольная форма и процедура
разрешения (§ 9)."""
import itertools
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts" / "gen"))
import q7  # noqa: E402
import hard07_der as H  # noqa: E402
import hard07_a as A  # noqa: E402
import hard07_a2 as A2  # noqa: E402
from hard07_a import CONV, L, card, items  # noqa: E402
from q7 import ALL, C, EL, EX, N, W, free_in, ftex, qfree, tex  # noqa: E402

rnd = random.Random(1970_0708)
ab, ac, ad, cb, cd, db, ba = A.ab, A.ac, A.ad, A.cb, A.cd, A.db, A.ba
K = {"A": ALL, "E": EX}
SRC8 = "с. 107–116, гл. 7, § 8"
TAUTR = ("Тавтология с ограничением (§ 9 гл. 5; MT1 § 8, с. 108) — тавтология по D3 § 7, в заключение бескванторной "
         "формы которой не входят элементарные высказывания, отсутствующие в посылке.")


# ================================================================ § 8: случаи 3–8 MT1 (с. 109–110)
def cases(z, v):
    cs = {}
    cs[3] = [(K[p]("a", z if s else N(z)), K[q]("a", z)) for p, s, q in
             [("A", 1, "A"), ("E", 1, "A"), ("A", 1, "E"), ("E", 1, "E"), ("A", 0, "A"), ("A", 0, "E"), ("E", 0, "A"),
              ("E", 0, "E")]]
    cs[4] = [(K[p]("a", C(z, v)), C(K[q]("a", z), K[r]("a", v))) for p in "AE" for q, r in ["AA", "AE", "EA", "EE"]]
    cs[5] = [(K[p]("a", W(z, v)), W(K[q]("a", z), K[r]("a", v))) for p in "AE" for q, r in ["AA", "AE", "EA", "EE"]]
    cs[6] = [(C(K[q]("a", z), K[r]("a", v)), K[p]("a", C(z, v))) for q, r in ["AA", "AE", "EA", "EE"] for p in "AE"]
    cs[7] = [(W(K[q]("a", z), K[r]("a", v)), K[p]("a", W(z, v))) for p in "AE" for q, r in ["AA", "AE", "EA", "EE"]]
    return cs


def cases8(z):
    return [(K[p]("a", K[q]("b", z)), K[r]("b", K[s]("a", z))) for p in "AE" for q in "AE" for r in "AE" for s in "AE"]


PROOFS = {  # какой теоремой § 6 (или $S^s$) доказывается тавтология случая
    ("A", "A"): None}


def proof_name(p, q):
    if p == q:
        return "$x \\vdash x$ системы $S^s$"
    for nm in ["A3", "A4", "T14", "T15", "T16", "T19", "T20", "T21", "T22", "T23", "T24", "T25", "T26", "T27", "T29",
               "T30", "T32", "T33", "T34", "T35", "T36", "T38", "T39", "T40", "T41", "T42"]:
        if q7.inst_of(A2.sch_of(nm), p, q) is not None:
            return nm
    # (∀a)(zv) ⊢ (∃a)z(∃a)v — по T20 и T27
    if p[0] == "all" and p[2][0] == "conj" and q[0] == "conj" and all(t[0] == "ex" for t in q[1]):
        return "T20, T27"
    return None


def zv():
    for _ in range(100):
        z, v = A.compound(), A.compound()
        if free_in("a", z) and free_in("a", v) and not (q7.patoms(z) & q7.patoms(v)) and z[0] != "neg":
            return z, v
    return ab, ac


def c_case_table(level=5):
    k = rnd.choice([3, 4, 5, 6, 7, 8])
    if k == 8:
        z = rnd.choice([ab, C(ab, cb), W(ab, N(db))])
        sub = cases8(z)
        idx = sorted(rnd.sample(range(16), 8))
    else:
        z, v = zv()
        sub = cases(z, v)[k]
        idx = list(range(8))
    its = [sub[i] for i in idx]
    ans, sol = [], []
    taut = []
    for j, (p, q) in enumerate(its):
        if q7.qtaut(p, q, nmax=2 if k == 8 else 3):
            nm = proof_name(p, q)
            assert nm, ftex(p, q)
            taut.append(j)
            sol.append(f"{j + 1}) ${ftex(p, q)}$ — тавтология; доказуема ({nm}).")
        else:
            sol.append(f"{j + 1}) ${ftex(p, q)}$ — не тавтология: {A2.cm_text(p, q)}.")
    ans = "Тавтологии: " + ", ".join(str(j + 1) for j in taut) + "; остальные — нет (значения — в решении)."
    cond = (f"{CONV} В доказательстве MT1 § 8 (с. 108–110) базисные формулы вида {k} без отрицаний перед кванторами "
            f"разбиваются на подслучаи. Для каждой формулы ниже установите, тавтология ли она (D3 § 7, с. 105); для "
            "тавтологии назовите теоремную или аксиомную схему, по которой она доказуема в $S^s_{cq}$, для нетавтологии "
            "укажите опровергающие значения интерпретационной формы.\n\n"
            + "\n".join(f"{j + 1}) ${ftex(p, q)}$" for j, (p, q) in enumerate(its)))
    return card(level, "C", "iso", "short", SRC8 if k != 8 else "с. 107–110, гл. 7, § 8", "кванторы, полнота, базисные формулы",
                cond, ans, "\n".join(sol))


def c_case_diag(level=6):
    k = rnd.choice([4, 5, 6, 7])
    z, v = zv()
    sub = rnd.sample(cases(z, v)[k], 6)
    truth = [q7.qtaut(p, q) for p, q in sub]
    wrong = rnd.sample(range(6), 2)
    body = "\n".join(f"{j + 1}. ${ftex(p, q)}$ — {'тавтология' if (t != (j in wrong)) else 'не тавтология'}"
                     for j, ((p, q), t) in enumerate(zip(sub, truth)))
    cond = (f"{CONV} Студент разобрал шесть подслучаев базисной формулы вида {k} (MT1 § 8, с. 108–110). Ровно в двух "
            f"строках он ошибся. Найдите их и обоснуйте верный ответ: для тавтологии — схемой § 6, по которой формула "
            f"доказуема, для нетавтологии — опровергающими значениями (D2–D3 § 7).\n\n{body}")
    ans, sol = [], []
    for j in sorted(wrong):
        p, q = sub[j]
        if truth[j]:
            ans.append(f"{j + 1}: тавтология ({proof_name(p, q)})")
            sol.append(f"{j + 1}. Тавтология: доказуема по {proof_name(p, q)} (с. 103–106), а доказуемые формулы — "
                       "тавтологии (процедура § 9).")
        else:
            ans.append(f"{j + 1}: не тавтология")
            sol.append(f"{j + 1}. Не тавтология: {A2.cm_text(p, q)}.")
    return card(level, "E", "vary", "text", SRC8, "кванторы, полнота, диагностика", cond, "; ".join(ans),
                "\n".join(sol) + "\n\nОстальные строки верны.")


# ---- базисные формулы (D1 § 8)
def strip(f):
    n = 0
    while f[0] == "neg":
        f, n = f[1], n + 1
    return n, f


def basis_type(p, q):
    if any(g[0] == "neg" and g[1][0] == "neg" for g in list(H.walk(p)) + list(H.walk(q))):
        return None
    np_, P = strip(p)
    nq_, Q = strip(q)

    def qa(f):
        n, g = strip(f)
        return g if g[0] in ("all", "ex") else None
    Pq, Qq = qa(p), qa(q)
    # 8: α(K1a)β(K2b)z ⊢ γ(K3b)δ(K4a)z
    if Pq and Qq:
        n1, Pin = strip(Pq[2])
        n2, Qin = strip(Qq[2])
        if Pin[0] in ("all", "ex") and Qin[0] in ("all", "ex") and Pin[1] != Pq[1] and Qq[1] == Pin[1] \
                and Qin[1] == Pq[1] and strip(Pin[2])[1] == Pin[2] and Pin[2] == Qin[2]:
            return 8
    if Pq and Qq and Pq[1] == Qq[1] and Pq[2] == Qq[2] and strip(Pq[2])[0] == strip(Qq[2])[0] == 0:
        return 3
    if Pq and Qq and Pq[1] == Qq[1]:
        n1, z1 = strip(Pq[2])
        n2, z2 = strip(Qq[2])
        if z1 == z2 and z1[0] not in ("all", "ex"):
            return 3
    if Pq and not Qq:
        n1, z1 = strip(Pq[2])
        if z1 == Q and Q[0] not in ("all", "ex", "conj", "wdis") or (z1 == Q and Q[0] == "el"):
            return 1
    if Qq and not Pq:
        n1, z1 = strip(Qq[2])
        if z1 == P and P[0] == "el":
            return 2
    # 4–7
    if Pq and Q[0] in ("conj", "wdis") and len(Q[1]) == 2 and nq_ == 0:
        m = [qa(t) for t in Q[1]]
        if all(m) and m[0][1] == m[1][1] == Pq[1]:
            zs = (strip(m[0][2])[1], strip(m[1][2])[1])
            body = Pq[2]
            if body[0] == Q[0] and len(body[1]) == 2 and tuple(body[1]) == zs:
                return 4 if Q[0] == "conj" else 5
    if Qq and P[0] in ("conj", "wdis") and len(P[1]) == 2 and np_ == 0:
        m = [qa(t) for t in P[1]]
        if all(m) and m[0][1] == m[1][1] == Qq[1]:
            zs = (strip(m[0][2])[1], strip(m[1][2])[1])
            body = Qq[2]
            if body[0] == P[0] and len(body[1]) == 2 and tuple(body[1]) == zs:
                return 6 if P[0] == "conj" else 7
    return None


def neg(f, k):
    for _ in range(k):
        f = N(f)
    return f


def mk_basis(t):
    z, v = zv()
    g = lambda: rnd.choice([0, 0, 1])
    Kq = lambda: rnd.choice([ALL, EX])
    if t == 1:
        return neg(Kq()("a", neg(ab, g())), g()), neg(ab, g())
    if t == 2:
        return neg(ac, g()), neg(Kq()("a", neg(ac, g())), g())
    if t == 3:
        return neg(Kq()("a", neg(z, g())), g()), neg(Kq()("a", neg(z, g())), g())
    if t == 4:
        return neg(Kq()("a", C(z, v)), g()), C(neg(Kq()("a", z), g()), neg(Kq()("a", v), g()))
    if t == 5:
        return neg(Kq()("a", W(z, v)), g()), W(neg(Kq()("a", z), g()), neg(Kq()("a", v), g()))
    if t == 6:
        return C(neg(Kq()("a", z), g()), neg(Kq()("a", v), g())), neg(Kq()("a", C(z, v)), g())
    if t == 7:
        return W(neg(Kq()("a", z), g()), neg(Kq()("a", v), g())), neg(Kq()("a", W(z, v)), g())
    zz = rnd.choice([ab, C(ab, cb)])
    return (neg(Kq()("a", neg(Kq()("b", zz), g())), g()), neg(Kq()("b", neg(Kq()("a", zz), g())), g()))


def mk_nonbasis():
    z, v = zv()
    return rnd.choice([
        (ALL("a", C(z, v)), C(ALL("a", z), ALL("b", v)), "в заключении группы с разными терминами ($a$ и $b$)"),
        (ALL("a", z), ALL("a", v), "под кванторами посылки и заключения разные высказывания"),
        (ALL("a", C(z, v)), C(ALL("a", z), ALL("a", v), ALL("a", z)), "в заключении три члена, а не два"),
        (C(ALL("a", z), v), EX("a", C(z, v)), "второй член посылки — не высказывание с квантором по $a$"),
        (ALL("a", ALL("b", ab)), ALL("a", ALL("b", ab)), "порядок кванторов не меняется, и группы стоят подряд — это "
         "не вид 8 (там $(K^3b)$ стоит впереди)"),
        (EX("a", W(z, v)), W(EX("a", v), EX("a", z)), "члены дизъюнкции переставлены: в виде 5 справа сначала $z$, потом $v$"),
    ])


BAS_TEX = ["\\alpha(Ka)\\beta z \\vdash \\gamma z", "\\gamma z \\vdash \\alpha(Ka)\\beta z",
           "\\alpha(K^1a)\\beta z \\vdash \\gamma(K^2a)\\delta z", "\\alpha(K^1a)(zv) \\vdash \\beta(K^2a)z\\gamma(K^3a)v",
           "\\alpha(K^1a)(z \\vee v) \\vdash \\beta(K^2a)z \\vee \\gamma(K^3a)v",
           "\\alpha(K^1a)z\\beta(K^2a)v \\vdash \\gamma(K^3a)(zv)",
           "\\alpha(K^1a)z \\vee \\beta(K^2a)v \\vdash \\gamma(K^3a)(z \\vee v)",
           "\\alpha(K^1a)\\beta(K^2b)z \\vdash \\gamma(K^3b)\\delta(K^4a)z"]
D1_8 = ("D1 § 8 (с. 107): базисные формулы — формулы видов " + "; ".join(f"{i + 1}) ${t}$" for i, t in enumerate(BAS_TEX))
        + ", где K, K¹–K⁴ — $\\forall$ или $\\exists$ в любых комбинациях, а $\\alpha, \\beta, \\gamma, \\delta$ — наличие или "
        "отсутствие отрицания.")


def c_basis(level=4, diag=False):
    its = []
    for t in rnd.sample(range(1, 9), 3):
        for _ in range(50):
            p, q = mk_basis(t)
            if basis_type(p, q) == t:
                its.append((p, q, t, None))
                break
    for _ in range(2):
        p, q, why = mk_nonbasis()
        if basis_type(p, q) is None and (p, q) not in [(i[0], i[1]) for i in its]:
            its.append((p, q, None, why))
    rnd.shuffle(its)
    if not diag:
        cond = (f"{CONV} Для каждой формулы установите, является ли она базисной, и если да — какого вида; если нет — "
                f"объясните, что мешает. Отрицание при $z$ под квантором здесь не входит в $z$. {D1_8}\n\n"
                + items([f"${ftex(p, q)}$" for p, q, _, _ in its]))
        ans = "; ".join(f"{L[k]}) " + (f"вид {t}" if t else "не базисная") for k, (_, _, t, _) in enumerate(its))
        sol = "\n".join(f"{L[k]}) " + (f"вид {t}: ${BAS_TEX[t - 1]}$ при подходящих K и $\\alpha, \\beta, \\ldots$" if t else
                                      f"не базисная: {why}") + "." for k, (_, _, t, why) in enumerate(its))
        return card(level, "R", "iso", "short", "с. 107, гл. 7, § 8", "кванторы, базисные формулы", cond, ans, sol)
    wrong = rnd.sample(range(len(its)), 2)
    lines = []
    for k, (p, q, t, why) in enumerate(its):
        if k in wrong:
            claim = "не базисная" if t else f"базисная вида {rnd.choice([3, 4, 5, 6, 7])}"
        else:
            claim = f"базисная вида {t}" if t else "не базисная"
        lines.append(f"{k + 1}. ${ftex(p, q)}$ — {claim}")
    cond = (f"{CONV} Студент классифицировал формулы по D1 § 8; ровно две строки неверны. Найдите их и исправьте. {D1_8}"
            "\n\n" + "\n".join(lines))
    ans = "; ".join(f"{k + 1}: " + (f"вид {its[k][2]}" if its[k][2] else "не базисная") for k in sorted(wrong))
    sol = "\n".join(f"{k + 1}. " + (f"Вид {its[k][2]}: совпадает со схемой ${BAS_TEX[its[k][2] - 1]}$." if its[k][2] else
                                    f"Не базисная: {its[k][3]}.") for k in sorted(wrong))
    return card(5, "E", "vary", "short", "с. 107, гл. 7, § 8", "кванторы, базисные формулы, диагностика", cond, ans,
                sol + "\n\nОстальные строки верны.")


def push(f):
    """Внесение отрицаний через кванторы по эквивалентностям с. 108: ∼(∀a)x → (∃a)∼x, ∼(∃a)x → (∀a)∼x, ∼∼x → x."""
    k = f[0]
    if k == "neg":
        g = f[1]
        if g[0] == "neg":
            return push(g[1])
        if g[0] == "all":
            return EX(g[1], push(N(g[2])))
        if g[0] == "ex":
            return ALL(g[1], push(N(g[2])))
        return N(push(g)) if g[0] not in ("el",) else f
    if k in ("all", "ex"):
        return (k, f[1], push(f[2]))
    if k in ("conj", "wdis"):
        return (k, tuple(push(a) for a in f[1]))
    return f


def c_reduce(level=6):
    for _ in range(200):
        t = rnd.choice([3, 4, 5, 6, 7, 1, 2])
        p, q = mk_basis(t)
        if basis_type(p, q) == t and any(g[0] == "neg" and g[1][0] in ("all", "ex") for g in H.walk(p) for _ in [0]) \
                or any(g[0] == "neg" and g[1][0] in ("all", "ex") for g in H.walk(q)):
            break
    rp, rq = push(p), push(q)
    tt = q7.qtaut(rp, rq)
    assert tt == q7.qtaut(p, q)
    cm = None if tt else q7.countermodel(rp, rq)
    cond = (f"{CONV} Сведите формулу ${ftex(p, q)}$ к формуле без отрицаний перед кванторами, пользуясь доказуемыми в "
            "$S^s_{cq}$ эквивалентностями (с. 108): $(\\forall a)x \\dashv\\vdash \\sim(\\exists a)\\sim x$, $(\\exists a)x "
            "\\dashv\\vdash \\sim(\\forall a)\\sim x$, $\\sim\\sim x \\dashv\\vdash x$; затем выясните, тавтология ли она "
            "(D3 § 7), и сделайте вывод об исходной формуле.")
    ans = f"${ftex(rp, rq)}$ — " + ("тавтология; исходная тоже." if tt else "не тавтология; исходная тоже.")
    sol = (f"1. По эквивалентностям: $\\sim(\\forall a)x \\dashv\\vdash \\sim\\sim(\\exists a)\\sim x \\dashv\\vdash "
           f"(\\exists a)\\sim x$ и $\\sim(\\exists a)x \\dashv\\vdash (\\forall a)\\sim x$; двойные отрицания снимаются. "
           f"Получаем ${ftex(rp, rq)}$.\n"
           "2. Эквивалентные части дают взаимовыводимые формулы, и интерпретационные формы у них равнозначны (законы де "
           "Моргана для конъюнкций и дизъюнкций по $ia$).\n" +
           (f"3. Тавтология: {proof_name(rp, rq) and 'доказуема по ' + proof_name(rp, rq) or 'проверка при любом n'}." if tt
            else f"3. Не тавтология: {A2.cm_text(rp, rq, cm)}."))
    if tt and not proof_name(rp, rq):
        return c_reduce(level)
    return card(level, "D", "vary", "short", "с. 108, гл. 7, § 8", "кванторы, базисные формулы, отрицания", cond, ans, sol)


def zs(n):
    preds = ["b", "c", "d", "e"]
    return [EL("a", preds[i]) for i in range(n)]


def mt_formula(kind, Kt, Ks):
    z = zs(len(Ks))
    if kind == "MT2":
        return Kt("a", C(*z)), C(*[k("a", zi) for k, zi in zip(Ks, z)])
    if kind == "MT3":
        return C(*[k("a", zi) for k, zi in zip(Ks, z)]), Kt("a", C(*z))
    if kind == "MT4":
        return Kt("a", W(*z)), W(*[k("a", zi) for k, zi in zip(Ks, z)])
    return W(*[k("a", zi) for k, zi in zip(Ks, z)]), Kt("a", W(*z))


MT_TEX = {"MT2": "(Ka)(z^1z^2z^3) \\vdash (K^1a)z^1(K^2a)z^2(K^3a)z^3",
          "MT3": "(K^1a)z^1(K^2a)z^2(K^3a)z^3 \\vdash (Ka)(z^1z^2z^3)",
          "MT4": "(Ka)(z^1 \\vee z^2 \\vee z^3) \\vdash (K^1a)z^1 \\vee (K^2a)z^2 \\vee (K^3a)z^3",
          "MT5": "(K^1a)z^1 \\vee (K^2a)z^2 \\vee (K^3a)z^3 \\vdash (Ka)(z^1 \\vee z^2 \\vee z^3)"}
MT_PAGE = {"MT2": "с. 110–111", "MT3": "с. 111–112", "MT4": "с. 112–113", "MT5": "с. 113"}


def c_mtpat(level=6, diag=False):
    kind = rnd.choice(["MT2", "MT3", "MT4", "MT5"])
    its = []
    seen = set()
    while len(its) < 4:
        Kt = rnd.choice([ALL, EX])
        Ks = tuple(rnd.choice([ALL, EX]) for _ in range(3))
        if (Kt, Ks) in seen:
            continue
        seen.add((Kt, Ks))
        p, q = mt_formula(kind, Kt, Ks)
        its.append((p, q, q7.qtaut(p, q, nmax=2)))
    if len({t for *_, t in its}) == 1:
        return c_mtpat(level, diag)
    ans, sol = [], []
    for k, (p, q, t) in enumerate(its):
        if t:
            ans.append(f"{L[k]}) тавтология — доказуема по {kind}")
            sol.append(f"{L[k]}) Тавтология (с ограничением: элементарные высказывания одни и те же); по {kind} § 8 "
                       f"({MT_PAGE[kind]}) доказуема — по образцу доказательства книги.")
        else:
            ans.append(f"{L[k]}) не тавтология")
            sol.append(f"{L[k]}) Не тавтология: {A2.cm_text(p, q)}.")
    if not diag:
        cond = (f"{CONV} {kind} § 8 ({MT_PAGE[kind]}): если формула ${MT_TEX[kind]}$ есть тавтология (с ограничением), "
                f"она доказуема в $S^s_{{cq}}$. Для каждой формулы ниже ($z^i$ — элементарные высказывания) выясните, "
                "тавтология ли она; для нетавтологии укажите опровергающие значения интерпретационной формы, для "
                "тавтологии — на какую метатеорему опирается её доказуемость.\n\n"
                + items([f"${ftex(p, q)}$" for p, q, _ in its]))
        return card(level, "C", "iso", "short", f"{MT_PAGE[kind]}, гл. 7, § 8", "кванторы, полнота, MT2–MT5", cond,
                    "; ".join(ans), "\n".join(sol))
    wrong = rnd.sample(range(4), 2)
    lines = "\n".join(f"{k + 1}. ${ftex(p, q)}$ — {'тавтология' if t != (k in wrong) else 'не тавтология'}"
                      for k, (p, q, t) in enumerate(its))
    cond = (f"{CONV} Студент применил {kind} § 8 ({MT_PAGE[kind]}: если ${MT_TEX[kind]}$ — тавтология с ограничением, "
            f"она доказуема) к четырём формулам. Ровно два его вывода о тавтологичности неверны. Найдите их и обоснуйте "
            f"значениями или ссылкой на теоремные схемы.\n\n{lines}")
    return card(6, "E", "vary", "text", f"{MT_PAGE[kind]}, гл. 7, § 8", "кванторы, полнота, диагностика", cond,
                "; ".join(f"{k + 1}: " + ("тавтология" if its[k][2] else "не тавтология") for k in sorted(wrong)),
                "\n".join(sol[k].replace(f"{L[k]})", f"{k + 1}.") for k in sorted(wrong)) + "\n\nОстальные выводы верны.")


SWAP = {("all", "all"): "T14", ("ex", "ex"): "T16", ("ex", "all"): "T15"}


def chain_derivation(pref, target):
    """Перестановка соседних кванторов по T14/T15/T16 с навешиванием внешних групп по R1/R2 (MT6, с. 114)."""
    z = pref[1]
    seq = list(pref[0])
    tgt = list(target)

    def build(sq):
        f = z
        for k, t in reversed(sq):
            f = (k, t, f)
        return f
    d = H.Der(build(seq))
    cur = 0
    while seq != tgt:
        moved = False
        for i in range(len(seq) - 1):
            (k1, t1), (k2, t2) = seq[i], seq[i + 1]
            if (k1, k2) in SWAP and tgt.index((k2, t2)) < tgt.index((k1, t1)):
                inner = build(seq[i:])
                nxt = seq[:i] + [seq[i + 1], seq[i]] + seq[i + 2:]
                inner2 = build(nxt[i:])
                k = d.add(inner, inner2, SWAP[(k1, k2)])
                for kk, tt in reversed(seq[:i]):
                    a0, b0 = d.lines[-1][0], d.lines[-1][1]
                    k = d.add((kk, tt, a0), (kk, tt, b0), ("R1" if kk == "all" else "R2", k))
                if cur:
                    d.add(d.P, d.lines[-1][1], ("tr", cur, k))
                cur = len(d.lines)
                seq = nxt
                moved = True
                break
        if not moved:
            return None
    return d


def c_mt6(level=6):
    z = C(ab, EL("c", "d")) if False else C(ab, EL("c", "b"))
    z = rnd.choice([C(EL("a", "b"), EL("c", "b")), W(EL("a", "c"), EL("b", "c")), C(EL("a", "b"), EL("b", "c"))])
    z = C(EL("a", "b"), EL("b", "c"))
    z3 = C(EL("a", "b"), EL("c", "b"))
    terms = ["a", "b", "c"] if "c" in q7.terms(z) else ["a", "b"]
    for _ in range(500):
        zz = rnd.choice([C(EL("a", "b"), EL("c", "b")), C(EL("a", "c"), EL("b", "c")), W(EL("a", "b"), EL("c", "b"))])
        ts = ["a", "b", "c"]
        seq = [(rnd.choice(["all", "ex"]), t) for t in rnd.sample(ts, 3)]
        tgt = rnd.sample(seq, 3)
        if tgt == seq:
            continue
        build = lambda sq: (lambda f: f)(None)
        f = zz
        for k, t in reversed(seq):
            f = (k, t, f)
        g = zz
        for k, t in reversed(tgt):
            g = (k, t, g)
        d = chain_derivation((seq, zz), tgt)
        valid = q7.qtaut(f, g, nmax=2)
        if d is not None and len(d.lines) < 4:
            continue
        if d is not None:
            assert not q7.check(d.lines, H.AX2 + H.T6USE) and valid and d.lines[-1][:2] == (f, g)
            break
        if not valid:
            d = None
            break
    cond = (f"{CONV} MT6 § 8 (с. 113–114): если $(K^1a^1)(K^2a^2)(K^3a^3)z \\vdash v$, где $v$ отличается от посылки лишь "
            "порядком кванторов, есть тавтология (с ограничением), она доказуема в $S^s_{cq}$. Докажите формулу "
            f"${ftex(f, g)}$, переставляя соседние кванторы по T14, T15, T16 (с. 104) и навешивая внешние группы по R1, "
            "R2, — или покажите значениями, что она не тавтология.")
    if d:
        ans = f"Доказуема: цепочка перестановок соседних кванторов (вывод в {len(d.lines)} строк — в решении)."
        sol = ("Как в доказательстве MT6 (случаи 1–4, с. 114): каждая перестановка двух соседних кванторов — базисная "
               "тавтология вида 8, доказуемая по T14, T15 или T16; внешние группы добавляются по R1, R2; цепочка "
               "соединяется по R1 $S^s$.\n\n" + H.show(d.lines))
        return card(level, "D", "vary", "proof", "с. 104, 113–114, гл. 7, § 6, 8", "кванторы, полнота, перестановка кванторов",
                    cond, ans, sol)
    cm = q7.countermodel(f, g, nmax=2)
    return card(level, "D", "vary", "short", "с. 104, 113–114, гл. 7, § 6, 8", "кванторы, полнота, перестановка кванторов",
                cond, "Не тавтология (значения — в решении).", f"{A2.cm_text(f, g, cm)[0].upper()}{A2.cm_text(f, g, cm)[1:]}"
                "; MT6 неприменима: формула не тавтология.")


def kind_of(f):
    k = f[0]
    return {"el": 1, "all": 2, "ex": 3, "wdis": 4, "conj": 5, "neg": 6}[k]


IK = {(1, 1): "теорема верна в силу $S^s$", (1, 2): "сводится к базисному", (1, 3): "сводится к базисному",
      (1, 4): "исключается", (1, 5): "исключается", (2, 1): "сводится к базисному",
      (2, 2): "при одинаковых $a$, $b$ — тавтология лишь при тавтологичной $z \\vdash v$ (тогда по R1); при различных — "
              "лишь при тавтологичной $z \\vdash (\\forall b)v$ (тогда по A1)",
      (2, 3): "аналогично $2 \\vdash 2$ (дополнительно T27)", (2, 4): "сводится к базисному или к случаю MT4",
      (2, 5): "сводится к базисному или к случаю MT2", (3, 1): "сводится к базисному",
      (3, 2): "при одинаковых $a$, $b$ — по T17 или T18 при условиях на свободные вхождения; при различных — по T18",
      (3, 3): "при одинаковых $a$, $b$ — по R2 при тавтологичной $z \\vdash v$; при различных — по R2 при тавтологичной "
              "$(\\exists a)z \\vdash v$",
      (3, 4): "сводится к базисным и к MT2–MT5", (3, 5): "сводится к базисным и к MT2–MT5",
      (4, 1): "исключается", (4, 5): "исключается", (5, 1): "исключается", (5, 4): "исключается"}
for _k in [(4, 2), (4, 3), (4, 4), (5, 2), (5, 3), (5, 5)]:
    IK[_k] = "сводится к базисным и к MT2–MT5"


def c_ik(level=5, sec=8):
    its = []
    pool = []
    for nm in ["A4", "T22", "T20", "T19", "T24", "T29", "A3", "T27", "T15", "T21", "T32", "T23", "T36"]:
        p, q, sb = A2.inst_arg(nm)
        pool.append((p, q))
    pool += [(ALL("a", ab), ab), (ab, EX("a", ab)), (EX("a", C(ab, cd)), cd)]
    its = rnd.sample(pool, 4)
    ans, sol = [], []
    for k, (p, q) in enumerate(its):
        i, j = kind_of(p), kind_of(q)
        ans.append(f"{L[k]}) ${i} \\vdash {j}$")
        sol.append(f"{L[k]}) $x$ — вид {i}, $y$ — вид {j}: случай ${i} \\vdash {j}$; в доказательстве MT7 (с. 115–116) "
                   f"он {IK[(i, j)]}.")
    cond = (f"{CONV} В доказательстве MT7 § 8 (с. 114–116) посылка $x$ и заключение $y$ классифицируются по виду: 1) "
            "элементарное высказывание; 2) $(\\forall a)z$; 3) $(\\exists a)z$; 4) дизъюнкция; 5) конъюнкция; 6) $\\sim z$ "
            "(сводится к остальным). Для каждой формулы определите случай $i \\vdash k$ и укажите, как он рассматривается "
            "в доказательстве книги.\n\n" + items([f"${ftex(p, q)}$" for p, q in its]))
    return card(level, "A", "iso", "short", "с. 114–116, гл. 7, § 8" if sec == 8 else "с. 114–119, гл. 7, § 8–9",
                "кванторы, полнота, MT7", cond, "; ".join(ans), "\n".join(sol))


def c_mt7check(level=6):
    its = []
    for nm in rnd.sample(["A4", "T22", "T20", "T32", "T24", "A3"], 2):
        p, q, sb = A2.inst_arg(nm)
        its.append((p, q, ("t", nm, sb)))
    p, q = A2.nontaut_item()
    its.append((p, q, ("n",)))
    p, q, sb = A2.inst_arg("T27")
    its.append((C(p, cd), q, ("q",)))
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (p, q, info) in enumerate(its):
        qp, qq = qfree(p), qfree(q)
        same = qp == qq or H.walk
        if info[0] == "t":
            ans.append(f"{L[k]}) доказуема по MT7")
            sol.append(f"{L[k]}) Бескванторные формы совпадают (${tex(qp)}$); формула — {A2.taut_text(info[1], info[2])}; "
                       "по MT7 доказуема.")
        elif info[0] == "n":
            ans.append(f"{L[k]}) MT7 неприменима: не тавтология")
            sol.append(f"{L[k]}) Бескванторные формы совпадают, но формула не тавтология: {A2.cm_text(p, q)}.")
        else:
            ans.append(f"{L[k]}) MT7 неприменима: бескванторные формы различны")
            sol.append(f"{L[k]}) Бескванторные формы ${tex(qp)}$ и ${tex(qq)}$ различаются не только заменой "
                       "$\\sim\\sim z$ на $z$ — условие MT7 не выполнено (о доказуемости MT7 ничего не говорит; эта формула "
                       "доказуема по $S^s$ и T27).")
    cond = (f"{CONV} MT7 § 8 (с. 114): если $x \\vdash y$ есть тавтология, а в её бескванторной форме $x^* \\vdash y^*$ "
            "$x^*$ и $y^*$ тождественны или одна получается из другой заменой вхождений $\\sim\\sim z$ на $z$, то $x \\vdash "
            "y$ доказуема в $S^s_{cq}$. Для каждой формулы проверьте оба условия и сделайте вывод.\n\n"
            + items([f"${ftex(p, q)}$" for p, q, _ in its]))
    return card(level, "C", "vary", "short", "с. 105, 114, гл. 7, § 7–8", "кванторы, полнота, MT7", cond, "; ".join(ans),
                "\n".join(sol))


def c_nat8(level=6):
    s, p, q = rnd.choice([
        ("«Есть $a$, которое стоит в отношении к каждому $b$; значит, к каждому $b$ найдётся $a$ в этом отношении»",
         EX("a", ALL("b", ab)), ALL("b", EX("a", ab))),
        ("«К каждому $b$ найдётся $a$ в отношении; значит, есть $a$, стоящее в отношении к каждому $b$»",
         ALL("b", EX("a", ab)), EX("a", ALL("b", ab))),
        ("«Каждое $a$ стоит в отношении к каждому $b$; значит, найдутся $b$ и $a$ в этом отношении»",
         ALL("a", ALL("b", ab)), EX("b", EX("a", ab)))])
    t = q7.qtaut(p, q, nmax=3)
    cond = (f"{CONV} $(a \\leftarrow b)$ прочтём как «$a$ стоит в отношении к $b$». Запишите рассуждение {s} базисной "
            "формулой вида 8 (D1 § 8, с. 107), выясните, тавтология ли она, и, если да, назовите теоремную схему § 6, по "
            "которой она доказуема; если нет — опишите опровергающий случай.")
    if t:
        nm = proof_name(p, q)
        return card(level, "C", "open", "short", "с. 104, 107–110, гл. 7, § 6, 8", "кванторы, полнота, формализация", cond,
                    f"${ftex(p, q)}$ — тавтология, {nm}.", f"Формула ${ftex(p, q)}$ — подслучай вида 8 (с. 110); "
                    f"{A2.taut_text(nm, {'x': ab})}.", form="nat")
    cm = q7.countermodel(p, q)
    return card(level, "C", "open", "short", "с. 107–110, гл. 7, § 8", "кванторы, полнота, формализация", cond,
                f"${ftex(p, q)}$ — не тавтология.", f"Формула ${ftex(p, q)}$: {A2.cm_text(p, q, cm)}; словами — разные "
                "предметы $1a$, $2a$, $1b$, $2b$, у каждого $b$ «свой» $a$, но общего $a$ нет.", form="nat")


def c_deriv8(level=7):
    c = A2.c_deriv6(src="с. 99–110, гл. 7, § 2, 6, 8", level=level)
    return c


# ================================================================ § 9: контрольная форма, процедура
def literals(f, acc=None, neg_=False):
    """Пары (элементарное высказывание, с отрицанием ли) по вхождениям."""
    acc = [] if acc is None else acc
    k = f[0]
    if k == "el":
        acc.append((f, neg_))
    elif k == "neg":
        if f[1][0] == "el":
            acc.append((f[1], True))
        else:
            literals(f[1], acc, neg_)
    elif k in q7.QK:
        literals(f[2], acc, neg_)
    elif k in ("conj", "wdis"):
        for a in f[1]:
            literals(a, acc, neg_)
    return acc


def repl_neg(f, e, r):
    k = f[0]
    if f == N(e):
        return r
    if k in ("el", "v"):
        return f
    if k == "neg":
        return N(repl_neg(f[1], e, r))
    if k in q7.QK:
        return (k, f[1], repl_neg(f[2], e, r))
    return (k, tuple(repl_neg(a, e, r) for a in f[1]))


def control(p, q):
    """Контрольная форма D1 § 9 для формул, бескванторные части которых — литералы и их конъюнкции/дизъюнкции
    (они уже в дизъюнктивной нормальной форме) и в которых нет ∼∼ перед элементарными высказываниями."""
    xs, ys = qfree(p), qfree(q)
    if not q7.is_taut1(ys) and not q7.is_contr(xs):
        return p, q, [], 1
    assert dnf_ok(p) and dnf_ok(q), ftex(p, q)
    pairs = []
    for side in (p, q):
        lit = literals(side)
        for e, ng in lit:
            if (e, True) in lit and (e, False) in lit and e not in pairs:
                pairs.append(e)
    used = q7.terms(p) | q7.terms(q)
    new_preds = [t for t in "efgh" if t not in used]
    bound = {g[1] for g in q7.groups(p) + q7.groups(q)}
    reps = []
    P, Q = p, q
    for i, e in enumerate(pairs):
        s_, p_ = e[1], e[2]
        assert not (s_ in bound and p_ in bound), "оба термина связаны"
        r = EL(new_preds[i], p_) if p_ in bound else EL(s_, new_preds[i])
        reps.append((e, r))
        P, Q = repl_neg(P, e, r), repl_neg(Q, e, r)
    return P, Q, reps, 2


TEMPL9 = [
    lambda z, v: (ALL("a", z), ALL("a", W(z, N(z)))),
    lambda z, v: (C(ALL("a", z), EX("a", N(z))), ALL("a", z)),
    lambda z, v: (C(EX("a", z), ALL("a", N(z))), EX("a", W(z, v))),
    lambda z, v: (ALL("a", C(z, v)), EX("a", W(v, N(v)))),
    lambda z, v: (EX("a", C(z, N(z))), EX("a", z)),
    lambda z, v: (ALL("a", W(z, N(z))), EX("a", W(z, N(z)))),
    lambda z, v: (C(ALL("a", z), ALL("a", N(z))), EX("a", C(z, v))),
    lambda z, v: (ALL("a", z), W(EX("a", z), EX("a", N(z)))),
    lambda z, v: (C(ALL("a", C(z, v)), EX("a", N(z))), ALL("a", v)),
    lambda z, v: (C(EX("a", W(z, v)), ALL("a", N(z))), EX("a", v)),
]


def zv9():
    return rnd.choice([(ab, ac), (ab, ad), (ac, ab), (ba, ac), (ad, ba)])


def ctrl_item():
    for _ in range(200):
        z, v = zv9()
        p, q = rnd.choice(TEMPL9)(z, v)
        if q7.ss_theorem(qfree(p), qfree(q)):
            P, Q, reps, case = control(p, q)
            return p, q, P, Q, reps, case
    raise RuntimeError


def taut_justify(P, Q):
    """Довод «тавтология при любом n» или None."""
    if q7.ptaut(P, Q) and len(q7.closures(P, Q)) == 1:
        return ("формула — тавтология, если высказывания с кванторами считать буквами; при любом числе отмеченных "
                "терминов интерпретационная форма получается заменой каждого такого высказывания одним и тем же "
                "выражением в посылке и в заключении — тавтология")
    if (P[0] == Q[0] and P[0] in ("all", "ex") and P[1] == Q[1] and q7.ptaut(P[2], Q[2])
            and len(q7.closures(P, Q)) == 1):
        op = "конъюнкции" if P[0] == "all" else "дизъюнкции"
        return (f"при любом $n$ посылка и заключение — {op} высказываний $z(ia)$ и $v(ia)$, где ${ftex(P[2], Q[2])}$ — "
                "тавтология; из каждого $z(ia)$ следует $v(ia)$, значит, из посылки следует заключение — тавтология")
    for nm in A2.ARG:
        sb = q7.inst_of(A2.sch_of(nm), P, Q)
        if sb is not None and A2.clean_inst(P, Q):
            return A2.taut_text(nm, sb)
    return None


def c_control(level=5):
    p, q, P, Q, reps, case = ctrl_item()
    cond = (f"{CONV} Постройте контрольную форму (D1 § 9, с. 116–117) формулы ${ftex(p, q)}$. D1: 1) если бескванторные "
            "формы формул $\\vdash y$ и $\\vdash \\sim x$ недоказуемы в $S^5$ (т. е. $y^*$ не тавтология, а $x^*$ не "
            "противоречие), формула не меняется; 2) иначе бескванторные части заменяются их дизъюнктивными нормальными "
            "формами, $\\sim\\sim a$ — на $a$, и если элементарное высказывание $a$ входит в $x$ (или в $y$) и без "
            "отрицания, и с отрицанием, то $\\sim a$ повсюду заменяется элементарным высказыванием, не входящим в формулу "
            "(здесь новое высказывание получаем, заменяя в заменяемом термин, не связанный в формуле, новым термином $e$; "
            "бескванторные части формулы уже в дизъюнктивной нормальной форме).")
    xs, ys = qfree(p), qfree(q)
    why = (f"$y^* = {tex(ys)}$ — тавтология" if q7.is_taut1(ys) else f"$x^* = {tex(xs)}$ — противоречие") if case == 2 else \
        f"$y^* = {tex(ys)}$ не тавтология, $x^* = {tex(xs)}$ не противоречие"
    ans = f"${ftex(P, Q)}$" + ("" if case == 2 else " (формула не меняется)")
    sol = f"Бескванторная форма: ${ftex(xs, ys)}$; {why} — п. {case} D1.\n"
    if case == 2:
        sol += "".join(f"Высказывание ${tex(e)}$ входит и без отрицания, и с отрицанием; $\\sim{tex(e)}$ повсюду заменяем на "
                       f"${tex(r)}$.\n" for e, r in reps)
    sol += f"Контрольная форма: ${ftex(P, Q)}$."
    return card(level, "T", "iso", "short", "с. 116–117, гл. 7, § 9", "кванторы, разрешимость, контрольная форма", cond,
                ans, sol)


def proc_item(kind):
    """Пункт процедуры с. 120: ('q' — шаг 1 отрицательный, 'n' — контрольная форма не тавтология, 't' — тавтология)."""
    for _ in range(400):
        res = _proc_item(kind)
        try:
            proc_verdict(*res)
            return res
        except RetryError:
            continue
    raise RuntimeError(kind)


def _proc_item(kind):
    for _ in range(400):
        if kind == "q":
            p, q, sb = A2.inst_arg(rnd.choice(["T20", "T21", "T27", "A3"]))
            p2, q2 = rnd.choice(A.mutate(p, q))
            if not q7.ss_theorem(qfree(p2), qfree(q2)):
                return p2, q2, None
        elif kind == "c2":
            p, q, P, Q, reps, case = ctrl_item()
            if case == 2:
                return p, q, (P, Q, reps)
        else:
            if kind == "n":
                p, q = A2.nontaut_item()
            else:
                p, q, sb = A2.inst_arg(rnd.choice(list(A2.ARG)))
            P, Q, reps, case = control(p, q)
            if case == 1:
                return p, q, (P, Q, reps)
    raise RuntimeError(kind)


class RetryError(Exception):
    pass


def dnf_ok(f):
    """Бескванторные части — литералы, их конъюнкции и дизъюнкции (дизъюнктивная нормальная форма) без ∼∼."""
    k = f[0]
    if k == "neg":
        return f[1][0] in ("el",) + q7.QK and (f[1][0] == "el" or dnf_ok(f[1]))
    if k in q7.QK:
        return dnf_ok(f[2])
    if k == "conj":
        return all(dnf_ok(a) and a[0] != "wdis" for a in f[1])
    if k == "wdis":
        return all(dnf_ok(a) for a in f[1])
    return True


def proc_verdict(p, q, info):
    xs, ys = qfree(p), qfree(q)
    if info is None:
        r = A.unprov_reason(p, q)
        return False, f"шаг 1: бескванторная форма ${ftex(xs, ys)}$ недоказуема в $S^s$ — формула недоказуема"
    P, Q, reps = info
    ctl = "контрольная форма совпадает с формулой" if not reps else f"контрольная форма ${ftex(P, Q)}$"
    j = taut_justify(P, Q)
    if j:
        return True, f"шаг 1: ${ftex(xs, ys)}$ доказуема в $S^s$; шаг 2: {ctl}; {j} — формула доказуема"
    cm = q7.countermodel(P, Q, nmax=3)
    if not cm:
        raise RetryError(ftex(P, Q))
    return False, f"шаг 1: ${ftex(xs, ys)}$ доказуема в $S^s$; шаг 2: {ctl}; {A2.cm_text(P, Q, cm)} — не тавтология, формула недоказуема"


PROC = ("Процедура § 9 (с. 120): 1) образовать бескванторную форму $x^* \\vdash y^*$ и установить, доказуема ли она в "
        "$S^s$; если нет — $x \\vdash y$ недоказуема в $S^s_{cq}$; 2) если да — образовать контрольную форму $x^{**} "
        "\\vdash y^{**}$ (D1 § 9) и установить, тавтология ли она (D3 § 7); если да — $x \\vdash y$ доказуема, если нет — "
        "недоказуема.")


def c_proc(level=6):
    kinds = ["q", "n", "t", rnd.choice(["c2", "t", "n"])]
    its = []
    for k in kinds:
        while True:
            p, q, info = proc_item(k)
            try:
                proc_verdict(p, q, info)
                break
            except RetryError:
                continue
        its.append((p, q, info))
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (p, q, info) in enumerate(its):
        v, why = proc_verdict(p, q, info)
        ans.append(f"{L[k]}) {'доказуема' if v else 'недоказуема'}")
        sol.append(f"{L[k]}) {why[0].upper() + why[1:]}.")
    cond = (f"{CONV} Примените к каждой формуле процедуру разрешения § 9 и установите её доказуемость в $S^s_{{cq}}$. "
            f"{PROC}\n\n" + items([f"${ftex(p, q)}$" for p, q, _ in its]))
    return card(level, "C", "open", "short", "с. 116–120, гл. 7, § 9", "кванторы, разрешимость, процедура", cond,
                "; ".join(ans), "\n".join(sol))


def c_proc_diag(level=6):
    its = [proc_item(k) for k in ["q", "n", "t", "t"]]
    rnd.shuffle(its)
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for k, (p, q, info) in enumerate(its):
        v, why = proc_verdict(p, q, info)
        if k in wrong:
            claim = ("недоказуема: контрольная форма не тавтология" if v else
                     "доказуема: бескванторная форма доказуема в $S^s$" if info is not None else
                     "доказуема: контрольная форма совпадает с формулой")
            ans.append(f"{k + 1}: {'доказуема' if v else 'недоказуема'}")
            sol.append(f"{k + 1}. Неверно: {why}.")
        else:
            claim = "доказуема" if v else "недоказуема"
        lines.append(f"{k + 1}. ${ftex(p, q)}$ — {claim}.")
    cond = (f"{CONV} Студент применил процедуру § 9 к четырём формулам; ровно два вывода неверны. Найдите их, назовите "
            f"пропущенный или неверно выполненный шаг процедуры и дайте верный ответ. {PROC}\n\n" + "\n".join(lines))
    return card(level, "E", "vary", "text", "с. 116–120, гл. 7, § 9", "кванторы, разрешимость, диагностика", cond,
                "; ".join(ans), "\n".join(sol) + "\n\nОстальные выводы верны.")


def c_control_diag(level=6):
    for _ in range(500):
        p, q, P, Q, reps, case = ctrl_item()
        others = [t for t in q7.patoms(qfree(p)) | q7.patoms(qfree(q)) if case == 2 and reps and t != reps[0][0]]
        if case == 2 and reps and N(reps[0][0]) in list(H.walk(p)) and others:
            break
    e, r = reps[0]
    old = rnd.choice(sorted(others, key=tex))
    P2 = repl_neg(p, e, old)       # ошибка 1: замена высказыванием, входящим в формулу
    Q2 = q                         # ошибка 2: в заключении замена не сделана
    if N(e) not in list(H.walk(q)):
        Q2 = N(Q) if Q[0] != "neg" else Q[1]
        err2 = ("в заключении добавлено отрицание" if Q[0] != "neg" else "в заключении снято отрицание") + \
            ", хотя D1 меняет только вхождения $\\sim a$"
    else:
        err2 = f"в заключении $\\sim{tex(e)}$ не заменено, а D1 требует замены «повсюду»"
    cond = (f"{CONV} Студент построил контрольную форму (D1 § 9, с. 116–117) формулы ${ftex(p, q)}$:\n\n"
            f"$${ftex(P2, Q2)}$$\n\nНайдите все ошибки и запишите верную контрольную форму (новое элементарное "
            "высказывание получайте, заменяя в заменяемом термин, не связанный в формуле, термином $e$).")
    ans = (f"Две ошибки: $\\sim{tex(e)}$ заменено высказыванием ${tex(old)}$, входящим в формулу; {err2}. Верно: "
           f"${ftex(P, Q)}$.")
    sol = (f"D1 § 9, п. 2: $y^*$ — тавтология или $x^*$ — противоречие, поэтому формула меняется; $\\sim a$ заменяется "
           "«любым элементарным высказыванием, не входящим в $x \\vdash y$», и «повсюду».\n"
           f"1. ${tex(old)}$ в формулу уже входит — замена им склеивает разные высказывания (а MT2 § 9 требует, чтобы в "
           "контрольной форме ни одно высказывание не входило вместе с отрицанием, и MT1 опирается на независимость "
           "нового высказывания).\n"
           f"2. {err2[0].upper() + err2[1:]}.\nВерно: ${ftex(P, Q)}$.")
    return card(level, "E", "vary", "text", "с. 116–117, гл. 7, § 9", "кванторы, разрешимость, диагностика", cond, ans,
                sol)


def c_mt2_9(level=5):
    p, q, P, Q, reps, case = ctrl_item()
    while case != 2:
        p, q, P, Q, reps, case = ctrl_item()
    xs, ys = qfree(P), qfree(Q)
    assert not q7.is_taut1(ys) and not q7.is_contr(xs)
    cond = (f"{CONV} Контрольная форма формулы ${ftex(p, q)}$ есть ${ftex(P, Q)}$. Проверьте на ней утверждение MT2 § 9 "
            "(с. 117): если $x^{**} \\vdash y^{**}$ — бескванторная форма контрольной формы, то $y^{**}$ не тавтология, "
            "$x^{**}$ не противоречие, $x^{**}$ не тавтология и $y^{**}$ не противоречие. Объясните, почему так будет "
            "всегда.")
    ans = f"$x^{{**}} = {tex(xs)}$, $y^{{**}} = {tex(ys)}$: все четыре условия выполнены."
    sol = (f"$x^{{**}} = {tex(xs)}$, $y^{{**}} = {tex(ys)}$. Ни одно элементарное высказывание не входит в них вместе с "
           "отрицанием (п. 2 D1 заменил $\\sim a$ новым высказыванием), а конъюнкция и дизъюнкция литералов без "
           "противоположных пар не бывает ни тавтологией, ни противоречием — значения подбираются по каждому литералу "
           "отдельно (MT2, с. 117).")
    return card(level, "C", "vary", "short", "с. 116–117, гл. 7, § 9", "кванторы, разрешимость, контрольная форма", cond,
                ans, sol)


def c_firststep(level=6):
    its = []
    while len(its) < 4:
        k = ["n", "t", "n", "t"][len(its)]
        p, q, info = proc_item(k)
        its.append((p, q, info))
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (p, q, info) in enumerate(its):
        v, why = proc_verdict(p, q, info)
        ans.append(f"{L[k]}) {'доказуема' if v else 'недоказуема'}")
        sol.append(f"{L[k]}) {why[0].upper() + why[1:]}.")
    cond = (f"{CONV} У всех формул ниже бескванторная форма доказуема в $S^s$, так что по MT3 § 3 их недоказуемость не "
            f"установить. Исследуйте доказуемость каждой в $S^s_{{cq}}$ по процедуре § 9 и объясните, почему первого шага "
            f"процедуры мало. {PROC}\n\n" + items([f"${ftex(p, q)}$" for p, q, _ in its]))
    return card(level, "C", "open", "short", "с. 100, 116–120, гл. 7, § 3, 9", "кванторы, разрешимость", cond,
                "; ".join(ans), "\n".join(sol) + "\n\nПервый шаг отбрасывает кванторные группы и не различает $\\forall$ и "
                "$\\exists$; это делает второй шаг (интерпретация § 7).")


def c_nat9(level=6):
    s, p, q = rnd.choice([
        ("«Все $a$ суть $b$. Следовательно, всякое $a$ есть $b$ или не есть $b$»", ALL("a", ab), ALL("a", W(ab, N(ab)))),
        ("«Некоторые $a$ суть $b$, а некоторые $a$ не суть $b$. Следовательно, все $a$ суть $b$ или не суть $b$»",
         C(EX("a", ab), EX("a", N(ab))), ALL("a", W(ab, N(ab)))),
        ("«Все $a$ суть $b$, и некоторые $a$ не суть $b$. Следовательно, все $a$ суть $b$»", C(ALL("a", ab), EX("a", N(ab))),
         ALL("a", ab))])
    P, Q, reps, case = control(p, q)
    v, why = proc_verdict(p, q, (P, Q, reps))
    cond = (f"{CONV} Запишите рассуждение {s} формулой следования ($(a \\leftarrow b)$ — «$a$ есть $b$») и примените к ней "
            f"процедуру § 9: постройте бескванторную и контрольную формы и установите доказуемость. {PROC}")
    return card(level, "C", "open", "short", "с. 116–120, гл. 7, § 9", "кванторы, разрешимость, формализация", cond,
                f"${ftex(p, q)}$; контрольная форма ${ftex(P, Q)}$; {'доказуема' if v else 'недоказуема'}.",
                f"Формула ${ftex(p, q)}$. " + why[0].upper() + why[1:] + ".", form="nat")


# ================================================================ планы по номерам
KEEP = {
    # § 8: 3–36 — занятие 53, 37–57 — 54
    "07.08-007": ("07.08-036", None), "07.08-013": ("07.08-038", None), "07.08-020": ("07.08-043", None),
    "07.08-027": ("07.08-047", None), "07.08-034": ("07.08-055", None),
    "07.08-041": ("07.08-041", None), "07.08-048": ("07.08-048", None), "07.08-055": ("07.08-057", None),
    # § 9: 1–13 — занятие 54, 14–42 — 55
    "07.09-005": ("07.09-026", None), "07.09-011": ("07.09-035", None),
    "07.09-020": ("07.09-037", None), "07.09-030": ("07.09-038", None), "07.09-039": ("07.09-041", None),
}


def plan():
    P = {}
    kept8 = {int(k.split("-")[1]) for k in KEEP if k.startswith("07.08")}
    rot8 = [c_case_table, c_basis, c_mtpat, c_reduce, c_case_diag, c_mt6, c_ik, lambda: A2.c_badstep6(),
            lambda: c_deriv8(7), c_case_table, lambda: c_mtpat(diag=True), c_mt7check,
            lambda: A.c_complete("с. 99–110, гл. 7, § 2, 6, 8", maker=A2.deriv6, sch=A2.SCH6), lambda: c_basis(diag=True),
            c_case_diag, c_nat8]
    i = 0
    for k in range(1, 58):
        if k in kept8:
            continue
        P[f"07.08-{k:03d}"] = rot8[i % len(rot8)]
        i += 1
    kept9 = {int(k.split("-")[1]) for k in KEEP if k.startswith("07.09")}
    rot9 = [c_control, c_proc, c_control_diag, lambda: c_ik(5, 9), c_proc_diag, c_mt2_9,
            c_firststep, lambda: A2.c_deriv6(src="с. 99–120, гл. 7, § 2, 6, 9", level=7), c_proc, lambda: A2.c_badstep6(),
            c_control, c_nat9, lambda: A2.c_diag6(), c_proc_diag,
            lambda: A.c_complete("с. 99–120, гл. 7, § 2, 6, 9", maker=A2.deriv6, sch=A2.SCH6), c_firststep]
    i = 0
    for k in range(1, 43):
        if k in kept9:
            continue
        P[f"07.09-{k:03d}"] = rot9[i % len(rot9)]
        i += 1
    return P
