"""Задачи гл. 7, § 6–9, для hard07.py: теоремные схемы и метатеоремы § 6, главная интерпретация § 7, полнота § 8,
контрольная форма и разрешимость § 9."""
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
from hard07_a import CONV, L, card, items  # noqa: E402
from q7 import ALL, C, EL, EX, N, W, free_in, ftex, qfree, tex  # noqa: E402

rnd = random.Random(1970_0706)
ab, ac, ad, cb, cd, db, ba, bc = A.ab, A.ac, A.ad, A.cb, A.cd, A.db, A.ba, A.bc
AX6 = H.AX2 + H.T6USE
SCH6 = (A.SCH2 + " Кроме того, разрешены теоремные схемы § 6 (с. 102–106) с их номерами книги: T1 $\\sim(\\forall a)x "
        "\\vdash (\\exists a)\\sim x$; T2 $(\\exists a)x \\vdash \\sim(\\forall a)\\sim x$; T3 $\\sim x \\vdash \\sim(\\forall "
        "a)x$; T4 $\\sim(\\exists a)x \\vdash \\sim x$; T14 $(\\forall a)(\\forall b)x \\vdash (\\forall b)(\\forall a)x$; "
        "T15 $(\\exists a)(\\forall b)x \\vdash (\\forall b)(\\exists a)x$; T16 $(\\exists a)(\\exists b)x \\vdash "
        "(\\exists b)(\\exists a)x$; T17 $x \\vdash (\\forall a)x$ и T18 $(\\exists a)x \\vdash x$, где $a$ не входит "
        "свободно в $x$; T19 $(\\forall a)x(\\forall a)y \\vdash (\\forall a)(xy)$; T20 — обратная; T21 $(\\exists a)(xy) "
        "\\vdash (\\exists a)x(\\exists a)y$; T22 $(\\exists a)(x \\vee y) \\vdash (\\exists a)x \\vee (\\exists a)y$; T23 — "
        "обратная; T24 $(\\forall a)x \\vee (\\forall a)y \\vdash (\\forall a)(x \\vee y)$; T27 $(\\forall a)x \\vdash "
        "(\\exists a)x$; T29 $(\\forall a)(xy) \\vdash (\\forall a)x(\\exists a)y$; T30 $(\\forall a)(xy) \\vdash "
        "(\\exists a)x(\\forall a)y$; T32 $(\\forall a)(x \\vee y) \\vdash (\\exists a)x \\vee (\\forall a)y$; T37 "
        "$\\sim(\\forall a)\\sim x \\vdash (\\exists a)x$ и др.")
SRC6 = "с. 99–106, гл. 7, § 2, 6"

# ================================================================ доводы «при любом n» (D2–D3 § 7)
ARG = {
    "A3": "посылка истинна, если истинны все $x(ia)$ и некоторое $y(ja)$; тогда истинен член $x(ja)y(ja)$ дизъюнкции "
          "заключения",
    "A4": "пусть истинны все $x(ia) \\vee y(ia)$; если истинны все $x(ia)$, истинна конъюнкция для $(\\forall a)x$; иначе "
          "при некотором $j$ $x(ja) = 0$, тогда $y(ja) = 1$, и истинна дизъюнкция для $(\\exists a)y$",
    "A6": "форма заключения $\\sim(\\sim x(1a) \\vee \\ldots \\vee \\sim x(na))$ по законам де Моргана равнозначна "
          "$x(1a) \\cdot \\ldots \\cdot x(na)$ — форме посылки",
    "A7": "форма посылки $\\sim(\\sim x(1a) \\vee \\ldots \\vee \\sim x(na))$ по законам де Моргана равнозначна "
          "$x(1a) \\cdot \\ldots \\cdot x(na)$ — форме заключения",
    "T1": "$\\sim(x(1a) \\cdot \\ldots \\cdot x(na))$ по законам де Моргана равнозначна $\\sim x(1a) \\vee \\ldots \\vee "
          "\\sim x(na)$",
    "T2": "$x(1a) \\vee \\ldots \\vee x(na)$ равнозначна $\\sim(\\sim x(1a) \\cdot \\ldots \\cdot \\sim x(na))$",
    "T37": "$\\sim(\\sim x(1a) \\cdot \\ldots \\cdot \\sim x(na))$ равнозначна $x(1a) \\vee \\ldots \\vee x(na)$",
    "T19": "обе части — конъюнкция всех $x(ia)$ и $y(ia)$, лишь в другом порядке",
    "T20": "обе части — конъюнкция всех $x(ia)$ и $y(ia)$, лишь в другом порядке",
    "T21": "если истинен член $x(ja)y(ja)$, то истинны $x(ja)$ и $y(ja)$, а с ними обе дизъюнкции заключения",
    "T22": "обе части — дизъюнкция всех $x(ia)$ и $y(ia)$, лишь в другом порядке",
    "T23": "обе части — дизъюнкция всех $x(ia)$ и $y(ia)$, лишь в другом порядке",
    "T24": "если истинны все $x(ia)$ или все $y(ia)$, то истинен каждый член $x(ia) \\vee y(ia)$",
    "T25": "если истинны все $x(ia)$, истинен член $x(1a) \\vee y(1a)$; если истинно некоторое $y(ja)$, истинен член "
           "$x(ja) \\vee y(ja)$",
    "T26": "если истинно некоторое $x(ja)$, истинен член $x(ja) \\vee y(ja)$; если истинны все $y(ia)$, истинен член "
           "$x(1a) \\vee y(1a)$",
    "T27": "конъюнкция $x(1a) \\cdot \\ldots \\cdot x(na)$ ($n \\geq 1$) влечёт свой член $x(1a)$, а он — дизъюнкцию",
    "T29": "из конъюнкции всех $x(ia)y(ia)$ следуют все $x(ia)$ и член $y(1a)$ дизъюнкции",
    "T30": "из конъюнкции всех $x(ia)y(ia)$ следуют член $x(1a)$ дизъюнкции и все $y(ia)$",
    "T32": "пусть истинны все $x(ia) \\vee y(ia)$; если истинны все $y(ia)$, истинна конъюнкция для $(\\forall a)y$; иначе "
           "$y(ja) = 0$ при некотором $j$, тогда $x(ja) = 1$ — истинна дизъюнкция для $(\\exists a)x$",
    "T34": "истинен член $x(1a) \\vee y(1a)$, а с ним одна из дизъюнкций заключения",
    "T35": "если истинны все $x(ia)$ или все $y(ia)$, истинен член $x(1a) \\vee y(1a)$",
    "T36": "из истинности всех $x(ia)$ и всех $y(ia)$ следует истинность члена $x(1a)y(1a)$",
    "T42": "если истинны $x(ja)$ и все $y(ia)$, истинен член $x(ja)y(ja)$",
    "T14": "обе части — конъюнкция всех $x(ia, jb)$ в разном порядке",
    "T16": "обе части — дизъюнкция всех $x(ia, jb)$ в разном порядке",
    "T15": "если при некотором $i$ истинны все $x(ia, jb)$, то для каждого $j$ истинен член $x(ia, jb)$ дизъюнкции по $i$",
    "T38": "из истинности всех $x(ia, jb)$ следует, что для каждого $j$ истинен член $x(1a, jb)$ дизъюнкции по $i$",
    "T39": "из истинности всех $x(ia, jb)$ следует истинность конъюнкции по $i$ при $j = 1$ — члена дизъюнкции по $j$",
    "T40": "из истинности всех $x(ia, jb)$ следует истинность $x(1a, 1b)$ — члена двойной дизъюнкции",
    "T41": "из конъюнкции по $i$ дизъюнкций по $j$ берём $i = 1$: истинен некоторый $x(1a, jb)$ — член двойной "
           "дизъюнкции",
}
TWO = {"T14", "T15", "T16", "T38", "T39", "T40", "T41"}


def sch_of(name):
    return q7.SCQ.get(name) or q7.T6[name]


def clean_inst(p, q):
    """Без замыкания по п. 1 D2 и без вырожденных групп — тогда доводы ARG верны дословно."""
    return (len(q7.closures(p, q)) == 1 and q7.closures(p, q)[0] == (p, q)
            and not any(q7.degenerate(g) for g in q7.groups(p) + q7.groups(q)))


def inst_arg(name, tries=300):
    for _ in range(tries):
        if name in TWO:
            X = rnd.choice([ab, C(ab, cb), W(ab, N(EL("c", "b"))), C(N(ab), EL("a", "c")), W(ba, EL("a", "c"))])
            if not ("a" in q7.terms(X) and "b" in q7.terms(X)):
                continue
            sb = {"x": X, "@a": "a", "@b": "b"}
        else:
            X, Y = A.two()
            X = X if free_in("a", X) else C(X, ac)
            Y = Y if free_in("a", Y) else W(Y, ad)
            if X == Y:
                continue
            sb = {"x": X, "y": Y, "@a": "a"}
        p, q = q7.build_inst(sch_of(name), sb)
        if clean_inst(p, q) and q7.restrict_ok(p, q):
            assert q7.qtaut(p, q, nmax=3), (name, ftex(p, q))
            return p, q, sb
    raise RuntimeError(name)


def sub_text(sb):
    return ", ".join(f"${k}$ := ${tex(v)}$" for k, v in sb.items() if not k.startswith("@"))


def taut_text(name, sb):
    return (f"пример {name} ({sub_text(sb)}); при любом числе отмеченных терминов {ARG[name]} — формула тавтология "
            "(D3 § 7, с. 105)")


def cm_text(p, q, cm=None):
    cm = cm or q7.countermodel(p, q)
    (P, Q), n, ip, iq, e = cm
    close = "" if (P, Q) == (p, q) else f"по п. 1 D2 формула заменяется на ${ftex(P, Q)}$; "
    vals = q7.env_tex(e)
    return (f"{close}при {q7.n_text(n)} интерпретационная форма — ${ftex(ip, iq)}$; при {vals} посылка 1, "
            "заключение 0")


# ================================================================ § 6: выводы с теоремными схемами
def nice(f):
    for g in H.walk(f):
        if g[0] in q7.QK and g[2][0] in q7.QK and g[2][1] == g[1]:
            return False
        if g[0] in q7.QK and q7.degenerate(g):
            return False
    return True


def prem6():
    X, Y = A.two()
    Z = rnd.choice(A.NO_A)
    return rnd.choice([
        ALL("a", C(X, Y)), ALL("a", W(X, Y)), EX("a", W(X, Y)), C(ALL("a", X), ALL("a", Y)), W(ALL("a", X), EX("a", Y)),
        N(ALL("a", N(X))), N(EX("a", C(X, Y))), ALL("a", ALL("b", C(ab, cb))), EX("a", ALL("b", W(ab, N(db)))),
        ALL("a", EX("b", C(ab, N(cb)))), C(EX("a", X), ALL("a", Y)), N(ALL("a", X)), EX("a", C(X, Y))])


def deriv6(least=8, most=12):
    for _ in range(3000):
        P = prem6()
        if not nice(P):
            continue
        lines = H.build(P, rnd.choice([least + 2, most, most + 3]), AX6, rnd, maxsize=44)
        if not lines:
            continue
        lines = H.prune(lines)
        key = ftex(lines[-1][0], lines[-1][1])
        if key in H.SEEN or not all(nice(b) for _, b, _ in lines) or q7.size(lines[-1][1]) < 10:
            continue
        names = {w for _, _, w in lines if isinstance(w, str)}
        if len([n for n in names if n.startswith("T")]) < 2:
            continue
        if H.good(lines, AX6, least, most, need_q=3):
            H.SEEN.add(key)
            return lines
    raise RuntimeError("нет вывода § 6")


def c_deriv6(src=SRC6, level=None):
    lines = deriv6()
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} Выведите в $S^s_{{cq}}$ формулу\n\n$${ftex(a, b)}$$\n\n{SCH6}")
    used = sorted({w for _, _, w in lines if isinstance(w, str)}, key=lambda s: (s[0], int(s[1:])))
    ans = f"Например, вывод в {len(lines)} строк (см. решение); схемы: {', '.join(used)}."
    return card(level or (7 if len(lines) >= 10 else 6), "D", "open", "proof", src, "кванторы, вывод, теоремные схемы",
                cond, ans, H.show(lines))


def c_complete6():
    return A.c_complete(SRC6, maker=deriv6, sch=SCH6)


WHY6 = dict(A.WHY2)
WHY6.update({"T19": "T19 соединяет $(\\forall a)x(\\forall a)y$ в $(\\forall a)(xy)$, T20 — обратная схема",
             "T20": "T20 разделяет $(\\forall a)(xy)$ на $(\\forall a)x(\\forall a)y$, T19 — обратная схема",
             "T21": "T21 — о конъюнкции под $(\\exists a)$, T22 — о дизъюнкции",
             "T22": "T22 — о дизъюнкции под $(\\exists a)$, T21 — о конъюнкции",
             "T1": "T1 — $\\sim(\\forall a)x \\vdash (\\exists a)\\sim x$, T2 — $(\\exists a)x \\vdash \\sim(\\forall a)\\sim x$",
             "T2": "T2 — $(\\exists a)x \\vdash \\sim(\\forall a)\\sim x$, T1 — $\\sim(\\forall a)x \\vdash (\\exists a)\\sim x$",
             "T14": "T14 переставляет два квантора общности, T15 — $(\\exists a)(\\forall b)$ в $(\\forall b)(\\exists a)$",
             "T15": "T15 — $(\\exists a)(\\forall b)x \\vdash (\\forall b)(\\exists a)x$, T14 — о двух кванторах общности",
             "T27": "T27 — $(\\forall a)x \\vdash (\\exists a)x$, A1 — $(\\forall a)x \\vdash x$",
             "T29": "T29 даёт $(\\forall a)x(\\exists a)y$, T30 — $(\\exists a)x(\\forall a)y$",
             "T30": "T30 даёт $(\\exists a)x(\\forall a)y$, T29 — $(\\forall a)x(\\exists a)y$",
             "T32": "T32 — $(\\forall a)(x \\vee y) \\vdash (\\exists a)x \\vee (\\forall a)y$, A4 — $(\\forall a)x \\vee "
                    "(\\exists a)y$",
             "T23": "T23 вносит $(\\exists a)$ в дизъюнкцию, T24 — о кванторе общности",
             "T24": "T24 — $(\\forall a)x \\vee (\\forall a)y \\vdash (\\forall a)(x \\vee y)$, T23 — о кванторе "
                    "существования"})


def c_diag6():
    return A.c_diag(SRC6, maker=deriv6, allowed=AX6, whys=WHY6, sch=SCH6)


def c_badstep6(level=6):
    for _ in range(3000):
        lines = deriv6(6, 10)
        P = lines[-1][0]
        facts = [(n, b) for n, (a, b, w) in enumerate(lines, 1) if a == P]
        cands = [(n, bm) for n, q in facts for bm in H.bad_moves(q, AX6) if bm[2] in ("T18bad", "T15bad", "A4bad",
                                                                                     "A3bad", "A5bad")]
        if not cands:
            continue
        n, (lab, r, kind) = rnd.choice(cands)
        q = lines[n - 1][1]
        bad = H.prune(list(lines) + [(q, r, lab), (P, r, ("tr", n, len(lines) + 1))])
        k = next(i for i, x in enumerate(bad, 1) if x == (q, r, lab))
        errs = q7.check(bad, AX6)
        cm = q7.countermodel(P, r, nmax=2)
        if len(errs) == 1 and errs[0].startswith(f"шаг {k}:") and cm and len(bad) >= 6 and k < len(bad):
            break
    else:
        raise RuntimeError("нет ошибочного шага § 6")
    cond = (f"{CONV} Студент вывел формулу ${ftex(P, r)}$. Найдите неверный шаг, назовите нарушенное условие схемы и "
            f"покажите значениями (интерпретационная форма § 7), что последняя строка не тавтология. {SCH6}\n\n"
            f"{H.show(bad)}")
    ans = f"Шаг {k}: {H.BAD_SHORT[kind]}; формула последней строки не тавтология."
    sol = (f"Шаг {k}: ${ftex(q, r)}$ [{lab}] — {H.BAD_WHY[kind]}. Остальные шаги верны.\n"
           f"Формула ${ftex(P, r)}$: {cm_text(P, r, cm)} — не тавтология (D3 § 7, с. 105), так что ошибка не "
           "исправляется другой ссылкой.")
    return card(level, "E", "vary", "text", "с. 99–106, гл. 7, § 2, 6–7", "кванторы, вывод, диагностика", cond, ans,
                sol)


NEAR6 = [  # (имя схемы, на которую ссылается студент, построитель неверной формулы, что мешает)
    ("T21", lambda X, Y: (C(EX("a", X), EX("a", Y)), EX("a", C(X, Y))),
     "это обращение T21; T21 идёт от $(\\exists a)(xy)$ к $(\\exists a)x(\\exists a)y$, а не наоборот"),
    ("T27", lambda X, Y: (EX("a", X), ALL("a", X)), "это обращение T27; от $(\\exists a)x$ к $(\\forall a)x$ можно "
     "перейти лишь по A5, если $a$ не входит свободно в $x$"),
    ("T24", lambda X, Y: (ALL("a", W(X, Y)), W(ALL("a", X), ALL("a", Y))), "это обращение T24; из "
     "$(\\forall a)(x \\vee y)$ следует лишь $(\\forall a)x \\vee (\\exists a)y$ (A4)"),
    ("T36", lambda X, Y: (EX("a", C(X, Y)), C(ALL("a", X), ALL("a", Y))), "это обращение T36; T36 идёт от "
     "$(\\forall a)x(\\forall a)y$ к $(\\exists a)(xy)$"),
    ("T22", lambda X, Y: (EX("a", W(X, Y)), W(ALL("a", X), EX("a", Y))),
     "в T22 в заключении оба члена — с $(\\exists a)$: $(\\exists a)x \\vee (\\exists a)y$"),
]


def c_near6(level=5):
    for _ in range(500):
        name, mk, why = rnd.choice(NEAR6)
        X, Y = A.two()
        if not (free_in("a", X) and free_in("a", Y) and X != Y):
            continue
        p, q = mk(X, Y)
        cm = q7.countermodel(p, q, nmax=2)
        if cm and q7.inst_of(sch_of(name), p, q) is None:
            break
    cond = (f"{CONV} Студент: «Формула ${ftex(p, q)}$ — пример {name} (§ 6, с. 104), значит, она доказуема в $S^s_{{cq}}$». "
            f"Найдите ошибку и выясните значениями (интерпретационная форма § 7, с. 105), тавтология ли эта формула. "
            f"{name}: ${q7.T6_TEX[name]}$.")
    ans = f"Не пример {name}: {why}; формула не тавтология (значения — в решении)."
    sol = (f"1. {why[0].upper() + why[1:]}; другой подстановки нет — формула не пример {name}.\n"
           f"2. {cm_text(p, q, cm)[0].upper() + cm_text(p, q, cm)[1:]}: формула не тавтология (D3 § 7, с. 105), и по "
           "процедуре § 9 (с. 120) она недоказуема.")
    return card(level, "E", "vary", "short", "с. 104–105, гл. 7, § 6–7", "кванторы, теоремные схемы, почти-пример",
                cond, ans, sol)


def atoms_set(f):
    return q7.patoms(qfree(f))


def c_mt6(level=6):
    """MT2, MT*1, MT*2 § 6: применимость (множества элементарных высказываний совпадают)."""
    its = []
    names = rnd.sample(["T20", "T21", "T22", "T27", "T29", "T32", "A3", "A4", "T19", "T24"], 3)
    for nm in names:
        p, q, sb = inst_arg(nm)
        its.append((p, q, nm))
    # одна теорема S^s с несовпадающими множествами
    X, Y = A.two()
    Z = rnd.choice(A.NO_A)
    its.append((C(ALL("a", X), Z), ALL("a", X), "S^s"))
    rnd.shuffle(its)
    mt = rnd.choice(["MT2", "MT*1", "MT*2"])
    ans, sol = [], []
    for k, (p, q, nm) in enumerate(its):
        eq = atoms_set(p) == atoms_set(q)
        res = {"MT2": (N(q), N(p)), "MT*1": (N(ALL("a", q)), N(ALL("a", p))), "MT*2": (N(EX("a", q)), N(EX("a", p)))}[mt]
        src = "теорема $S^s$" if nm == "S^s" else f"пример {nm}"
        if eq:
            assert q7.qtaut(*res, nmax=2)
            ans.append(f"{L[k]}) ${ftex(*res)}$")
            sol.append(f"{L[k]}) ({src}) Элементарные высказывания посылки и заключения: "
                       + ", ".join(f"${tex(e)}$" for e in sorted(atoms_set(p), key=tex)) +
                       f" — множества совпадают; по {mt} доказуема ${ftex(*res)}$.")
        else:
            extra = sorted(atoms_set(p) - atoms_set(q), key=tex)
            ans.append(f"{L[k]}) неприменима")
            sol.append(f"{L[k]}) ({src}) В посылку входит " + ", ".join(f"${tex(e)}$" for e in extra) +
                       f", которого нет в заключении: множества не совпадают, {mt} неприменима (и формула "
                       f"${ftex(*res)}$ нарушала бы непарадоксальность — MT1 § 3).")
    stmt = {"MT2": "если $x \\vdash y$ доказуема и множества элементарных высказываний $x$ и $y$ совпадают, то "
                   "$\\sim y \\vdash \\sim x$ доказуема",
            "MT*1": "если $x \\vdash y$ доказуема и множества элементарных высказываний $x$ и $y$ совпадают, то "
                    "$\\sim(\\forall a)y \\vdash \\sim(\\forall a)x$ доказуема",
            "MT*2": "при том же условии доказуема $\\sim(\\exists a)y \\vdash \\sim(\\exists a)x$"}[mt]
    cond = (f"{CONV} {mt} § 6 (с. 102–103): {stmt}. Каждая формула ниже доказуема в $S^s_{{cq}}$. Для каждой проверьте "
            f"условие {mt} и, если оно выполнено, запишите формулу, которую даёт {mt}; если нет — объясните, почему "
            "метатеорему применять нельзя.\n\n" + items([f"${ftex(p, q)}$" for p, q, _ in its]))
    return card(level, "C", "vary", "short", "с. 102–103, гл. 7, § 6", "кванторы, метатеоремы § 6", cond,
                "; ".join(ans), "\n".join(sol))


def c_series6(level=6):
    its = []
    names = rnd.sample(["T15", "T20", "T22", "T29", "T32", "T34", "T41", "T42", "T24", "A4"], 3)
    for nm in names:
        p, q, sb = inst_arg(nm)
        its.append((p, q, ("prov", nm, sb)))
    while len(its) < 5:
        p, q, sb = inst_arg(rnd.choice(["T20", "T21", "T27", "T19"]))
        for p2, q2 in A.mutate(p, q):
            r = A.unprov_reason(p2, q2)
            if r and len(tex(p2)) + len(tex(q2)) <= 130:
                its.append((p2, q2, ("no", r)))
                break
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (p, q, info) in enumerate(its):
        if info[0] == "prov":
            ans.append(f"{L[k]}) доказуема ({info[1]})")
            sol.append(f"{L[k]}) Доказуема: пример {info[1]} при {sub_text(info[2])} (с. 103–106).")
        else:
            ans.append(f"{L[k]}) недоказуема ({info[1][0]} § 3)")
            sol.append(f"{L[k]}) Недоказуема: {info[1][1]}.")
    cond = (f"{CONV} Исследуйте доказуемость в $S^s_{{cq}}$ каждой формулы: для доказуемой назовите теоремную или "
            f"аксиомную схему и замену, для недоказуемой — основание из § 3. {A.CRIT3}\n\n"
            + items([f"${ftex(p, q)}$" for p, q, _ in its]))
    return card(level, "C", "open", "short", SRC6, "кванторы, теоремные схемы, доказуемость", cond, "; ".join(ans),
                "\n".join(sol))


NAT6 = [
    ("Неверно, что все $a$ суть $b$. Следовательно, некоторые $a$ не суть $b$", N(ALL("a", ab)), EX("a", N(ab)), "T1"),
    ("Все $a$ суть $b$ и все $a$ суть $c$. Следовательно, все $a$ суть $b$ и $c$", C(ALL("a", ab), ALL("a", ac)),
     ALL("a", C(ab, ac)), "T19"),
    ("Некоторые $a$ суть $b$ или $c$. Следовательно, некоторые $a$ суть $b$ или некоторые $a$ суть $c$",
     EX("a", W(ab, ac)), W(EX("a", ab), EX("a", ac)), "T22"),
    ("Некоторое $a$ есть $b$ при любом $b$. Значит, при любом $b$ некоторое $a$ есть $b$", EX("a", ALL("b", ab)),
     ALL("b", EX("a", ab)), "T15"),
]


def c_nat6(k, level=6):
    s, p, q, nm = NAT6[k]
    d = H.Der(p)
    i = d.step(0, q, nm)
    extra = {"T1": lambda: d.step(i, N(ALL("a", N(N(ab)))), "T2"),
             "T19": lambda: d.step(i, C(ALL("a", ab), ALL("a", ac)), "T20"),
             "T22": lambda: d.step(i, EX("a", W(ab, ac)), "T23"),
             "T15": lambda: d.step(i, EX("b", EX("a", ab)), "A2")}[nm]
    extra()
    lines = d.lines
    assert not q7.check(lines, AX6)
    cond = (f"{CONV} $(a \\leftarrow b)$ читается «$a$ есть $b$» (с. 98). Запишите рассуждение «{s}» формулой следования, "
            "выведите её в $S^s_{cq}$ и выясните, можно ли из заключения вывести посылку обратно (одной схемой § 6); "
            f"ответ проверьте выводом. {SCH6}")
    ans = f"${ftex(p, q)}$ — пример {nm}; " + {"T1": "обратно — лишь $\\sim(\\forall a)\\sim\\sim(a \\leftarrow b)$ по T2 "
                                                     "(до $\\sim(\\forall a)(a \\leftarrow b)$ — ещё через R1 и MT*1)",
                                               "T19": "обратно — по T20", "T22": "обратно — по T23",
                                               "T15": "обращение T15 в § 6 не доказывается; из заключения следует "
                                                      "$(\\exists b)(\\exists a)(a \\leftarrow b)$ (A2)"}[nm] + "."
    return card(level, "F", "transfer", "proof", SRC6, "кванторы, формализация", cond, ans, H.show(lines), form="nat")


# ================================================================ § 7: главная интерпретация
def stmt7():
    return rnd.choice([
        (EX("a", C(ab, ac)), C(EX("a", ab), ALL("a", ac))),
        (ALL("a", W(ab, ac)), W(ALL("a", ab), ALL("a", ac))),
        (C(EX("a", ab), EX("a", ac)), EX("a", C(ab, ac))),
        (ALL("a", EX("b", ab)), EX("b", ALL("a", ab))),
        (EX("a", ab), ALL("a", ab)),
        (W(EX("a", ab), ALL("a", ac)), ALL("a", W(ab, ac))),
        (ALL("a", W(ab, N(ac))), W(EX("a", ab), ALL("a", N(ac)))),
        (EX("b", ALL("a", W(ab, cb))), ALL("a", EX("b", ab))),
        (C(ALL("a", W(ab, ac)), EX("a", N(ab))), ALL("a", ac)),
        (N(ALL("a", C(ab, ac))), EX("a", N(ab))),
        (ALL("a", EX("b", C(ab, cb))), EX("b", C(ALL("a", ab), cb))),
        (EX("a", W(ab, C(ac, ad))), C(EX("a", W(ab, ac)), ALL("a", W(ab, ad)))),
    ])


def c_interp7(level=5):
    for _ in range(200):
        p, q = stmt7()
        n = {t: 2 for t in q7.bound_terms(p) | q7.bound_terms(q)}
        ip, iq = q7.interp(p, n), q7.interp(q, n)
        if len(tex(ip)) + len(tex(iq)) < 260 and len(q7.closures(p, q)) == 1:
            break
    bad = [e for e in q7.penvs(ip, iq) if q7.pval(ip, e) and not q7.pval(iq, e)]
    cond = (f"{CONV} Постройте интерпретационную форму (D2 § 7, с. 105) формулы ${ftex(p, q)}$ при двух отмеченных "
            "терминах для каждого связанного термина ($1a, 2a$; $1b, 2b$) и исследуйте, тавтология ли эта форма; если нет, "
            "укажите значения, при которых посылка 1, а заключение 0. D2: $(\\forall b)z$ заменяется конъюнкцией "
            "$z(1b) \\cdot \\ldots \\cdot z(nb)$, $(\\exists b)z$ — дизъюнкцией $z(1b) \\vee \\ldots \\vee z(nb)$; $z(ib)$ "
            "получается из $z$ заменой $b$ на $ib$ везде, где $b$ входит свободно в $z$.")
    form = f"${ftex(ip, iq)}$"
    if bad:
        e = bad[0]
        ans = f"{form}; не тавтология: {q7.env_tex(e)}."
        sol = (f"Форма: {form}.\nПри {q7.env_tex(e)} посылка 1, заключение 0. Значит, и сама формула не тавтология "
               "(D3 § 7: тавтологией должна быть каждая интерпретационная форма).")
    else:
        ans = f"{form}; при двух отмеченных терминах — тавтология."
        sol = (f"Форма: {form}.\nПеребор значений элементарных высказываний формы не даёт набора, где посылка 1, а "
               "заключение 0. (Это ещё не значит, что формула — тавтология: D3 требует тавтологичности при любом числе "
               "отмеченных терминов.)")
    return card(level, "V", "iso", "short", "с. 105, гл. 7, § 7", "кванторы, интерпретация", cond, ans, sol)


def taut_item():
    nm = rnd.choice(["A3", "A4", "T15", "T20", "T21", "T22", "T24", "T27", "T29", "T32", "T34", "T36", "T41", "T42",
                     "A6", "T1", "T37"])
    p, q, sb = inst_arg(nm)
    return p, q, nm, sb


def nontaut_item():
    for _ in range(500):
        nm = rnd.choice(["T21", "T27", "T24", "T15", "T36", "T41", "T29", "A4"])
        p, q, sb = inst_arg(nm)
        if nm == "A4":
            p2, q2 = p, W(ALL("a", sb["x"]), ALL("a", sb["y"]))
        else:
            p2, q2 = q, p
        if q7.restrict_ok(p2, q2) and not q7.qtaut(p2, q2, nmax=2) and len(tex(p2)) + len(tex(q2)) < 140:
            return p2, q2
    raise RuntimeError("нет нетавтологии")


def c_series7(level=6):
    its = [("t",) + taut_item(), ("t",) + taut_item(), ("n",) + nontaut_item(), ("n",) + nontaut_item()]
    rnd.shuffle(its)
    ans, sol = [], []
    for k, it in enumerate(its):
        if it[0] == "t":
            _, p, q, nm, sb = it
            ans.append(f"{L[k]}) тавтология")
            sol.append(f"{L[k]}) Тавтология: {taut_text(nm, sb)}.")
        else:
            _, p, q = it
            cm = q7.countermodel(p, q)
            ans.append(f"{L[k]}) не тавтология (при {q7.n_text(cm[1])})")
            sol.append(f"{L[k]}) Не тавтология: {cm_text(p, q, cm)}.")
    cond = (f"{CONV} Для каждой формулы исследуйте, тавтология ли она по главной (косвенной) интерпретации § 7 (с. 105): "
            "формула — тавтология, если каждая её интерпретационная форма есть тавтология при любом числе отмеченных "
            "терминов для каждого термина. Для нетавтологии укажите число отмеченных терминов и значения, при которых "
            "посылка 1, заключение 0; для тавтологии дайте довод, годный при любом $n$.\n\n"
            + items([f"${ftex(it[1], it[2])}$" for it in its]))
    return card(level, "C", "open", "short", "с. 105–106, гл. 7, § 7", "кванторы, интерпретация, тавтологии", cond,
                "; ".join(ans), "\n".join(sol))


def interp_wrong(f, n, err, env=None):
    """Интерпретационная форма с ошибкой: 'conj' — ∃ раскрыт конъюнкцией; 'rebind' — замена и внутри
    вложенной группы с тем же термином."""
    env = env or {}
    k = f[0]
    if k == "el":
        return EL(env.get(f[1], f[1]), env.get(f[2], f[2]))
    if k == "neg":
        return N(interp_wrong(f[1], n, err, env))
    if k in ("all", "ex"):
        a = f[1]
        if not free_in(a, f[2]) and err != "rebind":
            return interp_wrong(f[2], n, err, env)
        if err == "rebind" and a in env:
            return interp_wrong(f[2], n, err, env)
        parts = [interp_wrong(f[2], n, err, {**env, a: f"{i}{a}"}) for i in range(1, n[a] + 1)]
        if k == "ex" and err == "conj":
            return C(*parts)
        return C(*parts) if k == "all" else W(*parts)
    return (k, tuple(interp_wrong(g, n, err, env) for g in f[1]))


def c_diag7(level=6):
    for _ in range(500):
        p, q = rnd.choice([
            (ALL("a", W(ab, EX("a", ac))), EX("a", W(ab, ac))),
            (EX("a", C(ab, ALL("a", ac))), C(EX("a", ab), ALL("a", ac))),
            (ALL("a", C(ab, EX("a", ac))), ALL("a", ab)),
            (EX("a", W(ab, N(EX("a", ac)))), EX("a", ab)),
        ])
        n = {"a": 2}
        good_p, good_q = q7.interp(p, n), q7.interp(q, n)
        e1, e2 = "rebind", "conj"
        bp, bq = interp_wrong(p, n, e1), interp_wrong(q, n, e2)
        if bp != good_p and bq != good_q:
            break
    cond = (f"{CONV} Студент построил интерпретационную форму формулы ${ftex(p, q)}$ при двух отмеченных терминах для "
            f"$a$ (D2 § 7, с. 105):\n\n$${ftex(bp, bq)}$$\n\nНайдите все ошибки, объясните их по D2 и запишите верную "
            "форму. Затем выясните, тавтология ли она.")
    tg = not any(q7.pval(good_p, e) and not q7.pval(good_q, e) for e in q7.penvs(good_p, good_q))
    ans = ("Посылка: замена $a$ на $ia$ проведена и внутри части с собственной группой $(\\exists a)$ (там вхождения "
           "связаны этой группой); заключение: $(\\exists a)$ раскрыт конъюнкцией вместо дизъюнкции. Верно: "
           f"${ftex(good_p, good_q)}$; " + ("тавтология." if tg else "не тавтология."))
    sol = ("1. По § 7 $x(ia)$ получается заменой $a$ на $ia$ лишь там, где $a$ входит свободно (с. 105). Внутренняя "
           "группа с тем же термином связывает свои вхождения: их раскрывает она сама, своей дизъюнкцией или "
           "конъюнкцией (п. 3 D2).\n"
           "2. По п. 3 D2 $(\\exists b)z$ заменяется дизъюнкцией $z(1b) \\vee \\ldots \\vee z(nb)$, а не конъюнкцией.\n"
           f"Верная форма: ${ftex(good_p, good_q)}$.\n" +
           ("Перебор значений не даёт набора с посылкой 1 и заключением 0 — при $n = 2$ форма тавтология." if tg else
            "При " + q7.env_tex(next(e for e in q7.penvs(good_p, good_q) if q7.pval(good_p, e) and not q7.pval(good_q, e)))
            + " посылка 1, заключение 0 — не тавтология, значит, и формула не тавтология (D3)."))
    return card(level, "E", "vary", "text", "с. 105, гл. 7, § 7", "кванторы, интерпретация, диагностика", cond, ans, sol)


def c_cm_diag(level=6):
    p, q = nontaut_item()
    cm = q7.countermodel(p, q)
    (P, Q), n, ip, iq, e = cm
    keys = sorted(e, key=tex)
    for _ in range(100):
        k = rnd.choice(keys)
        e2 = dict(e)
        e2[k] = 1 - e2[k]
        if not (q7.pval(ip, e2) and not q7.pval(iq, e2)):
            break
    vp, vq = q7.pval(ip, e2), q7.pval(iq, e2)
    cond = (f"{CONV} Студент доказывает, что ${ftex(p, q)}$ не тавтология: «При {q7.n_text(n)} интерпретационная форма — "
            f"${ftex(ip, iq)}$. При {q7.env_tex(e2)} посылка 1, а заключение 0». Проверьте рассуждение; если оно ошибочно, "
            "найдите ошибку и исправьте его.")
    ans = (f"При указанных значениях посылка {vp}, заключение {vq} — довод неверен; верно, например: "
           f"{q7.env_tex(e)} (посылка 1, заключение 0).")
    sol = (f"Подставляем значения студента: посылка ${tex(ip)}$ получает {vp}, заключение ${tex(iq)}$ — {vq}; набора с "
           f"посылкой 1 и заключением 0 студент не указал (ошибка в значении ${tex(k)}$). Исправление: при "
           f"{q7.env_tex(e)} посылка 1, заключение 0. Вывод студента верен, но его обоснование — нет (D3 § 7, с. 105).")
    return card(level, "E", "vary", "text", "с. 105, гл. 7, § 7", "кванторы, интерпретация, диагностика", cond, ans, sol)


def c_minn(level=7):
    p, q = rnd.choice([
        (EX("a", ab), ALL("a", ab)),
        (C(EX("a", ab), EX("a", ac)), EX("a", C(ab, ac))),
        (ALL("a", EX("b", ab)), EX("b", ALL("a", ab))),
        (ALL("a", W(ab, ac)), W(ALL("a", ab), ALL("a", ac))),
        (C(EX("a", ab), EX("a", ac)), ALL("a", W(ab, ac))),
        (ALL("a", W(ab, W(ac, ad))), W(ALL("a", ab), ALL("a", W(ac, ad)))),
    ])
    cm = q7.countermodel(p, q)
    (P, Q), n, ip, iq, e = cm
    smaller = []
    ts = sorted(n)
    for combo in itertools.product(range(1, 4), repeat=len(ts)):
        m = dict(zip(ts, combo))
        if sum(combo) < sum(n.values()):
            jp, jq = q7.interp(P, m), q7.interp(Q, m)
            assert all(not q7.pval(jp, x) or q7.pval(jq, x) for x in q7.penvs(jp, jq))
            smaller.append((m, jp, jq))
    cond = (f"{CONV} Найдите наименьшее суммарное число отмеченных терминов, при котором интерпретационная форма "
            f"(D2 § 7, с. 105) формулы ${ftex(p, q)}$ перестаёт быть тавтологией, и докажите, что при меньших числах она "
            "тавтология.")
    ans = f"При {q7.n_text(n)}: {q7.env_tex(e)} — посылка 1, заключение 0; при меньших числах форма — тавтология."
    sol = [f"При {q7.n_text(n)} форма ${ftex(ip, iq)}$; при {q7.env_tex(e)} посылка 1, заключение 0."]
    for m, jp, jq in smaller:
        sol.append(f"При {q7.n_text(m)} форма ${ftex(jp, jq)}$ — тавтология (каждый набор значений, где посылка 1, даёт "
                   "заключению 1; проверяется перебором).")
    return card(level, "K", "open", "short", "с. 105–106, гл. 7, § 7", "кванторы, интерпретация, контрпример", cond, ans,
                "\n".join(sol))


def c_closure7(level=6):
    p, q = rnd.choice([(ALL("a", ab), ab), (ab, EX("a", ab)), (EX("a", ab), ab), (ab, ALL("a", ab)),
                       (C(ALL("a", ab), ac), EX("a", C(ab, ac))), (EX("a", C(ab, ac)), C(ab, EX("a", ac)))])
    cls = q7.closures(p, q)
    rows = []
    for P, Q in cls:
        cm = q7.countermodel(P, Q, nmax=3)
        if cm and cm[0] == (P, Q):
            rows.append((P, Q, cm))
        else:
            rows.append((P, Q, None))
    taut = all(r[2] is None for r in rows)
    cond = (f"{CONV} В формуле ${ftex(p, q)}$ термин $a$ входит и свободно, и связанно. По п. 1 D2 § 7 (с. 105) формула "
            "заменяется на $(\\forall a)x \\vdash (\\forall a)y$ или $(\\exists a)x \\vdash (\\exists a)y$. Запишите обе "
            "замены, отбросьте вырожденные группы (п. 2) и исследуйте каждую; сделайте вывод о тавтологичности формулы "
            "(D3).")
    sol, ans = [], []
    for P, Q, cm in rows:
        dP = q7.interp(P, {"a": 1})
        if cm:
            sol.append(f"${ftex(P, Q)}$: {cm_text(P, Q, cm)} — не тавтология.")
            ans.append(f"${ftex(P, Q)}$ — не тавтология")
        else:
            sol.append(f"${ftex(P, Q)}$: после отбрасывания вырожденных групп при любом $n$ посылка и заключение — "
                       "конъюнкции или дизъюнкции одних и тех же $z(ia)$, причём из посылки следует заключение "
                       "(конъюнкция влечёт дизъюнкцию и самоё себя, дизъюнкция — самоё себя) — тавтология (проверено и "
                       "перебором при $n \\leq 3$).")
            ans.append(f"${ftex(P, Q)}$ — тавтология")
    ans.append("формула " + ("тавтология" if taut else "не тавтология"))
    return card(level, "C", "vary", "short", "с. 105, гл. 7, § 7", "кванторы, интерпретация, свободные термины", cond,
                "; ".join(ans) + ".", "\n".join(sol) + ("\n\nКаждая форма — тавтология: формула тавтология (D3)." if taut else
                                                        "\n\nОдна из форм не тавтология — формула не тавтология (D3)."))


def c_nat7(level=6):
    s, p, q = rnd.choice([
        ("«Для каждого $a$ найдётся $b$, такое что $a$ есть $b$; следовательно, найдётся $b$, такое что каждое $a$ есть "
         "$b$»", ALL("a", EX("b", ab)), EX("b", ALL("a", ab))),
        ("«Некоторые $a$ суть $b$ и некоторые $a$ суть $c$; следовательно, некоторые $a$ суть и $b$, и $c$»",
         C(EX("a", ab), EX("a", ac)), EX("a", C(ab, ac))),
        ("«Каждое $a$ есть $b$ или $c$; следовательно, каждое $a$ есть $b$ или каждое $a$ есть $c$»", ALL("a", W(ab, ac)),
         W(ALL("a", ab), ALL("a", ac)))])
    cm = q7.countermodel(p, q)
    cond = (f"{CONV} Запишите рассуждение {s} формулой следования ($(a \\leftarrow b)$ — «$a$ есть $b$») и исследуйте по "
            "D3 § 7 (с. 105), тавтология ли она. Если нет, опишите опровергающий случай словами: какие отмеченные термины "
            "и что о них истинно.")
    return card(level, "C", "open", "short", "с. 105, гл. 7, § 7", "кванторы, интерпретация, формализация", cond,
                f"${ftex(p, q)}$ — не тавтология: {cm_text(p, q, cm)}.",
                f"Формула ${ftex(p, q)}$. {cm_text(p, q, cm)[0].upper() + cm_text(p, q, cm)[1:]}. Словами: отмеченные "
                "термины — разные предметы; истинные элементарные высказывания формы говорят, что именно о них верно; "
                "при этом посылка рассуждения верна, а заключение — нет. Значит, формула не тавтология (D3).", form="nat")


# ================================================================ планы по номерам
KEEP = {
    "07.06-010": ("07.06-031", None), "07.06-018": ("07.06-032", None),
    "07.07-009": ("07.07-020", None), "07.07-017": ("07.07-021", None),
}


def plan():
    P = {}
    s6 = {1: lambda: A.c_subst_series("T17"), 2: c_deriv6, 3: c_complete6, 4: c_near6, 5: c_mt6, 6: c_series6,
          7: c_diag6, 8: lambda: A.c_subst_series("T18"), 9: c_deriv6, 11: c_badstep6, 12: lambda: c_nat6(0),
          13: c_complete6, 14: c_mt6, 15: c_near6, 16: c_deriv6, 17: c_series6, 19: c_diag6,
          20: lambda: A.c_subst_series("T7"), 21: c_complete6, 22: c_deriv6, 23: c_badstep6, 24: c_mt6, 25: c_near6,
          26: c_series6, 27: c_diag6, 29: lambda: c_nat6(rnd.choice([1, 2, 3])), 30: c_deriv6, 31: c_complete6,
          32: lambda: c_deriv6(level=7)}
    P.update({f"07.06-{k:03d}": v for k, v in s6.items()})
    s7 = {1: c_interp7, 2: c_series7, 3: c_diag7, 4: c_closure7, 5: c_cm_diag, 6: c_interp7, 7: c_series7,
          8: c_minn, 10: c_diag7, 11: c_series7, 12: c_closure7, 13: c_interp7, 14: c_cm_diag, 15: c_minn,
          16: c_nat7, 18: c_diag7, 19: c_series7, 20: lambda: c_series7(6)}
    P.update({f"07.07-{k:03d}": v for k, v in s7.items()})
    return P
