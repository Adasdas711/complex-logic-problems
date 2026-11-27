"""Задачи гл. 7, § 1–9, для hard07.py (система S^s_cq)."""
import itertools
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts" / "gen"))
import q7  # noqa: E402
import hard07_der as H  # noqa: E402
from q7 import ALL, C, EL, EX, N, W, free_in, ftex, qfree, tex  # noqa: E402

rnd = random.Random(1970_0701)
H.SEEN.clear()
L = "абвгдежз"
SYS = "S^s_cq"

CONV = ("Буквы $a, b, c, d, e$ — термины, $(a \\leftarrow b)$ и т. п. — элементарные высказывания (D1 § 1, с. 98); "
        "$\\sim$ и кванторная группа относятся к ближайшему следующему высказыванию: $(\\forall a)(a \\leftarrow b)"
        "(a \\leftarrow c)$ — конъюнкция $(\\forall a)(a \\leftarrow b)$ и $(a \\leftarrow c)$, а в $(\\forall a)((a "
        "\\leftarrow b)(a \\leftarrow c))$ квантор относится ко всей конъюнкции.")
SCH2 = ("Схемы и правила $S^s_{cq}$ (с. 99–100): A1 $(\\forall a)x \\vdash x$; A2 $x \\vdash (\\exists a)x$; "
        "A3 $(\\forall a)x(\\exists a)y \\vdash (\\exists a)(xy)$; A4 $(\\forall a)(x \\vee y) \\vdash (\\forall a)x \\vee "
        "(\\exists a)y$; A5 $(\\exists a)x \\vdash (\\forall a)x$, где $a$ не входит свободно в $x$; A6 $(\\forall a)x "
        "\\vdash \\sim(\\exists a)\\sim x$; A7 $\\sim(\\exists a)\\sim x \\vdash (\\forall a)x$; R1: если $x \\vdash y$, то "
        "$(\\forall a)x \\vdash (\\forall a)y$; R2: если $x \\vdash y$, то $(\\exists a)x \\vdash (\\exists a)y$. "
        "[$S^s$] — формула, доказуемая в $S^s$: сильная тавтология, если элементарные высказывания и высказывания с "
        "кванторами считать буквами (ссылка на систему $S^s$, § 6, с. 102); R1 $S^s$: из $x \\vdash y$ и $y \\vdash z$ — "
        "$x \\vdash z$; R2 $S^s$: из $x \\vdash y$ и $x \\vdash z$ — $x \\vdash yz$ (с. 17).")
SRC2 = "с. 99–100, гл. 7, § 2"


def card(level, typ, step, ans_kind, src, tags, cond, ans, sol, form="sym", system=SYS, condition="def"):
    return dict(level=level, type=typ, step=step, form=form, answer=ans_kind, source=src, tags=tags, cond=cond.strip(),
                ans=ans.strip(), sol=sol.strip(), system=system, condition=condition)


def items(fs):
    return "\n".join(f"{L[k]}) {f}" for k, f in enumerate(fs))


ab, ac, ad, cb, cd, db = EL("a", "b"), EL("a", "c"), EL("a", "d"), EL("c", "b"), EL("c", "d"), EL("d", "b")
ba, bc = EL("b", "a"), EL("b", "c")
WITH_A = [ab, ac, ad, ba]
NO_A = [cb, cd, db, bc]


# ================================================================ § 1: вхождения, вырожденные группы, D7
def rnd_stmt(depth, qterms=("a", "b"), pairs=None):
    pairs = pairs or [("a", "b"), ("a", "c"), ("c", "b"), ("b", "a"), ("c", "d"), ("a", "d"), ("d", "b")]
    if depth == 0 or rnd.random() < 0.18:
        return EL(*rnd.choice(pairs))
    u = rnd.random()
    if u < 0.12:
        return N(rnd_stmt(depth - 1, qterms, pairs))
    if u < 0.45:
        return (rnd.choice(["all", "ex"]), rnd.choice(qterms), rnd_stmt(depth - 1, qterms, pairs))
    op = C if u < 0.8 else W
    p, q = rnd_stmt(depth - 1, qterms, pairs), rnd_stmt(depth - 1, qterms, pairs)
    if p == q:
        return p
    k = "conj" if op is C else "wdis"
    mem = (p[1] if p[0] == k else (p,)) + (q[1] if q[0] == k else (q,))
    return (k, mem)


def els(f):
    return [g for g in H.walk(f) if g[0] == "el"]


def occ_table(f):
    occ = q7.occurrences(f)
    es = els(f)
    rows = []
    for i, e in enumerate(es):
        rows.append((i + 1, e, occ[2 * i], occ[2 * i + 1]))
    return rows


def rich_stmt(min_el=4, min_g=3, need_mixed=True, need_degen=None):
    for _ in range(20000):
        f = rnd_stmt(4)
        es, gs = els(f), q7.groups(f)
        if not (min_el <= len(es) <= 6 and min_g <= len(gs) <= 4):
            continue
        occ = q7.occurrences(f)
        mixed = any(any(t == a and fr for t, fr in occ) and any(t == a and not fr for t, fr in occ) for a in "ab")
        if need_mixed and not mixed:
            continue
        dg = [g for g in gs if q7.degenerate(g)]
        if need_degen is not None and bool(dg) != need_degen:
            continue
        if len(q7.tex(f)) > 150:
            continue
        return f
    raise RuntimeError("нет высказывания")


def gname(g):
    return f"$({q7.QTEX[g[0]].strip()} {g[1]})$"


def c_occ(level=4):
    f = rich_stmt(need_degen=rnd.random() < 0.6)
    rows = occ_table(f)
    gs = q7.groups(f)
    bound = [f"${t}$ в {n}-м" for n, e, *ps in rows for t, fr in ps if not fr]
    dg = [i + 1 for i, g in enumerate(gs) if q7.degenerate(g)]
    cond = (f"{CONV} Дано высказывание\n\n$${tex(f)}$$\n\nПронумеруйте его элементарные высказывания слева направо и "
            "для каждого вхождения термина в них установите, свободное оно или связанное (D5 § 1, с. 99). Затем "
            "пронумеруйте кванторные группы слева направо и найдите вырожденные (D6: группа $(Ka)$ вырождена в $(Ka)x$, "
            "если в $x$ нет свободных вхождений $a$).")
    ans = ("Связанные вхождения: " + (", ".join(bound) or "нет") + "; остальные — свободные. Вырожденные группы: " +
           (", ".join(f"{i}-я {gname(gs[i - 1])}" for i in dg) or "нет") + ".")
    sol = ["Элементарные высказывания: " + "; ".join(f"{n}) ${tex(e)}$" for n, e, *_ in rows) + "."]
    sol.append("По D5 вхождение термина $a$ связанное, если оно стоит в части $(\\forall a)z$ или $(\\exists a)z$ "
               "(там $a$ связан по D4), и свободное в остальных случаях.")
    for n, e, (t1, f1), (t2, f2) in rows:
        sol.append(f"{n}) ${tex(e)}$: ${t1}$ — {'свободное' if f1 else 'связанное'}, ${t2}$ — "
                   f"{'свободное' if f2 else 'связанное'}.")
    for i, g in enumerate(gs, 1):
        fr = free_in(g[1], g[2])
        sol.append(f"Группа {i} {gname(g)}: в её области ${tex(g[2])}$ термин ${g[1]}$ "
                   + ("входит свободно — группа не вырождена." if fr else "свободно не входит — группа вырождена (D6)."))
    return card(level, "A", "iso", "short", "с. 98–99, гл. 7, § 1", "кванторы, вхождения", cond, ans, "\n".join(sol),
                system=None)


def c_occ_diag(level=5):
    f = rich_stmt()
    rows = occ_table(f)
    flat = [(n, e, j, t, fr) for n, e, *ps in rows for j, (t, fr) in enumerate(ps)]
    wrong = set(rnd.sample(range(len(flat)), 2))
    lines = []
    for k, (n, e, j, t, fr) in enumerate(flat):
        claim = fr if k not in wrong else not fr
        lines.append(f"{n}) ${tex(e)}$, ${t}$ ({'субъект' if j == 0 else 'предикат'}) — "
                     f"{'свободное' if claim else 'связанное'}")
    cond = (f"{CONV} Студент разобрал вхождения терминов в элементарные высказывания высказывания\n\n$${tex(f)}$$\n\n"
            + "\n".join(lines) + "\n\nРовно две строки неверны. Найдите их и объясните ошибку по D5 § 1 (с. 99).")
    ans, sol = [], []
    for k in sorted(wrong):
        n, e, j, t, fr = flat[k]
        ans.append(f"{n}) ${t}$ — {'свободное' if fr else 'связанное'}")
        path = [g for g in q7.groups(f) if g[1] == t and e in list(H.walk(g[2]))]
        if fr:
            sol.append(f"{n}) ${tex(e)}$ не стоит ни в одной части вида $(\\forall {t})z$, $(\\exists {t})z$ — вхождение "
                       f"${t}$ свободное (D5, «в остальных случаях», с. 99).")
        else:
            g = path[0]
            sol.append(f"{n}) ${tex(e)}$ стоит в части ${tex((g[0], g[1], g[2]))}$, где ${t}$ связан (D4); по D5 все "
                       f"вхождения ${t}$ в эту часть — связанные вхождения и во всё высказывание.")
    return card(level, "E", "vary", "short", "с. 98–99, гл. 7, § 1", "кванторы, вхождения, диагностика", cond,
                "Неверны: " + "; ".join(ans) + ".", "\n".join(sol) + "\n\nОстальные строки верны.", system=None)


DEGEN_POOL = [
    (ALL("a", EX("a", ab)), "в области $(\\exists a)(a \\leftarrow b)$ термин $a$ входит только связанно"),
    (ALL("a", cd), "в $(c \\leftarrow d)$ термина $a$ нет"),
    (ALL("a", C(ab, EX("a", ac))), "в $(a \\leftarrow b)$ термин $a$ входит свободно"),
    (EX("b", C(ALL("b", ab), cd)), "в области $b$ входит только связанно (в $(\\forall b)(a \\leftarrow b)$)"),
    (EX("b", W(ALL("b", ab), cb)), "в $(c \\leftarrow b)$ термин $b$ входит свободно"),
    (ALL("a", N(EX("b", ba))), "в $(b \\leftarrow a)$ термин $a$ входит свободно"),
    (EX("a", ALL("b", cb)), "в области $(\\forall b)(c \\leftarrow b)$ нет термина $a$"),
    (ALL("b", EX("a", C(ab, ALL("b", cb)))), "в $(a \\leftarrow b)$ термин $b$ входит свободно"),
]


def c_degen(level=5):
    its = rnd.sample(DEGEN_POOL, 4)
    if all(not q7.degenerate((f[0], f[1], f[2])) for f, _ in its) or all(q7.degenerate((f[0], f[1], f[2])) for f, _ in its):
        its = [DEGEN_POOL[0], DEGEN_POOL[2]] + rnd.sample(DEGEN_POOL[3:], 2)
    ans, sol = [], []
    for k, (f, why) in enumerate(its):
        dg = q7.degenerate((f[0], f[1], f[2]))
        ans.append(f"{L[k]}) {'вырождена' if dg else 'не вырождена'}")
        sol.append(f"{L[k]}) Группа ${tex(f)[:tex(f).index(')') + 1]}$: {why} — "
                   + ("свободных вхождений нет, группа вырождена (D6)." if dg else "группа не вырождена (D6)."))
    cond = (f"{CONV} Для каждого высказывания установите, вырождена ли в нём первая (внешняя) кванторная группа, и "
            "обоснуйте по D5 и D6 § 1 (с. 99): группа $(Ka)$ вырождена в $(Ka)x$, если в $x$ нет свободных вхождений $a$.\n\n"
            + items([f"${tex(f)}$" for f, _ in its]))
    return card(level, "A", "vary", "short", "с. 99, гл. 7, § 1", "кванторы, вырожденные группы", cond, "; ".join(ans),
                "\n".join(sol), system=None)


def c_qfree(level=4, prov=False):
    for _ in range(500):
        p, q = rich_stmt(3, 2, need_mixed=False), rich_stmt(3, 2, need_mixed=False)
        if len(tex(p)) + len(tex(q)) < 170:
            break
    pp, qq = qfree(p), qfree(q)
    st = q7.ss_theorem(pp, qq)
    cond = (f"{CONV} Запишите бескванторную форму формулы\n\n$${ftex(p, q)}$$\n\n(D7 § 1, с. 99: исключаются все кванторные "
            "группы, остальное сохраняется)" + (" и исследуйте, доказуема ли она в $S^s$ (критерий: сильная тавтология — "
                                              "тавтология, в заключение которой не входят элементарные высказывания, "
                                              "отсутствующие в посылке)." if prov else "."))
    ans = f"${ftex(pp, qq)}$" + ((" — доказуема в $S^s$" if st else " — недоказуема в $S^s$") if prov else "")
    sol = (f"Исключаем кванторные группы {', '.join(gname(g) for g in q7.groups(p) + q7.groups(q))}; знаки $\\sim$, "
           f"конъюнкции и дизъюнкции остаются на местах: ${ftex(pp, qq)}$.")
    if prov:
        if st:
            sol += " Формула — тавтология, и все элементарные высказывания заключения есть в посылке: сильная тавтология."
        else:
            newa = q7.patoms(qq) - q7.patoms(pp)
            if newa:
                sol += (" В заключение входит " + ", ".join(f"${tex(e)}$" for e in sorted(newa, key=tex)) +
                        ", отсутствующее в посылке: не сильная тавтология.")
            else:
                e = next(e for e in q7.penvs(pp, qq) if q7.pval(pp, e) and not q7.pval(qq, e))
                sol += f" При {q7.env_tex(e)} посылка 1, заключение 0: не тавтология."
    return card(level, "T", "iso", "short", "с. 99, гл. 7, § 1", "кванторы, бескванторная форма", cond, ans, sol,
                system=None)


def drop_neg_before_q(f):
    """Типичная ошибка: вместе с кванторной группой стёрт стоящий перед ней знак ∼."""
    k = f[0]
    if k == "neg" and f[1][0] in ("all", "ex"):
        return qfree(f[1][2]), True
    if k in ("all", "ex"):
        return drop_neg_before_q(f[2])
    if k == "neg":
        g, ch = drop_neg_before_q(f[1])
        return N(g), ch
    if k in ("el", "v"):
        return f, False
    out, ch = [], False
    for a in f[1]:
        if ch:
            out.append(qfree(a))
        else:
            g, ch = drop_neg_before_q(a)
            out.append(g)
    return (k, tuple(out)), ch


def c_qfree_diag(level=5):
    for _ in range(3000):
        p = rich_stmt(3, 2, need_mixed=False)
        q = rich_stmt(3, 2, need_mixed=False)
        p2, ch = drop_neg_before_q(p)
        if ch and len(tex(p)) + len(tex(q)) < 170 and q[0] in ("conj", "wdis", "all", "ex"):
            break
    qq = qfree(q)
    # вторая ошибка: стёрто целиком высказывание под вырожденной группой или потерян член
    if qq[0] in ("conj", "wdis") and len(qq[1]) == 2:
        q2 = qq[1][0]
        err2 = f"в заключении потерян член ${tex(qq[1][1])}$: D7 исключает только кванторные группы"
    else:
        q2 = N(qq)
        err2 = "в заключении добавлен знак $\\sim$, которого в формуле нет"
    cond = (f"{CONV} Студент записал бескванторную форму (D7 § 1, с. 99) формулы\n\n$${ftex(p, q)}$$\n\nтак: "
            f"$${ftex(p2, q2)}$$\n\nНайдите все ошибки, объясните их и запишите верную бескванторную форму.")
    ans = (f"Две ошибки: в посылке вместе с кванторной группой стёрт знак $\\sim$ перед ней; {err2}. Верно: "
           f"${ftex(qfree(p), qq)}$.")
    sol = ("D7 (с. 99): бескванторная форма получается исключением всех кванторных групп; знак $\\sim$ перед "
           "кванторной группой относится к высказыванию $(Ka)z$ и при исключении группы остаётся перед $z$ (ср. "
           "бескванторные формы A6, A7 на с. 101: $x \\vdash \\sim\\sim x$, $\\sim\\sim x \\vdash x$).\n"
           f"1. Посылка: верно ${tex(qfree(p))}$, у студента ${tex(p2)}$ — пропал $\\sim$.\n"
           f"2. Заключение: верно ${tex(qq)}$; у студента {err2}.")
    return card(level, "E", "vary", "short", "с. 99, 101, гл. 7, § 1", "кванторы, бескванторная форма, диагностика",
                cond, ans, sol, system=None)


def c_build_occ():
    f1 = C(EX("a", ac), ALL("a", cd), ab)
    f2 = ALL("a", EX("a", ab))
    assert free_in("a", f1) and not q7.degenerate(q7.groups(f1)[0]) and q7.degenerate(q7.groups(f1)[1])
    assert q7.degenerate(q7.groups(f2)[0]) and "a" in q7.terms(f2[2])
    cond = (f"{CONV} Постройте высказывание или докажите, что его нет:\n\n"
            "а) термин $a$ имеет в высказывании и свободные, и связанные вхождения, причём одна из групп с термином $a$ "
            "вырождена, а другая нет;\n"
            "б) группа $(\\forall a)$ вырождена в $(\\forall a)x$, хотя термин $a$ входит в $x$;\n"
            "в) в высказывании $(\\forall a)x$ термин $a$ имеет свободное вхождение.\n\n"
            "Опора — D4–D6 § 1 (с. 99).")
    ans = (f"а) например, ${tex(f1)}$; б) например, ${tex(f2)}$; в) такого высказывания нет: все вхождения $a$ в "
           "$(\\forall a)x$ связанные.")
    sol = (f"а) В ${tex(f1)}$: вхождение $a$ в $(a \\leftarrow c)$ связанное (оно в части $(\\exists a)(a \\leftarrow c)$, "
           "D5), в последнем $(a \\leftarrow b)$ — свободное; группа $(\\exists a)$ не вырождена ($a$ свободен в "
           "$(a \\leftarrow c)$), группа $(\\forall a)$ вырождена — в $(c \\leftarrow d)$ нет $a$ (D6).\n"
           f"б) В ${tex(f2)}$ термин $a$ входит в $x = (\\exists a)(a \\leftarrow b)$, но только связанно (D4, D5), "
           "свободных вхождений в $x$ нет — группа $(\\forall a)$ вырождена (D6). Это не противоречит D6: она говорит о "
           "свободных вхождениях, а не о вхождениях вообще.\n"
           "в) Если $a$ входит в $x$, то по D4 $a$ связан в $(\\forall a)x$, и по D5 (первый пункт) все вхождения $a$ в "
           "$(\\forall a)x$ — связанные. Если $a$ не входит в $x$, вхождений нет вовсе. Свободного вхождения нет.")
    return card(6, "A", "open", "build", "с. 99, гл. 7, § 1", "кванторы, вхождения, построение", cond, ans, sol,
                system=None)


def c_d4d5():
    f = C(ab, ALL("a", ac))
    cond = (f"{CONV} Студент рассуждает о высказывании ${tex(f)}$: «По D4 термин $a$ свободен в $x$, если $a$ входит в $x$ "
            "и группы $(\\forall a)$, $(\\exists a)$ в $x$ не входят. Здесь группа $(\\forall a)$ входит в высказывание, "
            "значит, $a$ в нём не свободен, и все вхождения $a$ связанные. Поэтому группа $(\\exists a)$ в "
            f"$(\\exists a)({tex(ab)}{tex(ALL('a', ac))})$ вырождена». Найдите ошибки и дайте верный разбор.")
    ans = ("D4 не говорит, что $a$ связан в этом высказывании (оно не имеет вида $(Ka)z$); по D5 вхождение $a$ в "
           "$(a \\leftarrow b)$ свободное, в $(a \\leftarrow c)$ — связанное; группа $(\\exists a)$ не вырождена (D6).")
    sol = ("1. D4 (с. 99) даёт достаточное условие свободы ($a$ входит, групп с $a$ нет) и говорит, что $a$ связан в "
           "$(\\forall a)x$ и $(\\exists a)x$. Высказывание — конъюнкция, а не $(Ka)z$: из D4 о нём не следует ни "
           "«свободен», ни «связан». Ошибка — обращение D4: из «группы входят» студент заключил «связан».\n"
           "2. Вхождения определяет D5: если $a$ связан в части $(\\forall a)(a \\leftarrow c)$, его вхождение туда — "
           "связанное; «в остальных случаях» вхождение свободное. Значит, $a$ в $(a \\leftarrow b)$ входит свободно.\n"
           "3. D6: группа $(\\exists a)$ вырождена, если в её области нет свободных вхождений $a$. Свободное вхождение есть "
           "(в $(a \\leftarrow b)$) — группа не вырождена.")
    return card(5, "E", "vary", "text", "с. 99, гл. 7, § 1", "кванторы, вхождения, диагностика", cond, ans, sol,
                form="meta", system=None)


def c_impossible():
    cond = (f"{CONV} Докажите по D4–D6 § 1 (с. 99) три утверждения: (1) если группа $(Ka)$ вырождена в $(Ka)x$, то и "
            "в $(\\forall a)(Ka)x$ внешняя группа вырождена; (2) если $a$ не входит в $x$, то любая группа $(Ka)$ "
            "вырождена в $(Ka)x$; (3) обратное к (2) неверно — приведите высказывание, где $a$ входит в $x$, а группа "
            "$(\\forall a)$ всё же вырождена.")
    ans = ("(1) в $(Ka)x$ все вхождения $a$ связаны (D4, D5); (2) нет вхождений — нет и свободных; (3) например, "
           "$(\\forall a)((\\exists a)(a \\leftarrow b)(c \\leftarrow d))$.")
    f3 = ALL("a", C(EX("a", ab), cd))
    assert q7.degenerate(q7.groups(f3)[0])
    sol = ("1. По D4 $a$ связан в $(Ka)x$, если входит в $x$; по D5 все вхождения $a$ в $(Ka)x$ — связанные. Если $a$ не "
           "входит в $x$, вхождений нет. В обоих случаях в $(Ka)x$ нет свободных вхождений $a$, и по D6 внешняя группа "
           "$(\\forall a)$ в $(\\forall a)(Ka)x$ вырождена. (Условие «$(Ka)$ вырождена» здесь даже не нужно.)\n"
           "2. Свободное вхождение — частный случай вхождения; если $a$ не входит в $x$, свободных вхождений нет, по D6 "
           "группа вырождена.\n"
           f"3. В ${tex(f3)}$ термин $a$ входит в область, но только в часть $(\\exists a)(a \\leftarrow b)$, где он связан "
           "(D5); других вхождений нет — группа $(\\forall a)$ вырождена.")
    return card(6, "M", "open", "proof", "с. 99, гл. 7, § 1", "кванторы, вырожденные группы", cond, ans, sol,
                form="meta", system=None)


NAT1 = [
    ("Каждое $a$ есть $b$, и некоторое $a$ есть $c$", C(ALL("a", ab), EX("a", ac))),
    ("Неверно, что некоторое $a$ не есть $b$", N(EX("a", N(ab)))),
    ("Для каждого $a$: $a$ есть $b$ или $a$ есть $c$", ALL("a", W(ab, ac))),
    ("Некоторое $a$ есть $b$ и есть $c$, а $c$ есть $d$", C(EX("a", C(ab, ac)), cd)),
    ("Каждое $a$ есть $b$, или каждое $a$ есть $c$", W(ALL("a", ab), ALL("a", ac))),
    ("Для каждого $a$ найдётся $b$, такое что $a$ есть $b$", ALL("a", EX("b", ab))),
    ("Найдётся $b$, такое что каждое $a$ есть $b$", EX("b", ALL("a", ab))),
]


def c_nat1(level=5):
    its = rnd.sample(NAT1, 4)
    cond = (f"{CONV} Квантор $\\forall$ читается «все» («каждый»), $\\exists$ — «некоторые» («найдётся»), "
            "$(a \\leftarrow b)$ — «$a$ есть $b$» (алфавит § 1, с. 98). Запишите каждое предложение высказыванием "
            "теории кванторов и для каждого термина укажите, связан он или входит свободно; найдите вырожденные группы.\n\n"
            + items([f"«{s}»" for s, _ in its]))
    ans, sol = [], []
    for k, (s, f) in enumerate(its):
        fr = sorted(q7.free_terms(f))
        bd = sorted({t for t, x in q7.occurrences(f) if not x})
        ans.append(f"{L[k]}) ${tex(f)}$")
        sol.append(f"{L[k]}) ${tex(f)}$: связаны " + (", ".join(f"${t}$" for t in bd) or "—") + "; свободно входят "
                   + (", ".join(f"${t}$" for t in fr) or "—") + "; вырожденных групп "
                   + ("нет" if not any(q7.degenerate(g) for g in q7.groups(f)) else "есть") + ".")
    return card(level, "T", "vary", "short", "с. 98–99, гл. 7, § 1", "кванторы, перевод", cond, "; ".join(ans),
                "\n".join(sol) + "\n\nОпора: D2 (п. 3), D4–D6 § 1 (с. 98–99).", form="nat", system=None)


def c_same_qfree():
    p1, q1 = ALL("a", ab), ab
    p2, q2 = ALL("a", ab), EX("a", ab)
    p3, q3 = EX("a", ab), ALL("a", ab)
    cond = (f"{CONV} Постройте три формулы с одной и той же бескванторной формой $(a \\leftarrow b) \\vdash "
            "(a \\leftarrow b)$ (D7 § 1, с. 99), такие что: в первой термин $a$ входит в заключение свободно; во второй "
            "$a$ связан и в посылке, и в заключении, а формула — пример аксиомной схемы $S^s_{cq}$; третья — формула того "
            "же вида, что A5, но не пример A5. Проверьте каждое условие.")
    ans = f"Например: ${ftex(p1, q1)}$ (A1); ${ftex(EX('a', ab), EX('a', EX('a', ab)))}$ (A2); ${ftex(p3, q3)}$."
    assert q7.inst_of(q7.SCQ["A2"], EX("a", ab), EX("a", EX("a", ab))) is not None
    assert q7.inst_of(q7.SCQ["A5"], p3, q3) is None
    sol = (f"1. ${ftex(p1, q1)}$: в заключении $(a \\leftarrow b)$ вхождение $a$ свободное (D5); это пример A1.\n"
           f"2. ${ftex(EX('a', ab), EX('a', EX('a', ab)))}$ — пример A2 ($x \\vdash (\\exists a)x$ при $x$ := "
           "$(\\exists a)(a \\leftarrow b)$); $a$ связан в обеих частях (D4).\n"
           f"3. ${ftex(p3, q3)}$ имеет вид $(\\exists a)x \\vdash (\\forall a)x$, но $a$ входит в $x = (a \\leftarrow b)$ "
           "свободно — условие A5 (с. 99) нарушено.\n"
           "Бескванторная форма всех трёх — $(a \\leftarrow b) \\vdash (a \\leftarrow b)$: исключаются все группы.")
    return card(6, "A", "open", "build", "с. 99, гл. 7, § 1–2", "кванторы, бескванторная форма, построение", cond, ans,
                sol, system=None)


# ================================================================ § 2: выводы, схемы
def compound(with_a=True):
    e = rnd.choice(WITH_A if with_a else NO_A)
    u = rnd.random()
    if u < 0.45:
        return e
    if u < 0.6:
        return N(e)
    o = rnd.choice(NO_A + WITH_A)
    if o == e:
        return e
    return C(e, o) if u < 0.8 else W(e, o)


def two(with_a=True):
    for _ in range(100):
        X, Y = compound(with_a), compound(with_a)
        if X != Y and not (set(H.walk(X)) & set(H.walk(Y)) - {X} == set() and False):
            return X, Y
    return ab, ac


def wrap(d, rnd_, pre=None, post=None):
    """Префикс: P' ⊢ P [A7] (P = (∀a)z, P' = ∼(∃a)∼z); суффикс: q ⊢ r [w]."""
    lines = list(d.lines)
    P = d.P
    if pre and P[0] == "all":
        P2 = N(EX(P[1], N(P[2])))

        def sh(w):
            if isinstance(w, str) or w[0] == "Ss":
                return w
            return (w[0],) + tuple(k + 1 for k in w[1:])
        lines = [(P2, P, "A7")] + [(a, b, sh(w)) for a, b, w in lines]
        last = len(lines)
        lines.append((P2, lines[-1][1], ("tr", 1, last)))
        # строки с посылкой P, кроме последней, остаются: они — промежуточные теоремы
        P = P2
    if post:
        q = lines[-1][1]
        for w, r in post(q):
            lines.append((q, r, w))
            lines.append((P, r, ("tr", len(lines) - 1, len(lines))))
            q = r
    return lines


def plan2():
    """Случайный естественный вывод для § 2 (только A1–A7, R1, R2, S^s)."""
    a = "a"
    k = rnd.choice(["t20", "t19", "t14", "t15", "a5", "a3", "a4", "a4b", "t40"])
    if k == "t20":
        X, Y = two()
        d = H.plan_t20(X, Y, a, rnd)
    elif k == "t19":
        X, Y = two()
        d = H.plan_t19(X, Y, a, rnd)
    elif k in ("t14", "t15"):
        X = rnd.choice([ab, C(ab, cb), W(ab, N(ac)), C(ab, N(db)), W(ba, cd)])
        d = H.plan_t14(X, "a", "b", rnd, "all" if k == "t14" else "ex")
    elif k == "a5":
        X, Z = compound(True), rnd.choice(NO_A + [N(cd), C(cb, cd)])
        d = H.plan_a5(X, Z, a, rnd)
    elif k == "a3":
        X, Y = two()
        d = H.plan_a3(X, Y, a, rnd)
    elif k == "a4":
        X, Y = two()
        d = H.plan_a4(X, Y, rnd.choice(NO_A + [ad]), a, rnd)
    elif k == "a4b":
        X, Y = two()
        d = H.plan_a4b(X, Y, a, rnd)
    else:
        X = rnd.choice([ab, C(ab, cb), N(ba), W(ab, cd)])
        d = H.plan_t40(X, "a", "b", rnd)
    lines = d.lines
    if len(lines) < 8 and d.P[0] == "all" and rnd.random() < 0.7:
        lines = wrap(d, rnd, pre=True)
    if len(lines) < 8:
        q = lines[-1][1]
        post = None
        if q[0] == "all":
            post = lambda q: [("A6", N(EX(q[1], N(q[2]))))]
        elif q[0] == "conj" and len(q[1]) == 2:
            post = lambda q: [(("Ss",), C(q[1][1], q[1][0]))]
        if post:
            d2 = H.Der(lines[-1][0])
            d2.lines = lines
            lines = wrap(d2, rnd, post=post)
    return lines


def deriv_ok(least=8, most=12):
    for _ in range(500):
        lines = plan2()
        key = ftex(lines[-1][0], lines[-1][1])
        if least <= len(lines) <= most and not q7.check(lines, H.AX2) and key not in H.SEEN:
            assert q7.qtaut(lines[-1][0], lines[-1][1], nmax=2), key
            H.SEEN.add(key)
            return lines
    raise RuntimeError("нет вывода")


def c_deriv(src=SRC2, least=8):
    lines = deriv_ok(least)
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} Выведите в $S^s_{{cq}}$ формулу\n\n$${ftex(a, b)}$$\n\nпользуясь схемами A1–A7, правилами R1, R2 "
            "(с. 99–100) и ссылками на $S^s$. " + SCH2)
    used = sorted({w for _, _, w in lines if isinstance(w, str)})
    ans = (f"Например, вывод в {len(lines)} строк (см. решение); схемы: {', '.join(used)}; последняя строка — "
           f"[{q7.why_text(lines[-1][2])}].")
    sol = H.show(lines) + "\n\n" + SCH2
    return card(7 if len(lines) >= 10 else 6, "D", "open", "proof", src, "кванторы, вывод", cond, ans, sol)


def c_complete(src=SRC2, allowed=None, maker=None, sch=SCH2, system=SYS, systex="S^s_{cq}"):
    lines = (maker or (lambda: deriv_ok(9)))()
    sl = [n for n, (*_, w) in enumerate(lines, 1) if isinstance(w, str) or w[0] == "Ss"]
    rl = [n for n, (*_, w) in enumerate(lines, 1) if isinstance(w, tuple) and w[0] != "Ss"]
    hide_f = set(rnd.sample(sl[1:] or sl, min(2, max(1, len(sl) - 1))))
    rest = [n for n in sl if n not in hide_f]
    hide_why = set(rnd.sample(rest, min(2, len(rest))))
    hide_why |= set(rnd.sample(rl[:-1], min(2, len(rl) - 1)))
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} В выводе формулы ${ftex(a, b)}$ в ${systex}$ пропущены основания некоторых шагов и формулы "
            f"некоторых строк («…»). Восстановите их. {sch}\n\n{H.show_hidden(lines, hide_why, hide_f)}")
    parts = []
    for n in sorted(hide_why | hide_f):
        la, lb, w = lines[n - 1]
        parts.append(f"{n} — " + (f"${ftex(la, lb)}$ " if n in hide_f else "") +
                     (f"[{q7.why_text(w)}]" if n in hide_why else ""))
    sol = ("Формулу строки восстанавливаем по соседним: в R1 $S^s$ заключение одной строки — посылка другой, в R2 $S^s$ "
           "у строк общая посылка, R1 и R2 навешивают одну и ту же кванторную группу на обе части формулы указанной "
           "строки; основание — по виду формулы.\n\n" + H.show(lines))
    return card(5, "D", "complete", "build", src, "кванторы, вывод, дополнение", cond,
                "; ".join(p.strip() for p in parts), sol, system=system)


WHY2 = {"A6": "A6 — $(\\forall a)x \\vdash \\sim(\\exists a)\\sim x$, A7 — обратная схема",
        "A7": "A7 — $\\sim(\\exists a)\\sim x \\vdash (\\forall a)x$, A6 — обратная схема",
        "A1": "A1 снимает квантор общности: $(\\forall a)x \\vdash x$; A2 вводит квантор существования",
        "A2": "A2 вводит квантор существования: $x \\vdash (\\exists a)x$; A1 снимает квантор общности",
        "A3": "A3 — $(\\forall a)x(\\exists a)y \\vdash (\\exists a)(xy)$, A4 — о дизъюнкции",
        "A4": "A4 — $(\\forall a)(x \\vee y) \\vdash (\\forall a)x \\vee (\\exists a)y$, A3 — о конъюнкции",
        "A5": "A5 — $(\\exists a)x \\vdash (\\forall a)x$ при $a$, не входящем свободно в $x$; A1 снимает квантор"}


def why_rule(w):
    if w[0] == "tr":
        return (f"заключение строки {w[1]} — посылка строки {w[2]}: это R1 $S^s$ (с. 17), а R2 $S^s$ соединяет в "
                "конъюнкцию заключения строк с общей посылкой")
    if w[0] == "R1":
        return "кванторная группа — общности: это R1 (с. 100), а R2 навешивает квантор существования"
    return "кванторная группа — существования: это R2 (с. 100), а R1 навешивает квантор общности"


def c_diag(src=SRC2, maker=None, allowed=H.AX2, whys=WHY2, sch=SCH2, system=SYS):
    for _ in range(300):
        lines = (maker or (lambda: deriv_ok(8)))()
        res = H.two_errors(lines, allowed, rnd)
        if res:
            break
    else:
        raise RuntimeError("нет диагностики")
    bad, i, j = res
    p, q = sorted([i, j])
    fix = {i: lines[i][2], j: lines[j][2]}
    cond = (f"{CONV} В выводе формулы ${ftex(lines[-1][0], lines[-1][1])}$ ровно два основания указаны неверно (формулы "
            f"строк верны). Найдите их, объясните, почему каждое неверно, и исправьте. {sch}\n\n{H.show(bad)}")
    ans = f"Шаг {p + 1}: [{q7.why_text(fix[p])}]; шаг {q + 1}: [{q7.why_text(fix[q])}]."
    exp = []
    for k in (p, q):
        a, b, _ = lines[k]
        if k == i:
            w = fix[k]
            exp.append(f"Шаг {k + 1}: ${ftex(a, b)}$ — пример {q7.scheme_name(w)}, а не {q7.scheme_name(bad[k][2])}: "
                       f"{whys.get(w, 'вид посылки и заключения не совпадает со схемой ' + q7.scheme_name(bad[k][2]))}.")
        else:
            exp.append(f"Шаг {k + 1}: {why_rule(fix[k])}.")
    sol = "\n".join(exp) + "\n\nИсправленный вывод:\n\n" + H.show(lines)
    return card(6, "E", "vary", "text", src, "кванторы, вывод, диагностика", cond, ans, sol, system=system)


def c_badstep(src=SRC2, level=5, allowed=H.AX2, sch=SCH2):
    for _ in range(2000):
        lines = deriv_ok(6, 10)
        facts = [(n, b) for n, (a, b, w) in enumerate(lines, 1) if a == lines[-1][0]]
        cands = [(n, bm) for n, q in facts for bm in H.bad_moves(q, allowed)]
        cands += [(n, bm) for n, (a, b, w) in enumerate(lines, 1) for bm in H.bad_moves(b, allowed) if a == lines[0][0]]
        if not cands:
            continue
        n, (lab, r, kind) = rnd.choice(cands)
        q = lines[n - 1][1]
        P = lines[-1][0]
        bad = list(lines) + [(q, r, lab), (P, r, ("tr", n, len(lines) + 1))]
        bad = H.prune(bad)
        k = next(i for i, (a2, b2, w2) in enumerate(bad, 1) if (a2, b2, w2) == (q, r, lab))
        errs = q7.check(bad, allowed)
        if (len(errs) == 1 and errs[0].startswith(f"шаг {k}:") and not q7.qtaut(P, r, nmax=2) and len(bad) >= 6
                and k < len(bad)):
            break
    else:
        raise RuntimeError("нет ошибочного шага")
    cond = (f"{CONV} Студент вывел в $S^s_{{cq}}$ формулу ${ftex(P, r)}$. Найдите в выводе неверный шаг, назовите "
            f"нарушенное условие схемы или правила и объясните, что из найденной ошибки следует для последней строки. "
            f"{sch}\n\n{H.show(bad)}")
    ans = f"Шаг {k}: не пример {lab} — {H.BAD_SHORT[kind]}; последняя строка поэтому не доказана."
    sol = (f"Остальные шаги проверяются по схемам и правилам и верны. Шаг {k}: ${ftex(q, r)}$ [{lab}] — "
           f"{H.BAD_WHY[kind]}. Последняя строка опирается на шаг {k}, поэтому вывод формулы ${ftex(P, r)}$ не получен "
           "(и, как покажет § 7, она не тавтология).")
    return card(level, "E", "vary", "text", src, "кванторы, вывод, диагностика", cond, ans, sol)


# ---- составные замены и почти-примеры схем
def c_subst_series(scheme="A5", level=5):
    """Серия: пример ли формула схемы (с условием на свободные вхождения)."""
    out = []
    pool_yes, pool_no = [], []
    for _ in range(400):
        X = rich_stmt(2, 1, need_mixed=False) if rnd.random() < 0.7 else compound()
        if len(tex(X)) > 60:
            continue
        P, Qf = {"A5": (EX("a", X), ALL("a", X)), "T17": (X, ALL("a", X)), "T18": (EX("a", X), X),
                 "T7": (N(ALL("a", X)), N(EX("a", X)))}[scheme]
        sch = q7.SCQ.get(scheme) or q7.T6[scheme]
        ok = q7.inst_of(sch, P, Qf) is not None
        (pool_yes if ok else pool_no).append((P, Qf, X))
    # «ловушки»: a входит, но только связанно
    tricky = [t for t in pool_yes if "a" in q7.terms(t[2])]
    tricky_no = [t for t in pool_no if any(tt == "a" and not fr for tt, fr in q7.occurrences(t[2]))]
    pick = rnd.sample(tricky, min(2, len(tricky))) + rnd.sample(tricky_no or pool_no, 1)
    pick += rnd.sample([t for t in pool_no if t not in pick], 1)
    pick += rnd.sample([t for t in pool_yes if t not in pick], 1)
    rnd.shuffle(pick)
    stex = {"A5": "(\\exists a)x \\vdash (\\forall a)x", "T17": "x \\vdash (\\forall a)x", "T18": "(\\exists a)x \\vdash x",
            "T7": "\\sim(\\forall a)x \\vdash \\sim(\\exists a)x"}[scheme]
    where = {"A5": "схема A5 (с. 99)", "T17": "теоремная схема T17 (с. 104)", "T18": "теоремная схема T18 (с. 104)",
             "T7": "теоремная схема T7 (с. 103)"}[scheme]
    ans, sol = [], []
    for k, (P, Qf, X) in enumerate(pick):
        bad = [n for n, (t, fr) in enumerate(q7.occurrences(X)) if t == "a" and fr]
        if not bad:
            ans.append(f"{L[k]}) пример ($x$ := ${tex(X)}$)")
            sol.append(f"{L[k]}) $x$ := ${tex(X)}$; " + ("термин $a$ в $x$ не входит" if "a" not in q7.terms(X) else
                       "все вхождения $a$ в $x$ связанные (стоят в частях вида $(Ka)z$, D5)") + " — условие выполнено.")
        else:
            es = [e for e in els(X)]
            occ = q7.occurrences(X)
            e = es[bad[0] // 2]
            ans.append(f"{L[k]}) не пример: $a$ свободно в ${tex(e)}$")
            sol.append(f"{L[k]}) Вид схемы есть ($x$ := ${tex(X)}$), но вхождение $a$ в ${tex(e)}$ свободное (не стоит в "
                       "части $(Ka)z$, D5) — условие нарушено.")
    cond = (f"{CONV} {where[0].upper() + where[1:]}: ${stex}$, где $a$ не входит свободно в $x$. Для каждой формулы "
            "установите, получается ли она из схемы заменой $x$ высказыванием; для полученной укажите замену и проверьте "
            "условие на вхождения (D5 § 1, с. 99), для неполученной назовите, что мешает.\n\n"
            + items([f"${ftex(P, Qf)}$" for P, Qf, _ in pick]))
    return card(level, "A", "iso", "short", "с. 99, 103–104, гл. 7, § 1–2, 6", "кванторы, схемы, условие на вхождения",
                cond, "; ".join(ans), "\n".join(sol))


SC_TEX = q7.SCQ_TEX


def near_inst(name, X, Y):
    """Почти-пример схемы name: (посылка, заключение, что мешает)."""
    a = "a"
    if name == "A3":
        return (C(EX(a, X), EX(a, Y)), EX(a, C(X, Y)), "в посылке A3 первый множитель — с квантором общности "
                "$(\\forall a)x$, а здесь — $(\\exists a)$")
    if name == "A4":
        return (ALL(a, W(X, Y)), W(ALL(a, X), ALL(a, Y)), "во втором члене заключения A4 стоит $(\\exists a)y$, а здесь "
                "$(\\forall a)$")
    if name == "A6":
        return (ALL(a, X), N(EX(a, X)), "в заключении A6 отрицание стоит и перед $(\\exists a)$, и перед $x$: "
                f"должно быть ${tex(N(EX(a, N(X))))}$")
    if name == "A7":
        return (N(EX(a, X)), ALL(a, N(X)), "посылка A7 — $\\sim(\\exists a)\\sim x$ с отрицанием под квантором; здесь "
                f"под квантором стоит ${tex(X)}$ без отрицания, а заключение схемы было бы $(\\forall a)y$ при "
                f"$\\sim y$ = ${tex(X)}$")
    if name == "A2":
        Z = q7.EL("c", X[2]) if X[0] == "el" else cd
        return (X, EX(a, Z), "в заключении A2 под квантором стоит то же высказывание $x$, что и в посылке")
    if name == "A1":
        e = X if X[0] == "el" else ab
        r = EL("c" if e[1] == "a" else e[1], "c" if e[2] == "a" else e[2])
        return (ALL(a, e), r, "A1 оставляет под снятым квантором тот же $x$; замена термина $a$ на другой термин "
                "схемой не предусмотрена")
    raise ValueError(name)


def c_subst(name, yes, level=None):
    for _ in range(200):
        X, Y = compound(), compound()
        if X != Y:
            break
    if yes:
        sb = {"x": X, "y": Y, "@a": "a"}
        P, Qf = q7.build_inst(q7.SCQ[name], sb)
        assert q7.inst_of(q7.SCQ[name], P, Qf) is not None
    else:
        P, Qf, why = near_inst(name, X, Y)
        assert q7.inst_of(q7.SCQ[name], P, Qf) is None, (name, ftex(P, Qf))
    cond = (f"{CONV} Схема {name} системы $S^s_{{cq}}$ (с. 99): ${SC_TEX[name]}$. Установите, получается ли из неё формула "
            f"${ftex(P, Qf)}$ заменой $a$ термином, а $x$, $y$ — высказываниями (одинаковые буквы — одинаково). Если "
            "получается — укажите замену; если нет — назовите место, которое мешает.")
    if yes:
        st = f"$x$ := ${tex(X)}$" + (f", $y$ := ${tex(Y)}$" if name in ("A3", "A4") else "")
        return card(level or 4, "A", "vary", "short", SRC2, "кванторы, схемы, подстановка", cond, f"Получается: {st}.",
                    f"1. Посылка ${tex(P)}$ задаёт замену: {st}.\n2. При этой замене заключение схемы даёт ${tex(Qf)}$ — "
                    f"заключение данной формулы.\n3. Формула — пример {name} (с. 99).")
    return card(level or 4, "E", "vary", "short", SRC2, "кванторы, схемы, почти-пример", cond, f"Не получается: {why}.",
                f"1. Сравниваем главные операторы посылки и заключения формулы и схемы {name} ({SC_TEX[name]}).\n"
                f"2. Расхождение: {why}.\n3. Другой замены нет — формула не пример {name} (с. 99).")


def all_schemes(P, Qf, names):
    return [n for n in names if q7.inst_of(q7.SCQ.get(n) or q7.T6[n], P, Qf) is not None]


def c_recog(level=4):
    X, Y = two()
    Z = rnd.choice(NO_A)
    pool = [q7.build_inst(q7.SCQ["A3"], {"x": X, "y": Y, "@a": "a"}),
            q7.build_inst(q7.SCQ["A5"], {"x": C(Z, ALL("a", X)), "@a": "a"}),
            q7.build_inst(q7.SCQ["A2"], {"x": ALL("a", X), "@a": "a"}),
            q7.build_inst(q7.SCQ["A7"], {"x": W(X, Y), "@a": "a"}),
            near_inst(rnd.choice(["A4", "A6", "A3"]), X, Y)[:2],
            (EX("a", X), ALL("a", X))]
    pool = rnd.sample(pool, 5)
    names = ["A1", "A2", "A3", "A4", "A5", "A6", "A7"]
    ans = "; ".join(f"{L[k]}) " + (", ".join(all_schemes(P, Qf, names)) or "ни одной") for k, (P, Qf) in enumerate(pool))
    sol = []
    for k, (P, Qf) in enumerate(pool):
        s = all_schemes(P, Qf, names)
        if s:
            sol.append(f"{L[k]}) {', '.join(s)}: формула получается заменой букв" +
                       (" (условие A5 выполнено: $a$ не входит свободно в $x$)" if "A5" in s else "") + ".")
        elif P[0] == "ex" and Qf == ALL(P[1], P[2]):
            sol.append(f"{L[k]}) ни одной: вид A5 есть, но $a$ входит в $x$ свободно — условие A5 нарушено.")
        else:
            sol.append(f"{L[k]}) ни одной: вид посылки и заключения не совпадает ни с одной схемой.")
    cond = (f"{CONV} Для каждой формулы найдите все аксиомные схемы A1–A7 $S^s_{{cq}}$ (с. 99), примером которых она "
            f"является (с учётом условия A5); если ни одной — объясните, что мешает. {SCH2.split(' R1:')[0]}.\n\n"
            + items([f"${ftex(P, Qf)}$" for P, Qf in pool]))
    return card(level, "R", "iso", "short", SRC2, "кванторы, схемы", cond, ans, "\n".join(sol))


NAT2 = [
    ("Все $a$ суть $b$ и суть $c$. Следовательно, все $a$ суть $b$, а некоторые $a$ суть $c$", "t20", (ab, ac)),
    ("Каждое $a$ есть $b$, а некоторое $a$ есть $c$. Значит, некоторое $a$ есть $c$ и есть $b$", "a3", (ab, ac)),
    ("Неверно, что некоторое $a$ не есть $b$ или $c$. Следовательно, каждое $a$ есть $c$ или некоторое $a$ есть $b$",
     "a4b", (ac, ab)),
    ("Найдётся $a$, которое есть $b$, причём $c$ есть $d$. Значит, некоторое $a$ есть $b$, а $c$ есть $d$ при любом $a$",
     "a5", (ab, cd)),
]


def c_nat2(k, level=6):
    s, kind, (X, Y) = NAT2[k]
    d = {"t20": lambda: H.plan_t20(X, Y, "a", random.Random(1)), "a3": lambda: H.plan_a3(X, Y, "a", random.Random(1)),
         "a4b": lambda: H.plan_a4b(X, Y, "a", random.Random(2)), "a5": lambda: H.plan_a5(X, Y, "a", random.Random(5))}[kind]()
    lines = d.lines
    assert not q7.check(lines, H.AX2)
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} $(a \\leftarrow b)$ читается «$a$ есть $b$», $\\forall$ — «все», $\\exists$ — «некоторые» (с. 98). "
            f"Запишите рассуждение «{s}» формулой следования и выведите её в $S^s_{{cq}}$. {SCH2}")
    return card(level, "F", "transfer", "proof", SRC2, "кванторы, формализация, вывод", cond,
                f"${ftex(a, b)}$; вывод в {len(lines)} строк — в решении.", H.show(lines) + "\n\n" + SCH2, form="nat")


# ================================================================ § 3–4: MT1–MT3 § 3, бескванторные формы
CRIT3 = ("MT1 § 3 (с. 100): в доказуемых формулах $x \\vdash y$ в заключение не входят элементарные высказывания, "
         "отсутствующие в посылке; MT2 — следствие: недоказуемы формулы, в заключение которых входят термины, "
         "отсутствующие в посылке; MT3: если $x \\vdash y$ доказуема в $S^s_{cq}$, то её бескванторная форма "
         "доказуема в $S^s$ (сильная тавтология).")


def unprov_reason(p, q):
    """Причина недоказуемости по § 3 или None."""
    newe = q7.patoms(qfree(q)) - q7.patoms(qfree(p))
    newt = q7.terms(q) - q7.terms(p)
    if newt:
        t = sorted(newt)[0]
        return "MT2", (f"в заключение входит термин ${t}$, которого нет в посылке — по MT2 § 3 (с. 100) формула "
                       "недоказуема")
    if newe:
        e = sorted(newe, key=tex)[0]
        return "MT1", (f"в заключение входит элементарное высказывание ${tex(e)}$, отсутствующее в посылке — по MT1 § 3 "
                       "(с. 100) формула недоказуема")
    if not q7.ss_theorem(qfree(p), qfree(q)):
        e = next(e for e in q7.penvs(qfree(p), qfree(q)) if q7.pval(qfree(p), e) and not q7.pval(qfree(q), e))
        return "MT3", (f"бескванторная форма ${ftex(qfree(p), qfree(q))}$ не тавтология (при {q7.env_tex(e)} посылка 1, "
                       "заключение 0), значит, недоказуема в $S^s$, и по MT3 § 3 формула недоказуема")
    return None


def mutate(p, q):
    """Недоказуемые родственники доказуемой формулы."""
    out = []
    # новое элементарное высказывание / термин
    out.append((p, C(q, EL("c", "d")) if EL("c", "d") not in q7.patoms(qfree(p)) else C(q, EL("d", "c"))))
    out.append((p, W(q, EL("a", "e"))))
    out.append((p, N(q)))
    out.append((q, C(p, q)) if q7.patoms(qfree(p)) - q7.patoms(qfree(q)) else (p, N(q)))
    return out


def c_series3(level=6, src="с. 100, гл. 7, § 2–3"):
    its = []
    tries = 0
    while len(its) < 5 and tries < 500:
        tries += 1
        want = ["prov", "MT1", "MT3", "MT2", rnd.choice(["prov", "MT3", "MT1"])][len(its)]
        if want == "prov":
            lines = deriv_ok(5, 12)
            p, q = lines[-1][0], lines[-1][1]
            if len(tex(p)) + len(tex(q)) > 120:
                continue
            its.append((p, q, None, lines))
        else:
            lines = deriv_ok(5, 12)
            for p, q in mutate(lines[-1][0], lines[-1][1]):
                r = unprov_reason(p, q)
                if r and r[0] == want and len(tex(p)) + len(tex(q)) <= 120:
                    its.append((p, q, r, None))
                    break
    rnd.shuffle(its)
    ans, sol = [], []
    for k, (p, q, r, lines) in enumerate(its):
        if r is None:
            ans.append(f"{L[k]}) доказуема")
            sol.append(f"{L[k]}) Доказуема; вывод:\n\n" + H.show(lines) + "\n")
        else:
            ans.append(f"{L[k]}) недоказуема ({r[0]} § 3)")
            sol.append(f"{L[k]}) Недоказуема: {r[1]}.")
    cond = (f"{CONV} Исследуйте доказуемость в $S^s_{{cq}}$ каждой формулы: доказуемую выведите (схемы A1–A7, R1, R2, "
            f"ссылки на $S^s$), для недоказуемой укажите основание из § 3. {CRIT3}\n\n"
            + items([f"${ftex(p, q)}$" for p, q, _, _ in its]))
    return card(level, "C", "open", "short", src, "кванторы, непарадоксальность, доказуемость", cond, "; ".join(ans),
                "\n".join(sol) + "\n\n" + SCH2)


def c_series3_diag(level=6):
    its = []
    while len(its) < 4:
        lines = deriv_ok(5, 12)
        p, q = lines[-1][0], lines[-1][1]
        if len(its) % 2 == 0:
            if len(tex(p)) + len(tex(q)) <= 110:
                its.append((p, q, None))
        else:
            for p2, q2 in mutate(p, q):
                r = unprov_reason(p2, q2)
                if r and len(tex(p2)) + len(tex(q2)) <= 110:
                    its.append((p2, q2, r))
                    break
    rnd.shuffle(its)
    wrong = rnd.sample(range(4), 2)
    lines_t, ans, sol = [], [], []
    for k, (p, q, r) in enumerate(its):
        if k in wrong:
            if r is None:
                claim = rnd.choice(["недоказуема: в заключение входят кванторные группы, которых нет в посылке",
                                    "недоказуема по MT3 § 3: её бескванторная форма не тавтология"])
                ans.append(f"{k + 1}: доказуема")
                qf = ftex(qfree(p), qfree(q))
                sol.append(f"{k + 1}. Неверно. Бескванторная форма ${qf}$ — сильная тавтология; MT1–MT3 § 3 — лишь "
                           "необходимые условия, кванторные группы в них не учитываются; формула выводится (её вывод "
                           "строится по схемам A1–A7, R1, R2).")
            else:
                claim = "доказуема: её бескванторная форма доказуема в $S^s$" if r[0] != "MT3" else \
                    "доказуема: в заключении нет новых элементарных высказываний"
                if r[0] == "MT3" and "бескванторная форма доказуема" in claim:
                    claim = "доказуема: в заключении нет новых элементарных высказываний"
                ans.append(f"{k + 1}: недоказуема ({r[0]})")
                sol.append(f"{k + 1}. Неверно: {r[1]}.")
        else:
            claim = "доказуема" if r is None else f"недоказуема по {r[0]} § 3"
        lines_t.append(f"{k + 1}. ${ftex(p, q)}$ — {claim}.")
    cond = (f"{CONV} Студент исследовал доказуемость четырёх формул в $S^s_{{cq}}$:\n\n" + "\n".join(lines_t) +
            f"\n\nРовно два вывода неверны. Найдите их и обоснуйте верный ответ. {CRIT3}")
    return card(level, "E", "vary", "text", "с. 100, гл. 7, § 3", "кванторы, непарадоксальность, диагностика", cond,
                "; ".join(ans), "\n".join(sol) + "\n\nОстальные выводы верны.")


def c_lines_mt1(level=5):
    lines = deriv_ok(8, 11)
    rows = []
    for n, (a, b, w) in enumerate(lines, 1):
        pa, pb = q7.patoms(qfree(a)), q7.patoms(qfree(b))
        rows.append(f"{n}) " + ", ".join(f"${tex(e)}$" for e in sorted(pb, key=tex)) + " ⊆ " +
                    ", ".join(f"${tex(e)}$" for e in sorted(pa, key=tex)))
        assert pb <= pa
    cond = (f"{CONV} Для каждой строки вывода проверьте свойство из MT1 § 3 (с. 100): элементарные высказывания "
            "заключения входят в посылку. Объясните, почему схема или правило, указанные в основании, это свойство "
            f"сохраняет. {SCH2}\n\n{H.show(lines)}")
    sol = ("Множество элементарных высказываний заключения ⊆ множеству посылки:\n\n" + "\n".join(rows) +
           "\n\nСхемы A1–A7: если отбросить кванторные группы и отрицания и исключить повторения, в посылке и заключении "
           "одни и те же высказывания (с. 100). [$S^s$] — сильная тавтология (условие на элементарные высказывания входит "
           "в определение). R1, R2 навешивают одну группу на обе части; R1 $S^s$: если элементарные высказывания $z$ — в "
           "$y$, а $y$ — в $x$, то $z$ — в $x$; R2 $S^s$: элементарные высказывания $yz$ — в $x$, если в $x$ входят и те, и "
           "другие.")
    return card(level, "C", "iso", "text", "с. 100, гл. 7, § 3", "кванторы, непарадоксальность", cond,
                "Свойство выполнено во всех строках (перечень — в решении).", sol)


def c_build3():
    p, q = EX("a", ab), ALL("a", ab)
    cond = (f"{CONV} Постройте формулу $x \\vdash y$ системы $S^s_{{cq}}$ или докажите, что её нет: (1) в заключение не "
            "входят ни элементарные высказывания, ни термины, отсутствующие в посылке; (2) бескванторная форма доказуема "
            "в $S^s$; (3) формула не является примером ни одной аксиомной схемы A1–A7. Затем объясните, почему MT1–MT3 "
            f"§ 3 ничего не говорят о доказуемости такой формулы. {CRIT3}")
    ans = (f"Например, ${ftex(p, q)}$: условия выполнены (это не пример A5 — $a$ свободен в $x$); MT1–MT3 дают лишь "
           "необходимые условия доказуемости.")
    assert unprov_reason(p, q) is None and q7.inst_of(q7.SCQ["A5"], p, q) is None
    sol = (f"1. ${ftex(p, q)}$: элементарное высказывание одно, $(a \\leftarrow b)$; термины $a$, $b$ — в обеих частях.\n"
           "2. Бескванторная форма $(a \\leftarrow b) \\vdash (a \\leftarrow b)$ — теорема $S^s$.\n"
           "3. Вид A5 есть, но $a$ входит в $x = (a \\leftarrow b)$ свободно — условие A5 нарушено; с остальными схемами "
           "не совпадают главные операторы.\n"
           "4. MT1, MT2 и MT3 § 3 — утверждения вида «если доказуема, то …»: они позволяют доказать недоказуемость, но "
           "не доказуемость. Для этой формулы все необходимые условия выполнены, а вопрос о её доказуемости решается "
           "позже: по § 7 она не тавтология (при двух отмеченных терминах), по § 9 — недоказуема.")
    return card(6, "C", "open", "build", "с. 99–100, гл. 7, § 2–3", "кванторы, непарадоксальность, построение", cond,
                ans, sol)


def c_qf_lines(level=5):
    lines = deriv_ok(8, 11)
    rows = [f"{n}) ${ftex(qfree(a), qfree(b))}$" for n, (a, b, w) in enumerate(lines, 1)]
    for a, b, w in lines:
        assert q7.ss_theorem(qfree(a), qfree(b))
    cond = (f"{CONV} Запишите бескванторные формы (D7 § 1) всех строк вывода и проверьте, что каждая доказуема в $S^s$ "
            f"— так, как в доказательстве непротиворечивости $S^s_{{cq}}$ (§ 4, с. 100–101). {SCH2}\n\n{H.show(lines)}")
    sol = ("Бескванторные формы:\n\n" + "\n".join(rows) + "\n\nБескванторные формы примеров A1–A7 имеют вид $x \\vdash x$, "
           "$xy \\vdash xy$, $x \\vee y \\vdash x \\vee y$, $x \\vdash \\sim\\sim x$, $\\sim\\sim x \\vdash x$ (с. 101) — "
           "теоремы $S^s$; строки [R1], [R2] имеют ту же бескванторную форму, что и строка, к которой правило применено; "
           "[$S^s$] — уже бескванторна по строению; R1 $S^s$ и R2 $S^s$ переводят бескванторные формы посылок в "
           "бескванторную форму заключения.")
    return card(level, "T", "iso", "text", "с. 100–101, гл. 7, § 4", "кванторы, непротиворечивость, бескванторная форма",
                cond, "Все бескванторные формы — теоремы $S^s$ (перечень в решении).", sol)


def c_series4(level=6):
    its = []
    while len(its) < 5:
        lines = deriv_ok(5, 12)
        p, q = lines[-1][0], lines[-1][1]
        if len(its) in (1, 3):
            p, q = rnd.choice(mutate(p, q))
        if len(tex(p)) + len(tex(q)) <= 120 and (p, q) not in its:
            its.append((p, q))
    ans, sol = [], []
    for k, (p, q) in enumerate(its):
        pp, qq = qfree(p), qfree(q)
        st = q7.ss_theorem(pp, qq)
        ans.append(f"{L[k]}) ${ftex(pp, qq)}$ — " + ("доказуема в $S^s$" if st else "недоказуема в $S^s$"))
        if st:
            sol.append(f"{L[k]}) ${ftex(pp, qq)}$ — сильная тавтология; метод § 4 не запрещает доказуемость формулы (но и "
                       "не доказывает её).")
        else:
            r = unprov_reason(p, q)
            sol.append(f"{L[k]}) ${ftex(pp, qq)}$ — не теорема $S^s$; значит, ${ftex(p, q)}$ недоказуема в $S^s_{{cq}}$: "
                       "по § 4 бескванторные формы теорем $S^s_{cq}$ доказуемы в $S^s$." + (f" ({r[1]}.)" if r else ""))
    cond = (f"{CONV} Для каждой формулы запишите бескванторную форму (D7 § 1, с. 99), исследуйте её доказуемость в "
            "$S^s$ (сильная тавтология) и сделайте вывод о формуле по § 4 (с. 100–101): бескванторные формы доказуемых "
            "формул $S^s_{cq}$ доказуемы в $S^s$.\n\n" + items([f"${ftex(p, q)}$" for p, q in its]))
    return card(level, "C", "open", "short", "с. 99–101, гл. 7, § 1, 4", "кванторы, непротиворечивость", cond,
                "; ".join(ans), "\n".join(sol))


def c_badlines4(level=6):
    """Студенческий «вывод» с двумя строками, бескванторные формы которых не теоремы S^s."""
    for _ in range(500):
        lines = deriv_ok(8, 11)
        P = lines[-1][0]
        cands = [n for n, (a, b, w) in enumerate(lines, 1) if isinstance(w, str) and w in ("A1", "A2", "A6", "A7")]
        if len(cands) >= 2:
            break
    i, j = rnd.sample(cands, 2)
    bad = list(lines)
    for n in (i, j):
        a, b, w = bad[n - 1]
        if w == "A1":
            nb = q7.qfree(b) if False else b
            e = els(b)[0]
            rep = EL("c" if e[1] == "a" else e[1], "d" if e[2] in ("a", "b") else e[2])
            nb = substitute_el(b, e, rep)
        elif w == "A2":
            nb = EX(b[1], substitute_el(b[2], els(b[2])[0], EL("d", "c")))
        elif w == "A6":
            nb = N(EX(b[1][1], b[1][2][1]))
        else:
            nb = ALL(b[1], N(b[2]))
        bad[n - 1] = (a, nb, w)
    errs = []
    for n in sorted((i, j)):
        a, b, w = bad[n - 1]
        errs.append(n)
    cond = (f"{CONV} Проверьте строки вывода методом § 4 (с. 100–101): запишите бескванторные формы указанных шагов "
            "[A1], [A2], [A6], [A7] и найдите строки, бескванторные формы которых не доказуемы в $S^s$. Объясните, что "
            "отсюда следует для этих строк и для вывода в целом. Ссылки на строки после ошибочных не проверяйте.\n\n"
            + "\n".join(f"{n}. ${ftex(a, b)}$ [{q7.why_text(w)}]" for n, (a, b, w) in enumerate(bad, 1)
                        if isinstance(w, str)))
    sol = []
    for n, (a, b, w) in enumerate(bad, 1):
        if not isinstance(w, str):
            continue
        st = q7.ss_theorem(qfree(a), qfree(b))
        sol.append(f"{n}. ${ftex(qfree(a), qfree(b))}$ — " + ("теорема $S^s$." if st else
                   "не теорема $S^s$: по MT3 § 3 (§ 4) строка недоказуема в $S^s_{cq}$, основание указано неверно."))
    bads = [n for n, (a, b, w) in enumerate(bad, 1) if isinstance(w, str) and not q7.ss_theorem(qfree(a), qfree(b))]
    assert sorted(bads) == sorted(errs), (bads, errs)
    return card(level, "E", "vary", "text", "с. 100–101, гл. 7, § 3–4", "кванторы, непротиворечивость, диагностика",
                cond, f"Ошибочны строки {', '.join(map(str, sorted(bads)))}: их бескванторные формы не теоремы $S^s$.",
                "\n".join(sol) + "\n\nВерные бескванторные формы схем — с. 101.")


def substitute_el(f, e, r):
    k = f[0]
    if f == e:
        return r
    if k in ("el", "v"):
        return f
    if k == "neg":
        return N(substitute_el(f[1], e, r))
    if k in q7.QK:
        return (k, f[1], substitute_el(f[2], e, r))
    return (k, tuple(substitute_el(a, e, r) for a in f[1]))


def c_qf_same(level=7):
    p1, q1 = ALL("a", C(ab, cb)), C(ab, cb)
    p2, q2 = ALL("a", C(ab, cb)), C(EL("d", "b"), cb)
    cond = (f"{CONV} Постройте две формулы, бескванторные формы которых совпадают и доказуемы в $S^s$, причём первая — "
            "пример аксиомной схемы $S^s_{cq}$, а вторая недоказуема в $S^s_{cq}$; или докажите, что таких формул нет. "
            "Объясните, почему метод § 4 (с. 100–101) их не различает.")
    ans = ("Например, $(\\forall a)(a \\leftarrow b) \\vdash (a \\leftarrow b)$ (A1) и $(\\exists a)(a \\leftarrow b) "
           "\\vdash (\\forall a)(a \\leftarrow b)$ (не пример A5): бескванторная форма у обеих $(a \\leftarrow b) \\vdash "
           "(a \\leftarrow b)$.")
    sol = ("1. $(\\forall a)(a \\leftarrow b) \\vdash (a \\leftarrow b)$ — пример A1 (с. 99), доказуема.\n"
           "2. $(\\exists a)(a \\leftarrow b) \\vdash (\\forall a)(a \\leftarrow b)$: $a$ входит свободно в "
           "$(a \\leftarrow b)$, это не пример A5. Её недоказуемость устанавливается позже: по § 7 при двух отмеченных "
           "терминах $(1a \\leftarrow b) \\vee (2a \\leftarrow b) \\vdash (1a \\leftarrow b)(2a \\leftarrow b)$ при "
           "$(1a \\leftarrow b) = 1$, $(2a \\leftarrow b) = 0$ имеет значение 0, а по процедуре § 9 нетавтологичная "
           "формула, совпадающая со своей контрольной формой, недоказуема.\n"
           "3. Бескванторная форма у обеих одна — $(a \\leftarrow b) \\vdash (a \\leftarrow b)$, теорема $S^s$. Метод § 4 "
           "отбрасывает кванторные группы и потому не видит разницы между $\\forall$ и $\\exists$ — он даёт лишь "
           "необходимое условие доказуемости (MT3 § 3).")
    return card(level, "S", "transfer", "build", "с. 99–101, 105, 120, гл. 7, § 2–4, 7, 9", "кванторы, непротиворечивость",
                cond, ans, sol)


# ================================================================ § 5: независимость
def val_rule(rule, p, q):
    fp, fq = q7.free_terms(p), q7.free_terms(q)
    if rule == "A1" and fq - fp:
        t = sorted(fq - fp)[0]
        return 0, f"термин ${t}$ входит свободно в заключение, а в посылку свободно не входит — исключающее правило: 0"
    if rule == "A2" and fp - fq:
        t = sorted(fp - fq)[0]
        return 0, f"термин ${t}$ входит свободно в посылку, а в заключение свободно не входит — исключающее правило: 0"
    s = q7.ss_theorem(qfree(p), qfree(q))
    return int(s), (f"исключающее правило неприменимо; по общему правилу — значение бескванторной формы "
                    f"${ftex(qfree(p), qfree(q))}$: {int(s)}")


RULES5 = {"A1": "если в $x \\vdash y$ термин $a$ входит в $y$ свободно, а в $x$ — нет, то $x \\vdash y$ имеет значение 0",
          "A2": "если в $x \\vdash y$ термин $a$ входит в $x$ свободно, а в $y$ — нет, то $x \\vdash y$ имеет значение 0"}
GEN5 = ("общее правило: прочие формулы равнозначны своим бескванторным формам (с. 102); бескванторной форме "
        "приписываем 1, если она доказуема в $S^s$, и 0 иначе")


def inst_compound(name):
    X, Y = two()
    if name == "A5":
        X = C(rnd.choice(NO_A), ALL("a", compound()))
    if name == "A1" and not free_in("a", X):
        X = C(ab, X)
    return q7.build_inst(q7.SCQ[name], {"x": X, "y": Y, "@a": "a"})


def c_val5(rule, level=5):
    names = rnd.sample(["A1", "A2", "A3", "A4", "A5", "A6", "A7"], 3)
    if rule not in names:
        names[0] = rule
    its = [inst_compound(n) for n in names]
    lines = deriv_ok(5, 10)
    its.append((lines[-1][0], lines[-1][1]))
    res = [val_rule(rule, p, q) for p, q in its]
    cond = (f"{CONV} Для доказательства независимости {rule} приняты правила (§ 5, с. 101–102): исключающее — "
            f"{RULES5[rule]}; {GEN5}. Сначала применяется исключающее правило, затем общее. Найдите значения формул "
            "(первые три — примеры схем $S^s_{cq}$, последняя — теорема $S^s_{cq}$) и объясните, что показывают "
            "результаты.\n\n" + items([f"${ftex(p, q)}$" for p, q in its]))
    ans = "; ".join(f"{L[k]}) {r[0]}" for k, r in enumerate(res))
    sol = "\n".join(f"{L[k]}) {r[1]}." for k, r in enumerate(res))
    zero = [names[k] for k in range(3) if res[k][0] == 0]
    sol += (f"\n\nЗначение 0 получил только пример {rule}" if zero == [rule] else
            f"\n\nЗначение 0 получили примеры: {', '.join(zero) or 'нет'}") + \
        f" (при правилах для {rule} значение 0 получают лишь формулы, «нарушающие» связь, выраженную {rule}; " \
        "прочие схемы и правила сохраняют значение 1 — так доказывается независимость, с. 101)."
    return card(level, "V", "iso", "short", "с. 101–102, гл. 7, § 5", "кванторы, независимость", cond, ans, sol)


def c_val5_diag(level=6):
    rule = rnd.choice(["A1", "A2"])
    its = [inst_compound(n) for n in rnd.sample(["A1", "A2", "A3", "A4", "A6", "A7"], 4)]
    res = [val_rule(rule, p, q) for p, q in its]
    wrong = rnd.sample(range(4), 2)
    body = "\n".join(f"{k + 1}. ${ftex(p, q)}$ — {1 - r[0] if k in wrong else r[0]}" for k, ((p, q), r) in
                     enumerate(zip(its, res)))
    cond = (f"{CONV} Правила для независимости {rule} (§ 5, с. 101–102): исключающее — {RULES5[rule]}; {GEN5}. Студент "
            f"нашёл значения четырёх формул; ровно два значения неверны. Найдите их и обоснуйте.\n\n{body}")
    ans = "; ".join(f"строка {k + 1}: {res[k][0]}" for k in sorted(wrong))
    sol = "\n".join(f"Строка {k + 1}: {res[k][1]}." for k in sorted(wrong)) + \
        "\n\nТипичные ошибки: исключающее правило применено «наоборот» (для A1 смотрят свободные вхождения в заключении, " \
        "для A2 — в посылке) или оно забыто и сразу взята бескванторная форма."
    return card(level, "E", "vary", "text", "с. 101–102, гл. 7, § 5", "кванторы, независимость, диагностика", cond, ans,
                sol)


def c_val5_all(level=6):
    rule = rnd.choice(["A1", "A2"])
    others = [n for n in ["A2", "A3", "A4", "A5", "A6", "A7", "A1"] if n != rule][:5]
    its = [inst_compound(n) for n in others]
    res = [val_rule(rule, p, q) for p, q in its]
    assert all(r[0] == 1 for r in res), [(ftex(*i), r) for i, r in zip(its, res)]
    cond = (f"{CONV} Покажите на примерах с составными $x$, $y$, что при правилах для независимости {rule} (§ 5, "
            f"с. 101–102: исключающее — {RULES5[rule]}; {GEN5}) аксиомы других схем получают значение 1. Затем объясните, "
            "почему так будет для любых примеров этих схем.\n\n" + items([f"${ftex(p, q)}$ ({n})" for (p, q), n in
                                                                       zip(its, others)]))
    sol = "\n".join(f"{L[k]}) {r[1]}." for k, r in enumerate(res))
    sol += ("\n\nВ общем случае: " + ("в A2–A7 нет термина, свободного в заключении и не свободного в посылке (A2 "
                                     "связывает $a$ в заключении, в A3–A7 группы одинаковы по обе стороны)" if rule == "A1"
                                     else "в A1, A3–A7 нет термина, свободного в посылке и не свободного в заключении "
                                          "(A1 освобождает $a$ в заключении, в A3–A7 группы одинаковы по обе стороны)") +
            "; по общему правилу значение — 1, так как бескванторные формы схем ($x \\vdash x$, $xy \\vdash xy$, "
            "$x \\vee y \\vdash x \\vee y$, $x \\vdash \\sim\\sim x$, $\\sim\\sim x \\vdash x$, с. 101) — теоремы $S^s$.")
    return card(level, "V", "vary", "text", "с. 101–102, гл. 7, § 5", "кванторы, независимость", cond,
                "Все значения — 1 (обоснование в решении).", sol)


def c_rule5(level=5):
    k = rnd.choice(["R1", "R2"])
    z, v = rnd.choice([(EL("b", "c"), EL("b", "d")), (EL("b", "a"), EL("b", "d")), (EL("b", "c"), N(EL("b", "d")))])
    Kq = ALL if k == "R1" else EX
    p, q = Kq("b", C(z, v)), Kq("b", z)
    rule = {"R1": "если $(\\forall b)zv$ имеет значение 1 и в $z$ входит термин, отсутствующий в $v$, то $(\\forall b)z$ "
                  "имеет значение 0",
            "R2": "если $(\\exists b)(zv)$ имеет значение 1 и $z$ содержит термин, отсутствующий в $v$, то "
                  "$(\\exists b)z$ имеет значение 0"}[k]
    t = sorted(q7.terms(z) - q7.terms(v))[0]
    cond = (f"{CONV} Исключающее правило для независимости {k} (§ 5, с. 102): {rule}. Выведите в $S^s_{{cq}}$ с помощью "
            f"{k} формулу ${ftex(p, q)}$, найдите её значение по этому правилу при значении посылки 1 и объясните, что "
            f"доказывает результат.")
    ans = f"Вывод: ${ftex(C(z, v), z)}$ [$S^s$], затем [{k}]; значение 0 (в $z$ есть термин ${t}$, которого нет в $v$)."
    sol = (f"1. ${ftex(C(z, v), z)}$ — теорема $S^s$; по {k} (с. 100) — ${ftex(p, q)}$.\n"
           f"2. Посылка имеет значение 1, в $z = {tex(z)}$ входит термин ${t}$, отсутствующий в $v = {tex(v)}$; по "
           f"правилу заключение ${tex(q)}$ — 0, и формула имеет значение 0.\n"
           f"3. Прочие схемы и правила при этих правилах дают формулы со значением 1, а {k} из формулы со значением 1 "
           f"(${ftex(C(z, v), z)}$) даёт формулу со значением 0: без {k} её не вывести — {k} независимо (с. 102).")
    return card(level, "V", "vary", "short", "с. 100, 102, гл. 7, § 5", "кванторы, независимость", cond, ans, sol)


def c_hand5_e1():
    cond = (f"{CONV} Студент доказывает независимость A1 так: «При правилах для A1 формула $(\\forall a)(a \\leftarrow b) "
            "\\vdash (a \\leftarrow b)$ по общему правилу имеет значение 1, потому что её бескванторная форма "
            "$(a \\leftarrow b) \\vdash (a \\leftarrow b)$ — теорема $S^s$. А формула $(\\forall a)(a \\leftarrow b)(c "
            "\\leftarrow d) \\vdash (a \\leftarrow b)$ имеет значение 0. Значит, A1 независима». Найдите все ошибки.")
    ans = ("Сначала применяется исключающее правило (с. 101): в первой формуле $a$ свободен в заключении и не свободен в "
           "посылке — значение 0, а не 1; вторая формула — не пример A1, её значение ничего не говорит о схеме "
           "(и оно 0, а не довод независимости).")
    sol = ("1. Порядок правил (с. 101): «в каждом случае сначала применяется первое, затем — второе». Для "
           "$(\\forall a)(a \\leftarrow b) \\vdash (a \\leftarrow b)$ исключающее правило применимо: $a$ входит в "
           "заключение свободно, а в посылку — нет; значение 0. Именно это и нужно для независимости (с. 101).\n"
           "2. Вторая формула не пример A1 (посылка — конъюнкция, а не $(\\forall a)x$). Независимость требует: все "
           "аксиомы, кроме A1, получают 1, правила сохраняют 1, а некоторый пример A1 получает 0.\n"
           "3. Кроме того, студент не проверил, что прочие схемы и правила дают значение 1 (07.05: A2–A7 — 1, "
           "транзитивность сохраняет 1).")
    return card(5, "E", "vary", "text", "с. 101, гл. 7, § 5", "кванторы, независимость, диагностика", cond, ans,
                sol, form="meta")


def c_hand5_e2():
    cond = (f"{CONV} Студент: «Для независимости A5 надо отбросить ограничение на вхождение $a$ в $x$ (с. 101). Тогда "
            "$(\\exists a)(a \\leftarrow b) \\vdash (\\forall a)(a \\leftarrow b)$ становится аксиомой, и так как она не "
            "тавтология, A5 независима». Найдите ошибку в понимании метода и опишите правильный ход доказательства.")
    ans = ("Наоборот: в интерпретации для A5 формулы, где ограничение нарушено, должны получать значение, отличающее их "
           "от теорем; правило «отбрасывается ограничение» задаёт расширенную схему, примеры которой проверяются на "
           "сохранение выделенного свойства прочими схемами.")
    sol = ("Метод § 5 (с. 101): принимаются правила приписывания значений, при которых все аксиомы, кроме примеров "
           "проверяемой схемы, и все правила дают значение 1, а некоторый пример этой схемы — 0. Для A5 книга указывает "
           "лишь, что «отбрасывается ограничение на вхождение $a$ в $x$».\n"
           "Ошибка студента — он считает, что расширенная схема сама доказывает независимость. Но добавление "
           "нетавтологичной аксиомы не показывает, что A5 нельзя вывести из остальных схем. Правильный ход: показать, "
           "что A5 (с ограничением) не выводится из A1–A4, A6, A7, R1, R2, указав свойство, которое схемы и правила "
           "сохраняют, а пример A5 нарушает; правило с. 101 описывает, какое изменение в A5 отличает её от прочих схем.")
    return card(6, "E", "vary", "text", "с. 101, гл. 7, § 5", "кванторы, независимость, диагностика", cond, ans,
                sol, form="meta")


def c_zero_only():
    lines = None
    for _ in range(300):
        lines = deriv_ok(8, 12)
        vals = [val_rule("A1", a, b)[0] for a, b, w in lines]
        if any(v == 0 for v in vals):
            break
    rows = []
    for n, (a, b, w) in enumerate(lines, 1):
        v, why = val_rule("A1", a, b)
        rows.append(f"{n}. {v} — {why}")
    zero = [n for n, (a, b, w) in enumerate(lines, 1) if val_rule("A1", a, b)[0] == 0]
    cond = (f"{CONV} Найдите значения всех строк вывода по правилам для независимости A1 (§ 5, с. 101–102: "
            f"исключающее — {RULES5['A1']}; {GEN5}). Объясните, почему значение 0 могло появиться лишь на шагах, "
            f"опирающихся на A1. {SCH2}\n\n{H.show(lines)}")
    ans = ("Значение 0 у строк " + ", ".join(map(str, zero)) + "; остальные — 1.") if zero else "Все строки — 1."
    sol = "\n".join(rows) + ("\n\nПрочие схемы получают 1 (07.05: A2–A7 не создают свободных вхождений в заключении), "
                             "R1, R2 и правила $S^s$ сохраняют 1 (07.05); значит, 0 возникает только от A1.")
    return card(7, "V", "transfer", "text", "с. 101–102, гл. 7, § 5", "кванторы, независимость", cond, ans, sol)


# ================================================================ планы по номерам
def ids(sec, n):
    return [f"07.{sec:02d}-{k:03d}" for k in range(1, n + 1)]


KEEP = {}


def plan():
    P = {}
    # § 1 (занятие 48)
    s1 = [lambda: c_occ(4), lambda: c_occ(4), c_occ_diag, lambda: c_degen(5), lambda: c_qfree(4), c_qfree_diag,
          c_build_occ, c_d4d5, lambda: c_occ(5), lambda: c_nat1(5), lambda: c_occ_diag(6), lambda: c_degen(5),
          lambda: c_qfree(5, prov=True), c_same_qfree, lambda: c_nat1(5), c_impossible]
    P.update(zip(ids(1, 16), s1))
    # § 2: 1–3 — занятие 48, 4–37 — 49, 38–42 — 50; ступени 8–10 — в hard07_hand (№ 12, 20, 28, 36)
    s2 = {1: c_recog, 2: lambda: c_subst_series("A5"), 3: c_deriv,
          4: lambda: c_subst("A3", False), 5: c_complete, 6: c_deriv, 7: c_diag, 8: lambda: c_subst("A4", True),
          9: lambda: c_nat2(0), 10: c_badstep, 11: c_complete, 13: c_deriv, 14: lambda: c_subst("A6", False),
          15: c_recog, 16: c_diag, 17: c_deriv, 18: lambda: c_subst("A7", True), 19: c_complete,
          21: lambda: c_badstep(level=6), 22: c_deriv, 23: lambda: c_subst("A1", False), 24: lambda: c_nat2(1),
          25: c_diag, 26: c_complete, 27: lambda: c_subst_series("A5", 5), 29: c_deriv, 30: c_recog,
          31: lambda: c_subst("A3", True), 32: c_complete, 33: lambda: c_nat2(2), 34: c_deriv, 35: c_badstep,
          37: lambda: c_subst("A5", True) if False else c_deriv(),
          38: c_complete, 39: c_diag, 40: c_deriv, 41: lambda: c_nat2(3), 42: lambda: c_subst("A2", False)}
    P.update({f"07.02-{k:03d}": v for k, v in s2.items()})
    # § 3 (занятие 50): № 4 и 8 — прежние ручные (ступени 8, 9)
    s3 = {1: c_series3, 2: c_lines_mt1, 3: c_series3_diag, 5: c_build3, 6: lambda: c_series3(6),
          7: lambda: c_series3_diag(6), 9: lambda: c_series3(7, "с. 99–100, гл. 7, § 2–3"), 10: lambda: c_deriv("с. 99–100, гл. 7, § 2–3")}
    P.update({f"07.03-{k:03d}": v for k, v in s3.items()})
    # § 4 (занятие 50): № 6, 11, 16 — прежние ручные (8, 9, 10)
    s4 = {1: c_qf_lines, 2: c_series4, 3: c_badlines4, 4: c_qf_lines, 5: lambda: c_series4(6),
          7: lambda: c_complete("с. 99–101, гл. 7, § 2, 4"), 8: c_badlines4, 9: lambda: c_qfree_diag(5), 10: c_qf_same,
          12: lambda: c_qf_lines(5), 13: lambda: c_series4(6), 14: lambda: c_deriv("с. 99–101, гл. 7, § 2, 4"),
          15: lambda: c_deriv("с. 99–101, гл. 7, § 2, 4")}
    P.update({f"07.04-{k:03d}": v for k, v in s4.items()})
    # § 5: 1–3 — занятие 50, 4–16 — 51; № 7, 11, 15 — прежние ручные (8, 9, 10)
    s5 = {1: lambda: c_val5("A1"), 2: lambda: c_val5("A2"), 3: c_val5_diag, 4: c_rule5, 5: lambda: c_val5("A1", 5),
          6: c_hand5_e1, 8: c_val5_all, 9: lambda: c_val5("A2", 5), 10: c_val5_diag, 12: lambda: c_rule5(5),
          13: c_hand5_e2, 14: c_val5_all, 16: c_zero_only}
    P.update({f"07.05-{k:03d}": v for k, v in s5.items()})
    return P


KEEP.update({
    "07.02-028": ("07.02-041", 8), "07.02-036": ("07.02-042", None),
    "07.03-004": ("07.03-009", None), "07.03-008": ("07.03-010", None),
    "07.04-006": ("07.04-011", None), "07.04-011": ("07.04-014", None), "07.04-016": ("07.04-016", None),
    "07.05-007": ("07.05-011", None), "07.05-011": ("07.05-014", None), "07.05-015": ("07.05-016", None),
})
