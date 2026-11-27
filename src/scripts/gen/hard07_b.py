"""Задачи гл. 7, § 10–21, для hard07.py: S^5_cq, S^s*_cq, S^s_nq и её семантика, S^5_nq, классический вариант (A*13),
замена § 18, правила подстановки § 19, кванторы с несколькими терминами § 20, кванторы и условные высказывания § 21."""
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
import hard07_a3 as A3  # noqa: E402
from hard07_a import CONV, L, card, items  # noqa: E402
from q7 import (ALL, C, D, EL, EX, IMP, N, NALL, NEX, QALL, QEX, W, free_in, ftex, qf13, qfree, repl18,  # noqa: E402
                tex)

rnd = random.Random(1970_0710)
ab, ac, ad, cb, cd, db, ba = A.ab, A.ac, A.ad, A.cb, A.cd, A.db, A.ba
NQ = "S^s_nq"
CONVN = (CONV + " $(\\urcorner\\forall a)$, $(\\urcorner\\exists a)$ — кванторные группы с внутренним отрицанием, "
         "$(?\\forall a)$, $(?\\exists a)$ — с оператором неопределённости (§ 12, с. 122).")
SCHNQ = ("Схемы $S^s_{nq}$ (§ 12, с. 122–123): A1–A5 $S^s_{cq}$, R1, R2 и вместо A6, A7: $A^16$ $(\\forall a)x \\vdash "
         "(\\urcorner\\exists a)\\sim x$; $A^26$ $(\\urcorner\\forall a)x \\vdash (\\exists a)\\sim x$; $A^36$ $(?\\forall a)x "
         "\\vdash (?\\exists a)\\sim x$; $A^17$ $(\\urcorner\\exists a)\\sim x \\vdash (\\forall a)x$; $A^27$ $(\\exists a)\\sim x "
         "\\vdash (\\urcorner\\forall a)x$; $A^37$ $(?\\exists a)\\sim x \\vdash (?\\forall a)x$; дополнительные: $A^18$ "
         "$(\\forall a)x \\vdash \\sim(\\urcorner\\forall a)x\\sim(?\\forall a)x$; $A^28$ $(\\urcorner\\forall a)x \\vdash "
         "\\sim(\\forall a)x\\sim(?\\forall a)x$; $A^38$ $(?\\forall a)x \\vdash \\sim(\\forall a)x\\sim(\\urcorner\\forall a)x$; "
         "$A^19$–$A^39$ — обратные к ним; A10 $(\\urcorner\\forall a)(xy) \\vdash (\\urcorner\\forall a)x \\vee "
         "(\\urcorner\\forall a)y$; A11 — обратная; A12 $(\\urcorner\\exists a)x \\vee (\\urcorner\\exists a)y \\vdash "
         "(\\urcorner\\exists a)(xy)$. [$S^s$], R1 $S^s$, R2 $S^s$ — как в $S^s_{cq}$.")


def cardn(*a, **k):
    k.setdefault("system", NQ)
    return card(*a, **k)


# ================================================================ § 10: S^5_cq
TAUT10 = ("D1–D2 § 10 (с. 120–121): интерпретационная форма формулы $\\vdash x$ получается так: если термин входит "
          "в $x$ свободно, $\\vdash x$ заменяется на $\\vdash (\\forall a)x$ (так для всех таких терминов), далее — пп. 2, 3 "
          "D2 § 7; $\\vdash x$ — тавтология, если $x$ — тавтология при любом числе отмеченных терминов. MT1 § 10: если "
          "$\\vdash x$ доказуема в $S^5_{cq}$, она тавтология.")


def c10_series(level=6):
    its = []
    for kind in rnd.sample(["t", "t", "n", "n", "f"], 4):
        if kind == "t":
            p, q, nm, sb = A2.taut_item()
            its.append((IMP(p, q), ("t", nm, sb)))
        elif kind == "n":
            p, q = A2.nontaut_item()
            its.append((IMP(p, q), ("n",)))
        else:
            its.append((rnd.choice([IMP(ALL("a", ab), cb), IMP(cb, EX("a", ab)), IMP(ab, ALL("a", ab)),
                                    IMP(EX("a", ab), ab)]), ("n",)))
    ans, sol = [], []
    for k, (f, info) in enumerate(its):
        if info[0] == "t":
            ans.append(f"{L[k]}) тавтология")
            sol.append(f"{L[k]}) Тавтология: $x \\vdash y$ с той же посылкой и заключением — {A2.taut_text(info[1], info[2])}; "
                       "поэтому при любом $n$ форма $x \\supset y$ истинна при всех значениях.")
        else:
            cm = q7.countermodel1(f)
            assert cm
            n, g, e = cm
            ans.append(f"{L[k]}) не тавтология — недоказуема (MT1)")
            sol.append(f"{L[k]}) " + (f"Свободные термины закрываются: ${tex(g) if False else ''}$" if False else "") +
                       f"При {q7.n_text(n)} интерпретационная форма — ${tex(g)}$; при {q7.env_tex(e)} она ложна. Не "
                       "тавтология — по MT1 § 10 недоказуема в $S^5_{cq}$.")
    cond = (f"{CONV} Для каждой формулы $S^5_{{cq}}$ исследуйте, тавтология ли она, и сделайте вывод о доказуемости там, "
            f"где MT1 его позволяет. {TAUT10}\n\n" + items([f"$\\vdash {tex(f)}$" for f, _ in its]))
    return card(level, "C", "open", "short", "с. 120–121, гл. 7, § 10", "кванторы, S5cq, тавтологии", cond,
                "; ".join(ans), "\n".join(sol), system="S^5_cq")


def c10_closure(level=6):
    f = rnd.choice([IMP(ALL("a", ab), ab), IMP(ab, EX("a", ab)), IMP(ab, ALL("a", ab)), IMP(EX("a", ab), ab),
                    IMP(C(ALL("a", ab), ac), EX("a", C(ab, ac))), IMP(EX("a", C(ab, ac)), C(ab, EX("a", ac)))])
    g = ALL("a", f)
    cm = q7.countermodel1(f)
    cond = (f"{CONV} В формуле $\\vdash {tex(f)}$ системы $S^5_{{cq}}$ термин $a$ входит и свободно, и связанно. По D1 § 10 "
            "(с. 120) запишите её интерпретационную форму при одном и при двух отмеченных терминах для $a$ и выясните, "
            "тавтология ли формула (D2 § 10). Сравните с тем, что получилось бы, если бы свободное вхождение $a$ "
            "оставили без квантора.")
    i1, i2 = q7.interp(g, {"a": 1}), q7.interp(g, {"a": 2})
    t = cm is None
    wrong = q7.interp(f, {"a": 2})
    ans = (f"$\\vdash {tex(i2)}$ при $n = 2$; " + ("тавтология." if t else "не тавтология, недоказуема по MT1."))
    sol = (f"По D1 § 10 $\\vdash {tex(f)}$ заменяется на $\\vdash {tex(g)}$; внешняя группа охватывает и связанное вхождение, "
           f"но то связано своей группой. При $n = 1$: $\\vdash {tex(i1)}$; при $n = 2$: $\\vdash {tex(i2)}$.\n" +
           (f"При {q7.env_tex(cm[2])} ($n$ = {cm[0]['a']}) форма ложна — не тавтология; по MT1 § 10 недоказуема.\n" if not t
            else "При любом $n$ каждый член конъюнкции имеет вид, истинный при всех значениях (проверяется по строению) — "
                 "тавтология.\n") +
           f"Без замыкания свободное $a$ осталось бы неотмеченным: $\\vdash {tex(wrong)}$ — это не интерпретационная форма по "
           "D1 § 10.")
    return card(level, "C", "vary", "short", "с. 120–121, гл. 7, § 10", "кванторы, S5cq, свободные термины", cond, ans,
                sol, system="S^5_cq")


def c10_diag(level=6):
    f = rnd.choice([IMP(ab, ALL("a", ab)), IMP(EX("a", ab), ab), IMP(C(EX("a", ab), ac), ALL("a", W(ab, ac)))])
    cm = q7.countermodel1(f)
    assert cm
    n, g, e = cm
    stud = q7.interp(f, {"a": 2})
    cond = (f"{CONV} Студент рассуждает: «В $\\vdash {tex(f)}$ при двух отмеченных терминах интерпретационная форма — "
            f"$\\vdash {tex(stud)}$. Она истинна при любых значениях элементарных высказываний, значит, формула — "
            "тавтология и по MT1 § 10 доказуема в $S^5_{cq}$». Найдите все ошибки.")
    ans = ("Две ошибки: свободное вхождение $a$ не закрыто квантором общности (D1 § 10), поэтому форма построена неверно, "
           "и формула не тавтология; кроме того, MT1 § 10 даёт лишь необходимое условие: из тавтологичности доказуемость не "
           "следует.")
    sol = (f"1. D1 § 10 (с. 120): если термин входит в $x$ свободно, $\\vdash x$ заменяется на $\\vdash (\\forall a)x$. "
           f"Верная форма при {q7.n_text(n)}: $\\vdash {tex(g)}$; при {q7.env_tex(e)} она ложна.\n"
           "2. MT1 § 10: «если доказуема, то тавтология»; обратное книга не утверждает, так что «тавтология, значит, "
           "доказуема» — неверный вывод даже для настоящей тавтологии.")
    return card(level, "E", "vary", "text", "с. 120–121, гл. 7, § 10", "кванторы, S5cq, диагностика", cond, ans, sol,
                system="S^5_cq")


def c10_rule(level=5):
    cond = (f"{CONV} В $S^5_{{cq}}$ принято правило R1: если $\\vdash x$, то $\\vdash (\\forall a)x$ (с. 120). Студент "
            "применяет его так: «Из доказуемой в $S^s_{cq}$ формулы $(a \\leftarrow b)(c \\leftarrow d) \\vdash "
            "(c \\leftarrow d)$ по R1 $S^5_{cq}$ получаем $(\\forall a)((a \\leftarrow b)(c \\leftarrow d)) \\vdash "
            "(\\forall a)(c \\leftarrow d)$, а из $\\vdash (a \\leftarrow b) \\supset (a \\leftarrow b)$ — "
            "$\\vdash (\\forall a)(a \\leftarrow b) \\supset (\\forall a)(a \\leftarrow b)$». Найдите ошибки и дайте верные "
            "применения правил.")
    ans = ("R1 $S^5_{cq}$ применяется к формулам $\\vdash x$, а не $x \\vdash y$ (первую формулу даёт R1 $S^s_{cq}$, "
           "с. 100); из $\\vdash (a \\leftarrow b) \\supset (a \\leftarrow b)$ R1 даёт $\\vdash (\\forall a)((a \\leftarrow b) "
           "\\supset (a \\leftarrow b))$ — квантор ко всей формуле.")
    sol = ("1. Правило R1 § 10 говорит о формулах вырожденного следования $\\vdash x$ (с. 120). Для $x \\vdash y$ квантор "
           "навешивают R1 и R2 $S^s_{cq}$ (с. 100) — результат студента верен, но основание не то.\n"
           "2. R1 § 10 навешивает квантор на всё $x$: из $\\vdash (a \\leftarrow b) \\supset (a \\leftarrow b)$ получается "
           "$\\vdash (\\forall a)((a \\leftarrow b) \\supset (a \\leftarrow b))$. Формула студента получается иначе (это не "
           "применение R1).")
    return card(level, "E", "vary", "text", "с. 100, 120, гл. 7, § 2, 10", "кванторы, S5cq, диагностика", cond, ans, sol,
                system="S^5_cq")


def c10_compare(level=7):
    its = [(ALL("a", ab), cb, "MT2 § 3: новый термин $c$", "не тавтология (MT2 § 10)"),
           (ALL("a", ab), W(cb, N(cb)), "MT1 § 3: новое элементарное высказывание $(c \\leftarrow b)$",
            "тавтология (заключение импликации истинно всегда)"),
           (C(ALL("a", ab), cd), cd, "доказуема по $S^s$", "тавтология"),
           (EX("a", ab), ALL("a", ab), "недоказуема по процедуре § 9 (не тавтология)", "не тавтология")]
    rnd.shuffle(its)
    sol = []
    for k, (p, q, s1, s5) in enumerate(its):
        f = IMP(p, q)
        cm = q7.countermodel1(f)
        assert (cm is None) == ("не" not in s5.split()[0]), (ftex(p, q), s5)
        sol.append(f"{L[k]}) ${ftex(p, q)}$ в $S^s_{{cq}}$ — {s1}; $\\vdash {tex(f)}$ — {s5}" +
                   (f": при {q7.n_text(cm[0])} форма ${tex(cm[1])}$ ложна при {q7.env_tex(cm[2])}" if cm else "") + ".")
    cond = (f"{CONV} Сравните каждую формулу $x \\vdash y$ системы $S^s_{{cq}}$ с формулой $\\vdash x \\supset y$ системы "
            f"$S^5_{{cq}}$ (§ 10): исследуйте доказуемость первой (§ 3, § 9) и тавтологичность второй (D1–D2 § 10). Найдите "
            "формулы, на которых результаты расходятся, и объясните расхождение.\n\n" +
            items([f"${ftex(p, q)}$ и $\\vdash {tex(IMP(p, q))}$" for p, q, _, _ in its]))
    return card(level, "S", "transfer", "short", "с. 100, 120–121, гл. 7, § 3, 10", "кванторы, сравнение систем", cond,
                "Расходятся формулы с новым элементарным высказыванием в заключении: для $S^s_{cq}$ — «парадокс», "
                "для $\\vdash x \\supset y$ — тавтология.", "\n".join(sol) + "\n\nВ $S^s_{cq}$ действует условие "
                "непарадоксальности (MT1 § 3), а импликация $\\supset$ его не знает: $x \\supset y$ истинна при истинном "
                "$y$ независимо от $x$.", system="S^5_cq")


def c10_nat(level=6):
    s, f = rnd.choice([("«Если все $a$ суть $b$, то $c$ есть $b$»", IMP(ALL("a", ab), cb)),
                       ("«Если $c$ есть $b$, то некоторое $a$ есть $b$»", IMP(cb, EX("a", ab)))])
    cm = q7.countermodel1(f)
    cond = (f"{CONV} Запишите утверждение {s} формулой $\\vdash x$ системы $S^5_{{cq}}$ и исследуйте её тавтологичность "
            f"(D1–D2 § 10); сделайте вывод о доказуемости. {TAUT10}")
    return card(level, "C", "open", "short", "с. 120–121, гл. 7, § 10", "кванторы, S5cq, формализация", cond,
                f"$\\vdash {tex(f)}$ — не тавтология, недоказуема (MT1, MT2 § 10).",
                f"При {q7.n_text(cm[0])} форма $\\vdash {tex(cm[1])}$ ложна при {q7.env_tex(cm[2])}. По MT1 § 10 формула "
                "недоказуема; она — одна из формул MT2 § 10 (с. 121) с переименованными буквами.", form="nat",
                system="S^5_cq")


# ================================================================ § 11: S^s*_cq
AST5 = ("$A^*5$ (§ 11, с. 121): $(\\exists a)x \\vdash (\\forall a)x$, где $a$ не входит свободно в $x$ или $\\vdash x$ "
        "доказуема в $S^5$ (т. е. $x$ — тавтология)")


def x11():
    return rnd.choice([W(ab, N(ab)), W(ab, N(ac)), C(ab, N(ab)), W(N(C(ab, ac)), ab), W(cd, N(cd)), C(cd, ab),
                       W(C(ab, ac), N(ab)), W(ab, W(N(ab), ac)), EX("a", ab), W(ALL("a", ab), cd)])


def ast5_ok(X):
    nf = not free_in("a", X)
    taut = q7.is_taut1(X) and not any(g[0] in q7.QK for g in H.walk(X))
    return nf or taut, nf, taut


def c11_series(level=5, diag=False):
    its = []
    for X in rnd.sample([W(ab, N(ab)), W(ab, N(ac)), C(ab, N(ab)), W(N(C(ab, ac)), ab), W(cd, N(cd)), C(cd, ab),
                         W(C(ab, ac), N(ab)), EX("a", ab), W(ALL("a", ab), cd), W(ab, W(N(ab), ac))], 5):
        its.append(X)
    res = [ast5_ok(X) for X in its]
    if len({r[0] for r in res}) == 1:
        return c11_series(level, diag)
    ans, sol = [], []
    for k, (X, (ok, nf, tt)) in enumerate(zip(its, res)):
        if nf:
            why = "$a$ не входит в $x$ свободно"
        elif tt:
            why = "$a$ входит свободно, но $x$ — тавтология ($\\vdash x$ доказуема в $S^5$)"
        else:
            e = next(e for e in q7.penvs(X) if not q7.pval(X, e))
            why = f"$a$ входит свободно, и $x$ не тавтология (при {q7.env_tex(e)} $x$ ложно)"
        ans.append(f"{L[k]}) {'пример' if ok else 'не пример'}")
        sol.append(f"{L[k]}) $x$ := ${tex(X)}$: {why}; в $S^s_{{cq}}$ (A5) — {'пример' if nf else 'не пример'}.")
    fs = [f"${ftex(EX('a', X), ALL('a', X))}$" for X in its]
    if not diag:
        cond = (f"{CONV} {AST5}. Для каждой формулы установите, пример ли она $A^*5$, и сравните с A5 системы "
                "$S^s_{cq}$ (там допускается лишь первое условие).\n\n" + items(fs))
        return card(level, "A", "iso", "short", "с. 99, 121, гл. 7, § 2, 11", "кванторы, S*cq, схемы", cond,
                    "; ".join(ans), "\n".join(sol), system="S^s*_cq")
    wrong = rnd.sample(range(5), 2)
    lines = "\n".join(f"{k + 1}. {fs[k]} — {'пример' if (res[k][0] != (k in wrong)) else 'не пример'} $A^*5$"
                      for k in range(5))
    cond = (f"{CONV} {AST5}. Студент проверил пять формул; ровно две оценки неверны. Найдите их и объясните.\n\n{lines}")
    return card(6, "E", "vary", "text", "с. 121, гл. 7, § 11", "кванторы, S*cq, диагностика", cond,
                "; ".join(f"{k + 1}: {'пример' if res[k][0] else 'не пример'}" for k in sorted(wrong)),
                "\n".join(sol[k].replace(f"{L[k]})", f"{k + 1}.") for k in sorted(wrong)) + "\n\nОстальные оценки верны.",
                system="S^s*_cq")


def c11_compare(level=7):
    its = [(W(ab, N(ab)), ALL("a", W(ab, N(ab))), "T1 § 11"), (EX("a", W(ac, N(ac))), W(ac, N(ac)), "T2 § 11"),
           (EX("a", ab), ab, None), (W(C(ab, ac), N(ab)), ALL("a", W(C(ab, ac), N(ab))), None)]
    rnd.shuffle(its)
    sol, ans = [], []
    for k, (p, q, nm) in enumerate(its):
        P, Q, reps, case = A3.control(p, q)
        v, why = A3.proc_verdict(p, q, (P, Q, reps)) if q7.ss_theorem(qfree(p), qfree(q)) else (False, "шаг 1 отрицателен")
        if nm:
            ans.append(f"{L[k]}) в $S^{{s*}}_{{cq}}$ доказуема ({nm}); в $S^s_{{cq}}$ — {'доказуема' if v else 'недоказуема'}")
            sol.append(f"{L[k]}) $S^{{s*}}_{{cq}}$: пример {nm} ($x$ — тавтология, $\\vdash x$ доказуема в $S^5$, как требует § 11). "
                       f"$S^s_{{cq}}$: {why}.")
        else:
            ans.append(f"{L[k]}) $S^{{s*}}_{{cq}}$: $x$ не тавтология, $a$ свободно — схемы § 11 неприменимы; "
                       f"в $S^s_{{cq}}$ — {'доказуема' if v else 'недоказуема'}")
            sol.append(f"{L[k]}) Ни $A^*5$, ни T1–T4 § 11 не применимы ($a$ входит свободно, а высказывание под квантором не "
                       "тавтология). "
                       f"$S^s_{{cq}}$: {why}.")
    cond = (f"{CONV} {AST5}; в $S^{{s*}}_{{cq}}$ доказуемы T1 $x \\vdash (\\forall a)x$, T2 $(\\exists a)x \\vdash x$, T3 "
            "$(\\exists a)\\sim x \\vdash \\sim x$, T4 $\\sim x \\vdash (\\forall a)\\sim x$ при доказуемой $\\vdash x$ "
            "(с. 121). Для каждой формулы выясните, обосновывается ли её доказуемость в $S^{s*}_{cq}$ схемами § 11, и "
            f"исследуйте её доказуемость в $S^s_{{cq}}$ по процедуре § 9. {A3.PROC}\n\n"
            + items([f"${ftex(p, q)}$" for p, q, _ in its]))
    return card(level, "S", "transfer", "short", "с. 116–121, гл. 7, § 9, 11", "кванторы, S*cq, сравнение систем", cond,
                "; ".join(ans), "\n".join(sol), system="S^s*_cq")


def c11_e(level=5):
    cond = (f"{CONV} Студент: «В $S^{{s*}}_{{cq}}$ по T4 § 11 доказуема $\\sim(a \\leftarrow b) \\vdash (\\forall a)\\sim(a "
            "\\leftarrow b)$, а по T3 — $(\\exists a)\\sim(a \\leftarrow b) \\vdash \\sim(a \\leftarrow b)$». Найдите ошибку и "
            "приведите правильные примеры T3 и T4.")
    ans = ("T3, T4 требуют, чтобы $\\vdash x$ была доказуема в $S^5$, т. е. $\\sim x$ было противоречием (с. 121); "
           "$\\sim(a \\leftarrow b)$ не противоречие. Верно, например, при $x = (a \\leftarrow b) \\vee \\sim(a \\leftarrow b)$: "
           "$\\sim((a \\leftarrow b) \\vee \\sim(a \\leftarrow b)) \\vdash (\\forall a)\\sim((a \\leftarrow b) \\vee \\sim(a "
           "\\leftarrow b))$.")
    sol = ("Т1–T4 § 11 имеют силу «в которых доказуема $\\vdash x$ (т. е. $x$ есть тавтология)»; «в случае T3 и T4 "
           "высказывание $\\sim x$ есть противоречие» (с. 121). У студента $x = (a \\leftarrow b)$ — не тавтология, и $a$ "
           "входит в $x$ свободно, так что ни $A^*5$, ни A5 не помогают. Правильные примеры — с тавтологичным $x$ (см. ответ) "
           "и с T3: $(\\exists a)\\sim((a \\leftarrow b) \\vee \\sim(a \\leftarrow b)) \\vdash \\sim((a \\leftarrow b) \\vee "
           "\\sim(a \\leftarrow b))$.")
    return card(level, "E", "vary", "text", "с. 121, гл. 7, § 11", "кванторы, S*cq, диагностика", cond, ans, sol,
                system="S^s*_cq")


def c11_a8(level=6):
    Xs = rnd.choice([(ab,), (ab, cd), (ab, N(ac)), (C(ab, ac),)])
    X = C(*Xs) if len(Xs) > 1 else Xs[0]
    core = N(C(X, N(X)))
    p, q = EX("a", core), ALL("a", core)
    cond = (f"{CONV} Схема A8 (§ 11, с. 122): $(\\exists a)\\sim((x^1 \\ldots x^n)\\sim(x^1 \\ldots x^n)) \\vdash (\\forall a)"
            f"\\sim((x^1 \\ldots x^n)\\sim(x^1 \\ldots x^n))$, $n \\geq 1$. Покажите, что формула ${ftex(p, q)}$ — её пример, "
            "что она пример $A^*5$, и докажите по D3 § 7, что она тавтология при любом числе отмеченных терминов. Выясните, "
            "пример ли она A5 $S^s_{cq}$.")
    nf = not free_in("a", core)
    ans = (f"Пример A8 при $n = {len(Xs)}$, $x^i$ := " + ", ".join(f"${tex(t)}$" for t in Xs) +
           f"; пример $A^*5$ ($x$ — тавтология); тавтология; " + ("пример A5." if nf else "не пример A5 ($a$ свободно)."))
    sol = (f"1. $x^1 \\ldots x^n$ = ${tex(X)}$; высказывание ${tex(core)}$ — тавтология (отрицание противоречия), т. е. "
           "$\\vdash x$ доказуема в $S^5$ — это условие $A^*5$.\n"
           f"2. При любом $n$ интерпретационная форма — дизъюнкция ⊢ конъюнкция высказываний вида ${tex(core)}$ с отмеченными "
           "терминами; каждое из них истинно при всех значениях, поэтому заключение истинно всегда — тавтология.\n"
           f"3. A5 требует, чтобы $a$ не входил в $x$ свободно; " + ("здесь так и есть." if nf else "здесь $a$ входит свободно."))
    return card(level, "C", "vary", "short", "с. 121–122, гл. 7, § 11", "кванторы, S*cq", cond, ans, sol, system="S^s*_cq")


def c11_mt1(level=6):
    z = rnd.choice([ab, ac, ba])
    p, q, nm = rnd.choice([(z, ALL("a", W(z, N(z))), "T5"), (EX("a", C(N(z), z)), z, "T6")])
    P, Q, reps, case = A3.control(p, q)
    cm = q7.countermodel(P, Q, nmax=3)
    assert cm and case == 2
    cond = (f"{CONV} MT1 § 11 (с. 122): если $x \\vdash y$ — тавтология, а её бескванторная форма доказуема в $S^s$, то она "
            f"доказуема в $S^{{s*}}_{{cq}}$. Формула ${ftex(p, q)}$ — типа {nm} § 11 (с. 121). Примените к ней MT1 и исследуйте "
            f"её доказуемость в $S^s_{{cq}}$ по процедуре § 9. {A3.PROC}")
    taut = {"T5": "при любом $n$ (и при любом замыкании $a$ по п. 1 D2) заключение — конъюнкция высказываний вида "
                  f"${tex(W(z, N(z)))}$ с отмеченными терминами, каждое истинно всегда",
            "T6": "при любом $n$ посылка — дизъюнкция противоречий вида $\\sim zz$ с отмеченными терминами, она ложна "
                  "всегда"}[nm]
    ans = f"В $S^{{s*}}_{{cq}}$ доказуема (MT1 § 11); в $S^s_{{cq}}$ недоказуема (контрольная форма не тавтология)."
    sol = (f"1. Бескванторная форма ${ftex(qfree(p), qfree(q))}$ — сильная тавтология. Формула — тавтология: {taut}. По "
           "MT1 § 11 доказуема в $S^{s*}_{cq}$.\n"
           f"2. $S^s_{{cq}}$: шаг 1 процедуры положителен; " + ("$y^*$ — тавтология" if nm == "T5" else "$x^*$ — противоречие") +
           f", поэтому контрольная форма строится по п. 2 D1 § 9: ${ftex(P, Q)}$; {A2.cm_text(P, Q, cm)} — не тавтология, "
           "формула недоказуема. Это согласуется с книгой: «формулы типа T5 и T6 недоказуемы в $S^s_{cq}$» (с. 121).")
    return card(level, "C", "transfer", "short", "с. 116–122, гл. 7, § 9, 11", "кванторы, S*cq, полнота", cond, ans, sol,
                system="S^s*_cq")


# ================================================================ § 12–14: S^s_nq
def prem_nq():
    X, Y = A.two()
    return rnd.choice([ALL("a", C(X, Y)), NALL("a", X), QALL("a", X), EX("a", N(X)), C(ALL("a", X), NALL("a", Y)),
                       NALL("a", C(X, Y)), W(NALL("a", X), NALL("a", Y)), W(NEX("a", X), NEX("a", Y)),
                       C(N(NALL("a", X)), N(QALL("a", X))), C(N(ALL("a", X)), N(QALL("a", X))), NEX("a", N(X))])


def deriv_nq(least=7, most=12):
    for _ in range(4000):
        P = prem_nq()
        lines = H.build(P, rnd.choice([least + 2, most, most + 2]), H.AXNQ, rnd, maxsize=46)
        if not lines:
            continue
        lines = H.prune(lines)
        key = ftex(lines[-1][0], lines[-1][1])
        if key in H.SEEN or q7.size(lines[-1][1]) < 10:
            continue
        names = {w for _, _, w in lines if isinstance(w, str)}
        if not any(n.startswith("A^") or n in ("A10", "A11", "A12") for n in names) or len(names) < 2:
            continue
        if not (least <= len(lines) <= most) or q7.check(lines, H.AXNQ):
            continue
        if any(not q7.ss_theorem(qf13(a), qf13(b)) for a, b, w in lines):
            raise AssertionError("бескванторная форма не теорема S^s")
        if not ({w[0] for _, _, w in lines if isinstance(w, tuple)} & {"R1", "R2", "cj", "tr"}):
            continue
        H.SEEN.add(key)
        return lines
    raise RuntimeError("нет вывода nq")


def c12_deriv(level=None, src="с. 99–100, 122–123, гл. 7, § 2, 12"):
    lines = deriv_nq()
    a, b = lines[-1][0], lines[-1][1]
    cond = f"{CONVN} Выведите в $S^s_{{nq}}$ формулу\n\n$${ftex(a, b)}$$\n\n{SCHNQ}"
    used = sorted({q7.scheme_name(w) for _, _, w in lines if isinstance(w, str)})
    return cardn(level or (7 if len(lines) >= 10 else 6), "D", "open", "proof", src, "кванторы, Snq, вывод", cond,
                 f"Например, вывод в {len(lines)} строк (см. решение); схемы: {', '.join(used)}.", H.show(lines))


def c12_complete(src="с. 122–123, гл. 7, § 12"):
    c = A.c_complete(src, maker=lambda: deriv_nq(8, 12), sch=SCHNQ, system=NQ, systex="S^s_{nq}")
    c["cond"] = c["cond"].replace(CONV, CONVN, 1)
    return c


NQWHY = {"A^16": "$A^16$ — $(\\forall a)x \\vdash (\\urcorner\\exists a)\\sim x$, $A^17$ — обратная",
         "A^17": "$A^17$ — $(\\urcorner\\exists a)\\sim x \\vdash (\\forall a)x$, $A^16$ — обратная",
         "A^26": "$A^26$ — $(\\urcorner\\forall a)x \\vdash (\\exists a)\\sim x$, $A^27$ — обратная",
         "A^27": "$A^27$ — $(\\exists a)\\sim x \\vdash (\\urcorner\\forall a)x$, $A^26$ — обратная",
         "A^18": "$A^18$ вводит $\\sim(\\urcorner\\forall a)x\\sim(?\\forall a)x$, $A^19$ — обратная",
         "A^19": "$A^19$ выводит $(\\forall a)x$ из $\\sim(\\urcorner\\forall a)x\\sim(?\\forall a)x$, $A^18$ — обратная",
         "A^28": "$A^28$ — из $(\\urcorner\\forall a)x$, $A^29$ — обратная", "A^29": "$A^29$ — к $(\\urcorner\\forall a)x$, "
         "$A^28$ — обратная", "A10": "A10 раскрывает $(\\urcorner\\forall a)(xy)$ в дизъюнкцию, A11 — обратная",
         "A11": "A11 собирает дизъюнкцию в $(\\urcorner\\forall a)(xy)$, A10 — обратная"}


def c12_diag(src="с. 122–123, гл. 7, § 12"):
    w = dict(A.WHY2)
    w.update(NQWHY)
    c = A.c_diag(src, maker=lambda: deriv_nq(8, 12), allowed=H.AXNQ, whys=w, sch=SCHNQ, system=NQ)
    c["cond"] = c["cond"].replace(CONV, CONVN, 1)
    return c


def nq_inst(name):
    X, Y = A.two()
    return q7.build_inst(q7.NQ[name] if name in q7.NQ else q7.SCQ[name], {"x": X, "y": Y, "@a": "a"})


def c12_rec(level=4):
    names = rnd.sample(["A^16", "A^26", "A^36", "A^17", "A^27", "A^37", "A^18", "A^28", "A^39", "A10", "A12"], 4)
    its = [nq_inst(n) for n in names]
    X, Y = A.two()
    its.append(rnd.choice([(ALL("a", X), NEX("a", X)), (NALL("a", X), EX("a", X)), (W(NALL("a", X), NALL("a", Y)),
                                                                                   NEX("a", C(X, Y)))]))
    rnd.shuffle(its)
    allnames = list(q7.NQ) + ["A1", "A2", "A3", "A4", "A5"]
    sch = {**q7.NQ, **{k: q7.SCQ[k] for k in ["A1", "A2", "A3", "A4", "A5"]}}
    res = [[q7.scheme_name(n) for n in allnames if q7.inst_of(sch[n], p, q) is not None] for p, q in its]
    cond = (f"{CONVN} Для каждой формулы найдите все схемы $S^s_{{nq}}$, примером которых она является; если ни одной — "
            f"объясните, что мешает. {SCHNQ}\n\n" + items([f"${ftex(p, q)}$" for p, q in its]))
    ans = "; ".join(f"{L[k]}) " + (", ".join(r) or "ни одной") for k, r in enumerate(res))
    sol = "\n".join(f"{L[k]}) " + (", ".join(r) + ": получается заменой $x$, $y$ высказываниями." if r else
                                  "ни одной: в схемах с $(\\urcorner Ka)$ при переходе меняется квантор и добавляется или "
                                  "снимается $\\sim$ под ним; здесь этого соответствия нет.") for k, r in enumerate(res))
    return cardn(level, "R", "iso", "short", "с. 122–123, гл. 7, § 12", "кванторы, Snq, схемы", cond, ans, sol)


def c12_badE(level=5):
    X = A.compound()
    cond = (f"{CONVN} Студент выводит в $S^s_{{nq}}$: «1. ${ftex(ALL('a', X), N(EX('a', N(X))))}$ [A6]; 2. "
            f"${ftex(N(EX('a', N(X))), ALL('a', X))}$ [A7]». Найдите ошибку и выясните, какими схемами $S^s_{{nq}}$ можно "
            f"заменить эти шаги. {SCHNQ}")
    ans = ("В $S^s_{nq}$ схем A6, A7 нет: они заменены на $A^i6$, $A^i7$ (с. 123). Ближайшие аналоги: $A^16$ "
           f"${ftex(ALL('a', X), NEX('a', N(X)))}$ и $A^17$ — обратная; внешнее отрицание $\\sim$ и внутреннее $\\urcorner$ "
           "в неклассическом случае различаются.")
    sol = ("§ 12 (с. 123): «вместо аксиомных схем A6 и A7 системы $S^s_{cq}$ принимаются такие аксиомные схемы» — "
           "$A^16$–$A^37$. Значит, ссылка на A6, A7 в $S^s_{nq}$ неверна. Схемы $A^16$ и $A^17$ связывают $(\\forall a)x$ "
           "с $(\\urcorner\\exists a)\\sim x$, а не с $\\sim(\\exists a)\\sim x$; формулы студента в $S^s_{nq}$ недоказуемы "
           "(для $\\sim(\\exists a)\\sim x \\vdash (\\forall a)x$ — MT3 § 15, с. 126).")
    return cardn(level, "E", "vary", "text", "с. 122–126, гл. 7, § 12, 15", "кванторы, Snq, диагностика", cond, ans, sol)


def c12_subst(name, yes, level=None):
    X, Y = A.two()
    if yes:
        p, q = q7.build_inst(q7.NQ[name], {"x": X, "y": Y, "@a": "a"})
        why = None
    else:
        p, q, why = {
            "A^16": (ALL("a", X), NEX("a", X), "в $A^16$ под $(\\urcorner\\exists a)$ стоит $\\sim x$, а здесь — $x$"),
            "A^26": (NALL("a", X), EX("a", X), "в $A^26$ под $(\\exists a)$ стоит $\\sim x$"),
            "A10": (NALL("a", C(X, Y)), C(NALL("a", X), NALL("a", Y)), "A10 даёт дизъюнкцию, а не конъюнкцию"),
            "A12": (W(NEX("a", X), NEX("a", Y)), NEX("a", W(X, Y)), "в A12 под $(\\urcorner\\exists a)$ в заключении — "
                    "конъюнкция $xy$")}[name]
        assert q7.inst_of(q7.NQ[name], p, q) is None
    cond = (f"{CONVN} Схема {q7.scheme_name(name)} системы $S^s_{{nq}}$ (с. 123): ${q7.NQ_TEX[name]}$. Установите, получается "
            f"ли из неё формула ${ftex(p, q)}$ заменой букв; если да — укажите замену, если нет — назовите, что мешает.")
    if yes:
        st = f"$x$ := ${tex(X)}$" + (f", $y$ := ${tex(Y)}$" if name in ("A10", "A11", "A12") else "")
        return cardn(level or 4, "A", "vary", "short", "с. 123, гл. 7, § 12", "кванторы, Snq, подстановка", cond,
                     f"Получается: {st}.", f"Посылка задаёт замену {st}; заключение схемы при ней совпадает с данным.")
    return cardn(level or 5, "E", "vary", "short", "с. 123, гл. 7, § 12", "кванторы, Snq, почти-пример", cond,
                 f"Не получается: {why}.", f"Сравниваем формулу со схемой: {why}; другой замены нет.")


def c12_occ(level=5):
    f = C(NALL("a", W(ab, EX("a", ac))), QEX("b", C(ab, cb)), ad)
    cond = (f"{CONVN} В определение свободных и связанных терминов добавляется ссылка на группы $(\\urcorner\\forall a)$, "
            f"$(?\\forall a)$, $(\\urcorner\\exists a)$, $(?\\exists a)$ (§ 12, с. 122). Для высказывания ${tex(f)}$ "
            "установите для каждого вхождения терминов в элементарные высказывания, свободное оно или связанное, и найдите "
            "вырожденные группы; затем запишите бескванторную форму по D1 § 13 (с. 123).")
    rows = A.occ_table(f)
    occ = "; ".join(f"{n}) ${tex(e)}$: ${t1}$ — {'своб.' if f1 else 'связ.'}, ${t2}$ — {'своб.' if f2 else 'связ.'}"
                    for n, e, (t1, f1), (t2, f2) in rows)
    dg = [g for g in q7.groups(f) if q7.degenerate(g)]
    qf = qf13(f)
    ans = occ + f"; вырожденных групп {'нет' if not dg else len(dg)}; бескванторная форма ${tex(qf)}$."
    sol = (occ + ".\nГруппы $(\\urcorner\\forall a)$ и $(?\\exists b)$ связывают свои термины так же, как $(\\forall a)$ и "
           "$(\\exists b)$ (D4–D5 с дополнением § 12). D1 § 13: $(?\\exists b)z$ → $\\sim(\\exists b)z\\sim(\\urcorner\\exists "
           f"b)z$, $(\\urcorner Kb)z$ → $\\sim(Kb)z$, затем группы исключаются: ${tex(qf)}$.")
    return cardn(level, "A", "iso", "short", "с. 98–99, 122–123, гл. 7, § 1, 12–13", "кванторы, Snq, вхождения", cond,
                 ans, sol)


def c13_qf(level=5):
    for _ in range(100):
        p = rnd.choice([QALL("a", C(ab, N(ac))), NEX("a", W(ab, cd)), C(NALL("a", ab), QEX("a", ac)),
                        W(QALL("a", ab), N(NALL("a", ac))), N(QEX("a", C(ab, ac)))])
        q = rnd.choice([QALL("a", ab), C(N(ALL("a", ab)), N(NALL("a", ab))), EX("a", N(ab)), NEX("a", N(ac)),
                        W(NALL("a", ab), QALL("a", ab))])
        if p != q:
            break
    pp, qq = qf13(p), qf13(q)
    st = q7.ss_theorem(pp, qq)
    cond = (f"{CONVN} Постройте бескванторную форму (D1 § 13, с. 123) формулы ${ftex(p, q)}$ и исследуйте её доказуемость в "
            "$S^s$; сделайте вывод о формуле по § 13. D1: 1) $(?\\forall b)z$ и $(?\\exists b)z$ заменяются на "
            "$\\sim(\\forall b)z\\sim(\\urcorner\\forall b)z$ и $\\sim(\\exists b)z\\sim(\\urcorner\\exists b)z$; 2) "
            "$(\\urcorner\\forall b)z$, $(\\urcorner\\exists b)z$ — на $\\sim(\\forall b)z$, $\\sim(\\exists b)z$; 3) все "
            "кванторные группы исключаются.")
    if st:
        tail = "доказуема в $S^s$ — по § 13 недоказуемость не следует"
    else:
        r = q7.patoms(qq) - q7.patoms(pp)
        tail = ("недоказуема в $S^s$ (новое элементарное высказывание)" if r else "недоказуема в $S^s$ (не тавтология)") + \
            " — формула недоказуема в $S^s_{nq}$ (бескванторные формы теорем доказуемы в $S^s$, с. 124)"
    return cardn(level, "T", "iso", "short", "с. 123–124, гл. 7, § 13", "кванторы, Snq, непротиворечивость", cond,
                 f"${ftex(pp, qq)}$ — {tail}.", f"Пп. 1–3 D1 по шагам дают ${ftex(pp, qq)}$; {tail}.")


def c13_lines(level=5):
    lines = deriv_nq(7, 11)
    rows = [f"{n}) ${ftex(qf13(a), qf13(b))}$" for n, (a, b, w) in enumerate(lines, 1)]
    cond = (f"{CONVN} Запишите бескванторные формы (D1 § 13, с. 123) всех строк вывода в $S^s_{{nq}}$ и проверьте, что "
            f"каждая доказуема в $S^s$ — как в доказательстве непротиворечивости $S^s_{{nq}}$ (с. 124).\n\n{H.show(lines)}")
    sol = ("\n".join(rows) + "\n\nБескванторные формы схем $A^i6$–$A^i9$, A10–A12 перечислены на с. 124 и доказуемы в "
           "$S^s$; R1, R2 не меняют бескванторной формы; правила $S^s$ сохраняют доказуемость в $S^s$.")
    return cardn(level, "T", "iso", "text", "с. 123–124, гл. 7, § 13", "кванторы, Snq, непротиворечивость", cond,
                 "Все бескванторные формы — теоремы $S^s$ (перечень в решении).", sol)


def drop_inner(f):
    """Ошибка: внутреннее отрицание при группе просто стёрто."""
    k = f[0]
    if k in ("nall", "nex"):
        return ("all" if k == "nall" else "ex", f[1], drop_inner(f[2]))
    if k in ("all", "ex", "qall", "qex"):
        return (k, f[1], drop_inner(f[2]))
    if k == "neg":
        return N(drop_inner(f[1]))
    if k in ("conj", "wdis"):
        return (k, tuple(drop_inner(a) for a in f[1]))
    return f


def c13_diag(level=6):
    p = rnd.choice([QALL("a", ab), QEX("a", N(ac))])
    q = rnd.choice([NALL("a", W(ab, ac)), C(N(NEX("a", ab)), ac)])
    good = (qf13(p), qf13(q))
    if p[0] == "qall":
        bad_p = C(N(p[2]), p[2])
        e1 = "$(?\\forall b)z$ заменяется на $\\sim(\\forall b)z\\sim(\\urcorner\\forall b)z$, т. е. после п. 2 — на $\\sim z\\sim\\sim z$, а не на $\\sim z z$"
    else:
        bad_p = N(p[2])
        e1 = "$(?\\exists b)z$ заменяется на $\\sim(\\exists b)z\\sim(\\urcorner\\exists b)z$ — две части, а не одна"
    bad_q = qf13(drop_inner(q))
    e2 = "внутреннее отрицание при квантор­ной группе по п. 2 D1 становится внешним $\\sim$; оно потеряно"
    cond = (f"{CONVN} Студент записал бескванторную форму (D1 § 13, с. 123) формулы ${ftex(p, q)}$ так: "
            f"${ftex(bad_p, bad_q)}$. Найдите все ошибки и дайте верную форму.")
    return cardn(level, "E", "vary", "text", "с. 123, гл. 7, § 13", "кванторы, Snq, диагностика", cond,
                 f"Посылка: {e1}; заключение: {e2.replace('квантор­ной', 'кванторной')}. Верно: ${ftex(*good)}$.",
                 f"1. {e1[0].upper() + e1[1:]} (пп. 1–2 D1).\n2. {e2[0].upper() + e2[1:].replace('квантор­ной', 'кванторной')} "
                 f"(п. 2 D1).\nВерно: ${ftex(*good)}$.")


def c13_badlines(level=6):
    for _ in range(300):
        lines = deriv_nq(7, 11)
        cands = [n for n, (a, b, w) in enumerate(lines, 1) if isinstance(w, str) and w in ("A^16", "A^26", "A^17", "A^27",
                                                                                             "A1", "A2")]
        if len(cands) >= 2:
            break
    i, j = rnd.sample(cands, 2)
    bad = list(lines)
    for n in (i, j):
        a, b, w = bad[n - 1]
        if w in ("A^16", "A^17", "A^26", "A^27"):
            nb = N(b) if b[0] != "neg" else b[1]
        elif w == "A1":
            nb = A.substitute_el(b, A.els(b)[0], EL("d", "c"))
        else:
            nb = (b[0], b[1], A.substitute_el(b[2], A.els(b[2])[0], EL("d", "c")))
        bad[n - 1] = (a, nb, w)
    shown = [(n, a, b, w) for n, (a, b, w) in enumerate(bad, 1) if isinstance(w, str)]
    bads = [n for n, a, b, w in shown if not q7.ss_theorem(qf13(a), qf13(b))]
    assert sorted(bads) == sorted([i, j]), (bads, i, j)
    cond = (f"{CONVN} Проверьте методом § 13 (бескванторные формы D1, с. 123–124) шаги «вывода» в $S^s_{{nq}}$, "
            "основанные на схемах, и найдите строки, которые не могут быть теоремами $S^s_{nq}$.\n\n"
            + "\n".join(f"{n}. ${ftex(a, b)}$ [{q7.why_text(w)}]" for n, a, b, w in shown))
    sol = "\n".join(f"{n}. ${ftex(qf13(a), qf13(b))}$ — " + ("теорема $S^s$." if n not in bads else
                    "не теорема $S^s$: строка недоказуема в $S^s_{nq}$, основание указано неверно.") for n, a, b, w in shown)
    return cardn(level, "E", "vary", "text", "с. 123–124, гл. 7, § 13", "кванторы, Snq, диагностика", cond,
                 f"Ошибочны строки {', '.join(map(str, sorted(bads)))}.", sol)


def c13_series(level=6):
    its = []
    for _ in range(4):
        lines = deriv_nq(5, 12)
        p, q = lines[-1][0], lines[-1][1]
        if len(its) % 2:
            p, q = rnd.choice(A.mutate(p, q))
        its.append((p, q))
    ans, sol = [], []
    for k, (p, q) in enumerate(its):
        st = q7.ss_theorem(qf13(p), qf13(q))
        ans.append(f"{L[k]}) " + ("бескванторная форма доказуема — § 13 ничего не запрещает" if st else "недоказуема"))
        sol.append(f"{L[k]}) ${ftex(qf13(p), qf13(q))}$ — " + ("теорема $S^s$." if st else
                   "не теорема $S^s$, значит, формула недоказуема в $S^s_{nq}$ (§ 13)."))
    cond = (f"{CONVN} Для каждой формулы постройте бескванторную форму D1 § 13 (с. 123), исследуйте её доказуемость в "
            "$S^s$ и сделайте вывод о доказуемости формулы в $S^s_{nq}$ там, где метод § 13 это позволяет.\n\n"
            + items([f"${ftex(p, q)}$" for p, q in its]))
    return cardn(level, "C", "open", "short", "с. 123–124, гл. 7, § 13", "кванторы, Snq, непротиворечивость", cond,
                 "; ".join(ans), "\n".join(sol))


def c14_mt1(level=5):
    its = []
    for _ in range(4):
        lines = deriv_nq(5, 12)
        p, q = lines[-1][0], lines[-1][1]
        if len(its) % 2:
            q = C(q, EL("c", "d")) if EL("c", "d") not in q7.patoms(qf13(p)) else W(q, EL("d", "c"))
        its.append((p, q))
    ans, sol = [], []
    for k, (p, q) in enumerate(its):
        new = q7.patoms(qf13(q)) - q7.patoms(qf13(p))
        ans.append(f"{L[k]}) " + ("недоказуема (MT1 § 14)" if new else "условие MT1 выполнено"))
        sol.append(f"{L[k]}) " + (("В заключение входит " + ", ".join(f"${tex(e)}$" for e in sorted(new, key=tex)) +
                                  ", которого нет в посылке — по MT1 § 14 (с. 124) недоказуема.") if new else
                                 "Новых элементарных высказываний в заключении нет; MT1 не препятствует доказуемости "
                                 "(формула выводится — вывод строится по схемам)."))
    cond = (f"{CONVN} MT1 § 14 (с. 124): если $x \\vdash y$ доказуема в $S^s_{{nq}}$, то в $y$ не входят элементарные "
            "высказывания, отсутствующие в $x$. Проверьте условие для каждой формулы и сделайте вывод.\n\n"
            + items([f"${ftex(p, q)}$" for p, q in its]))
    return cardn(level, "P", "iso", "short", "с. 124, гл. 7, § 14", "кванторы, Snq, непарадоксальность", cond,
                 "; ".join(ans), "\n".join(sol))


def c14_t(level=6):
    X = A.compound()
    d = H.Der(EX("a", X))
    i = d.lift(0, N(N(X)), ("Ss",))
    d.step(i, NALL("a", N(X)), "A^27")
    d2 = H.Der(NALL("a", N(X)))
    j = d2.step(0, EX("a", N(N(X))), "A^26")
    d2.lift(j, X, ("Ss",))
    for dd in (d, d2):
        assert not q7.check(dd.lines, H.AXNQ)
    cond = (f"{CONVN} Выведите в $S^s_{{nq}}$ обе формулы теоремной схемы T1 § 14 (с. 124) $(\\exists a)x \\dashv\\vdash "
            f"(\\urcorner\\forall a)\\sim x$ при $x$ := ${tex(X)}$, т. е. ${ftex(d.P, d.lines[-1][1])}$ и обратную. {SCHNQ}")
    return cardn(level, "D", "vary", "proof", "с. 123–124, гл. 7, § 12, 14", "кванторы, Snq, теоремные схемы", cond,
                 "Прямая: $\\sim\\sim$ под квантором по R2, затем $A^27$; обратная: $A^26$, затем снятие $\\sim\\sim$ по R2.",
                 "Прямая:\n\n" + H.show(d.lines) + "\n\nОбратная:\n\n" + H.show(d2.lines))


def c14_near(level=5):
    X, Y = A.two()
    p, q = ALL("a", W(X, Y)), W(ALL("a", X), ALL("a", Y))
    cm = q7.countermodel(p, q, nmax=2)
    cond = (f"{CONVN} Студент: «T8 § 14 (с. 124) — $(\\forall a)x \\vee (\\forall a)y \\vdash (\\forall a)(x \\vee y)$; значит, "
            f"и обратная формула ${ftex(p, q)}$ доказуема в $S^s_{{nq}}$». Найдите ошибку и покажите значениями (для "
            "кванторов $\\forall$, $\\exists$ без $\\urcorner$ и $?$ интерпретационная форма — как в § 7), что формула не "
            "тавтология.")
    return cardn(level, "E", "vary", "short", "с. 124–125, гл. 7, § 14–15", "кванторы, Snq, диагностика", cond,
                 "Из доказуемости формулы не следует доказуемость обратной; обратная к T8 не тавтология.",
                 f"T8 даёт лишь одно направление (знак ⊢, а не ⊣⊢). {A2.cm_text(p, q, cm)[0].upper()}{A2.cm_text(p, q, cm)[1:]} — "
                 "не тавтология, а доказуемые в $S^s_{nq}$ формулы — тавтологии (MT1 § 15, с. 125).")


def c14_badstep(level=6):
    for _ in range(500):
        lines = deriv_nq(6, 10)
        P = lines[-1][0]
        cands = [(n, b) for n, (a, b, w) in enumerate(lines, 1) if a == P and b[0] == "all"]
        if cands:
            n, q = rnd.choice(cands)
            r = N(EX(q[1], N(q[2])))
            bad = H.prune(list(lines) + [(q, r, "A6"), (P, r, ("tr", n, len(lines) + 1))])
            k = next(i for i, x in enumerate(bad, 1) if x == (q, r, "A6"))
            if len(bad) >= 5 and k < len(bad):
                break
    cond = (f"{CONVN} Студент вывел в $S^s_{{nq}}$ формулу ${ftex(P, r)}$. Найдите неверный шаг и объясните ошибку. "
            f"{SCHNQ}\n\n{H.show(bad)}")
    return cardn(level, "E", "vary", "text", "с. 122–123, гл. 7, § 12", "кванторы, Snq, вывод, диагностика", cond,
                 f"Шаг {k}: схемы A6 в $S^s_{{nq}}$ нет — она заменена на $A^16$–$A^36$ (с. 123).",
                 f"Шаг {k}: ${ftex(q, r)}$ [A6] — в $S^s_{{nq}}$ A6 и A7 не принимаются; $A^16$ даёт "
                 f"${ftex(q, NEX(q[1], N(q[2])))}$, а не формулу с внешним $\\sim$. Остальные шаги верны.")


# ================================================================ § 15: семантика S^s_nq
def br(e, neg_, env):
    return ("v", ("{~" if neg_ else "{") + tex(EL(env.get(e[1], e[1]), env.get(e[2], e[2]))) + "}")


def interp15(f, n, env=None):
    """Косвенная интерпретация § 15 для формул, где под кванторами — элементарные высказывания или их отрицания:
    (∀b)z → {z(1b)}·…, (∃b)z → {z(1b)} ∨ …; (⌝∀b)z → (∃b)∼z; (⌝∃b)z → (∀b)∼z; (?Kb)z → ∼(Kb)z∼(⌝Kb)z."""
    env = env or {}
    k = f[0]
    if k == "el":
        return br(f, False, env)
    if k == "neg":
        return N(interp15(f[1], n, env))
    if k in ("conj", "wdis"):
        return (k, tuple(interp15(a, n, env) for a in f[1]))
    if k == "qall":
        return interp15(C(N(ALL(f[1], f[2])), N(NALL(f[1], f[2]))), n, env)
    if k == "qex":
        return interp15(C(N(EX(f[1], f[2])), N(NEX(f[1], f[2]))), n, env)
    if k == "nall":
        return interp15(EX(f[1], N(f[2])), n, env)
    if k == "nex":
        return interp15(ALL(f[1], N(f[2])), n, env)
    if k in ("all", "ex"):
        a, z = f[1], f[2]
        neg_ = z[0] == "neg"
        e = z[1] if neg_ else z
        assert e[0] == "el", "под квантором — элементарное высказывание или его отрицание"
        parts = [br(e, neg_, {**env, a: f"{i}{a}"}) for i in range(1, n[a] + 1)]
        if len(parts) == 1:
            return parts[0]
        return C(*parts) if k == "all" else W(*parts)
    raise ValueError(k)


def nq_envs(*fs):
    names = sorted(set().union(*(q7.patoms(f) for f in fs)), key=repr)
    for vs in itertools.product((0, 1), repeat=len(names)):
        e = dict(zip(names, vs))
        ok = True
        for nm in names:
            s = nm[1]
            if s.startswith("{~") and e.get(("v", "{" + s[2:]), 0) and e[nm]:
                ok = False
                break
        if ok:
            yield e


def cm15(p, q, nmax=3):
    ts = sorted({g[1] for g in q7.groups(p) + q7.groups(q)})
    for combo in sorted(itertools.product(range(1, nmax + 1), repeat=len(ts)), key=lambda c: (sum(c), c)):
        n = dict(zip(ts, combo))
        ip, iq = interp15(p, n), interp15(q, n)
        for e in nq_envs(ip, iq):
            if q7.pval(ip, e) and not q7.pval(iq, e):
                return n, ip, iq, e
    return None


def btex(f):
    t = tex(f).replace("{~", "\x00").replace("{", "\\{").replace("}", "\\}")
    return t.replace("\x00", "\\{\\sim ")


def benv(e):
    return ", ".join(f"${btex(k)} = {v}$" for k, v in sorted(e.items(), key=lambda kv: btex(kv[0])))


RULES15 = ("Косвенная интерпретация § 15 (с. 125): если $x$ — высказывание, то $\\{x\\}$ — высказывание; если одно из "
           "$\\{x\\}$, $\\{\\sim x\\}$ имеет значение 1, другое — 0, если одно — 0, значение другого не зависит от первого; "
           "$(?\\forall b)z$, $(?\\exists b)z$ заменяются на $\\sim(\\forall b)z\\sim(\\urcorner\\forall b)z$ и "
           "$\\sim(\\exists b)z\\sim(\\urcorner\\exists b)z$; $(\\urcorner\\forall b)z$, $(\\urcorner\\exists b)z$ — на "
           "$(\\exists b)\\sim z$ и $(\\forall b)\\sim z$; $(\\forall b)z$, $(\\exists b)z$ — на $\\{z(1b)\\} \\cdot \\ldots "
           "\\cdot \\{z(nb)\\}$ и $\\{z(1b)\\} \\vee \\ldots \\vee \\{z(nb)\\}$.")
POOL15 = [
    (N(ALL("a", N(ab))), EX("a", ab)), (N(EX("a", N(ab))), ALL("a", ab)), (N(NALL("a", ab)), ALL("a", ab)),
    (N(NEX("a", ab)), EX("a", ab)), (N(EX("a", ab)), ALL("a", N(ab))), (ALL("a", ab), N(NALL("a", ab))),
    (NALL("a", ab), N(ALL("a", ab))), (QALL("a", ab), N(ALL("a", ab))), (ALL("a", ab), EX("a", ab)),
    (EX("a", N(ab)), NALL("a", ab)), (ALL("a", ab), C(N(NALL("a", ab)), N(QALL("a", ab)))),
    (NALL("a", ab), C(N(ALL("a", ab)), N(QALL("a", ab)))), (N(ALL("a", ab)), W(NALL("a", ab), QALL("a", ab))),
    (W(ALL("a", ab), NALL("a", ab)), N(QALL("a", ab))), (ALL("a", N(ab)), N(EX("a", ab))),
]


def taut15(p, q):
    return cm15(p, q) is None


def c15_series(level=6):
    its = rnd.sample(POOL15, 4)
    while len({taut15(*i) for i in its}) == 1:
        its = rnd.sample(POOL15, 4)
    ans, sol = [], []
    for k, (p, q) in enumerate(its):
        cm = cm15(p, q)
        if cm is None:
            n1 = {"a": 2}
            ans.append(f"{L[k]}) тавтология")
            sol.append(f"{L[k]}) Тавтология: при $n = 2$ форма ${btex(interp15(p, n1))} \\vdash {btex(interp15(q, n1))}$; "
                       "при любом $n$ посылка и заключение составлены из одних и тех же $\\{z(ia)\\}$, $\\{\\sim z(ia)\\}$, и "
                       "из истинности посылки при условии «$\\{x\\}$ и $\\{\\sim x\\}$ не оба 1» следует истинность "
                       "заключения (проверено перебором при $n \\leq 3$; рассуждение не зависит от $n$).")
        else:
            n, ip, iq, e = cm
            ans.append(f"{L[k]}) не тавтология")
            sol.append(f"{L[k]}) Не тавтология: при {q7.n_text(n)} форма ${btex(ip)} \\vdash {btex(iq)}$; при {benv(e)} "
                       "(условие на $\\{x\\}$, $\\{\\sim x\\}$ соблюдено) посылка 1, заключение 0; по MT1 § 15 недоказуема.")
    cond = (f"{CONVN} Для каждой формулы исследуйте, тавтология ли она по косвенной интерпретации § 15, и сделайте вывод "
            f"о доказуемости в $S^s_{{nq}}$ (MT1 § 15: доказуемые формулы — тавтологии). {RULES15}\n\n"
            + items([f"${ftex(p, q)}$" for p, q in its]))
    return cardn(level, "C", "open", "short", "с. 125–126, гл. 7, § 15", "кванторы, Snq, интерпретация", cond,
                 "; ".join(ans), "\n".join(sol))


def c15_compare(level=7):
    its = rnd.sample([i for i in POOL15 if not any(g[0] in ("nall", "nex", "qall", "qex") for g in H.walk(i[0]) for _ in [0])
                      and not any(g[0] in ("nall", "nex", "qall", "qex") for g in H.walk(i[1]))], 3)
    ans, sol = [], []
    for k, (p, q) in enumerate(its):
        tc = q7.qtaut(p, q)
        cm = cm15(p, q)
        ans.append(f"{L[k]}) § 7 — {'тавтология' if tc else 'нет'}; § 15 — {'тавтология' if cm is None else 'нет'}")
        s = f"{L[k]}) § 7: " + ("тавтология" if tc else A2.cm_text(p, q)) + "; § 15: "
        if cm is None:
            s += "тавтология (условие на $\\{x\\}$, $\\{\\sim x\\}$ не мешает)."
        else:
            n, ip, iq, e = cm
            s += f"при {q7.n_text(n)} форма ${btex(ip)} \\vdash {btex(iq)}$ ложна при {benv(e)}."
        sol.append(s)
    cond = (f"{CONV} Сравните классический и неклассический случаи: для каждой формулы выясните, тавтология ли она по "
            f"интерпретации § 7 (для $S^s_{{cq}}$) и по интерпретации § 15 (для $S^s_{{nq}}$). {RULES15} Объясните, откуда "
            "расхождения.\n\n" + items([f"${ftex(p, q)}$" for p, q in its]))
    return cardn(level, "S", "transfer", "short", "с. 105, 125–126, гл. 7, § 7, 15", "кванторы, классический и "
                 "неклассический случаи", cond, "; ".join(ans), "\n".join(sol) + "\n\nВ § 15 $\\{x\\}$ и $\\{\\sim x\\}$ могут "
                 "быть ложны оба (случай неопределённости), поэтому $\\sim\\{x\\}$ уже не равнозначно $\\{\\sim x\\}$: "
                 "законы, связывающие $\\forall$ и $\\exists$ через отрицание, перестают действовать (MT3 § 15).")


def c15_direct(level=5):
    st = rnd.choice([("K", "1"), ("U", "0"), ("Q", "0")])
    # состояния тройки ((∀a)x, (⌝∀a)x, (?∀a)x)
    states = {"K": (1, 0, 0), "N": (0, 1, 0), "Q": (0, 0, 1)}
    s = rnd.choice(["K", "N", "Q"])
    va, vn, vq = states[s]
    A_, Nn, Qq = ALL("a", ab), NALL("a", ab), QALL("a", ab)
    fs = [W(A_, Nn), N(C(A_, Nn)), C(N(A_), N(Nn)), W(Qq, A_), D(A_, Nn, Qq), C(N(A_), W(Nn, Qq))]
    fs = rnd.sample(fs, 4)
    env = {A_: va, Nn: vn, Qq: vq}
    vals = [q7.pval(f, env) for f in fs]
    given = {"K": "$(\\forall a)(a \\leftarrow b)$ имеет значение 1",
             "N": "$(\\urcorner\\forall a)(a \\leftarrow b)$ имеет значение 1",
             "Q": "$(\\forall a)(a \\leftarrow b)$ и $(\\urcorner\\forall a)(a \\leftarrow b)$ имеют значение 0"}[s]
    cond = (f"{CONVN} Прямая интерпретация § 15 (с. 125): $(?Ka)x$ равнозначно $\\sim(Ka)x\\sim(\\urcorner Ka)x$; если одно из "
            "$(Ka)x$, $(\\urcorner Ka)x$ имеет значение 1, другое — 0, если одно — 0, значение другого от него не зависит. "
            f"Пусть {given}. Найдите значения всех трёх высказываний $(\\forall a)(a \\leftarrow b)$, $(\\urcorner\\forall a)"
            "(a \\leftarrow b)$, $(?\\forall a)(a \\leftarrow b)$ и каждого высказывания ниже ($:$ — «одно и только одно из»).\n\n"
            + items([f"${tex(f)}$" for f in fs]))
    ans = (f"$(\\forall a)(a \\leftarrow b) = {va}$, $(\\urcorner\\forall a)(a \\leftarrow b) = {vn}$, $(?\\forall a)(a "
           f"\\leftarrow b) = {vq}$; " + "; ".join(f"{L[k]}) {v}" for k, v in enumerate(vals)))
    sol = ({"K": "По п. 2 $(\\urcorner\\forall a)(a \\leftarrow b) = 0$; по п. 1 $(?\\forall a)(a \\leftarrow b) = \\sim 1 "
                 "\\cdot \\sim 0 = 0$.",
            "N": "По п. 2 $(\\forall a)(a \\leftarrow b) = 0$; по п. 1 $(?\\forall a)(a \\leftarrow b) = \\sim 0 \\cdot "
                 "\\sim 1 = 0$.",
            "Q": "По п. 1 $(?\\forall a)(a \\leftarrow b) = \\sim 0 \\cdot \\sim 0 = 1$."}[s] + "\n" +
           "\n".join(f"{L[k]}) {v}." for k, v in enumerate(vals)))
    return cardn(level, "V", "iso", "short", "с. 125, гл. 7, § 15", "кванторы, Snq, прямая интерпретация", cond, ans, sol)


def c15_cm_diag(level=6):
    p, q = rnd.choice([(N(ALL("a", N(ab))), EX("a", ab)), (N(EX("a", N(ab))), ALL("a", ab)), (N(NALL("a", ab)), ALL("a", ab))])
    n = {"a": 1}
    ip, iq = interp15(p, n), interp15(q, n)
    names = sorted(q7.patoms(ip) | q7.patoms(iq), key=repr)
    good = cm15(p, q)
    cond = (f"{CONVN} Студент доказывает, что ${ftex(p, q)}$ — тавтология по § 15: «при $n = 1$ форма "
            f"${btex(ip)} \\vdash {btex(iq)}$; если $\\{{(1a \\leftarrow b)\\}} = 0$, то $\\{{\\sim(1a \\leftarrow b)\\}} = 1$, и "
            "посылка ложна; если $\\{(1a \\leftarrow b)\\} = 1$, заключение истинно. Значит, тавтология, как и в $S^s_{cq}$». "
            f"Найдите ошибку. {RULES15}")
    n0, ip0, iq0, e0 = good
    return cardn(level, "E", "vary", "text", "с. 125–126, гл. 7, § 15", "кванторы, Snq, диагностика", cond,
                 "Из $\\{x\\} = 0$ не следует $\\{\\sim x\\} = 1$: по п. 2 значение другого не зависит от первого; при обоих "
                 "0 посылка 1, заключение 0 — не тавтология (MT3 § 15).",
                 f"П. 2 (с. 125): если одно из $\\{{x\\}}$, $\\{{\\sim x\\}}$ имеет значение 0, значение другого от него не "
                 f"зависит. При {benv(e0)} посылка ${btex(ip0)}$ истинна, заключение ${btex(iq0)}$ ложно. Формула — одна из "
                 "недоказуемых по MT2–MT3 § 15 (с. 125–126); студент перенёс классическое правило.")


def c15_e2(level=5):
    cond = (f"{CONVN} Студент: «По прямой интерпретации § 15 высказывания $(\\forall a)x$ и $(\\urcorner\\forall a)x$ не могут "
            "быть оба истинны и не могут быть оба ложны, поэтому $(\\urcorner\\forall a)x$ равнозначно $\\sim(\\forall a)x$, и "
            "$\\sim(\\urcorner\\forall a)x \\vdash (\\forall a)x$ — тавтология». Найдите ошибку.")
    return cardn(level, "E", "vary", "text", "с. 125, гл. 7, § 15", "кванторы, Snq, диагностика", cond,
                 "Оба могут быть ложны: тогда истинно $(?\\forall a)x$ (п. 1–2 прямой интерпретации); "
                 "$\\sim(\\urcorner\\forall a)x \\vdash (\\forall a)x$ недоказуема (MT2 § 15).",
                 "П. 2 (с. 125): «если одно из них имеет значение 0, то значение другого не зависит от первого» — значит, "
                 "оба могут иметь значение 0; тогда по п. 1 $(?\\forall a)x$ = $\\sim(\\forall a)x\\sim(\\urcorner\\forall a)x$ = 1. "
                 "При таком распределении $\\sim(\\urcorner\\forall a)x$ = 1, $(\\forall a)x$ = 0 — формула не тавтология; по "
                 "MT2 § 15 она недоказуема в $S^s_{nq}$.")


# ================================================================ § 16–17: S^5_nq и классический вариант
def fam(kind, a="a", x=ab):
    return {"K": ALL(a, x), "N": NALL(a, x), "Q": QALL(a, x)}[kind]


def st_val(f, s):
    env = {fam("K"): int(s == "K"), fam("N"): int(s == "N"), fam("Q"): int(s == "Q")}
    return q7.pval(f, env)


def c16_series(level=6, classical=False):
    K_, N_, Q_ = fam("K"), fam("N"), fam("Q")
    pool = [D(K_, N_, Q_), W(K_, N_), N(C(K_, N_)), IMP(N(N_), K_), W(K_, N_, Q_), D(K_, N_, C(N(K_), N(N_))),
            N(Q_), W(N_, Q_), N(C(N_, Q_)), D(K_, Q_, C(N(K_), N(Q_))), IMP(N(K_), W(N_, Q_)), IMP(N(K_), N_)]
    its = rnd.sample(pool, 4)
    states = ["K", "N"] if classical else ["K", "N", "Q"]
    res = []
    for f in its:
        bad = [s for s in states if not st_val(f, s)]
        res.append(bad)
    if len({bool(b) for b in res}) == 1:
        return c16_series(level, classical)
    names = {"K": "$(\\forall a)x$ истинно", "N": "$(\\urcorner\\forall a)x$ истинно", "Q": "$(?\\forall a)x$ истинно"}
    ans = "; ".join(f"{L[k]}) " + ("тавтология" if not b else "не тавтология") for k, b in enumerate(res))
    sol = "\n".join(f"{L[k]}) " + ("истинна во всех случаях — тавтология." if not b else
                                  f"ложна в случае: {names[b[0]]} — не тавтология" + ("" if classical else
                                                                                         ", по MT2 § 16 недоказуема.") +
                                  "") for k, b in enumerate(res))
    if classical:
        cond = (f"{CONVN} В классическом варианте (§ 17, с. 127: принята схема $A^*13$ $\\sim(\\forall a)x \\vdash "
                "(\\urcorner\\forall a)x$) из трёх высказываний $(\\forall a)x$, $(\\urcorner\\forall a)x$, $(?\\forall a)x$ "
                "истинно ровно одно, причём $(?\\forall a)x$ всегда ложно (T1 § 17: $\\vdash \\sim(?Ka)x$). Исследуйте "
                "тавтологичность каждой формулы ($x$ := $(a \\leftarrow b)$; $:$ — «одно и только одно из»).\n\n"
                + items([f"$\\vdash {tex(f)}$" for f in its]))
        return cardn(level, "C", "open", "short", "с. 126–127, гл. 7, § 16–17", "кванторы, классический вариант", cond,
                     ans, sol)
    cond = (f"{CONVN} По § 15–16 (с. 125–126) из высказываний $(\\forall a)x$, $(\\urcorner\\forall a)x$, $(?\\forall a)x$ "
            "истинно одно и только одно (T5 § 16). Исследуйте тавтологичность каждой формулы $S^5_{nq}$, перебрав три "
            "случая, и сделайте вывод о доказуемости там, где позволяет MT2 § 16 ($x$ := $(a \\leftarrow b)$; $:$ — «одно и "
            "только одно из»).\n\n" + items([f"$\\vdash {tex(f)}$" for f in its]))
    return cardn(level, "C", "open", "short", "с. 125–126, гл. 7, § 15–16", "кванторы, S5nq, тавтологии", cond, ans, sol,
                 system="S^5_nq")


def c16_compare(level=7):
    K_, N_, Q_ = fam("K"), fam("N"), fam("Q")
    its = [W(K_, N_), IMP(N(N_), K_), N(Q_), D(K_, N_, Q_), N(C(K_, N_))]
    rnd.shuffle(its)
    its = its[:4]
    ans, sol = [], []
    for k, f in enumerate(its):
        c = all(st_val(f, s) for s in "KN")
        nc = all(st_val(f, s) for s in "KNQ")
        ans.append(f"{L[k]}) класс. — {'тавт.' if c else 'нет'}, некласс. — {'тавт.' if nc else 'нет'}")
        sol.append(f"{L[k]}) Классический случай (два случая: истинно $(\\forall a)x$ или $(\\urcorner\\forall a)x$): "
                   f"{'истинна в обоих' if c else 'ложна в одном'}; неклассический (ещё случай $(?\\forall a)x$): "
                   f"{'истинна во всех трёх' if nc else 'ложна в случае $(?\\forall a)x$'}.")
    cond = (f"{CONVN} Сравните классический вариант (§ 17, схема $A^*13$, с. 127; T1 $\\vdash \\sim(?Ka)x$) и неклассический "
            "случай (§ 15–16): для каждой формулы выясните, тавтология ли она в каждом случае; найдите разделяющие формулы "
            "($x$ := $(a \\leftarrow b)$).\n\n" + items([f"$\\vdash {tex(f)}$" for f in its]))
    return cardn(level, "S", "transfer", "short", "с. 125–127, гл. 7, § 15–17", "кванторы, классический и неклассический "
                 "случаи", cond, "; ".join(ans), "\n".join(sol) + "\n\nРазделяют формулы, ложные лишь в случае "
                 "неопределённости: их делает тавтологиями только $A^*13$ (ср. MT3 § 16, T3 § 17).", system="S^5_nq")


def c16_diag(level=6, classical=False):
    K_, N_, Q_ = fam("K"), fam("N"), fam("Q")
    fs = rnd.sample([W(K_, N_), N(C(K_, N_)), D(K_, N_, Q_), IMP(N(N_), K_), N(C(N_, Q_)), W(K_, Q_)], 4)
    truth = [all(st_val(f, s) for s in "KNQ") for f in fs]
    wrong = rnd.sample(range(4), 2)
    lines = "\n".join(f"{k + 1}. $\\vdash {tex(f)}$ — {'тавтология' if t != (k in wrong) else 'не тавтология'}"
                      for k, (f, t) in enumerate(zip(fs, truth)))
    cond = (f"{CONVN} Студент проверил тавтологичность четырёх формул $S^5_{{nq}}$ (истинно ровно одно из $(\\forall a)x$, "
            "$(\\urcorner\\forall a)x$, $(?\\forall a)x$, T5 § 16, с. 126); ровно два ответа неверны. Найдите их и обоснуйте "
            f"($x$ := $(a \\leftarrow b)$).\n\n{lines}")
    sol = []
    for k in sorted(wrong):
        f = fs[k]
        bad = [s for s in "KNQ" if not st_val(f, s)]
        sol.append(f"{k + 1}. " + ("Тавтология: истинна во всех трёх случаях." if not bad else
                                  f"Не тавтология: ложна, когда истинно {'$(\\forall a)x$' if bad[0] == 'K' else '$(\\urcorner\\forall a)x$' if bad[0] == 'N' else '$(?\\forall a)x$'}."))
    return cardn(level, "E", "vary", "text", "с. 126, гл. 7, § 16", "кванторы, S5nq, диагностика", cond,
                 "; ".join(f"{k + 1}: {'тавтология' if truth[k] else 'не тавтология'}" for k in sorted(wrong)),
                 "\n".join(sol) + "\n\nОстальные ответы верны.", system="S^5_nq")


def c16_mt1(level=6):
    ab_ = rnd.choice([("", "\\urcorner "), ("", "?"), ("\\urcorner ", "?")])
    cond = (f"{CONVN} MT1 § 16 (с. 126): формулы $(\\alpha Ka)x : (\\beta Ka)x : \\sim(\\alpha Ka)x\\sim(\\beta Ka)x \\vdash "
            "(\\alpha Ka)x : (\\beta Ka)x$, где $\\alpha$, $\\beta$ различаются как $\\urcorner$, $?$ или отсутствие обоих, "
            f"недоказуемы в неклассических системах. Запишите такую формулу при $\\alpha$ = «{ab_[0] or 'нет'}», $\\beta$ = "
            f"«{ab_[1]}», K = $\\forall$, $x$ := $(a \\leftarrow b)$ и покажите по T5 § 16 (истинно ровно одно из трёх), что "
            "она не тавтология. Почему книга делает отсюда вывод о «неклассическом отношении» $(\\alpha Ka)x$ и "
            "$(\\beta Ka)x$?")
    third = {("", "\\urcorner "): "?", ("", "?"): "\\urcorner ", ("\\urcorner ", "?"): ""}[ab_]
    t3 = {"?": "$(?\\forall a)x$", "\\urcorner ": "$(\\urcorner\\forall a)x$", "": "$(\\forall a)x$"}[third]
    return cardn(level, "C", "vary", "short", "с. 126, гл. 7, § 16", "кванторы, S5nq, неклассические отношения", cond,
                 f"Посылка истинна, а заключение ложно, когда истинно {t3}.",
                 f"Посылка — «ровно одно из: $(\\alpha Ka)x$, $(\\beta Ka)x$, ни то ни другое»; она истинна всегда. Заключение "
                 f"«ровно одно из $(\\alpha Ka)x$, $(\\beta Ka)x$» ложно, когда истинно третье — {t3}. Значит, формула не "
                 "тавтология и (MT2 § 16) недоказуема: $(\\alpha Ka)x$ и $(\\beta Ka)x$ не исчерпывают всех случаев — это и "
                 "есть неклассическое отношение (ср. гл. 5, § 6).", system="S^5_nq")


def c16_T(level=5):
    K_ = rnd.choice(["\\forall", "\\exists"])
    cond = (f"{CONVN} Теоремные схемы $S^5_{{nq}}$ (§ 16, с. 126) T1–T8 записаны для K — $\\forall$ или $\\exists$. Запишите "
            f"примеры T4, T5 и T6 при K = ${K_}$ и $x$ := $(a \\leftarrow b)(c \\leftarrow d)$ и проверьте каждую формулу "
            "перебором трёх случаев (истинно ровно одно из $(Ka)x$, $(\\urcorner Ka)x$, $(?Ka)x$).")
    X = "(a \\leftarrow b)(c \\leftarrow d)"
    g = lambda pre: f"({pre}{K_} a)({X})"
    t4 = f"\\vdash {g('')} \\vee {g('\\urcorner ')} \\vee {g('?')}"
    t5 = f"\\vdash {g('')} : {g('\\urcorner ')} : {g('?')}"
    t6 = f"\\vdash {g('')} : {g('\\urcorner ')} : \\sim{g('')}\\sim{g('\\urcorner ')}"
    return cardn(level, "A", "iso", "short", "с. 126, гл. 7, § 16", "кванторы, S5nq, теоремные схемы", cond,
                 f"T4: ${t4}$; T5: ${t5}$; T6: ${t6}$ — все истинны во всех трёх случаях.",
                 "В каждом из трёх случаев истинен ровно один из трёх членов: дизъюнкция T4 истинна, сильная дизъюнкция T5 "
                 "истинна; в T6 третий член $\\sim(Ka)x\\sim(\\urcorner Ka)x$ истинен ровно в случае $(?Ka)x$ — снова ровно "
                 "один истинный член.", system="S^5_nq")


def c16_nat(level=5):
    cond = (f"{CONVN} $(\\forall a)(a \\leftarrow b)$ — «все $a$ суть $b$», $(\\urcorner\\forall a)(a \\leftarrow b)$ — "
            "«не все $a$ суть $b$» (внутреннее отрицание), $(?\\forall a)(a \\leftarrow b)$ — «неопределённо, все ли $a$ "
            "суть $b$». Переведите на язык $S^5_{nq}$ утверждения «либо все $a$ суть $b$, либо не все» и «верно ровно одно: "
            "все $a$ суть $b$, не все или неопределённо» и выясните по § 16 (с. 126), какое из них тавтология.")
    return cardn(level, "T", "vary", "short", "с. 126, гл. 7, § 16", "кванторы, S5nq, перевод", cond,
                 "$\\vdash (\\forall a)(a \\leftarrow b) \\vee (\\urcorner\\forall a)(a \\leftarrow b)$ — не тавтология "
                 "(MT3 § 16); $\\vdash (\\forall a)(a \\leftarrow b) : (\\urcorner\\forall a)(a \\leftarrow b) : (?\\forall a)"
                 "(a \\leftarrow b)$ — тавтология (T5).",
                 "Первое ложно в случае неопределённости — недоказуемо (MT3 § 16, с. 126–127). Второе истинно во всех трёх "
                 "случаях — это T5 § 16.", form="nat", system="S^5_nq")


def c17_e(level=5):
    cond = (f"{CONVN} Студент: «В $S^s_{{nq}}$ доказуема $\\sim(\\forall a)x \\vdash (\\urcorner\\forall a)x$, ведь внутреннее и "
            "внешнее отрицания при кванторе — одно и то же; поэтому $\\vdash (\\forall a)x \\vee (\\urcorner\\forall a)x$ "
            "доказуема и в $S^5_{nq}$». Найдите ошибки.")
    return cardn(level, "E", "vary", "text", "с. 126–127, гл. 7, § 16–17", "кванторы, классический вариант, диагностика",
                 cond, "Это схема $A^*13$, которую принимают лишь для классического случая (§ 17); без неё "
                 "$\\vdash (Ka)x \\vee (\\urcorner Ka)x$ недоказуема (MT3 § 16), а с ней — доказуема (T3 § 17).",
                 "§ 17 (с. 127): системы для классического случая получают из неклассических, «приняв дополнительную "
                 "аксиомную схему $A^*13$ $\\sim(\\forall a)x \\vdash (\\urcorner\\forall a)x$». Значит, в $S^s_{nq}$ её нет, "
                 "и $\\sim(\\forall a)x$ при неопределённости истинно, а $(\\urcorner\\forall a)x$ — нет. По MT3 § 16 "
                 "$\\vdash (Ka)x \\vee (\\urcorner Ka)x$ недоказуема в $S^5_{nq}$; в классическом варианте это T3 § 17.")


# ================================================================ § 18–21
LIST18 = {"A^16": 1, "A^26": 2, "A^17": 4, "A^27": 5, "A^18": 7, "A^28": 8, "A^38": 9, "A^19": 10, "A^29": 11,
          "A^39": 12, "A10": 13, "A11": 14, "A12": 15}


def c18_repl(level=5):
    f = rnd.choice([C(QALL("a", ab), NEX("a", ac)), W(NALL("a", C(ab, ac)), QEX("a", ab)),
                    N(QALL("a", W(ab, cd))), C(NEX("a", N(ab)), QALL("a", ac)), IMP(NALL("a", ab), QEX("a", ac))])
    g = repl18(f)
    cond = (f"{CONVN} Выполните замену § 18 (с. 127) в высказывании ${tex(f)}$: $(\\urcorner\\forall b)z$ → "
            "$(\\exists b)\\sim z$, $(?\\forall b)z$ → $\\sim(\\forall b)z\\sim(\\exists b)\\sim z$, $(\\urcorner\\exists b)z$ → "
            "$(\\forall b)\\sim z$, $(?\\exists b)z$ → $\\sim(\\exists b)z\\sim(\\forall b)\\sim z$. Затем запишите "
            "бескванторную форму результата (D7 § 1) и сравните с бескванторной формой исходного высказывания по D1 § 13.")
    return cardn(level, "T", "iso", "short", "с. 123, 127, гл. 7, § 13, 18", "кванторы, Snq, замена § 18", cond,
                 f"${tex(g)}$; бескванторные формы: ${tex(qfree(g))}$ и ${tex(qf13(f))}$.",
                 f"Заменяем каждое вхождение по правилам с. 127: ${tex(g)}$. D7: ${tex(qfree(g))}$; D1 § 13 для исходного: "
                 f"${tex(qf13(f))}$." + (" Формы совпадают." if qfree(g) == qf13(f) else " Формы различаются: замена § 18 "
                                          "переводит $(\\urcorner\\forall b)z$ в $(\\exists b)\\sim z$, а D1 § 13 — в "
                                          "$\\sim(\\forall b)z$; после исключения групп это $\\sim z$ в обоих случаях, но "
                                          "$(?\\ldots)$ даёт разные выражения."))


def c18_scheme(level=5):
    names = rnd.sample(list(LIST18), 4)
    its = []
    for nm in names:
        p, q, c = q7.NQ[nm]
        its.append((nm, q7.repl18(p), q7.repl18(q)))
    cond = (f"{CONVN} Замена § 18 (с. 127) переводит схемы $A^i6$–$A^i9$, A10–A12 в схемы 1–15 (с. 128). Выполните замену в "
            "каждой схеме ниже и запишите результат.\n\n" + items([f"{q7.scheme_name(nm)}: ${q7.NQ_TEX[nm]}$"
                                                                   for nm, _, _ in its]))
    return cardn(level, "T", "iso", "short", "с. 127–128, гл. 7, § 18", "кванторы, Snq, замена § 18", cond,
                 "; ".join(f"{L[k]}) ${ftex(p, q)}$ (схема {LIST18[nm]})" for k, (nm, p, q) in enumerate(its)),
                 "\n".join(f"{L[k]}) ${ftex(p, q)}$ — схема {LIST18[nm]} на с. 128." for k, (nm, p, q) in enumerate(its)))


def c18_diag(level=6):
    nm = rnd.choice(["A^18", "A^28", "A^19", "A^29"])
    p, q, c = q7.NQ[nm]
    good = (repl18(p), repl18(q))
    bad_p = repl18(p)
    bad_q = qfree(q) if False else q
    # ошибка 1: (⌝∀b)z → ∼(∀b)z вместо (∃b)∼z; ошибка 2: (?∀b)z → ∼(∀b)z∼(⌝∀b)z оставлено с ⌝
    def wrong(f):
        k = f[0]
        if k == "nall":
            return N(ALL(f[1], f[2]))
        if k == "qall":
            return C(N(ALL(f[1], f[2])), N(NALL(f[1], f[2])))
        if k == "neg":
            return N(wrong(f[1]))
        if k in ("conj", "wdis"):
            return (k, tuple(wrong(a) for a in f[1]))
        return f
    bp, bq = wrong(p), wrong(q)
    cond = (f"{CONVN} Студент выполнил замену § 18 (с. 127) в схеме {q7.scheme_name(nm)} ${q7.NQ_TEX[nm]}$ и получил "
            f"${ftex(bp, bq)}$. Найдите все ошибки и запишите верный результат.")
    return cardn(level, "E", "vary", "text", "с. 127–128, гл. 7, § 18", "кванторы, Snq, замена § 18, диагностика", cond,
                 "$(\\urcorner\\forall b)z$ заменено по D1 § 13 ($\\sim(\\forall b)z$), а не по § 18 ($(\\exists b)\\sim z$); "
                 "в $(?\\forall b)z$ оставлена группа с $\\urcorner$. Верно: " + f"${ftex(*good)}$.",
                 "Замена § 18 устраняет $\\urcorner$ и $?$ полностью: $(\\urcorner\\forall b)z$ → $(\\exists b)\\sim z$, "
                 "$(?\\forall b)z$ → $\\sim(\\forall b)z\\sim(\\exists b)\\sim z$ (с. 127). Студент спутал её с бескванторной "
                 f"формой D1 § 13 и не довёл замену внутри $(?\\forall b)z$. Верно: ${ftex(*good)}$ (схема {LIST18[nm]}, с. 128).")


def c18_dep(level=6):
    cond = (f"{CONV} После замены § 18 схемы 1–4, 5, 6, 9, 12 «отпадают как зависимые» (с. 128). Покажите это для схем 1 "
            "$(\\forall a)x \\vdash (\\forall a)\\sim\\sim x$, 4 $(\\forall a)\\sim\\sim x \\vdash (\\forall a)x$, 5 "
            "$(\\exists a)\\sim x \\vdash (\\exists a)\\sim x$ и 12 $\\sim(\\forall a)x\\sim(\\exists a)\\sim x \\vdash "
            "\\sim(\\forall a)x\\sim(\\exists a)\\sim x$: выведите каждую в $S^s_{cq}$ без A6, A7.")
    X = q7.V("x")
    d1 = H.Der(ALL("a", X)); d1.lift(0, N(N(X)), ("Ss",))
    d4 = H.Der(ALL("a", N(N(X)))); d4.lift(0, X, ("Ss",))
    for dd in (d1, d4):
        assert not q7.check(dd.lines, ["A1"])
    return card(level, "D", "vary", "proof", "с. 100, 128, гл. 7, § 2, 18", "кванторы, замена § 18, зависимость", cond,
                "1, 4 — по R1 из теорем $S^s$ $x \\vdash \\sim\\sim x$ и $\\sim\\sim x \\vdash x$; 5, 12 — примеры $x \\vdash x$ "
                "системы $S^s$.", "Схема 1:\n\n" + H.show(d1.lines) + "\n\nСхема 4:\n\n" + H.show(d4.lines) +
                "\n\nСхемы 5 и 12 имеют вид $z \\vdash z$ — теоремы $S^s$ (ссылка на систему, § 6).", system=NQ)


def c18_sem(level=6):
    s = rnd.choice(["A", "E", "O"])
    vals = {"A": (1, 0), "E": (0, 1), "O": (0, 0)}[s]
    Az, Enz = ALL("b", EL("a", "b")), EX("b", N(EL("a", "b")))
    fs = rnd.sample([C(N(Az), N(Enz)), W(Az, Enz), N(C(Az, Enz)), W(Az, Enz, C(N(Az), N(Enz)))], 3)
    env = {Az: vals[0], Enz: vals[1]}
    given = {"A": "$(\\forall b)z$ имеет значение 1", "E": "$(\\exists b)\\sim z$ имеет значение 1",
             "O": "$(\\forall b)z$ и $(\\exists b)\\sim z$ имеют значение 0"}[s]
    cond = (f"{CONV} Семантическое правило § 18 (с. 127–128): если одно из $(\\forall b)z$ и $(\\exists b)\\sim z$ имеет "
            f"значение 1, то другое — 0; если одно — 0, значение другого не зависит от первого. Пусть $z$ — $(a \\leftarrow "
            f"b)$ и {given}. Найдите значения второго высказывания (если оно определено) и формул ниже; объясните, какое "
            "высказывание $S^s_{nq}$ после замены § 18 выражает каждая.\n\n" + items([f"${tex(f)}$" for f in fs]))
    sol = "\n".join(f"{L[k]}) {q7.pval(f, env)}." for k, f in enumerate(fs))
    return cardn(level, "V", "iso", "short", "с. 127–128, гл. 7, § 18", "кванторы, Snq, семантика § 18", cond,
                 f"$(\\forall b)z = {vals[0]}$, $(\\exists b)\\sim z = {vals[1]}$; " + "; ".join(f"{L[k]}) {q7.pval(f, env)}"
                                                                                       for k, f in enumerate(fs)),
                 sol + "\n\n$\\sim(\\forall b)z\\sim(\\exists b)\\sim z$ — образ $(?\\forall b)z$, $(\\exists b)\\sim z$ — "
                 "образ $(\\urcorner\\forall b)z$ (замена § 18, с. 127).")


T19 = {}


def t19(n, c):
    a, b = "a", "b"
    e = EL(a, b)
    return {1: (ALL(c, e), e), 2: (e, EX(c, e)), 3: (ALL(c, e), N(EX(c, N(e)))), 4: (N(EX(c, N(e))), ALL(c, e)),
            5: (C(ALL(c, EL("a1", b)), EX(c, EL("a2", b))), EX(c, C(EL("a1", b), EL("a2", b)))),
            6: (C(ALL(c, EL(a, "b1")), EX(c, EL(a, "b2"))), EX(c, C(EL(a, "b1"), EL(a, "b2")))),
            7: (ALL(c, W(EL("a1", b), EL("a2", b))), W(ALL(c, EL("a1", b)), EX(c, EL("a2", b)))),
            8: (ALL(c, W(EL(a, "b1"), EL(a, "b2"))), W(ALL(c, EL(a, "b1")), EX(c, EL(a, "b2")))),
            9: (ALL(c, e), ALL(c, ALL(c, e))), 10: (EX(c, e), ALL(c, EX(c, e))), 11: (EX(c, EX(c, e)), EX(c, e)),
            12: (EX(c, ALL(c, e)), ALL(c, e)), 13: (e, ALL("a1", e)), 14: (EX("a1", e), e)}[n]


def sub_el(f, e, r):
    return A.substitute_el(f, e, r)


def c19_subst(level=5):
    n = rnd.choice([1, 2, 3, 4, 9, 10, 11, 12])
    c = rnd.choice(["a", "b"])
    p, q = t19(n, c)
    r = rnd.choice([C(EL("a", "c"), EL("d", "b")), W(EL("a", "b"), N(EL("a", "c"))), N(EL("c", "b")),
                    EX("b", EL("a", "b"))])
    P, Q = sub_el(p, EL("a", "b"), r), sub_el(q, EL("a", "b"), r)
    assert q7.qtaut(p, q) and q7.qtaut(P, Q)
    cond = (f"{CONV} Теорема {n} § 19 (с. 129) при $c$ = ${c}$: ${ftex(p, q)}$. Подставьте высказывание ${tex(r)}$ на место "
            "элементарного высказывания $(a \\leftarrow b)$ везде, где оно входит, и объясните по MT2 § 19, почему результат "
            "доказуем в $S^s_{cq}$; проверьте ответ интерпретацией § 7 (найдите, примером какой схемы $S^s_{cq}$ он является).")
    nm = next((k for k in ["A1", "A2", "A6", "A7", "T14", "T16", "T17", "T18"]
               if q7.inst_of(A2.sch_of(k), P, Q) is not None), None)
    return card(level, "D", "iso", "short", "с. 129, гл. 7, § 19", "кванторы, правила подстановки", cond,
                f"${ftex(P, Q)}$" + (f" — пример {nm}" if nm else "") + "; доказуема по MT2 § 19.",
                f"Подстановка во все вхождения $(a \\leftarrow b)$ даёт ${ftex(P, Q)}$. MT2 § 19: если $x \\vdash y$ — одна из "
                "T1–T12, а $v \\vdash z$ получена подстановкой любого высказывания на место элементарного везде, где оно "
                "входит, то $v \\vdash z$ доказуема." + (f" Действительно, это пример {nm}." if nm else ""))


def c19_t13(level=6):
    n = rnd.choice([13, 14])
    p, q = t19(n, None)
    r = rnd.choice([EL("a1", "b"), C(EL("a", "b"), EL("a1", "c")), W(EL("c", "a1"), EL("a", "b"))])
    P, Q = sub_el(p, EL("a", "b"), r), sub_el(q, EL("a", "b"), r)
    cm = q7.countermodel(P, Q, nmax=2)
    assert cm
    cond = (f"{CONV} Студент подставил в теорему {n} § 19 ${ftex(p, q)}$ высказывание ${tex(r)}$ на место $(a \\leftarrow b)$ "
            f"и получил ${ftex(P, Q)}$, «доказуемую по MT2». Найдите ошибку и покажите значениями, что результат не "
            "тавтология.")
    return card(level, "E", "vary", "text", "с. 129–130, гл. 7, § 7, 19", "кванторы, правила подстановки, диагностика",
                cond, "MT2 относится к T1–T12; для T13, T14 действует MT4: подставляемое высказывание не должно содержать "
                "$a^1$, а здесь содержит; результат не тавтология.",
                f"MT4 § 19 (с. 130): для T13 и T14 подстановка допустима, «если в высказывание, которое подставляется на место "
                f"элементарного, не входит $a^1$». Здесь входит. {A2.cm_text(P, Q, cm)[0].upper()}{A2.cm_text(P, Q, cm)[1:]}.")


def c19_term(level=5):
    n = rnd.choice([1, 3, 5, 7, 9])
    c = "a" if n in (1, 3, 9) else "a"
    p, q = t19(n, "b" if n in (5, 7) else c)
    newt = rnd.choice(["c", "d"])
    old = "a1" if n in (5, 7) else "a"
    P = A.substitute_el(p, None, None) if False else rename(p, old, newt)
    Q = rename(q, old, newt)
    assert q7.qtaut(P, Q)
    cond = (f"{CONV} MT3 § 19 (с. 130): если $x \\vdash y$ — одна из T1–T12, а $v \\vdash z$ получается подстановкой любого "
            "субъекта (предиката) на место простого субъекта (предиката) везде, где он входит, то $v \\vdash z$ доказуема. "
            f"Подставьте ${newt}$ на место ${q7.term_tex(old)}$ в теорему {n} § 19 ${ftex(p, q)}$ и проверьте, что результат — "
            "тавтология (D3 § 7).")
    return card(level, "D", "vary", "short", "с. 129–130, гл. 7, § 19", "кванторы, правила подстановки", cond,
                f"${ftex(P, Q)}$ — доказуема по MT3 § 19.", f"Замена всех вхождений даёт ${ftex(P, Q)}$; по MT3 § 19 она "
                "доказуема; интерпретационная форма при любом $n$ получается из формы исходной теоремы переименованием, "
                "поэтому тавтологичность сохраняется.")


def rename(f, old, new):
    k = f[0]
    if k == "el":
        return EL(new if f[1] == old else f[1], new if f[2] == old else f[2])
    if k == "neg":
        return N(rename(f[1], old, new))
    if k in q7.QK:
        return (k, new if f[1] == old else f[1], rename(f[2], old, new))
    if k in ("conj", "wdis"):
        return (k, tuple(rename(a, old, new) for a in f[1]))
    return f


def c19_series(level=6):
    its = []
    for _ in range(4):
        n = rnd.choice(list(range(1, 15)))
        p, q = t19(n, rnd.choice(["a", "b"]))
        r = rnd.choice([EL("a1", "c"), C(EL("a", "c"), EL("d", "b")), N(EL("c", "d")), EL("c", "a1")])
        if EL("a", "b") not in A.els(p) + A.els(q):
            continue
        P, Q = sub_el(p, EL("a", "b"), r), sub_el(q, EL("a", "b"), r)
        ok = n <= 12 or "a1" not in q7.terms(r)
        its.append((n, r, P, Q, ok))
    while len(its) < 4:
        p, q = t19(13, None)
        r = EL("a1", "b")
        its.append((13, r, sub_el(p, EL("a", "b"), r), sub_el(q, EL("a", "b"), r), False))
    ans, sol = [], []
    for k, (n, r, P, Q, ok) in enumerate(its):
        if ok:
            ans.append(f"{L[k]}) доказуема (MT{2 if n <= 12 else 4})")
            sol.append(f"{L[k]}) Теорема {n}; подстановка ${tex(r)}$ — " + ("MT2" if n <= 12 else "MT4 (нет $a^1$)") +
                       f" § 19: ${ftex(P, Q)}$ доказуема.")
        else:
            cm = q7.countermodel(P, Q, nmax=2)
            ans.append(f"{L[k]}) правила не применимы" + (" — не тавтология" if cm else ""))
            sol.append(f"{L[k]}) Теорема {n} (T13 или T14), а в ${tex(r)}$ входит $a^1$ — условие MT4 нарушено" +
                       (f"; {A2.cm_text(P, Q, cm)}" if cm else "") + ".")
    cond = (f"{CONV} Для каждой подстановки (теорема § 19, с. 129; подставляемое высказывание на место $(a \\leftarrow b)$) "
            "выясните, гарантирует ли MT2 или MT4 § 19 доказуемость результата; если нет — исследуйте его значениями.\n\n"
            + items([f"теорема {n}, подставляется ${tex(r)}$" for n, r, *_ in its]))
    return card(level, "C", "open", "short", "с. 129–130, гл. 7, § 19", "кванторы, правила подстановки", cond,
                "; ".join(ans), "\n".join(sol))


def c19_e(level=5):
    p, q = ALL("a", EL("a", "b")), EL("a", "b")
    r = EX("a", EL("c", "a"))
    cond = (f"{CONV} Студент: «В теорему 1 § 19 ${ftex(p, q)}$ подставляю $(\\exists a)(c \\leftarrow a)$ на место только "
            "второго вхождения $(a \\leftarrow b)$ и получаю $(\\forall a)(a \\leftarrow b) \\vdash (\\exists a)(c \\leftarrow "
            "a)$; по MT2 она доказуема». Найдите ошибку и проверьте результат.")
    P, Q = p, r
    newt = q7.terms(Q) - q7.terms(P)
    return card(level, "E", "vary", "text", "с. 100, 129, гл. 7, § 3, 19", "кванторы, правила подстановки, диагностика",
                cond, "MT2 требует подстановки «везде, где оно входит»; результат недоказуем: в заключение входит термин $c$, "
                "которого нет в посылке (MT2 § 3).",
                "MT2 § 19 (с. 129): подстановка на место элементарного высказывания «везде, где оно входит в $x \\vdash y$». "
                "Студент заменил одно вхождение. Полученная формула недоказуема: термин $c$ есть в заключении и нет в "
                "посылке (MT2 § 3, с. 100). Правильная подстановка: $(\\forall a)(\\exists a)(c \\leftarrow a) \\vdash "
                "(\\exists a)(c \\leftarrow a)$ — пример A1.")


# § 20: группы с несколькими терминами (только запись)
def qm(K, ts, body):
    return f"({K}({', '.join(ts)})){body}"


def c20_rewrite(level=5):
    seq = [rnd.choice(["\\forall", "\\exists"]) for _ in range(4)]
    ts = ["a", "b", "c", "d"]
    body = "x"
    orig = "".join(f"({k} {t})" for k, t in zip(seq, ts)) + body
    # склеиваем соседние одинаковые
    groups = []
    for k, t in zip(seq, ts):
        if groups and groups[-1][0] == k:
            groups[-1][1].append(t)
        else:
            groups.append([k, [t]])
    res = "".join(f"({k}({', '.join(g)}))" if len(g) > 1 else f"({k} {g[0]})" for k, g in groups) + body
    cond = (f"{CONV} По схемам $A^*I$ § 20 (с. 130–131): $(Ka)(Kb)x \\dashv\\vdash (K(a, b))x$, $(Ka^1)\\ldots(Ka^n)x "
            "\\dashv\\vdash (K(a^1, \\ldots, a^n))x$, K — $\\forall$ или $\\exists$. Запишите высказывание "
            f"${orig}$ с наименьшим числом кванторных групп, объединяя по $A^*I$ только то, что схемы позволяют, и "
            "объясните, почему дальнейшее объединение невозможно.")
    return card(level, "T", "iso", "short", "с. 130–131, гл. 7, § 20", "кванторы, расширения, A*I", cond, f"${res}$.",
                f"$A^*I$ объединяет лишь соседние группы с одним и тем же K. Соседние одинаковые группы склеиваем: ${res}$. "
                "Группы с разными K схема не объединяет (в ней один и тот же K), а несоседние нельзя сблизить без "
                "перестановки, которую $A^*I$ не даёт.", system=SYS_)


SYS_ = "S^s_cq"


def c20_comb(level=5):
    k1, k2 = rnd.choice(["\\forall", "\\exists"]), rnd.choice(["\\forall", "\\exists"])
    al, be = rnd.choice(["", "\\sim "]), rnd.choice(["", "\\sim "])
    kind = rnd.choice(["neg_conj", "neg_dis", "dis", "conj"])
    g1, g2 = f"{al}({k1} a)", f"{be}({k2} b)"
    if kind == "conj":
        src = f"({g1}\\cdot {g2})x"
        res = f"{al}({k1} a)x{be}({k2} b)x"
        steps = "схему $A^*II$ $(\\alpha(K^1a)\\beta(K^2b))x \\dashv\\vdash \\alpha(K^1a)x\\beta(K^2b)x$"
    elif kind == "dis":
        src = f"({g1} \\vee {g2})x"
        res = f"{al}({k1} a)x \\vee {be}({k2} b)x"
        steps = "схему $(\\alpha(K^1a) \\vee \\beta(K^2b))x \\dashv\\vdash \\alpha(K^1a)x \\vee \\beta(K^2b)x$"
    elif kind == "neg_conj":
        src = f"\\sim({g1}{g2})x"
        res = f"\\sim {al}({k1} a)x \\vee \\sim {be}({k2} b)x"
        steps = ("схему $\\sim(\\alpha(K^1a)\\beta(K^2b))x \\dashv\\vdash (\\sim\\alpha(K^1a) \\vee \\sim\\beta(K^2b))x$, "
                 "затем схема для дизъюнкции групп")
    else:
        src = f"\\sim({g1} \\vee {g2})x"
        res = f"\\sim {al}({k1} a)x\\sim {be}({k2} b)x"
        steps = ("схему $\\sim(\\alpha(K^1a) \\vee \\beta(K^2b))x \\dashv\\vdash (\\sim\\alpha(K^1a)\\sim\\beta(K^2b))x$, "
                 "затем $A^*II$ для конъюнкции групп")
    cond = (f"{CONV} § 20 (с. 131) вводит кванторные группы вида $((K^1a) \\cdot (K^2b))$, $((K^1a) \\vee (K^2b))$ со схемами "
            "$A^*II$: $(\\alpha(K^1a)\\beta(K^2b))x \\dashv\\vdash \\alpha(K^1a)x\\beta(K^2b)x$; $(\\alpha(K^1a) \\vee \\beta(K^2b))x "
            "\\dashv\\vdash \\alpha(K^1a)x \\vee \\beta(K^2b)x$; $\\sim(\\alpha(K^1a)\\beta(K^2b))x \\dashv\\vdash (\\sim\\alpha(K^1a) "
            "\\vee \\sim\\beta(K^2b))x$; $\\sim(\\alpha(K^1a) \\vee \\beta(K^2b))x \\dashv\\vdash (\\sim\\alpha(K^1a)\\sim\\beta(K^2b))x$, "
            f"где $\\alpha$, $\\beta$ — $n \\geq 0$ отрицаний. Преобразуйте ${src}$ в высказывание без составных групп.")
    return card(level, "T", "vary", "short", "с. 131, гл. 7, § 20", "кванторы, расширения, A*II", cond, f"${res}$.",
                f"Применяем {steps}: ${src} \\dashv\\vdash {res}$.".replace("\\sim \\sim", "\\sim\\sim"), system=SYS_)


def c20_diag(level=6):
    cond = (f"{CONV} Студент: «По $A^*I$ (с. 130) $(\\forall a)(\\exists b)x \\dashv\\vdash (\\forall(a, b))x$, а по $A^*II$ "
            "$\\sim((\\forall a)(\\exists b))x \\dashv\\vdash \\sim(\\forall a)x\\sim(\\exists b)x$». Найдите обе ошибки и "
            "исправьте.")
    return card(level, "E", "vary", "text", "с. 130–131, гл. 7, § 20", "кванторы, расширения, диагностика", cond,
                "1) $A^*I$ объединяет только группы с одним и тем же K; 2) отрицание конъюнкции групп даёт дизъюнкцию: "
                "$\\sim(\\forall a)x \\vee \\sim(\\exists b)x$.",
                "1. В $A^*I$ стоит один и тот же K: $(Ka)(Kb)x \\dashv\\vdash (K(a, b))x$; для $(\\forall a)(\\exists b)x$ "
                "схема неприменима (смешение кванторов меняет смысл: ср. T15 и необратимость перестановки, § 8).\n"
                "2. По схеме $\\sim(\\alpha(K^1a)\\beta(K^2b))x \\dashv\\vdash (\\sim\\alpha(K^1a) \\vee \\sim\\beta(K^2b))x$ и "
                "схеме для дизъюнкции групп получается $\\sim(\\forall a)x \\vee \\sim(\\exists b)x$, а не конъюнкция.",
                system=SYS_)


def c20_chain(level=6):
    k = rnd.choice(["\\forall", "\\exists"])
    nm = "T14" if k == "\\forall" else "T16"
    cond = (f"{CONV} Докажите формулу $({k} a)({k} b)({k} c)x \\vdash ({k}(a, c))({k} b)x$, пользуясь {nm} (с. 104), R1/R2 "
            "(с. 100) и $A^*I$ § 20 (с. 130); укажите основание каждой строки.")
    R = "R1" if k == "\\forall" else "R2"
    sol = (f"1. $({k} b)({k} c)x \\vdash ({k} c)({k} b)x$ [{nm}]\n"
           f"2. $({k} a)({k} b)({k} c)x \\vdash ({k} a)({k} c)({k} b)x$ [{R}: 1]\n"
           f"3. $({k} a)({k} c)({k} b)x \\vdash ({k}(a, c))({k} b)x$ [$A^*I$ при $x$ := $({k} b)x$]\n"
           f"4. $({k} a)({k} b)({k} c)x \\vdash ({k}(a, c))({k} b)x$ [R1 $S^s$: 2, 3]")
    return card(level, "D", "vary", "proof", "с. 100, 104, 130, гл. 7, § 2, 6, 20", "кванторы, расширения, вывод", cond,
                "Вывод в 4 строки (см. решение).", sol, system=SYS_)


def c20_nat(level=5):
    cond = (f"{CONV} $(a \\leftarrow b)$ прочтём «$a$ стоит в отношении к $b$». Запишите утверждения «для всех $a$ и $b$: $a$ "
            "стоит в отношении к $b$» и «найдутся $a$ и $b$, такие что $a$ не стоит в отношении к $b$» двумя способами — "
            "отдельными группами и группой с несколькими терминами (§ 20, с. 130), — и с помощью $A^*I$ и схем § 6 "
            "докажите, что второе утверждение следует из отрицания первого.")
    return card(level, "T", "vary", "short", "с. 102–103, 130, гл. 7, § 6, 20", "кванторы, расширения, перевод", cond,
                "$(\\forall a)(\\forall b)(a \\leftarrow b) \\dashv\\vdash (\\forall(a, b))(a \\leftarrow b)$; $(\\exists a)"
                "(\\exists b)\\sim(a \\leftarrow b) \\dashv\\vdash (\\exists(a, b))\\sim(a \\leftarrow b)$; из "
                "$\\sim(\\forall a)(\\forall b)(a \\leftarrow b)$ по T1, R2, T1 — $(\\exists a)(\\exists b)\\sim(a "
                "\\leftarrow b)$.",
                "1. $\\sim(\\forall a)(\\forall b)(a \\leftarrow b) \\vdash (\\exists a)\\sim(\\forall b)(a \\leftarrow b)$ [T1].\n"
                "2. $\\sim(\\forall b)(a \\leftarrow b) \\vdash (\\exists b)\\sim(a \\leftarrow b)$ [T1].\n"
                "3. $(\\exists a)\\sim(\\forall b)(a \\leftarrow b) \\vdash (\\exists a)(\\exists b)\\sim(a \\leftarrow b)$ [R2: 2].\n"
                "4. Транзитивность (R1 $S^s$): 1, 3; $A^*I$ переводит запись в $(\\exists(a, b))\\sim(a \\leftarrow b)$.",
                form="nat", system=SYS_)


# § 21: кванторы и условные высказывания
def IF(a, b):
    return ("if", a, b)


S21 = ("Схемы § 21 (с. 131): 1) $(x \\rightarrow y) \\vdash (\\forall a)(x \\rightarrow y)$; 2) $(\\exists a)(x "
       "\\urcorner\\!\\rightarrow y) \\vdash (x \\urcorner\\!\\rightarrow y)$; 3) $(\\exists a)(x? \\rightarrow y) \\vdash "
       "\\sim(x \\rightarrow y)$; 4) $(x \\rightarrow y) \\dashv\\vdash (x \\rightarrow (\\forall a)y)$; 5) $(x \\rightarrow y) "
       "\\dashv\\vdash ((\\exists a)x \\rightarrow y)$.")


def par(t):
    """Высказывание в антецеденте или консеквенте: составное (кроме отрицания элементарного) — в скобках."""
    simple = t.count("\\leftarrow") == 1 and (t.startswith("(") or t.startswith("\\sim"))
    quant = t.startswith("(\\forall") or t.startswith("(\\exists")
    return t if simple or quant else f"({t})"


def iftex(x, y):
    return f"({par(x)} \\rightarrow {par(y)})"


def c21_chain(level=6):
    X, Y = tex(A.compound()), tex(A.compound())
    t = rnd.choice(["a", "b"])
    s = rnd.choice(["a", "b"])
    Xe = f"(\\exists {s}){X if X.startswith('(') else '(' + X + ')'}" if False else f"(\\exists {s})" + (X if X.startswith("(") and X.endswith(")") and X.count("(") == 1 else f"({X})")
    Ya = f"(\\forall {t})" + (Y if Y.startswith("(") and Y.endswith(")") and Y.count("(") == 1 else f"({Y})")
    lines = [f"1. ${iftex(X, Y)} \\vdash {iftex(X, Ya)}$ [схема 4]",
             f"2. ${iftex(X, Ya)} \\vdash {iftex(Xe, Ya)}$ [схема 5 при $y$ := ${Ya}$]",
             f"3. ${iftex(X, Y)} \\vdash {iftex(Xe, Ya)}$ [R1 $S^s$: 1, 2]",
             f"4. ${iftex(Xe, Ya)} \\vdash {iftex(X, Ya)}$ [схема 5, обратная формула]",
             f"5. ${iftex(X, Ya)} \\vdash {iftex(X, Y)}$ [схема 4, обратная формула]",
             f"6. ${iftex(Xe, Ya)} \\vdash {iftex(X, Y)}$ [R1 $S^s$: 4, 5]"]
    cond = (f"{CONV} {S21} Докажите ${iftex(X, Y)} \\dashv\\vdash {iftex(Xe, Ya)}$, указывая основание каждой строки "
            "(R1 $S^s$ — транзитивность, с. 17).")
    return card(level, "D", "iso", "proof", "с. 17, 131, гл. 1, § 1; гл. 7, § 21", "кванторы, условные высказывания, вывод",
                cond, "Вывод в 6 строк (см. решение): схемы 4 и 5 в обе стороны и транзитивность.", "\n".join(lines),
                system="S^s_cq")


def c21_inst(level=5, yes=True):
    X, Y = tex(A.compound()), tex(A.compound())
    opts_yes = [(f"{iftex(X, Y)} \\vdash (\\forall b){iftex(X, Y)}", "схема 1 ($a$ := $b$)"),
                (f"(\\exists a)({X} \\urcorner\\!\\rightarrow {Y}) \\vdash ({X} \\urcorner\\!\\rightarrow {Y})", "схема 2"),
                (f"(\\exists a)({X}? \\rightarrow {Y}) \\vdash \\sim{iftex(X, Y)}", "схема 3")]
    opts_no = [(f"(\\exists a){iftex(X, Y)} \\vdash {iftex(X, Y)}", "в схеме 2 под квантором $x \\urcorner\\!\\rightarrow y$, "
                "а не $x \\rightarrow y$"),
               (f"(\\forall a)({X}? \\rightarrow {Y}) \\vdash \\sim{iftex(X, Y)}", "в схеме 3 квантор существования"),
               (f"(\\exists a)({X} \\urcorner\\!\\rightarrow {Y}) \\vdash \\sim{iftex(X, Y)}", "схема 2 даёт "
                "$x \\urcorner\\!\\rightarrow y$, схема 3 — о $x? \\rightarrow y$")]
    f, why = rnd.choice(opts_yes if yes else opts_no)
    cond = (f"{CONV} {S21} Установите, получается ли формула ${f}$ из одной из схем 1–3 заменой букв; если да — укажите "
            "схему и замену, если нет — назовите, что мешает.")
    if yes:
        return card(level, "A", "iso", "short", "с. 131, гл. 7, § 21", "кванторы, условные высказывания", cond,
                    f"Получается: {why}, $x$ := ${X}$, $y$ := ${Y}$.", f"Сопоставление со схемой: {why}.", system="S^s_cq")
    return card(level, "E", "vary", "short", "с. 131, гл. 7, § 21", "кванторы, условные высказывания, почти-пример",
                cond, f"Не получается: {why}.", f"Сравниваем с перечнем с. 131: {why}; другой подходящей схемы среди 1–3 "
                "нет.", system="S^s_cq")


def c21_diag(level=6):
    X, Y = tex(A.compound()), tex(A.compound())
    cond = (f"{CONV} {S21} Студент доказывает: «1. ${iftex(X, Y)} \\vdash {iftex(X, '(\\exists a)' + ('(' + Y + ')' if not Y.startswith('(') else Y))}$ "
            f"[схема 4]; 2. ${iftex(X, Y)} \\vdash ((\\forall a){'(' + X + ')' if not X.startswith('(') else X} \\rightarrow {Y})$ [схема 5]». "
            "Найдите обе ошибки.")
    return card(level, "E", "vary", "text", "с. 131, гл. 7, § 21", "кванторы, условные высказывания, диагностика", cond,
                "Схема 4 вводит в консеквент квантор общности, а не существования; схема 5 вводит в антецедент квантор "
                "существования, а не общности.",
                "Схема 4: $(x \\rightarrow y) \\dashv\\vdash (x \\rightarrow (\\forall a)y)$; схема 5: $(x \\rightarrow y) "
                "\\dashv\\vdash ((\\exists a)x \\rightarrow y)$ (с. 131). У студента кванторы перепутаны в обоих шагах.",
                system="S^s_cq")


def c21_nat(level=5):
    cond = (f"{CONV} {S21} Прочтите схемы 4 и 5 на обычном языке для условного высказывания «если $c$ есть $d$, то $a$ есть "
            "$b$» (квантор — по $a$) и запишите получающиеся равнозначные высказывания.")
    return card(level, "F", "vary", "short", "с. 131, гл. 7, § 21", "кванторы, условные высказывания, перевод", cond,
                "$((c \\leftarrow d) \\rightarrow (a \\leftarrow b)) \\dashv\\vdash ((c \\leftarrow d) \\rightarrow (\\forall a)"
                "(a \\leftarrow b))$: «если $c$ есть $d$, то все $a$ суть $b$»; по схеме 5 — $((\\exists a)(c \\leftarrow d) "
                "\\rightarrow (a \\leftarrow b))$.",
                "Схема 4 вносит квантор общности в консеквент, схема 5 — квантор существования в антецедент. Так как $a$ не "
                "входит в $(c \\leftarrow d)$, группа $(\\exists a)$ в антецеденте вырождена (D6 § 1): по смыслу антецедент "
                "не меняется. В консеквенте «$a$ есть $b$» переходит в «все $a$ суть $b$».", form="nat", system="S^s_cq")


# ================================================================ планы
KEEP = {
    "07.13-002": ("07.13-011", None), "07.13-006": ("07.13-014", None), "07.13-009": ("07.13-016", None),
    "07.13-012": ("07.13-012", None), "07.13-014": ("07.13-013", None), "07.13-016": ("07.13-015", None),
    "07.18-004": ("07.18-009", None), "07.18-008": ("07.18-011", None), "07.18-012": ("07.18-013", None),
    "07.19-004": ("07.19-008", None), "07.19-008": ("07.19-010", None),
}


def plan():
    P = {}
    s10 = [c10_series, c10_closure, c10_diag, c10_compare, c10_series, c10_rule, c10_closure, c10_series, c10_diag,
           c10_compare, c10_nat]
    P.update({f"07.10-{k:03d}": f for k, f in enumerate(s10, 1)})
    s11 = [c11_series, c11_compare, lambda: c11_series(diag=True), c11_a8, c11_e, c11_mt1, c11_compare,
           lambda: c11_series(5), lambda: c11_series(diag=True), c11_mt1, c11_compare]
    P.update({f"07.11-{k:03d}": f for k, f in enumerate(s11, 1)})
    s12 = {1: c12_rec, 2: lambda: c12_subst("A^16", True), 3: c12_deriv, 4: lambda: c12_subst("A^26", False),
           5: c12_occ, 6: c12_deriv, 7: c12_complete, 8: c12_badE, 9: c12_diag, 10: c12_rec, 11: c12_deriv}
    P.update({f"07.12-{k:03d}": f for k, f in s12.items()})
    s13 = {1: c13_qf, 3: c13_lines, 4: c13_diag, 5: c13_series, 7: c13_badlines, 8: c13_qf, 10: c13_lines,
           11: c13_diag, 13: c13_badlines, 15: c13_series}
    P.update({f"07.13-{k:03d}": f for k, f in s13.items()})
    s14 = [c14_t, lambda: c12_deriv(src="с. 122–124, гл. 7, § 12, 14"), c14_mt1, c14_near,
           lambda: c12_complete("с. 122–124, гл. 7, § 12, 14"), c14_badstep, lambda: c12_deriv(src="с. 122–124, гл. 7, § 12, 14"),
           lambda: c12_diag("с. 122–124, гл. 7, § 12, 14"), c14_mt1, lambda: c12_deriv(7, "с. 122–124, гл. 7, § 12, 14")]
    P.update({f"07.14-{k:03d}": f for k, f in enumerate(s14, 1)})
    s15 = {1: c15_direct, 2: c15_series, 3: c15_cm_diag, 4: c15_compare, 5: c15_series, 7: c15_direct, 8: c15_e2,
           9: c15_compare, 10: c15_series}
    P.update({f"07.15-{k:03d}": f for k, f in s15.items()})
    s16 = [c16_T, c16_series, c16_diag, c16_compare, c16_mt1, c16_series, c16_nat, c16_diag, c16_series, c16_compare]
    P.update({f"07.16-{k:03d}": f for k, f in enumerate(s16, 1)})
    s17 = [lambda: c16_series(6, True), c16_compare, c17_e, lambda: c12_deriv(src="с. 122–127, гл. 7, § 12, 17"),
           lambda: c16_series(6, True), lambda: c16_diag(6), c16_compare, lambda: c16_series(5, True), c17_e,
           c16_nat]
    P.update({f"07.17-{k:03d}": f for k, f in enumerate(s17, 1)})
    s18 = {1: c18_repl, 2: c18_scheme, 3: c18_diag, 5: c18_sem, 6: c18_repl, 7: c18_dep, 9: c18_diag, 10: c18_sem,
           11: c18_scheme, 13: c18_repl}
    P.update({f"07.18-{k:03d}": f for k, f in s18.items()})
    s19 = {1: c19_subst, 2: c19_t13, 3: c19_term, 5: c19_series, 6: c19_e, 7: c19_subst, 9: c19_t13, 10: c19_series}
    P.update({f"07.19-{k:03d}": f for k, f in s19.items()})
    s20 = [c20_rewrite, c20_comb, c20_diag, c20_chain, c20_comb, c20_nat, c20_rewrite, c20_chain, c20_comb, c20_diag]
    P.update({f"07.20-{k:03d}": f for k, f in enumerate(s20, 1)})
    s21 = {1: c21_chain, 2: lambda: c21_inst(5, True), 3: lambda: c21_inst(5, False), 4: c21_chain, 6: c21_diag,
           7: c21_nat, 8: c21_chain, 10: lambda: c21_inst(5, True)}
    P.update({f"07.21-{k:03d}": f for k, f in s21.items()})
    return P
