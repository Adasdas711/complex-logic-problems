"""Гл. 6: дополнительные генераторы — ситуации § 4, естественный язык § 4, S⁵_if (MT3, построения), перенос § 9,
парадоксы § 10, подстановка и распространение базисных формул § 11, банки утверждений для диагностики."""
from hard06_lib import F, C, IF, IFN, IFQ, IMP, N, V, W, ftex, tex, rnd, x, y, z, v, u, L, CV, card, SYSNAME, sys_text
from hard06_sem import comp, nn, explain_non, explain_taut, INTERP, lit_tex, c_tex
import hard06_sem as S
import hard06_lib as H
import hard06_sys as SY
import hard06_lang as G

# ---------------------------------------------------------------- § 4: ситуации и правила
SIT = [
    ("$x \\rightarrow y$ имеет значение 1 и $x$ — 1", "$y$ должно иметь значение 1", "1", "$y$ может иметь любое значение"),
    ("$x \\rightarrow y$ имеет значение 1 и $y$ — 0", "$x$ должно иметь значение 0", "2", "$x$ может иметь любое значение"),
    ("$x \\rightarrow y$ имеет значение 0 и $x$ — 1", "значение $y$ не зависит от значения $x$: рассматриваются оба случая",
     "3", "$y$ должно иметь значение 0, как у материальной импликации"),
    ("$x \\rightarrow y$ имеет значение 0 и $y$ — 0", "значение $x$ не зависит от значения $y$", "4",
     "$x$ должно иметь значение 1"),
    ("$x$ имеет значение 0", "значение $x \\rightarrow y$ не зависит от значения $x$", "9",
     "$x \\rightarrow y$ должно иметь значение 1"),
    ("$y$ имеет значение 1", "значение $x \\rightarrow y$ не зависит от значения $y$", "9",
     "$x \\rightarrow y$ должно иметь значение 1"),
    ("$x \\rightarrow y$ имеет значение 1", "$x \\urcorner\\!\\rightarrow y$ имеет значение 0", "10",
     "$x \\urcorner\\!\\rightarrow y$ может иметь любое значение"),
    ("$x \\rightarrow y$ имеет значение 0", "значение $x \\urcorner\\!\\rightarrow y$ может быть и 1, и 0", "11",
     "$x \\urcorner\\!\\rightarrow y$ должно иметь значение 1"),
    ("$x \\rightarrow y$ и $x \\urcorner\\!\\rightarrow y$ имеют значение 0", "$x? \\rightarrow y$ имеет значение 1", "12",
     "это невозможно: одно из них должно иметь значение 1"),
    ("$x$ приписано 1, и вследствие этого мы вынуждены приписать $y$ значение 1",
     "$x \\rightarrow y$ должно иметь значение 1", "5", "$x \\rightarrow y$ может иметь значение 0"),
    ("$y$ приписано 0, и вследствие этого мы вынуждены приписать $x$ значение 0",
     "$x \\rightarrow y$ должно иметь значение 1", "6", "$x \\rightarrow y$ может иметь значение 0"),
    ("$x$ приписано 1, и это не обязывает приписывать $y$ значение 1", "$x \\rightarrow y$ можно приписать значение 0", "7",
     "$x \\rightarrow y$ должно иметь значение 1"),
    ("$y$ приписано 0, и это не обязывает приписывать $x$ значение 0", "$x \\rightarrow y$ можно приписать значение 0", "8",
     "$x \\rightarrow y$ должно иметь значение 1"),
]


def sub_xy(s, X, Y):
    s = s.replace("$x \\rightarrow y$", "§A").replace("$x \\urcorner\\!\\rightarrow y$", "§B").replace(
        "$x? \\rightarrow y$", "§C").replace("$x$", "§X").replace("$y$", "§Y")
    return s.replace("§A", f"${tex(IF(X, Y))}$").replace("§B", f"${tex(IFN(X, Y))}$").replace(
        "§C", f"${tex(IFQ(X, Y))}$").replace("§X", f"${tex(X)}$").replace("§Y", f"${tex(Y)}$")


def c_sit_diag(level=5, src="с. 86–87, гл. 6, § 4"):
    its = rnd.sample(SIT, 4)
    wrong = rnd.sample(range(4), 2)
    X, Y = comp(2) or (x, y)
    lines, ans, sol = [], [], []
    for i, (sit, good, n, bad) in enumerate(its):
        claim = good if i not in wrong else bad
        lines.append(f"{i + 1}. Если {sub_xy(sit, X, Y)}, то {sub_xy(claim, X, Y)}.")
        if i in wrong:
            ans.append(f"{i + 1}: {sub_xy(good, X, Y)} (п. {n})")
            sol.append(f"{i + 1}. По п. {n} § 4 (с. 86–87): если {sub_xy(sit, X, Y)}, то {sub_xy(good, X, Y)}. Вывод студента "
                       f"«{sub_xy(bad, X, Y)}» правилам не соответствует" +
                       (" — он считает $\\rightarrow$ материальной импликацией (ср. с. 88)." if n in ("3", "9") else "."))
    cond = (f"{CV} Студент применил правила интерпретации § 4 гл. 6 к высказываниям $X = {tex(X)}$, $Y = {tex(Y)}$:\n\n" +
            "\n".join(lines) + "\n\nРовно два вывода неверны. Найдите их, назовите пункт правил, который нарушен, и дайте "
            "верный вывод. Правила — пп. 1–12, с. 86–87 (в том числе п. 10: если одно из $x \\rightarrow y$ и $x \\urcorner\\!"
            "\\rightarrow y$ имеет значение 1, то другое — 0; п. 11: если одно имеет значение 0, значение другого от него не "
            "зависит; п. 12: $x? \\rightarrow y$ равнозначно $\\sim(x \\rightarrow y)\\sim(x \\urcorner\\!\\rightarrow y)$). " + INTERP)
    return card(level, "E", "vary", "text", src, "условность, интерпретация, диагностика", cond, "; ".join(ans) + ".",
                "\n".join(sol) + "\n\nОстальные выводы верны.")


def c_nat_sem(level=6, src="с. 87–88, гл. 6, § 4"):
    ph = rnd.choice([G.PH, G.PH2])
    items = []
    keys = [("good", rnd.choice(["A3", "A4", "T7", "T8", "A2"])), ("bad", rnd.choice(["split", "orcons", "conv", "inv"]))]
    for kind, k in keys:
        for _ in range(300):
            X, Y, Z, Vv = (G.lit() for _ in range(4))
            if len({t[1] if t[0] == "neg" else t for t in (X, Y, Z, Vv)}) < 4:
                continue
            a, b = (S.GOOD if kind == "good" else S.BAD)[k](X, Y, Z, Vv)
            if nn(a) or nn(b) or not F.flat(C(a, b)):
                continue
            r = F.sem_robust(a, b)
            if r and r[0] == (kind == "good"):
                items.append((a, b, r))
                break
    rnd.shuffle(items)
    leg = "; ".join(f"${kk}$ — «{p}»" for kk, (p, _) in ph.items())
    cond = (f"Обозначения: {leg}. Запишите каждое рассуждение формулой с оператором условности и исследуйте, тавтология ли "
            f"она при интерпретации § 4 (по образцу с. 87–88); обоснуйте значениями. {INTERP}\n\n" +
            "\n".join(f"{L[i]}) «{G.cap(G.nat(a, ph))}; следовательно, {G.nat(b, ph)}»." for i, (a, b, _) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) ${ftex(a, b)}$ — " + ("тавтология" if r[0] else "не тавтология") for i, (a, b, r) in enumerate(items))
    sol = "\n".join(f"{L[i]}) ${ftex(a, b)}$. " + (explain_taut(a, b) if r[0] else explain_non(a, b, r[1]))
                    for i, (a, b, r) in enumerate(items))
    return card(level, "V", "open", "short", src, "условность, интерпретация", cond, ans, sol, form="nat")


# ---------------------------------------------------------------- § 8: MT3/MT4, построения
def c_mt34(level=6, src="с. 92, гл. 6, § 8"):
    """Из данных ⊢ (F → (G → H)), ⊢ F, ⊢ G вывести ⊢ H по доказательству MT3."""
    for _ in range(100):
        Fm, Gm, Hm = comp(3) or (x, y, z)
        if not nn(C(Fm, Gm, Hm)):
            break
    big = IF(Fm, IF(Gm, Hm))
    lines = [(None, big, "given"), (None, Fm, "given"), (None, Gm, "given")]
    H.mp(lines, 1, 2)
    k = len(lines)
    H.mp(lines, k, 3)
    assert not F.check(lines, "5"), F.check(lines, "5")
    cond = (f"{CV} В $S^5_{{if}}$ даны доказуемые формулы ${ftex(None, big)}$, ${ftex(None, Fm)}$, ${ftex(None, Gm)}$. Выведите "
            f"${ftex(None, Hm)}$, повторив доказательство MT3 § 8 (с. 92) — без ссылки на саму MT3. {H.S5_RULES}")
    ans = f"Вывод из {len(lines)} строк: дважды A1, MT6 гл. 4, $R^d1$ (см. решение)."
    sol = (F.show(lines, "5") + "\n\nДоказательство MT3 (с. 92): $(x \\rightarrow y)x \\vdash y$ доказуема (A1); по условию "
           "$\\vdash (x \\rightarrow y)$ и $\\vdash x$, по MT6 гл. 4 — $\\vdash (x \\rightarrow y)x$; по $R^d1$ — $\\vdash y$. Здесь "
           "оно применено дважды.")
    return card(level, "D", "iso", "proof", src, "условность, S5if, вывод", cond, ans, sol, system="S^5_if")


def c_s5_build(level=7, src="с. 91–92, гл. 6, § 8"):
    for _ in range(500):
        lt = rnd.sample("xyz", 2)
        a = SY.rnd_w(lt, 1)
        b = SY.rnd_w(lt + ["v"], 2)
        if nn(a) or nn(b) or not F.taut_imp(a, b) or F.strong_p(a, b) or not F.atoms(b) - F.atoms(a):
            continue
        if 5 <= F.size(a) + F.size(b) <= 16:
            break
    new = sorted(F.atoms(b) - F.atoms(a))
    lines = H.discharge(a, b, new)
    cond = (f"{CV} Постройте формулу $\\vdash (x \\rightarrow y)$ ($x$, $y$ без оператора условности), доказуемую в "
            f"$S^5_{{if}}$, для которой $x \\vdash y$ недоказуема в $S^s$, и выведите её в $S^5_{{if}}$ по правилам (без ссылки на "
            f"MT5 § 8) — или докажите, что такой формулы нет. {H.S5_RULES} {G.SS_CRIT}")
    ans = f"Например, $\\vdash ({tex(a)} \\rightarrow {tex(b)})$: вывод из {len(lines)} строк."
    sol = (f"${tex(a)} \\vdash {tex(b)}$ в $S^s$ недоказуема: в заключение входит {', '.join('$' + t + '$' for t in new)}, "
           f"отсутствующее в посылке. Но ${tex(a)} \\supset {tex(b)}$ — тавтология, и формула выводится с вспомогательной "
           f"тавтологией (её $\\vdash$ дана основанием «$S^5$»):\n\n" + F.show(lines, "5"))
    return card(level, "D", "open", "build", src, "условность, S5if, построение", cond, ans, sol, system="S^5_if")


def c_discharge(level=7, src="с. 91–92, гл. 6, § 8"):
    for _ in range(500):
        X, Y, Z = comp(3) or (x, y, z)
        pool = [(C(X, Y), W(X, Z)), (X, W(Y, N(Y))) if Y[0] == "v" else (X, W(Z, N(Z))) if Z[0] == "v" else (X, Y),
                (C(X, N(X)), Y), (W(X, Y), W(X, W(Y, Z)))]
        a, b = rnd.choice(pool)
        new = sorted(F.atoms(b) - F.atoms(a))
        if nn(a) or nn(b) or not new or not F.taut_imp(a, b):
            continue
        break
    lines = H.discharge(a, b, new)
    return H.c_deriv("5", src=src, lines=lines, extra=" В $S^s$ формула $" + ftex(a, b) + "$ недоказуема (в заключении "
                     "новые элементарные высказывания), так что R1 § 8 сразу не применить.") | {"level": level}


# ---------------------------------------------------------------- § 9: перенос выводов S⁵*_if → S⁵_if
def translate_5s(lines):
    """B1 → A1; B2 → вывод T4 по A2, A1; B3 → A5 и R1 § 8."""
    out, mp_ = [], {}
    for n, (a, b, wh) in enumerate(lines, 1):
        if wh == "B1":
            out.append((a, b, "A1"))
        elif wh == "B2":
            Fx, Fy = a[1][0], a[1][1]          # (X → Y), ∼Y
            X, Y = Fx[1], Fx[2]
            base = len(out)
            out += [(a, Fx, "Ss"), (Fx, IF(N(Y), N(X)), "A2"), (a, IF(N(Y), N(X)), ("R1", base + 1, base + 2)),
                    (a, Fy, "Ss"), (a, C(IF(N(Y), N(X)), Fy), ("R2", base + 3, base + 4)),
                    (C(IF(N(Y), N(X)), Fy), N(X), "A1"), (a, b, ("R1", base + 5, base + 6))]
        elif wh == "B3":
            P, Q = b[1], b[2]
            out.append((P, Q, "A5"))
            out.append((None, b, ("Rif", len(out))))
        elif isinstance(wh, str):
            out.append((a, b, wh))
        else:
            out.append((a, b, (wh[0],) + tuple(mp_[i] for i in wh[1:])))
        mp_[n] = len(out)
    return out


def c_mt1_9(level=7, src="с. 93–94, гл. 6, § 9"):
    for _ in range(50):
        lines = H.s5_deriv("5s")
        if any(wh in ("B2", "B3") for *_, wh in lines):
            break
    t = translate_5s(lines)
    errs = F.check(t, "5")
    assert not errs, errs
    f_ = lines[-1][1]
    cond = (f"{CV} Ниже — вывод формулы ${ftex(None, f_)}$ в $S^{{5*}}_{{if}}$. Не ссылаясь на MT1 § 9, постройте вывод той же "
            f"формулы в $S^5_{{if}}$: каждую строку с A1–A3 § 9 замените выводом в $S^5_{{if}}$, остальные перенумеруйте. "
            f"{H.SCH_5S} {H.S5_RULES} В $S^s_{{if}}$: A1 $(x \\rightarrow y)x \\vdash y$, A2 $(x \\rightarrow y) \\vdash (\\sim y "
            f"\\rightarrow \\sim x)$, A5 $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$.\n\n{F.show(lines, '5s')}")
    ans = f"Вывод в $S^5_{{if}}$ из {len(t)} строк (см. решение): A1 § 9 → A1; A2 § 9 → A2, A1, R1, R2; A3 § 9 → A5 и R1 § 8."
    sol = ("A1 § 9 совпадает с A1 § 6. A2 § 9 $(x \\rightarrow y)\\sim y \\vdash \\sim x$ — теорема T4 $S^s_{if}$ [A2, A1] (с. 91). "
           "A3 § 9 получается из A5 по R1 § 8. Остальные основания ($S^s$, R1–R3, $R^d1$, MT6) — общие.\n\n" + F.show(t, "5") +
           "\n\nЭто часть MT1 § 9 (с. 94): в $S^5_{if}$ доказуемы A1 и A3 системы $S^{5*}_{if}$.")
    return card(level, "S", "transfer", "proof", src, "условность, S5*if, перенос", cond, ans, sol, system="S^5*_if")


# ---------------------------------------------------------------- § 10: парадоксы
def par_lines(kind, X, Y):
    if kind == "t7":          # ⊢ (X → (Y → X))
        lines = [(C(X, Y), X, "Ss"), (None, IF(C(X, Y), X), ("Rif", 1)), (IF(C(X, Y), X), IF(X, IF(Y, X)), "A5"),
                 (None, IF(X, IF(Y, X)), ("Rd1", 3, 2))]
        return lines
    if kind == "t5":          # ⊢ (X → Y ∨ ∼Y), Y — буква
        return H.discharge(X, W(Y, N(Y)), sorted(F.atoms(Y) - F.atoms(X)))
    if kind == "t6":          # ⊢ (∼YY → X)
        return H.discharge(C(N(Y), Y), X, sorted(F.atoms(X) - F.atoms(Y)))
    raise ValueError


def c_par_deriv(level=7, src="с. 94, гл. 6, § 10"):
    for _ in range(300):
        kind = rnd.choice(["t5", "t6", "t7"])
        X, Y = comp(2) or (x, y)
        if kind in ("t5", "t6") and Y[0] != "v":
            continue
        if nn(C(X, Y)) or (kind == "t6" and X[0] == "v" and False):
            continue
        lines = par_lines(kind, X, Y)
        if not F.check(lines, "5"):
            break
    f_ = lines[-1][1]
    name = {"t7": "$\\vdash (x \\rightarrow (y \\rightarrow x))$", "t5": "$\\vdash (x \\rightarrow y \\vee \\sim y)$",
            "t6": "$\\vdash (\\sim yy \\rightarrow x)$"}[kind]
    return H.c_deriv("5", src=src, lines=lines, extra=f" Это пример «парадокса» {name} (§ 10, с. 94).") | {
        "level": level, "tags": "условность, парадоксы, вывод"}


def c_par_e(level=6, src="с. 94–95, гл. 6, § 10"):
    for _ in range(100):
        X, Y = comp(2) or (x, y)
        if not nn(C(X, Y)):
            break
    lines = [(C(X, Y), X, "Ss"), (None, IF(C(X, Y), X), ("Rif", 1)), (IF(C(X, Y), X), IF(X, IF(Y, X)), "A5"),
             (None, IF(X, IF(Y, X)), ("Rd1", 3, 2))]
    shown = F.show(lines, "5").replace("[A5]", "[$A^*5$]")
    cond = (f"{CV} Студент «выводит» парадокс ${ftex(None, IF(X, IF(Y, X)))}$ в системе $S^i_{{if}}$, где A5 заменена на $A^*5$ "
            f"$(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$ с условием: $\\vdash (x \\rightarrow z)$ и "
            f"$\\vdash (y \\rightarrow z)$ недоказуемы в $S^5_{{if}}$ (с. 95):\n\n{shown}\n\nНайдите ошибку и назовите нарушенное "
            f"условие. {H.S5_RULES}")
    ans = (f"Шаг 3: $A^*5$ неприменима — $\\vdash ({tex(X)} \\rightarrow {tex(X)})$ доказуема в $S^5_{{if}}$ ($x := {tex(X)}$, "
           f"$z := {tex(X)}$), а условие $A^*5$ требует её недоказуемости (с. 95).")
    sol = (f"В шаге 3 замена $x := {tex(X)}$, $y := {tex(Y)}$, $z := {tex(X)}$. Условие $A^*5$: $\\vdash ({tex(X)} \\rightarrow "
           f"{tex(X)})$ и $\\vdash ({tex(Y)} \\rightarrow {tex(X)})$ недоказуемы в $S^5_{{if}}$. Но ${tex(X)} \\vdash {tex(X)}$ — "
           f"теорема $S^s$ (сильная тавтология), и по R1 § 8 $\\vdash ({tex(X)} \\rightarrow {tex(X)})$ доказуема. Значит, шаг 3 — "
           f"не пример $A^*5$; именно так $A^*5$ исключает парадоксы вида $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow "
           f"z))$ (с. 94–95). Остальные шаги верны.")
    return card(level, "E", "open", "text", src, "условность, парадоксы, диагностика", cond, ans, sol, system="S^i_if")


# ---------------------------------------------------------------- § 11: подстановка и распространение
def c_sub(level=6, src="с. 96–97, гл. 6, § 11"):
    k, sch = rnd.choice([(3, "A7"), (9, "A8"), (1, "A1"), (6, "T11")])
    pa, pb = SY.BPAT[k]
    if k == 1:
        pa, pb = C(IF(V("a"), V("b")), V("a")), V("b")
    lets = sorted(F.atoms(pa) | F.atoms(pb))
    for _ in range(100):
        vals = comp(len(lets))
        if vals and not nn(C(*vals)):
            break
    m = dict(zip(lets, vals))
    A, B = F.subst(pa, m), F.subst(pb, m)
    mm = F.instance(sch, A, B)
    assert mm is not None
    cond = (f"{CV} Базисная формула вида {k} ${ftex(pa, pb)}$ доказуема в $S^s_{{if}}$. Подставьте вместо элементарных "
            f"высказываний: " + ", ".join(f"${t}$ := ${tex(vv)}$" for t, vv in m.items()) + f". Докажите, что полученная "
            f"формула доказуема (п. 2 D2 § 11), указав схему и замену её букв. {H.SCH_S} T11 $(x \\rightarrow y)(v \\rightarrow "
            f"z) \\vdash (x \\vee v \\rightarrow y \\vee z)$ (с. 91).")
    ans = f"${ftex(A, B)}$ — пример {sch} (замена {SY.m_tex(mm)})."
    sol = (f"1. Подстановка даёт ${ftex(A, B)}$.\n2. Исходная формула — пример {sch}; подстановка в пример схемы — снова пример той "
           f"же схемы: замена {SY.m_tex(mm)}.\n3. Это и есть довод книги: п. 2 D2 выполняется «в силу того, что мы используем "
           f"аксиомные схемы» (с. 97).")
    return card(level, "D", "vary", "proof", src, "условность, полнота, подстановка", cond, ans, sol, system="S^s_if")


def c_extend(level=7, src="с. 96–97, гл. 6, § 11"):
    """Распространение базисных видов 3 и 6 на три члена: вывод по A7 / T11."""
    kind = rnd.choice([3, 6])
    a_, b_, c_, d_, e_, f_ = (N(t) if rnd.random() < 0.3 else t for t in rnd.sample([V(c) for c in "xyzvuw"], 6))
    p1, p2, p3 = IF(a_, b_), IF(c_, d_), IF(e_, f_)
    P = C(p1, p2, p3)
    op_a, op_c, sch = (C, C, "A7") if kind == 3 else (W, W, "T11")
    if kind == 3:
        g12 = IF(C(a_, c_), C(b_, d_))
        g = IF(C(C(a_, c_), e_), C(C(b_, d_), f_))
    else:
        g12 = IF(W(a_, c_), W(b_, d_))
        g = IF(W(W(a_, c_), e_), W(W(b_, d_), f_))
    lines = [(P, p1, "Ss"), (P, p2, "Ss"), (P, C(p1, p2), ("R2", 1, 2)), (C(p1, p2), g12, sch), (P, g12, ("R1", 3, 4)),
             (P, p3, "Ss"), (P, C(g12, p3), ("R2", 5, 6)), (C(g12, p3), g, sch), (P, g, ("R1", 7, 8))]
    errs = F.check(lines, "sT")
    assert not errs, errs
    cond = (f"Буквы $x, y, z, v, u, w$ — высказывания; $\\rightarrow$ — оператор условности. По с. 97 «распространить правила для базисных формул на любое число членов дизъюнкций и конъюнкций не "
            f"представляет труда». Выведите в $S^s_{{if}}$ формулу ${ftex(P, g)}$ — распространение вида {kind} D1 § 11 на три "
            f"условных высказывания, пользуясь {'A7' if kind == 3 else 'T11'} и правилами общей теории дедукции. "
            f"{'A7 $(x \\rightarrow y)(z \\rightarrow v) \\vdash (xz \\rightarrow yv)$' if kind == 3 else 'T11 $(x \\rightarrow y)(v \\rightarrow z) \\vdash (x \\vee v \\rightarrow y \\vee z)$ (с. 91)'}. "
            f"{H.RULES}")
    ans = f"Вывод из {len(lines)} строк: дважды {sch} с R1, R2 (см. решение)."
    sol = F.show(lines, "sT") + f"\n\nДля $n$ членов — индукция: $n - 1$ раз применить {sch} к уже полученному и следующему члену."
    return card(level, "D", "vary", "proof", src, "условность, полнота, вывод", cond, ans, sol, system="S^s_if")


# ---------------------------------------------------------------- банки утверждений
CLAIMS4 = [
    ("Если $x \\rightarrow y$ имеет значение 1 и $x$ — 1, то $y$ должно иметь значение 1", True, "п. 1, с. 86."),
    ("Если $x$ имеет значение 0, то $x \\rightarrow y$ имеет значение 1", False, "по п. 9 при $x$ = 0 значение $x \\rightarrow y$ "
     "не зависит от значения $x$ (с. 87)."),
    ("$x \\rightarrow y$ может иметь значение 0 при $x$ = 1 и $y$ = 1", True, "с. 88."),
    ("$x \\rightarrow y$ и $x \\supset y$ сходны лишь в одном: при $x$ = 1, $y$ = 0 оба имеют значение 0", True, "с. 88."),
    ("Если истинно $x \\supset y$, то истинно $x \\rightarrow y$", False, "не всякому истинному $x \\supset y$ соответствует "
     "истинное $x \\rightarrow y$; обратное верно (с. 88)."),
    ("Если одно из $x \\rightarrow y$ и $x \\urcorner\\!\\rightarrow y$ имеет значение 0, то другое имеет значение 1", False,
     "по п. 11 значение другого от значения первого не зависит (с. 87)."),
    ("$x? \\rightarrow y$ равнозначно $\\sim(x \\rightarrow y)\\sim(x \\urcorner\\!\\rightarrow y)$", True, "п. 12, с. 87."),
    ("Формула $z \\vdash (x \\rightarrow z)$ — тавтология: при $z$ = 1 консеквент истинен", False, "приписав $z$ значение 1, мы не "
     "определяем $x \\rightarrow z$ — оно может иметь значение 0 по п. 9; $z$ получает 1 не вследствие того, что $x$ "
     "приписано 1 (с. 87)."),
    ("Высказывание $xy \\rightarrow x$ имеет значение 1 по п. 5", True, "консеквент принимает 1, если антецедент принимает 1 "
     "(с. 87)."),
]
CLAIMS5 = [
    ("Системы неклассического случая содержат $A^n1$–$A^n6$", True, "с. 89."),
    ("Классический случай получается добавлением $A^n7$ $\\sim(x \\rightarrow y) \\vdash (x \\urcorner\\!\\rightarrow y)$", True,
     "это один из двух способов (с. 89)."),
    ("В системе с $A^n1$–$A^n7$ доказуема $\\vdash (x? \\rightarrow y)$", False, "доказуема $\\vdash \\sim(x? \\rightarrow y)$ "
     "(MT1 § 5, с. 89)."),
    ("$\\sim(x \\urcorner\\!\\rightarrow y) \\vdash (x \\rightarrow y)$ доказуема в системах с $A^n1$–$A^n6$", False,
     "она не тавтология и потому недоказуема (MT3 § 5, с. 89)."),
    ("Формулы $A^n1$–$A^n6$ — тавтологии, и множества элементарных высказываний посылок и заключений у них совпадают", True,
     "MT2 § 5, с. 89."),
    ("В варианте с $D^*1$ оператор неопределённости сохраняется в алфавите", False, "из алфавита и определений исключается "
     "оператор неопределённости и все символы, содержащие его; $(x? \\rightarrow y)$ — сокращение (с. 89–90)."),
    ("$A^*2$: $(x \\urcorner\\!\\rightarrow y) \\vdash \\sim(x \\rightarrow y)$", True, "с. 90."),
]
CLAIMS6 = [
    ("$(x \\rightarrow y)y \\vdash x$ доказуема в $S^s_{if}$ по A1", False, "A1 — $(x \\rightarrow y)x \\vdash y$; «утверждение "
     "консеквента» не тавтология и по MT1 § 6 недоказуемо (с. 90)."),
    ("По MT3 § 6 в $S^s_{if}$ недоказуема формула вида $x \\vdash (y \\rightarrow z)$, где в $x$ нет оператора условности", True,
     "с. 90."),
    ("$(x \\rightarrow y) \\vdash (x \\rightarrow yz)$ доказуема по A4", False, "A4 — $(x \\rightarrow yz) \\vdash (x \\rightarrow "
     "y)(x \\rightarrow z)$; формула студента вводит новое $z$ и по MT2 § 6 недоказуема."),
    ("T4 $(x \\rightarrow y)\\sim y \\vdash \\sim x$ получается по A2 и A1", True, "с. 91, [A2, A1]."),
    ("Все доказуемые в $S^s_{if}$ формулы — тавтологии", True, "MT1 § 6, с. 90."),
    ("$(x \\rightarrow y) \\vdash (\\sim x \\rightarrow \\sim y)$ — это A2", False, "A2 — $(x \\rightarrow y) \\vdash (\\sim y "
     "\\rightarrow \\sim x)$, контрапозиция, а не обращение отрицаний (с. 90)."),
    ("T7 $(x \\vee y \\rightarrow z) \\vdash (x \\rightarrow z)(y \\rightarrow z)$ получается по A2, A4, A2", True, "с. 91."),
]
CLAIMS8 = [
    ("Если $\\vdash (x \\rightarrow y)$ доказуема в $S^5_{if}$, то $x \\supset y$ — тавтология", True, "MT2 § 8, с. 92."),
    ("Если $\\vdash (x \\rightarrow y)$ доказуема в $S^5_{if}$, то $\\vdash (x \\supset y)$ доказуема в $S^5$ при любых $x$, $y$",
     False, "MT6 § 8 требует, чтобы $x$, $y$ были высказываниями $S^5$; пример с. 93: $\\vdash ((x \\rightarrow y)(y \\rightarrow "
     "z) \\rightarrow (x \\rightarrow z))$ доказуема в $S^5_{if}$, а с $\\supset$ в $S^5$ — нет."),
    ("Обратное MT7 неверно", True, "с. 93: $\\vdash ((xy \\supset z \\vee v) \\supset ((x \\supset z) \\vee (y \\supset v)))$ "
     "доказуема в $S^5$, а аналог с $\\rightarrow$ — нет."),
    ("MT3 § 8 доказывается по A1, R1 § 8 и $R^d1$", True, "с. 92."),
    ("В доказательстве MT5 используются T13 и T15 $S^5_{if}$", True, "с. 93."),
    ("R1 § 8: если $\\vdash (x \\rightarrow y)$, то $x \\vdash y$", False, "R1 § 8 идёт в другую сторону: если $x \\vdash y$, то "
     "$\\vdash (x \\rightarrow y)$ (с. 91)."),
    ("В $S^5_{if}$ доказуема $\\vdash (x \\rightarrow x \\vee y)$", True, "T13, с. 92."),
]
CLAIMS9 = [
    ("$S^{5*}_{if}$ получается присоединением к $S^5$ схем A1–A3 и правила R1", True, "с. 93."),
    ("A2 § 9 — это $(x \\rightarrow y) \\vdash (\\sim y \\rightarrow \\sim x)$", False, "A2 § 9 — $(x \\rightarrow y)\\sim y \\vdash "
     "\\sim x$; контрапозиция — A2 § 6 (с. 90, 93)."),
    ("Формулы $\\vdash (x \\rightarrow y)$, доказуемые в $S^5_{if}$, доказуемы в $S^{5*}_{if}$, и наоборот", True, "MT1 § 9, с. 94."),
    ("A3 § 9 — формула следования $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$", False, "A3 § 9 — "
     "$\\vdash ((xy \\rightarrow z) \\rightarrow (x \\rightarrow (y \\rightarrow z)))$ (с. 93)."),
    ("В $S^{5*}_{if}$ имеет силу T8 $\\vdash ((x \\rightarrow y)(y \\rightarrow z) \\rightarrow (x \\rightarrow z))$", True, "с. 94."),
]
CLAIMS10 = [
    ("В $S^5_{if}$ доказуема $\\vdash (x \\rightarrow (y \\rightarrow x))$", True, "с. 94."),
    ("Для исключения парадоксов достаточно заменить A5 $S^s_{if}$ на $A^*5$, а A3 $S^{5*}_{if}$ — на $A^*3$", True, "с. 95."),
    ("Для систем с ограничением $A^*5$ верна теорема, аналогичная MT5 § 8", False, "она неверна (с. 95)."),
    ("Исключение парадоксов из системы исключает их из ситуаций, где применяются её правила", False, "интуитивно несомненно, "
     "что если $xy \\rightarrow z$ и $y$ истинно, то $x \\rightarrow z$; исключив парадоксы из системы, мы не исключим их из "
     "ситуаций (с. 94)."),
    ("Все доказуемые формулы $\\vdash (x \\rightarrow y)$ систем с ограничением непарадоксальны в том же смысле, что и формулы "
     "общей теории дедукции", True, "с. 95."),
]
CLAIMS11 = [
    ("Критерии полноты общей теории дедукции достаточны для теории условных высказываний", False, "они недостаточны: "
     "$(xy \\rightarrow z) \\vdash (xy \\rightarrow y)$ — тавтология и непарадоксальна, но как правило следования неприемлема "
     "(с. 95–96)."),
    ("В $(xy \\rightarrow z) \\vdash (xy \\rightarrow y)$ высказывание $xy \\rightarrow y$ всегда имеет значение 1", True, "с. 95."),
    ("По D2 § 11 достаточная полнота требует доказуемости всех тавтологий", False, "п. 1 требует доказуемости лишь базисных "
     "формул, являющихся тавтологиями и непарадоксальных; п. 2 — формул, получаемых из базисных подстановкой (с. 97)."),
    ("Пункт 2 D2 § 11 выполняется в силу того, что используются аксиомные схемы", True, "с. 97."),
    ("Отрицания в антецедентах и консеквентах условных высказываний всегда могут быть доведены до элементарных "
     "высказываний", True, "с. 97."),
    ("Книга приводит полное доказательство того, что системы полны в смысле D2", False, "книга его не приводит: оно "
     "осуществляется пересмотром всех случаев (с. 97)."),
]


def claims_card(bank, sec, level=5, nat=False):
    intro = {2: "Студент оценил утверждения об условных высказываниях и следовании (гл. 6, § 2):",
             3: "Студент оценил утверждения об операторе условности и материальной импликации (гл. 6, § 3):",
             4: "Студент оценил утверждения об интерпретации условных высказываний (гл. 6, § 4):",
             5: "Студент оценил утверждения о классическом и неклассическом случаях (гл. 6, § 5):",
             6: "Студент оценил утверждения о системе $S^s_{if}$ (гл. 6, § 6):",
             8: "Студент оценил утверждения о системе $S^5_{if}$ (гл. 6, § 8):",
             9: "Студент оценил утверждения о системе $S^{5*}_{if}$ (гл. 6, § 9):",
             10: "Студент оценил утверждения о парадоксах $S^i_{if}$ (гл. 6, § 10):",
             11: "Студент оценил утверждения о полноте теории условных высказываний (гл. 6, § 11):"}[sec]
    src = {2: "с. 83, 85, гл. 6, § 2", 3: "с. 83–88, гл. 6, § 3", 4: "с. 86–88, гл. 6, § 4", 5: "с. 89–90, гл. 6, § 5",
           6: "с. 90–91, гл. 6, § 6", 8: "с. 91–93, гл. 6, § 8", 9: "с. 93–94, гл. 6, § 9", 10: "с. 94–95, гл. 6, § 10",
           11: "с. 95–97, гл. 6, § 11"}[sec]
    return SY.c_claims(bank, CV + " " + intro if sec in (3, 4, 6, 8, 9) else intro, src, "условность, диагностика",
                       level=level, nat=nat)
