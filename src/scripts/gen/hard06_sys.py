"""Гл. 6, § 5–11: серии доказуемости, почти-примеры схем, S⁵_if, S⁵*_if, Sⁱ_if, три состояния, базисные формулы."""
from hard06_lib import (F, C, IF, IFN, IFQ, IMP, N, V, W, ftex, tex, rnd, x, y, z, v, u, L, CV, card, SYSNAME,
                        sys_text, SCH_S, SCH_W, RULES)
from hard06_sem import comp, nn, explain_non, INTERP, lit_tex
import hard06_lib as H

MT_S = ("Метатеоремы § 6 (с. 90): MT1 — все доказуемые в $S^s_{if}$ формулы суть тавтологии (интерпретация § 4); MT2 — если "
        "$x \\vdash y$ доказуема, то в $y$ не входят элементарные высказывания, отсутствующие в $x$; MT3 — если $x \\vdash y$ "
        "доказуема и в $y$ входит оператор условности, то он входит и в $x$.")
MT_W = ("Метатеоремы § 7 (с. 91): MT1 — если $x \\vdash y$ доказуема в $S^w_{if}$, то в $x$ и $y$ входит по крайней мере одно "
        "одинаковое элементарное высказывание; MT2 — доказуемые в $S^w_{if}$ формулы суть тавтологии.")
T_S = ("Теоремные схемы $S^s_{if}$ (с. 91): T1 $(x \\rightarrow y)(yz \\rightarrow v) \\vdash (xz \\rightarrow v)$; T4 "
       "$(x \\rightarrow y)\\sim y \\vdash \\sim x$; T6 $(xy \\rightarrow z)x \\vdash (y \\rightarrow z)$; T7 $(x \\vee y "
       "\\rightarrow z) \\vdash (x \\rightarrow z)(y \\rightarrow z)$; T8 $(x \\rightarrow z)(y \\rightarrow z) \\vdash (x \\vee y "
       "\\rightarrow z)$; T11 $(x \\rightarrow y)(v \\rightarrow z) \\vdash (x \\vee v \\rightarrow y \\vee z)$.")
TSCH = {"T1": (C(IF(x, y), IF(C(y, z), v)), IF(C(x, z), v)), "T4": (C(IF(x, y), N(y)), N(x)),
        "T6": (C(IF(C(x, y), z), x), IF(y, z)), "T7": (IF(W(x, y), z), C(IF(x, z), IF(y, z))),
        "T8": (C(IF(x, z), IF(y, z)), IF(W(x, y), z)), "T11": (C(IF(x, y), IF(v, z)), IF(W(x, v), W(y, z)))}


def m_tex(m):
    return ", ".join(f"${k}$ := ${tex(vv)}$" for k, vv in sorted(m.items()))


def sch_inst(name, args):
    if name in TSCH:
        pa, pb = TSCH[name]
    else:
        pa, pb = F.SCH[name]
    m = dict(zip("xyzv", args))
    return (None if pa is None else F.subst(pa, m)), F.subst(pb, m), {k: vv for k, vv in m.items()
                                                                      if k in F.atoms(pb) | (F.atoms(pa) if pa else set())}


def find_inst(a, b, names):
    for n in names:
        if n in TSCH:
            pa, pb = TSCH[n]
            m = {}
            if F.match(pa, a, m) and F.match(pb, b, m):
                return n, m
        else:
            m = F.instance(n, a, b)
            if m is not None:
                return n, m
    return None


# ---------------------------------------------------------------- серии доказуемости S^s_if, S^w_if
def prov_item(kind, sysk):
    for _ in range(500):
        args = comp(4)
        if not args:
            continue
        X, Y, Z, Vv = args
        if kind == "ax":
            name = rnd.choice(["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "T1", "T4", "T6", "T7", "T8", "T11"]
                              + (["A9", "A9"] if sysk == "w" else []))
            a, b, m = sch_inst(name, args)
            if nn(a) or nn(b):
                continue
            return a, b, True, f"пример схемы {name} (замена {m_tex(m)})", f"доказуема ({name})"
        if kind == "new":
            a, b = rnd.choice([(IF(X, Y), IF(C(X, Z), Y)), (IF(X, Y), IF(X, W(Y, Z))), (C(IF(X, Y), X), C(Y, Z)),
                               (IF(C(X, Y), Vv), IF(X, IF(Y, W(Vv, Z))))])
            new = sorted(F.atoms(b) - F.atoms(a))
            if not new:
                continue
            nt = ", ".join(f"${t}$" for t in new)
            return a, b, False, f"в заключение входит {nt}, отсутствующее в посылке; по MT2 § 6 недоказуема", \
                f"недоказуема (MT2: {nt})"
        if kind == "cond":
            a, b = rnd.choice([(C(X, Y), IF(X, Y)), (W(N(X), Y), IF(X, Y)), (C(X, IF(X, Y)), IF(N(Y), N(X))) if False
                               else (C(N(X), N(Y)), IF(X, Y)), (Y, IF(X, Y))])
            if nn(a) or nn(b) or F.atoms(b) - F.atoms(a):
                continue
            return a, b, False, ("в заключение входит оператор условности, а в посылку — нет; по MT3 § 6 недоказуема"), \
                "недоказуема (MT3)"
        if kind == "nontaut":
            import hard06_sem as S
            key = rnd.choice(["conv", "inv", "affirm", "deny", "chain", "split", "orcons", "split2"])
            a, b = S.BAD[key](X, Y, Z, Vv)
            if nn(a) or nn(b) or F.atoms(b) - F.atoms(a) or not F.flat(C(a, b)):
                continue
            r = F.sem_robust(a, b)
            if r is None or r[0]:
                continue
            ex = explain_non(a, b, r[1])
            return a, b, False, ("не тавтология при интерпретации § 4 — " + ex[0].lower() + ex[1:] +
                                 " По " + ("MT2 § 7" if sysk == "w" else "MT1 § 6") + " недоказуема"), \
                "недоказуема (не тавтология)"
        if kind == "disjoint":
            a, b = IF(X, Y), IF(Z, Vv)
            return a, b, False, "в посылке и заключении нет одинаковых элементарных высказываний; по MT1 § 7 недоказуема", \
                "недоказуема (MT1 § 7)"
    raise RuntimeError(kind)


def c_prov_series(sysk="s", level=6, src="с. 90–91, гл. 6, § 6", kinds=None):
    kinds = kinds or (["ax", "ax", "new", "nontaut"] if sysk == "s" else ["ax", "ax", "disjoint", "nontaut"])
    kinds = list(kinds)
    rnd.shuffle(kinds)
    items = []
    while len(items) < len(kinds):
        it = prov_item(kinds[len(items)], sysk)
        if ftex(it[0], it[1]) not in [ftex(i[0], i[1]) for i in items] and 12 <= F.size(it[0]) + F.size(it[1]) <= 48:
            items.append(it)
    sname = SYSNAME[sysk]
    mts = MT_S if sysk == "s" else MT_W + " " + MT_S.replace("Метатеоремы § 6", "Для $S^s_{if}$ — метатеоремы § 6")
    cond = (f"{CV} Исследуйте доказуемость каждой формулы в ${sname}$: доказуемую обоснуйте схемой (укажите замену букв), "
            f"недоказуемую — метатеоремой или значениями. {SCH_S if sysk == 's' else SCH_W} {T_S} {mts}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b, *_) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {it[4]}" for i, it in enumerate(items))
    sol = "\n".join(f"{L[i]}) {it[3][0].upper() + it[3][1:]}." for i, it in enumerate(items))
    return card(level, "C", "open", "short", src, "условность, доказуемость", cond, ans, sol,
                system=sname.replace("{", "").replace("}", ""))


def c_cmp_sw(level=7, src="с. 90–91, гл. 6, § 6–7"):
    """Доказуемость в S^s_if и S^w_if — разделяющие формулы."""
    items = []
    plan = ["a9", "ax", "disjoint", rnd.choice(["new", "a9"])]
    rnd.shuffle(plan)
    for k in plan:
        for _ in range(300):
            args = comp(4)
            if not args:
                continue
            X, Y, Z, Vv = args
            if k == "a9":
                a, b = rnd.choice([(IF(X, Y), IF(C(X, Z), Y)), (C(IF(X, Y), IF(Y, Vv)), IF(C(X, Z), Vv))])
                if F.atoms(b) <= F.atoms(a):
                    continue
                if a[0] == "conj":
                    ws = "выводится по A3 и A9 (A3, затем A9 и R1)"
                else:
                    ws = "пример A9"
                items.append((a, b, "нет", "да", "$S^s_{if}$: в заключение входит новое элементарное высказывание — по "
                              f"MT2 § 6 недоказуема; $S^w_{{if}}$: {ws}"))
            elif k == "ax":
                name = rnd.choice(["A3", "A4", "A7", "A8", "T1", "T7"])
                a, b, m = sch_inst(name, args)
                items.append((a, b, "да", "да", f"пример {name} (замена {m_tex(m)}); схемы $S^s_{{if}}$ входят в "
                              "$S^w_{if}$ (с. 91)"))
            elif k == "disjoint":
                a, b = IF(X, Y), IF(Z, Vv)
                items.append((a, b, "нет", "нет", "общих элементарных высказываний нет: по MT1 § 7 недоказуема в "
                              "$S^w_{if}$, а значит, и в $S^s_{if}$ (её теоремы — теоремы $S^w_{if}$)"))
            else:
                a, b = IF(X, Y), IF(X, W(Y, Z))
                items.append((a, b, "нет", "да", "$S^s_{if}$: новое элементарное высказывание — MT2 § 6; $S^w_{if}$: "
                              "T1 § 7 [A2, A9, A2] (с. 91)"))
            if nn(a) or nn(b):
                items.pop()
                continue
            break
    cond = (f"{CV} Для каждой формулы исследуйте доказуемость в $S^s_{{if}}$ и в $S^w_{{if}}$ ($S^w_{{if}}$ — $S^s_{{if}}$ с "
            f"аксиомной схемой A9 $(x \\rightarrow y) \\vdash (xz \\rightarrow y)$, с. 91) и найдите формулы, разделяющие "
            f"системы. {MT_S} {MT_W} В $S^w_{{if}}$ доказуема T1 $(x \\rightarrow y) \\vdash (x \\rightarrow y \\vee z)$.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b, *_) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) $S^s_{{if}}$ — {s}, $S^w_{{if}}$ — {w}" for i, (_, _, s, w, _) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {t}." for i, (*_, t) in enumerate(items))
    sep = [L[i] for i, (_, _, s, w, _) in enumerate(items) if s != w]
    sol += f"\n\nРазделяют системы: {', '.join(sep) + ')'}" if sep else ""
    return card(level, "S", "transfer", "short", src, "условность, сравнение систем", cond, ans, sol, system="S^w_if")


# ---------------------------------------------------------------- почти-примеры и опознание схем
NEAR = {
    "A1": (lambda X, Y, Z, Vv: (C(IF(X, Y), Y), X), "в A1 вторым членом посылки стоит антецедент, а выводится консеквент"),
    "A2": (lambda X, Y, Z, Vv: (IF(X, Y), IF(N(X), N(Y))), "A2 меняет антецедент и консеквент местами и ставит перед "
                                                            "обоими $\\sim$"),
    "A3": (lambda X, Y, Z, Vv: (C(IF(X, Y), IF(Z, Vv)), IF(X, Vv)), "в A3 консеквент первого условного высказывания должен "
                                                                     "совпадать с антецедентом второго"),
    "A4": (lambda X, Y, Z, Vv: (IF(X, W(Y, Z)), C(IF(X, Y), IF(X, Z))), "в A4 консеквент посылки — конъюнкция, а не "
                                                                         "дизъюнкция"),
    "A5": (lambda X, Y, Z, Vv: (IF(C(X, Y), Z), IF(Y, IF(X, Z))), "A5 сохраняет порядок членов: первый член конъюнкции "
                                                                   "становится внешним антецедентом"),
    "A6": (lambda X, Y, Z, Vv: (IF(X, IF(Y, Z)), IF(C(Y, X), Z)), "A6 сохраняет порядок: внешний антецедент — первый член "
                                                                   "конъюнкции"),
    "A7": (lambda X, Y, Z, Vv: (C(IF(X, Y), IF(Z, Vv)), IF(C(X, Z), C(Vv, Y))), "в A7 члены консеквента идут в том же "
                                                                               "порядке, что и члены антецедента"),
    "A8": (lambda X, Y, Z, Vv: (W(IF(X, Y), IF(Z, Vv)), IF(W(X, Z), W(Y, Vv))), "в заключении A8 антецедент — "
                                                                                "конъюнкция антецедентов посылки"),
    "A9": (lambda X, Y, Z, Vv: (IF(X, Y), IF(X, C(Y, Z))), "A9 усиливает антецедент, а не консеквент"),
    "B2": (lambda X, Y, Z, Vv: (C(IF(X, Y), N(X)), N(Y)), "в A2 § 9 вторым членом посылки стоит отрицание консеквента"),
    "B1": (lambda X, Y, Z, Vv: (C(IF(X, Y), Y), X), "в A1 § 9 вторым членом посылки стоит антецедент, а выводится консеквент"),
    "B3": (lambda X, Y, Z, Vv: (None, IF(IF(C(X, Y), Z), IF(Y, IF(X, Z)))), "A3 § 9 сохраняет порядок членов: первый член "
           "конъюнкции становится внешним антецедентом"),
}


def c_near(name, yes, level=None, src="с. 90–91, гл. 6, § 6", sysk="s"):
    for _ in range(300):
        args = comp(4)
        if not args:
            continue
        X, Y, Z, Vv = args
        if yes:
            pa, pb = F.SCH[name]
            m = dict(zip("xyzv", args))
            a, b = (None if pa is None else F.subst(pa, m)), F.subst(pb, m)
        else:
            a, b = NEAR[name][0](X, Y, Z, Vv)
        if nn(a) or nn(b):
            continue
        if (F.instance(name, a, b) is not None) == yes:
            break
    lab = F.LABEL[name] + (" § 9" if name.startswith("B") else "")
    pa, pb = F.SCH[name]
    sch = ftex(pa, pb)
    cond = (f"{CV} Схема {lab}: ${sch}$. Установите, получается ли из неё формула ${ftex(a, b)}$ заменой букв "
            f"высказываниями (одинаковые буквы — одинаковыми высказываниями). Если получается — укажите замену; если нет — "
            f"назовите место, которое мешает (а если посылка подходит под схему — запишите пример схемы с этой посылкой).")
    if yes:
        m = F.instance(name, a, b)
        ans = f"Получается: {m_tex(m)}."
        sol = (f"1. Посылка задаёт замену {m_tex(m)}.\n2. При этой замене заключение схемы совпадает с заключением формулы.\n"
               f"3. Формула — пример {lab} ({H.PAGE.get(sysk, 'с. 90')}).")
        return card(level or 5, "A", "vary", "short", src, "условность, схемы, подстановка", cond, ans, sol)
    m = {}
    good = None
    if pa is not None and F.match(pa, a, m):
        good = F.subst(pb, m)
    elif pa is None and F.match(pb[1], b[1], m):
        good = F.subst(pb, m)
    why = NEAR[name][1]
    ans = f"Не получается: {why}." + (f" С той же посылкой: ${ftex(a, good)}$." if good is not None else "")
    sol = (f"1. " + (f"Посылка однозначно задаёт замену {m_tex(m)}; при ней схема даёт ${ftex(a, good)}$, а в формуле "
                     f"заключение ${tex(b)}$." if good is not None else
                     "Посылка формулы не имеет вида посылки схемы.") +
           f"\n2. {why[0].upper() + why[1:]} ({H.PAGE.get(sysk, 'с. 90')}).\n3. Другой замены нет: формула — не пример {lab}.")
    return card(level or 5, "E", "vary", "short", src, "условность, схемы, почти-пример", cond, ans, sol)


def c_recog(level=4, sysk="s", src="с. 90–91, гл. 6, § 6"):
    names = F.SYSTEMS[sysk]
    pool = []
    for _ in range(200):
        if len(pool) >= 5:
            break
        args = comp(4)
        if not args:
            continue
        r = rnd.random()
        nm = rnd.choice(names)
        if r < 0.6:
            pa, pb = F.SCH[nm]
            m = dict(zip("xyzv", args))
            a, b = (None if pa is None else F.subst(pa, m)), F.subst(pb, m)
        else:
            key = rnd.choice([k for k in NEAR if k in names] or list(NEAR))
            a, b = NEAR[key][0](*args)
        if nn(a) or nn(b) or ftex(a, b) in [ftex(p, q) for p, q in pool]:
            continue
        pool.append((a, b))
    if sum(1 for a, b in pool if not [n for n in names if F.instance(n, a, b) is not None]) == 0:
        pool[-1] = NEAR["A5"][0](*comp(4))
    rnd.shuffle(pool)

    def found(a, b):
        return [F.LABEL[n] for n in names if F.instance(n, a, b) is not None]
    cond = (f"{CV} Для каждой формулы найдите все аксиомные схемы ${SYSNAME[sysk]}$, примерами которых она является "
            f"(замена букв высказываниями); если таких нет — объясните, что мешает. "
            f"{SCH_S if sysk == 's' else SCH_W if sysk == 'w' else H.SCH_5S}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(pool)))
    ans = "; ".join(f"{L[i]}) " + (", ".join(found(a, b)) or "ни одной") for i, (a, b) in enumerate(pool))
    sol = "\n".join(f"{L[i]}) " + (", ".join(f"{n} (замена {m_tex(F.instance(k, a, b))})" for k, n in
                                             [(k, F.LABEL[k]) for k in names if F.instance(k, a, b) is not None])
                                   or "ни одной: посылка задаёт замену, а заключение с ней не согласуется (или посылка не "
                                      "имеет вида посылки ни одной схемы)") + "."
                    for i, (a, b) in enumerate(pool))
    return card(level, "R", "iso", "short", src, "условность, схемы", cond, ans, sol)


# ---------------------------------------------------------------- S⁵_if: ⊢ (x → y) при x, y без →
S5_CRIT = ("По MT2 § 8 (с. 92): если $\\vdash (x \\rightarrow y)$ доказуема, то $x \\supset y$ — тавтология; по MT5 § 8 (с. 92): "
           "если $\\vdash (x \\supset y)$ доказуема в $S^5$, то $\\vdash (x \\rightarrow y)$ доказуема в $S^5_{if}$; по MT4 § 3 "
           "гл. 4 (с. 69) $\\vdash (x \\supset y)$ доказуема в $S^5$, если $x \\supset y$ — тавтология.")


def rnd_w(names, depth):
    if depth == 0 or rnd.random() < 0.2:
        t = V(rnd.choice(names))
        return N(t) if rnd.random() < 0.3 else t
    k = rnd.random()
    if k < 0.15:
        s_ = rnd_w(names, depth - 1)
        return s_ if s_[0] == "neg" else N(s_)
    op = C if k < 0.6 else W
    a, b = rnd_w(names, depth - 1), rnd_w(names, depth - 1)
    return op(a, b) if a != b else a


def s5_items(n_yes=2, n_no=2):
    items = []
    while len(items) < n_yes + n_no:
        want = len(items) < n_yes
        lt = rnd.sample("xyzv", 3)
        a, b = rnd_w(lt[:2] + ([lt[2]] if rnd.random() < 0.4 else []), 2), rnd_w(lt, 2)
        if a == b or nn(a) or nn(b) or not 8 <= F.size(a) + F.size(b) <= 30:
            continue
        if F.s5if_prov(a, b) == want and (a, b) not in items:
            items.append((a, b))
    rnd.shuffle(items)
    return items


def s5_just(a, b):
    if F.s5if_prov(a, b):
        extra = ""
        if F.atoms(b) - F.atoms(a):
            extra = " (хотя $" + ftex(a, b) + "$ в $S^s$ недоказуема — в заключении новые буквы)"
        return "доказуема", f"$({tex(a)} \\supset {tex(b)})$ — тавтология (нет значений, где антецедент 1, а консеквент 0); по MT4 гл. 4 и MT5 § 8 доказуема{extra}"
    e = F.entails([a], b, F.atoms(a) | F.atoms(b))
    return f"недоказуема ({lit_tex(e)})", f"при {lit_tex(e)} антецедент 1, консеквент 0: $x \\supset y$ не тавтология; по MT2 § 8 недоказуема"


def c_s5_series(level=6, src="с. 91–93, гл. 6, § 8", sysn="S^5_{if}", extra=""):
    items = s5_items()
    cond = (f"{CV} Исследуйте доказуемость в ${sysn}$ каждой формулы (в $x$ и $y$ здесь нет оператора условности) и "
            f"обоснуйте значениями. {S5_CRIT}{extra}\n\n" +
            "\n".join(f"{L[i]}) $\\vdash ({tex(a)} \\rightarrow {tex(b)})$" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {s5_just(a, b)[0]}" for i, (a, b) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {s5_just(a, b)[1]}." for i, (a, b) in enumerate(items))
    return card(level, "C", "open", "short", src, "условность, S5if, доказуемость", cond, ans, sol,
                system=sysn.replace("{", "").replace("}", ""))


def c_s5_diag(level=6, src="с. 91–93, гл. 6, § 8"):
    items = s5_items()
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, (a, b) in enumerate(items):
        ok = F.s5if_prov(a, b)
        claim = ok if i not in wrong else not ok
        if claim and not ok:
            reason = "в консеквент не входят элементарные высказывания, отсутствующие в антецеденте"
        elif claim:
            reason = "$x \\supset y$ — тавтология"
        elif ok:
            reason = rnd.choice(["в консеквент входит буква, которой нет в антецеденте, — по MT2 § 6 недоказуема",
                                 "$x \\vdash y$ недоказуема в $S^s$, значит, R1 § 8 неприменимо"])
        else:
            reason = "при некоторых значениях антецедент 1, а консеквент 0"
        lines.append(f"{i + 1}. $\\vdash ({tex(a)} \\rightarrow {tex(b)})$ — {'доказуема' if claim else 'недоказуема'}: {reason}.")
        if i in wrong:
            ans.append(f"{i + 1}: {s5_just(a, b)[0]}")
            if ok:
                sol.append(f"{i + 1}. Неверно: MT2 § 6 относится к формулам $x \\vdash y$ системы $S^s_{{if}}$, а R1 § 8 — не "
                           f"единственный путь; {s5_just(a, b)[1]}.")
            else:
                sol.append(f"{i + 1}. Неверно: условия на элементарные высказывания мало; {s5_just(a, b)[1]}.")
    cond = (f"{CV} Студент исследовал доказуемость в $S^5_{{if}}$ четырёх формул (в $x$, $y$ нет оператора условности):\n\n"
            + "\n".join(lines) + f"\n\nРовно два вывода неверны. Найдите их, объясните ошибку и дайте верный ответ. {S5_CRIT}")
    return card(level, "E", "vary", "text", src, "условность, S5if, диагностика", cond, "; ".join(ans) + ".",
                "\n".join(sol) + "\n\nОстальные выводы верны.", system="S^5_if")


def c_mt6(level=7, src="с. 92–93, гл. 6, § 8"):
    """MT6 § 8 и её граница: формулы с → в x, y."""
    items = []
    for a, b in s5_items(1, 1):
        items.append(("free", a, b))
    for _ in range(100):
        X, Y, Z = comp(3) or (x, y, z)
        if not nn(C(X, Y, Z)):
            break
    t15 = (C(IF(X, Y), IF(Y, Z)), IF(X, Z))
    items.append(("t15", *t15))
    items.append(("t13", X, W(X, Y)))
    rnd.shuffle(items)
    cond = (f"{CV} MT6 § 8 (с. 93): если $x$ и $y$ суть высказывания $S^5$ (без оператора условности) и $\\vdash (x \\rightarrow "
            f"y)$ доказуема в $S^5_{{if}}$, то $\\vdash (x \\supset y)$ доказуема в $S^5$. Для каждой пары $x$, $y$ исследуйте "
            f"доказуемость $\\vdash (x \\rightarrow y)$ в $S^5_{{if}}$ и $\\vdash (x \\supset y)$ в $S^5$; объясните, где MT6 "
            f"применима, а где нет. {S5_CRIT} В $S^5_{{if}}$ доказуемы T13 $\\vdash (x \\rightarrow x \\vee y)$ и T15 "
            f"$\\vdash ((x \\rightarrow y)(y \\rightarrow z) \\rightarrow (x \\rightarrow z))$ (с. 92); в $S^5$ доказуемы "
            f"тавтологии и только они, если условные высказывания считать элементарными (MT1, MT4 § 3 гл. 4).\n\n" +
            "\n".join(f"{L[i]}) $x = {tex(a)}$, $y = {tex(b)}$" for i, (_, a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (k, a, b) in enumerate(items):
        if k == "free":
            ok = F.s5if_prov(a, b)
            ans.append(f"{L[i]}) обе {'доказуемы' if ok else 'недоказуемы'}")
            sol.append(f"{L[i]}) $x$, $y$ без $\\rightarrow$: " + s5_just(a, b)[1] + (
                "; по MT6 тогда и $\\vdash (x \\supset y)$ доказуема в $S^5$." if ok else
                "; $x \\supset y$ не тавтология, так что и в $S^5$ $\\vdash (x \\supset y)$ недоказуема (MT1 § 3 гл. 4)."))
        elif k == "t13":
            ans.append(f"{L[i]}) обе доказуемы")
            sol.append(f"{L[i]}) Пример T13 § 8; $x \\supset x \\vee y$ — тавтология, по MT4 гл. 4 доказуема в $S^5$ (как и "
                       f"требует MT6).")
        else:
            ans.append(f"{L[i]}) в $S^5_{{if}}$ доказуема, в $S^5$ недоказуема")
            tab = {}
            sol.append(f"{L[i]}) Пример T15 § 8 — доказуема в $S^5_{{if}}$. Но $x$ и $y$ содержат $\\rightarrow$: MT6 неприменима. "
                       f"В $S^5$ условные высказывания — элементарные; при значениях ${tex(a[1][0])} = 1$, ${tex(a[1][1])} = 1$, "
                       f"${tex(b)} = 0$ формула $x \\supset y$ ложна — не тавтология, по MT1 § 3 гл. 4 недоказуема "
                       f"(ср. пример с. 93).")
    return card(level, "S", "transfer", "short", src, "условность, S5if, S5", cond, "; ".join(ans) + ".", "\n".join(sol),
                system="S^5_if")


def c_mt7(level=6, src="с. 93, гл. 6, § 8"):
    lines = H.s5_deriv("5")
    f_ = lines[-1][1]
    g = F.to_imp(f_)
    assert F.s5_taut(g)
    cond = (f"{CV} В $S^5_{{if}}$ доказуема формула ${ftex(None, f_)}$ (вывод — в решении). По MT7 § 8 (с. 93) запишите "
            f"формулу, доказуемую в $S^5$, и проверьте значениями, что она тавтология. Затем объясните, почему из "
            f"доказуемости в $S^5$ формулы, полученной заменой $\\rightarrow$ на $\\supset$, нельзя заключить о доказуемости "
            f"исходной в $S^5_{{if}}$ (с. 93).")
    names = sorted(F.atoms(g))
    ans = f"${ftex(None, g)}$ — тавтология; обратное MT7 неверно."
    sol = (f"Вывод в $S^5_{{if}}$:\n\n{F.show(lines, '5')}\n\nMT7 § 8: если $\\vdash x$ доказуема в $S^5_{{if}}$, то в $S^5$ "
           f"доказуема $\\vdash y$, где $y$ получается из $x$ заменой всех вхождений $\\rightarrow$ на $\\supset$: "
           f"${ftex(None, g)}$. Перебор {2 ** len(names)} наборов значений ${', '.join(names)}$: значение 0 не получается — "
           f"тавтология (MT1, MT4 § 3 гл. 4). Обратное неверно: $\\vdash ((xy \\supset z \\vee v) \\supset ((x \\supset z) "
           f"\\vee (y \\supset v)))$ доказуема в $S^5$, а $\\vdash ((xy \\rightarrow z \\vee v) \\rightarrow ((x \\rightarrow z) "
           f"\\vee (y \\rightarrow z)))$ недоказуема (с. 93).")
    return card(level, "S", "transfer", "short", src, "условность, S5if, MT7", cond, ans, sol, system="S^5_if")


# ---------------------------------------------------------------- § 10: A*5
A5S = ("$S^i_{if}$: в $S^s_{if}$ схема A5 заменена на $A^*5$ $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$, где "
       "$\\vdash (x \\rightarrow z)$ и $\\vdash (y \\rightarrow z)$ недоказуемы в $S^5_{if}$ (с. 95). " + S5_CRIT)


def a5s_items(n_yes=2, n_no=2):
    items = []
    while len(items) < n_yes + n_no:
        want = len(items) < n_yes
        lt = rnd.sample("xyzvu", 4)
        X, Y, Z = rnd_w(lt[:2], 1), rnd_w(lt[1:3], 1), rnd_w([lt[0], lt[2], lt[3]], 2)
        if nn(C(X, Y, Z)) or len({X, Y, Z}) < 3 or not 6 <= F.size(C(X, Y, Z)) <= 18:
            continue
        ok = not F.s5if_prov(X, Z) and not F.s5if_prov(Y, Z)
        if ok == want and (X, Y, Z) not in items:
            items.append((X, Y, Z))
    rnd.shuffle(items)
    return items


def a5s_just(X, Y, Z):
    out = []
    for t, nm in ((X, "x"), (Y, "y")):
        if F.s5if_prov(t, Z):
            out.append(f"$\\vdash ({tex(t)} \\rightarrow {tex(Z)})$ доказуема в $S^5_{{if}}$: ${tex(t)} \\supset {tex(Z)}$ — "
                       "тавтология (MT5 § 8)")
        else:
            e = F.entails([t], Z, F.atoms(t) | F.atoms(Z))
            out.append(f"$\\vdash ({tex(t)} \\rightarrow {tex(Z)})$ недоказуема: при {lit_tex(e)} антецедент 1, консеквент 0 "
                       "(MT2 § 8)")
    ok = not F.s5if_prov(X, Z) and not F.s5if_prov(Y, Z)
    return ok, "; ".join(out) + (". Условие выполнено — пример $A^*5$." if ok else ". Условие нарушено — не пример $A^*5$.")


def c_a5s(level=6, src="с. 94–95, гл. 6, § 10"):
    items = a5s_items()
    cond = (f"{CV} Для каждой формулы $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$ с данными $x$, $y$, $z$ "
            f"(без оператора условности) исследуйте, является ли она примером $A^*5$, и обоснуйте значениями. {A5S}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(IF(C(X, Y), Z), IF(X, IF(Y, Z)))}$" for i, (X, Y, Z) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) " + ("пример $A^*5$" if a5s_just(*it)[0] else "не пример") for i, it in enumerate(items))
    sol = "\n".join(f"{L[i]}) {a5s_just(*it)[1]}" for i, it in enumerate(items))
    return card(level, "C", "open", "short", src, "условность, парадоксы, A*5", cond, ans, sol, system="S^i_if")


def c_a5s_diag(level=6, src="с. 94–95, гл. 6, § 10"):
    items = a5s_items()
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, it in enumerate(items):
        ok, just = a5s_just(*it)
        claim = ok if i not in wrong else not ok
        X, Y, Z = it
        reason = ("антецедент и консеквент не имеют общих букв" if claim and not ok else
                  "$x \\supset z$ и $y \\supset z$ не тавтологии" if claim else
                  rnd.choice(["в $z$ входит буква из $x$", "$xy \\supset z$ — не тавтология"]) if ok else
                  "одна из формул $\\vdash (x \\rightarrow z)$, $\\vdash (y \\rightarrow z)$ доказуема")
        lines.append(f"{i + 1}. ${ftex(IF(C(X, Y), Z), IF(X, IF(Y, Z)))}$ — {'пример' if claim else 'не пример'} $A^*5$: {reason}.")
        if i in wrong:
            ans.append(f"{i + 1}: " + ("пример" if ok else "не пример"))
            sol.append(f"{i + 1}. Неверно: условие $A^*5$ — недоказуемость $\\vdash (x \\rightarrow z)$ и $\\vdash (y \\rightarrow z)$ "
                       f"в $S^5_{{if}}$ (с. 95). {just}")
    cond = (f"{CV} Студент проверял, какие формулы — примеры $A^*5$:\n\n" + "\n".join(lines) +
            f"\n\nРовно два вывода неверны. Найдите их и исправьте, обосновав значениями. {A5S}")
    return card(level, "E", "vary", "text", src, "условность, парадоксы, A*5, диагностика", cond, "; ".join(ans) + ".",
                "\n".join(sol) + "\n\nОстальные выводы верны.", system="S^i_if")


# ---------------------------------------------------------------- § 5: три состояния, Aⁿ
THREE = ("По пп. 10–12 § 4 (с. 87) из $x \\rightarrow y$, $x \\urcorner\\!\\rightarrow y$, $x? \\rightarrow y$ истинно ровно одно; "
         "в неклассическом случае возможны все три, в классическом (схема $A^n7$ $\\sim(x \\rightarrow y) \\vdash "
         "(x \\urcorner\\!\\rightarrow y)$, с. 89) $x? \\rightarrow y$ невозможно (MT1 § 5). Разные пары антецедент — "
         "консеквент независимы.")
KIND = {"if": IF, "ifn": IFN, "ifq": IFQ}


def three_formula(pairs, depth=2):
    k = rnd.random()
    if depth == 0 or k < 0.3:
        p_ = rnd.choice(pairs)
        f_ = KIND[rnd.choice(list(KIND))](*p_)
        return N(f_) if rnd.random() < 0.4 else f_
    a, b = three_formula(pairs, depth - 1), three_formula(pairs, depth - 1)
    if a == b:
        return a
    f_ = C(a, b) if k < 0.65 else W(a, b)
    return N(f_) if rnd.random() < 0.15 else f_


def three_items(n=4):
    pairs = [(x, y), (x, z)] if rnd.random() < 0.6 else [(x, y)]
    want = [(True, True), (False, True), (False, False), rnd.choice([(True, True), (False, False)])]
    items = []
    tries = 0
    while len(items) < n and tries < 20000:
        tries += 1
        a, b = three_formula(pairs, 2), three_formula(pairs, 1)
        if a == b or not 12 <= F.size(a) + F.size(b) <= 52:
            continue
        r = (F.three_taut(a, b)[0], F.three_taut(a, b, True)[0])
        if r == want[len(items)] and (a, b) not in items:
            items.append((a, b))
    rnd.shuffle(items)
    return items


def st_tex(st):
    nm = {"if": "\\rightarrow", "ifn": "\\urcorner\\!\\rightarrow", "ifq": "? \\rightarrow"}
    out = []
    for (p, q), k in st.items():
        out.append(f"${tex(IF(p, q)) if k == 'if' else tex(IFN(p, q)) if k == 'ifn' else tex(IFQ(p, q))}$")
    return "истинно " + ", ".join(out)


def c_three_series(level=6, src="с. 87–90, гл. 6, § 4–5"):
    items = three_items()
    cond = (f"{CV} Исследуйте каждую формулу: тавтология ли она в неклассическом случае и в классическом? Обоснуйте "
            f"перебором состояний: для нетавтологии укажите, какие условные высказывания истинны. {THREE}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        r1, s1 = F.three_taut(a, b)
        r2, s2 = F.three_taut(a, b, True)
        ans.append(f"{L[i]}) неклассический — {'тавтология' if r1 else 'нет'}, классический — {'тавтология' if r2 else 'нет'}")
        t = []
        t.append("в неклассическом случае: " + ("при всех состояниях посылка 1 влечёт заключение 1" if r1 else
                                               f"{st_tex(s1)}: посылка 1, заключение 0"))
        t.append("в классическом: " + ("при всех состояниях без $? \\rightarrow$ посылка 1 влечёт заключение 1" if r2 else
                                      f"{st_tex(s2)}: посылка 1, заключение 0"))
        sol.append(f"{L[i]}) " + "; ".join(t) + ".")
    return card(level, "V", "transfer", "short", src, "условность, неклассический случай", cond, "; ".join(ans) + ".",
                "\n".join(sol))


def c_three_diag(level=6, src="с. 87–90, гл. 6, § 4–5"):
    items = three_items()
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, (a, b) in enumerate(items):
        r1, s1 = F.three_taut(a, b)
        claim = r1 if i not in wrong else not r1
        reason = ("в классическом случае это тавтология, значит, и в неклассическом" if claim and not r1 else
                  "посылка 1 при всех состояниях влечёт заключение 1" if claim else
                  "можно взять состояние, где истинно $x? \\rightarrow y$, — тогда заключение 0" if r1 else
                  "есть состояние с посылкой 1 и заключением 0")
        lines.append(f"{i + 1}. ${ftex(a, b)}$ — {'тавтология' if claim else 'не тавтология'} в неклассическом случае: {reason}.")
        if i in wrong:
            ans.append(f"{i + 1}: {'тавтология' if r1 else 'не тавтология'}")
            sol.append(f"{i + 1}. Неверно: " + (
                f"в неклассическом случае возможно и истинное $x? \\rightarrow y$ (п. 12); {st_tex(s1)} — посылка 1, "
                f"заключение 0." if not r1 else
                "перебор всех трёх состояний каждой пары (пп. 10–12) не даёт посылки 1 при заключении 0."))
    cond = (f"{CV} Студент исследовал четыре формулы в неклассическом случае:\n\n" + "\n".join(lines) +
            f"\n\nРовно два вывода неверны. Найдите их, назовите нарушенный пункт и дайте верный ответ. {THREE}")
    return card(level, "E", "vary", "text", src, "условность, неклассический случай, диагностика", cond,
                "; ".join(ans) + ".", "\n".join(sol) + "\n\nОстальные выводы верны.")


AN_OF = {"if": ("N1", "N2"), "ifn": ("N3", "N4"), "ifq": ("N5", "N6")}


def an_deriv():
    """K1 ∨ K2 ⊢ ∼K3 (одна пара) через Aⁿ и R3."""
    X, Y = comp(2) or (x, y)
    k1, k2 = rnd.sample(list(KIND), 2)
    k3 = [k for k in KIND if k not in (k1, k2)][0]
    K1, K2, K3 = KIND[k1](X, Y), KIND[k2](X, Y), KIND[k3](X, Y)
    a1, a2 = AN_OF[k1]
    b1, b2 = AN_OF[k2]
    R1_ = F.SCH[a1][1]
    m = {"x": X, "y": Y}
    E1 = F.subst(F.SCH[a1][1], m)
    E2 = F.subst(F.SCH[b1][1], m)
    P = W(K1, K2)
    P1 = W(E1, K2)
    P2 = W(E1, E2)
    lines = [(K1, E1, a1), (E1, K1, a2), (P, P1, ("R3", 1, 2)), (K2, E2, b1), (E2, K2, b2), (P1, P2, ("R3", 4, 5)),
             (P2, N(K3), "Ss"), (P, P2, ("R1", 3, 6)), (P, N(K3), ("R1", 8, 7))]
    assert not F.check(lines, "n"), F.check(lines, "n")
    return lines


def c_an_deriv(level=7, src="с. 89, гл. 6, § 5"):
    lines = an_deriv()
    return H.c_deriv("n", src=src, lines=lines) | {"level": level, "system": "S^s + A^n"}


def c_an_diag(level=6, src="с. 89, гл. 6, § 5"):
    return H.c_diag("n", src=src, lines_fn=an_deriv, kinds_pool=[("ax", "r12"), ("ax", "ax"), ("ax", "ss")]) | \
        {"system": "S^s + A^n"}


# ---------------------------------------------------------------- § 11: базисные формулы
BASIS = {1: "(a \\rightarrow b)c \\vdash d", 2: "(a \\rightarrow b)(c \\rightarrow d) \\vdash (e \\rightarrow f)",
         3: "(a \\rightarrow b)(c \\rightarrow d) \\vdash (ac \\rightarrow bd)",
         4: "(a \\rightarrow b)(c \\rightarrow d) \\vdash (a \\vee c \\rightarrow bd)",
         5: "(a \\rightarrow b)(c \\rightarrow d) \\vdash (ac \\rightarrow b \\vee d)",
         6: "(a \\rightarrow b)(c \\rightarrow d) \\vdash (a \\vee c \\rightarrow b \\vee d)",
         7: "(a \\rightarrow b) \\vee (c \\rightarrow d) \\vdash (ac \\rightarrow bd)",
         8: "(a \\rightarrow b) \\vee (c \\rightarrow d) \\vdash (a \\vee c \\rightarrow bd)",
         9: "(a \\rightarrow b) \\vee (c \\rightarrow d) \\vdash (ac \\rightarrow b \\vee d)",
         10: "(a \\rightarrow b) \\vee (c \\rightarrow d) \\vdash (a \\vee c \\rightarrow b \\vee d)",
         11: "(ab \\rightarrow c) \\vdash z", 12: "(a \\rightarrow bc) \\vdash z", 13: "(a \\vee b \\rightarrow c) \\vdash z",
         14: "(a \\rightarrow b \\vee c) \\vdash z", 15: "(ab \\rightarrow cd) \\vdash z", 16: "(ab \\rightarrow c \\vee d) \\vdash z",
         17: "(a \\vee b \\rightarrow cd) \\vdash z", 18: "(a \\vee b \\rightarrow c \\vee d) \\vdash z"}
a_, b_, c_, d_, e_, f_ = (V(t) for t in "abcdef")
BPAT = {1: (C(IF(a_, b_), c_), d_), 2: (C(IF(a_, b_), IF(c_, d_)), IF(e_, f_)),
        3: (C(IF(a_, b_), IF(c_, d_)), IF(C(a_, c_), C(b_, d_))), 4: (C(IF(a_, b_), IF(c_, d_)), IF(W(a_, c_), C(b_, d_))),
        5: (C(IF(a_, b_), IF(c_, d_)), IF(C(a_, c_), W(b_, d_))), 6: (C(IF(a_, b_), IF(c_, d_)), IF(W(a_, c_), W(b_, d_))),
        7: (W(IF(a_, b_), IF(c_, d_)), IF(C(a_, c_), C(b_, d_))), 8: (W(IF(a_, b_), IF(c_, d_)), IF(W(a_, c_), C(b_, d_))),
        9: (W(IF(a_, b_), IF(c_, d_)), IF(C(a_, c_), W(b_, d_))), 10: (W(IF(a_, b_), IF(c_, d_)), IF(W(a_, c_), W(b_, d_))),
        11: (IF(C(a_, b_), c_), None), 12: (IF(a_, C(b_, c_)), None), 13: (IF(W(a_, b_), c_), None),
        14: (IF(a_, W(b_, c_)), None), 15: (IF(C(a_, b_), C(c_, d_)), None), 16: (IF(C(a_, b_), W(c_, d_)), None),
        17: (IF(W(a_, b_), C(c_, d_)), None), 18: (IF(W(a_, b_), W(c_, d_)), None)}
BDEF = ("D1 § 11 (с. 96–97): формула $x \\vdash y$ — базисная, если имеет один из видов 1–18, где $a, b, c, d, e, f$ — элементарные "
        "высказывания или их отрицания, а $z$ — высказывание, образованное из $a, b, c, d$, их отрицаний и операторов "
        "$\\cdot$, $\\vee$, $\\sim$, $\\rightarrow$. Виды: " + "; ".join(f"{k}. ${s}$" for k, s in BASIS.items()) + ".")


def is_lit(t):
    return t[0] == "v" or (t[0] == "neg" and t[1][0] == "v")


def basis_kind(a, b):
    for k, (pa, pb) in BPAT.items():
        m = {}
        if not F.match(pa, a, m):
            continue
        if not all(is_lit(t) for t in m.values()):
            continue
        if pb is not None:
            if F.match(pb, b, m) and all(is_lit(t) for t in m.values()):
                return k, m
            continue
        base = set().union(*(F.atoms(t) for t in m.values()))
        ok = F.atoms(b) <= base and not F.has(b, ("ifn", "ifq", "imp"))
        if ok:
            return k, m
    return None


def basis_items(n=4):
    items = []
    tries = 0
    while len(items) < n and tries < 3000:
        tries += 1
        ls = [N(t) if rnd.random() < 0.3 else t for t in rnd.sample([x, y, z, v, u], 4)]
        k = rnd.choice(list(BPAT))
        m = dict(zip("abcdef", ls + ls[:2]))
        pa, pb = BPAT[k]
        A = F.subst(pa, {kk: vv for kk, vv in m.items()})
        if pb is not None:
            B = F.subst(pb, m)
        else:
            used = [m[t] for t in "abcd" if t in F.atoms(pa)]
            B = rnd.choice([IF(used[0], used[-1]), C(IF(used[0], used[-1]), IF(used[1], used[-1])),
                            W(IF(used[0], used[-1]), IF(used[1], used[-1])), IF(used[1], used[-1]), IF(N(used[-1]), N(used[0]))])
        if rnd.random() < 0.3:
            # испортить: отрицание составного или лишний член
            A = rnd.choice([F.subst(A, {}) if False else IF(N(C(ls[0], ls[1])), ls[2]),
                            C(IF(C(ls[0], ls[1]), ls[2]), IF(ls[2], ls[3]))])
            B = IF(ls[0], ls[3]) if A[0] == "conj" else IF(N(ls[2]), ls[0])
        if nn(A) or nn(B) or ftex(A, B) in [ftex(p, q) for p, q in items]:
            continue
        items.append((A, B))
    return items


def c_basis(level=5, src="с. 96–97, гл. 6, § 11"):
    for _ in range(50):
        items = basis_items(5)
        ks = [basis_kind(a, b) for a, b in items]
        if 1 <= sum(1 for k in ks if k is None) <= 2:
            break
    cond = (f"Буквы $x, y, z, v, u$ — элементарные высказывания. Для каждой формулы установите, базисная ли она по D1 § 11; "
            f"для базисной укажите вид и что подставлено вместо $a, b, c, \\ldots$, для небазисной — что мешает. {BDEF}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, ((a, b), k) in enumerate(zip(items, ks)):
        if k:
            ans.append(f"{L[i]}) вид {k[0]}")
            sol.append(f"{L[i]}) Вид {k[0]} (${BASIS[k[0]]}$): " + m_tex(k[1]).replace(":=", "=") + "; все — элементарные "
                       "высказывания или их отрицания" + ("; заключение составлено из них операторами" if BPAT[k[0]][1] is None else "") + ".")
        else:
            ans.append(f"{L[i]}) не базисная")
            why = ("в антецеденте отрицание составного высказывания — $a$ должно быть элементарным высказыванием или его "
                   "отрицанием" if a[0] == "if" and a[1][0] == "neg" else
                   "посылка не имеет ни одного из видов 1–18 (два условных высказывания с составным антецедентом)")
            sol.append(f"{L[i]}) Не базисная: {why}.")
    return card(level, "R", "iso", "short", src, "условность, полнота, базисные формулы", cond, "; ".join(ans) + ".",
                "\n".join(sol))


def c_basis_taut(level=6, src="с. 95–97, гл. 6, § 11"):
    """Для базисных формул: требует ли D2 (п. 1) доказуемости — тавтология и непарадоксальность."""
    import hard06_sem as S
    items = []
    tries = 0
    while tries < 20000:
        tries += 1
        if len(items) == 4:
            needs = [r[0] and not par for _, _, r, par, _ in items]
            if any(needs) and not all(needs) and sum(1 for _, _, r, par, _ in items if not r[0]) >= 1:
                break
            items.pop(rnd.randrange(4))
        ls = [N(t) if rnd.random() < 0.3 else t for t in rnd.sample([x, y, z, v, u], 4)]
        k = rnd.choice([1, 2, 2, 3, 4, 5, 6, 7, 9, 10])
        m = dict(zip("abcd", ls))
        if k == 2:
            e_ = rnd.choice([x, y, z, v, u])
            m["e"], m["f"] = (e_, e_) if rnd.random() < 0.3 else (rnd.choice(ls), rnd.choice(ls))
        if k == 1:
            m["c"] = rnd.choice([ls[0], ls[2]])
            m["d"] = rnd.choice([ls[1], ls[3]])
        A, B = F.subst(BPAT[k][0], m), F.subst(BPAT[k][1], m)
        if nn(A) or nn(B) or not F.flat(C(A, B)) or ftex(A, B) in [ftex(p_, q_) for p_, q_, *_ in items]:
            continue
        r = F.sem_robust(A, B)
        if r is None or basis_kind(A, B) is None:
            continue
        par = bool(F.atoms(B) - F.atoms(A))
        items.append((A, B, r, par, basis_kind(A, B)[0]))
    rnd.shuffle(items)
    cond = (f"Буквы $x, y, z, v, u$ — элементарные высказывания. Все формулы ниже — базисные (D1 § 11). Для каждой установите, "
            f"требует ли п. 1 D2 § 11 её доказуемости, то есть тавтология ли она при интерпретации § 4 и непарадоксальна ли "
            f"(в заключение не входят элементарные высказывания, отсутствующие в посылке); обоснуйте значениями. D2 § 11 "
            f"(с. 97): теория условных высказываний достаточно полна, если 1) все базисные формулы, являющиеся тавтологиями "
            f"и непарадоксальные, доказуемы; 2) доказуемы все формулы, получаемые из базисных подстановкой. {INTERP}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$ (вид {k})" for i, (a, b, _, _, k) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b, r, par, k) in enumerate(items):
        need = r[0] and not par
        ans.append(f"{L[i]}) " + ("требует" if need else "не требует") + (" (тавтология, непарадоксальна)" if need else
                                                                           " (парадоксальна)" if r[0] else " (не тавтология)"))
        if r[0]:
            new = sorted(F.atoms(b) - F.atoms(a))
            fi = find_inst(a, b, ["A1", "A3", "A7", "A8"])
            sol.append(f"{L[i]}) " + S.explain_taut(a, b) + (
                f" Но в заключение входит {', '.join('$' + t + '$' for t in new)}, отсутствующее в посылке: парадоксальна, "
                f"п. 1 её не касается." if par else " Непарадоксальна: п. 1 требует доказуемости" +
                (f" — и она доказуема в $S^s_{{if}}$ как пример {fi[0]}." if fi else
                 " — и она доказуема в $S^s_{if}$ шагом общей теории дедукции (сильная тавтология, если условные "
                 "высказывания считать элементарными)." if F.s_step(a, b) else ".")))
        else:
            sol.append(f"{L[i]}) " + explain_non(a, b, r[1]) + " П. 1 её не касается.")
    return card(level, "C", "open", "short", src, "условность, полнота", cond, "; ".join(ans) + ".", "\n".join(sol))


def c_basis_diag(level=6, src="с. 95–97, гл. 6, § 11"):
    c0 = c_basis_taut(level, src)
    # переделать в диагностику: студент ошибся в двух пунктах
    import re
    ans_items = re.findall(r"([а-г])\) (требует|не требует)", c0["ans"])
    wrong = rnd.sample(range(len(ans_items)), 2)
    claims = []
    for i, (lt, verdict) in enumerate(ans_items):
        cl = verdict if i not in wrong else ("не требует" if verdict == "требует" else "требует")
        claims.append(f"{lt}) {cl}")
    cond = c0["cond"].replace("Для каждой установите, требует ли", "Студент установил для каждой, требует ли").replace(
        "; обоснуйте значениями.", ", и ответил так: " + "; ".join(claims) +
        ". Ровно два ответа неверны. Найдите их и обоснуйте значениями верный ответ.")
    sol_lines = c0["sol"].split("\n")
    sol = "\n".join(sol_lines[i] for i in sorted(wrong)) + "\n\nОстальные ответы верны."
    ans = "; ".join(f"{ans_items[i][0]}) {ans_items[i][1]}" for i in sorted(wrong)) + "."
    return card(level, "E", "vary", "text", src, "условность, полнота, диагностика", cond, ans, sol)


# ---------------------------------------------------------------- утверждения по тексту книги (диагностика)
def c_claims(bank, intro, src, tags, level=5, n=4, nat=False):
    items = rnd.sample(bank, n)
    while sum(1 for _, ok, _ in items if ok) in (0, n):
        items = rnd.sample(bank, n)
    wrong = rnd.sample(range(n), 2)
    lines, ans, sol = [], [], []
    for i, (text, ok, why) in enumerate(items):
        mark = ok if i not in wrong else not ok
        lines.append(f"{i + 1}. «{text}» — {'верно' if mark else 'неверно'}.")
        if i in wrong:
            ans.append(f"{i + 1}: {'верно' if ok else 'неверно'}")
            sol.append(f"{i + 1}. Утверждение {'верно' if ok else 'неверно'}: {why}")
    cond = (f"{intro}\n\n" + "\n".join(lines) + "\n\nРовно две оценки ошибочны. Найдите их и исправьте со ссылкой на "
            "страницу книги.")
    return card(level, "E", "vary", "text", src, tags, cond, "; ".join(ans) + ".", "\n".join(sol) +
                "\n\nОстальные оценки верны.", form="nat" if nat else "meta")
