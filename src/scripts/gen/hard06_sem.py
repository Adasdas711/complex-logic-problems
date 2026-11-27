"""Гл. 6, § 3–4, 11: серии формул с обоснованием значениями по интерпретации § 4 (с. 86–88)."""
from hard06_lib import F, C, IF, IMP, N, V, W, ftex, tex, rnd, x, y, z, v, u, L, CV, card

INTERP = ("Правила интерпретации § 4 (с. 86–87): если $x \\rightarrow y$ приписано 1 и $x$ — 1, то $y$ — 1 (п. 1); если "
          "$x \\rightarrow y$ — 1 и $y$ — 0, то $x$ — 0 (п. 2); если приписали $x$ значение 1 и вследствие этого вынуждены "
          "приписать $y$ значение 1 (или $y$ — 0 и вследствие этого $x$ — 0), то $x \\rightarrow y$ приписываем 1 (пп. 5–6); "
          "если $x$ = 1 не обязывает приписывать $y$ значение 1 (или $y$ = 0 не обязывает приписывать $x$ значение 0), то "
          "$x \\rightarrow y$ можно приписать 0 (пп. 7–8); при $x$ = 0 или $y$ = 1 значение $x \\rightarrow y$ от них не "
          "зависит (п. 9). Формула — тавтология, если при всяком допустимом приписывании, где посылка имеет значение 1, "
          "заключение имеет значение 1.")


def lit_tex(e):
    return ", ".join(f"${k} = {vv}$" for k, vv in sorted(e.items()))


def c_tex(c):
    return ", ".join(f"${tex(g)} = {vv}$" for g, vv in c.items())


def laws_of(c):
    return [g for g, vv in c.items() if vv]


def explain_non(a, b, wit):
    e, c = wit
    names = set().union(*(F.atoms(f) for f in (a, b) if f is not None))
    laws = [IMP(g[1], g[2]) for g in laws_of(c)]
    parts = [f"Припишем {c_tex(c)}; буквам — {lit_tex(e)}."]
    if laws_of(c):
        parts.append("Высказываниям со значением 1 значения букв не противоречат: нет случая «антецедент 1, консеквент 0» "
                     "(пп. 1–2).")
    for g, vv in c.items():
        if vv == 0:
            wv = F.not_forced_witness(g, laws, names)
            parts.append(f"${tex(g)}$ = 0 допустимо: приписав ${tex(g[1])}$ значение 1, мы не вынуждены приписывать "
                         f"${tex(g[2])}$ значение 1 — " + (f"при {lit_tex(wv)} " if wv else "") +
                         ("условные высказывания со значением 1 соблюдены, " if laws else "") +
                         f"антецедент 1, а консеквент 0 (пп. 7–8, 9).")
    pa = "" if a is None else f"посылка — {F.cv(a, e, c)}, "
    parts.append(f"Тогда {pa}заключение — {F.cv(b, e, c)}: формула не тавтология.")
    return " ".join(parts)


def explain_taut(a, b, why=""):
    parts = []
    if a is not None:
        prem = a[1] if a[0] == "conj" else (a,)
        laws = [g for g in prem if g[0] == "if"]
        fs = [g for g in prem if not F.has(g)]
        if a[0] == "wdis":
            parts.append("Посылка — дизъюнкция условных высказываний: при значении 1 хотя бы одно из них имеет значение 1; "
                         "рассматриваем оба случая.")
        else:
            if laws:
                parts.append("Пусть посылка имеет значение 1: " + ", ".join(f"${tex(g)}$" for g in laws) + " — 1" +
                             (", " + ", ".join(f"${tex(g)}$" for g in fs) + " — 1" if fs else "") + ".")
    cs = F.conds(b) if b[0] != "neg" else []
    if b[0] in ("if", "conj") and all(t[0] == "if" for t in (b[1] if b[0] == "conj" else (b,))):
        for g in (b[1] if b[0] == "conj" else (b,)):
            parts.append(f"Приписав ${tex(g[1])}$ значение 1, мы вынуждены приписать ${tex(g[2])}$ значение 1 "
                         "(пп. 1–2 для высказываний посылки" + (" в каждом случае" if a is not None and a[0] == "wdis" else "")
                         + "), значит, по п. 5 $" + tex(g) + "$ имеет значение 1.")
    elif not cs:
        parts.append("По пп. 1–2 при значении 1 посылки заключение получает значение 1.")
    parts.append("Формула — тавтология" + (f" ({why})" if why else "") + ".")
    return " ".join(parts)


# ---------------------------------------------------------------- пулы формул
LETTERS = [x, y, z, v, u]


def lits(k):
    out = []
    for t in rnd.sample(LETTERS, k):
        out.append(N(t) if rnd.random() < 0.3 else t)
    return out


def comp(k):
    """Высказывания для замены: буквы, отрицания, конъюнкции/дизъюнкции двух букв; попарно без общих букв."""
    base = rnd.sample(LETTERS, 5)
    out = []
    i = 0
    for _ in range(k):
        r = rnd.random()
        if r < 0.55 or i + 1 >= len(base):
            t = base[i]
            out.append(N(t) if rnd.random() < 0.3 else t)
            i += 1
        else:
            a_, b_ = base[i], base[i + 1]
            out.append(C(a_, N(b_)) if r < 0.75 else W(a_, b_))
            i += 2
        if i >= len(base) and len(out) < k:
            return None
    return out


GOOD = {
    "A1": lambda X, Y, Z, Vv: (C(IF(X, Y), X), Y),
    "A2": lambda X, Y, Z, Vv: (IF(X, Y), IF(N(Y), N(X))),
    "A3": lambda X, Y, Z, Vv: (C(IF(X, Y), IF(Y, Z)), IF(X, Z)),
    "A4": lambda X, Y, Z, Vv: (IF(X, C(Y, Z)), C(IF(X, Y), IF(X, Z))),
    "A7": lambda X, Y, Z, Vv: (C(IF(X, Y), IF(Z, Vv)), IF(C(X, Z), C(Y, Vv))),
    "A8": lambda X, Y, Z, Vv: (W(IF(X, Y), IF(Z, Vv)), IF(C(X, Z), W(Y, Vv))),
    "T1": lambda X, Y, Z, Vv: (C(IF(X, Y), IF(C(Y, Z), Vv)), IF(C(X, Z), Vv)),
    "T4": lambda X, Y, Z, Vv: (C(IF(X, Y), N(Y)), N(X)),
    "T7": lambda X, Y, Z, Vv: (IF(W(X, Y), Z), C(IF(X, Z), IF(Y, Z))),
    "T8": lambda X, Y, Z, Vv: (C(IF(X, Z), IF(Y, Z)), IF(W(X, Y), Z)),
    "T11": lambda X, Y, Z, Vv: (C(IF(X, Y), IF(Vv, Z)), IF(W(X, Vv), W(Y, Z))),
    "T5": lambda X, Y, Z, Vv: (C(IF(X, W(Y, Z)), N(Y)), IF(X, Z)),
    "T2": lambda X, Y, Z, Vv: (C(IF(X, W(Y, Z)), IF(Z, Vv)), IF(X, W(Y, Vv))),
}
GOOD_TEX = {"A1": "A1", "A2": "A2", "A3": "A3", "A4": "A4", "A7": "A7", "A8": "A8", "T1": "T1", "T2": "T2", "T4": "T4",
            "T5": "T5", "T7": "T7", "T8": "T8", "T11": "T11"}
BAD = {
    "conj": lambda X, Y, Z, Vv: (C(X, Y), IF(X, Y)),
    "negneg": lambda X, Y, Z, Vv: (C(N(X), N(Y)), IF(X, Y)),
    "negpos": lambda X, Y, Z, Vv: (C(N(X), Y), IF(X, Y)),
    "dis": lambda X, Y, Z, Vv: (W(N(X), Y), IF(X, Y)),
    "negif": lambda X, Y, Z, Vv: (N(IF(X, Y)), C(X, N(Y))),
    "split": lambda X, Y, Z, Vv: (IF(C(X, Y), Z), W(IF(X, Z), IF(Y, Z))),
    "split2": lambda X, Y, Z, Vv: (IF(C(X, Y), W(Z, Vv)), W(IF(X, Z), IF(Y, Vv))),
    "orcons": lambda X, Y, Z, Vv: (IF(X, W(Y, Z)), W(IF(X, Y), IF(X, Z))),
    "fact": lambda X, Y, Z, Vv: (Z, IF(X, Z)),
    "conv": lambda X, Y, Z, Vv: (IF(X, Y), IF(Y, X)),
    "inv": lambda X, Y, Z, Vv: (IF(X, Y), IF(N(X), N(Y))),
    "affirm": lambda X, Y, Z, Vv: (C(IF(X, Y), Y), X),
    "deny": lambda X, Y, Z, Vv: (C(IF(X, Y), N(X)), N(Y)),
    "chain": lambda X, Y, Z, Vv: (C(IF(X, Y), IF(Y, Z)), IF(Z, X)),
}
BAD_WHY = {"conj": "с. 84", "negneg": "с. 84", "negpos": "с. 84", "dis": "с. 84", "negif": "с. 84", "split": "с. 85, 87",
           "split2": "с. 84", "orcons": "с. 88", "fact": "с. 87"}


def nn(f):
    return f is not None and any(g[0] == "neg" and g[1][0] == "neg" for g in F.subs(f))


def pick(pool_keys, pool, want_taut, tries=400):
    for _ in range(tries):
        k = rnd.choice(pool_keys)
        args = comp(4)
        if not args:
            continue
        a, b = pool[k](*args)
        if not F.flat(C(a, b)) if a is not None else not F.flat(b):
            continue
        r = F.sem_robust(a, b)
        if r is None or r[0] != want_taut:
            continue
        if not 10 <= F.size(a) + F.size(b) <= 46 or nn(a) or nn(b):
            continue
        return k, a, b, r
    raise RuntimeError("нет формулы")


def series_items(n_t=2, n_f=2, good_keys=None, bad_keys=None):
    good_keys = good_keys or list(GOOD)
    bad_keys = bad_keys or list(BAD)
    items = []
    seen = set()
    while len(items) < n_t + n_f:
        want = len(items) < n_t
        k, a, b, r = pick(good_keys if want else bad_keys, GOOD if want else BAD, want)
        key = ftex(a, b)
        if key in seen or any(kk == k for kk, *_ in items):
            continue
        seen.add(key)
        items.append((k, a, b, r))
    rnd.shuffle(items)
    return items


def item_solution(k, a, b, r, letter):
    if r[0]:
        why = f"пример {GOOD_TEX[k]} § 6 с заменой букв высказываниями; ср. MT1 § 6, с. 90" if k in GOOD_TEX else ""
        return f"{letter}) {explain_taut(a, b, why)}"
    return f"{letter}) {explain_non(a, b, r[1])}"


def item_short(a, b, r):
    if r[0]:
        return "тавтология"
    e, c = r[1]
    zeros = [g for g, vv in c.items() if vv == 0 and g in F.conds(b)]
    return "не тавтология (" + ", ".join(f"${tex(g)} = 0$" for g in zeros[:2]) + (", " if zeros else "") + lit_tex(e) + ")"


def c_sem_series(level=6, src="с. 86–88, гл. 6, § 4", n_t=2, n_f=2, good_keys=None, bad_keys=None, tags="условность, интерпретация"):
    items = series_items(n_t, n_f, good_keys, bad_keys)
    cond = (f"{CV} Исследуйте каждую формулу: установите, тавтология ли она при интерпретации § 4 гл. 6, и обоснуйте "
            f"значениями — для тавтологии укажите, какие пункты правил вынуждают значение 1 заключения, для остальных "
            f"постройте приписывание, где посылка 1, а заключение 0. {INTERP}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (_, a, b, _) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {item_short(a, b, r)}" for i, (_, a, b, r) in enumerate(items))
    sol = "\n".join(item_solution(k, a, b, r, L[i]) for i, (k, a, b, r) in enumerate(items))
    return card(level, "V", "open", "short", src, tags, cond, ans, sol)


def c_sem_diag(level=6, src="с. 86–88, гл. 6, § 4", tags="условность, интерпретация, диагностика"):
    items = series_items(2, 2)
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, (k, a, b, r) in enumerate(items):
        claim = r[0] if i not in wrong else not r[0]
        if claim and not r[0]:
            reason = rnd.choice(["заключение получает 1 при всех значениях букв, где посылка 1, если считать "
                                 "$\\rightarrow$ материальной импликацией",
                                 "в заключение не входят элементарные высказывания, отсутствующие в посылке"])
        elif claim:
            reason = "приписав антецеденту 1, мы вынуждены приписать консеквенту 1"
        else:
            reason = rnd.choice(["условное высказывание заключения можно приписать 0 по п. 9",
                                 "при значениях, где антецедент 0, условное высказывание может иметь значение 0"])
        lines.append(f"{i + 1}. ${ftex(a, b)}$ — {'тавтология' if claim else 'не тавтология'}: {reason}.")
        if i in wrong:
            ans.append(f"{i + 1}: {item_short(a, b, r)}")
            if r[0]:
                sol.append(f"{i + 1}. Неверно: значение 0 условному высказыванию можно приписать лишь тогда, когда консеквент "
                           f"не вынужден антецедентом (пп. 7–8); здесь он вынужден. " + explain_taut(a, b))
            else:
                sol.append(f"{i + 1}. Неверно: оператор условности не есть материальная импликация (с. 88), и отсутствия "
                           f"новых элементарных высказываний мало. " + explain_non(a, b, r[1]))
    cond = (f"{CV} Студент исследовал четыре формулы при интерпретации § 4 гл. 6:\n\n" + "\n".join(lines) +
            f"\n\nРовно два вывода неверны. Найдите их, назовите нарушенный пункт правил интерпретации и дайте верный ответ "
            f"с обоснованием значениями. {INTERP}")
    return card(level, "E", "vary", "text", src, tags, cond, "; ".join(ans) + ".", "\n".join(sol) + "\n\nОстальные выводы верны.")


def c_sem_build(level=7, src="с. 86–88, гл. 6, § 4", typ="K"):
    want = rnd.random() < 0.65
    k, a, b, r = pick(list(GOOD if not want else BAD), GOOD if not want else BAD, not want)
    cond = (f"{CV} Постройте приписывание значений по правилам § 4 гл. 6, при котором посылка формулы ${ftex(a, b)}$ "
            f"имеет значение 1, а заключение — 0, или докажите, что такого приписывания нет. {INTERP}")
    if r[0]:
        ans = "Такого приписывания нет: формула — тавтология."
        sol = explain_taut(a, b, f"пример {GOOD_TEX[k]} § 6" if k in GOOD_TEX else "")
    else:
        e, c = r[1]
        ans = "Например: " + c_tex(c) + "; " + lit_tex(e) + "."
        sol = explain_non(a, b, r[1])
    return card(level, typ, "open", "build", src, "условность, интерпретация, построение", cond, ans, sol)


def c_sem_fill(level=5, src="с. 87–88, гл. 6, § 4"):
    """Рассуждение по образцу с. 87–88 с пропусками: номера пунктов и значения."""
    k, a, b, r = pick(["split", "split2", "orcons"], BAD, False)
    e, c = r[1]
    names = set().union(F.atoms(a), F.atoms(b))
    laws = [IMP(g[1], g[2]) for g in laws_of(c)]
    steps = []
    p0 = a
    steps.append((f"Припишем ${tex(p0)}$ значение 1.", None, None))
    zeros = [g for g, vv in c.items() if vv == 0]
    if k in ("split", "split2"):
        Zc = p0[2]
        steps.append((f"Припишем консеквенту ${tex(Zc)}$ значение 0; тогда по п. [?1] антецеденту ${tex(p0[1])}$ надо "
                      f"приписать значение [?2].", "2", "0"))
        for g in zeros:
            wv = F.not_forced_witness(g, laws, names)
            steps.append((f"Приписав ${tex(g[2])}$ значение 0, мы не обязаны приписывать ${tex(g[1])}$ значение 0 "
                          f"(${tex(p0[1])}$ может иметь значение 0 за счёт другого члена; например, {lit_tex(wv)}); "
                          f"по п. [?] высказыванию ${tex(g)}$ можно приписать значение [?].", "8", "0"))
    else:
        steps.append((f"Приписав ${tex(p0[1])}$ значение 1, по п. [?1] должны приписать ${tex(p0[2])}$ значение [?2].",
                      "1", "1"))
        for g in zeros:
            wv = F.not_forced_witness(g, laws, names)
            steps.append((f"Но это не означает, что ${tex(g[2])}$ непременно 1 (например, {lit_tex(wv)}); по п. [?] "
                          f"высказыванию ${tex(g)}$ можно приписать значение [?].", "7", "0"))
    text, ans, n = [], [], 1
    for s, r1, r2 in steps:
        if r1 is None:
            text.append(s)
            continue
        s2 = s.replace("[?1]", f"[{n}]").replace("[?2]", f"[{n + 1}]")
        if "[?]" in s2:
            s2 = s2.replace("[?]", f"[{n}]", 1).replace("[?]", f"[{n + 1}]", 1)
        text.append(s2)
        ans.append(f"[{n}] — п. {r1}, [{n + 1}] — {r2}")
        n += 2
    concl = f"Итак, ${tex(b)}$ может иметь значение 0 при значении 1 посылки: формула не тавтология."
    cond = (f"{CV} Восстановите пропуски [1], [2], … (номер пункта правил интерпретации § 4 или значение) в рассуждении "
            f"по образцу с. 87–88 о формуле ${ftex(a, b)}$. {INTERP}\n\n" + "\n".join(text) + "\n" + concl)
    sol = ("Пункты правил § 4 (с. 86–87); рассуждение — по образцу разбора формул $(xy \\rightarrow z) \\vdash (x \\rightarrow z) "
           "\\vee (y \\rightarrow z)$ и $(x \\rightarrow y \\vee z) \\vdash (x \\rightarrow y) \\vee (x \\rightarrow z)$ (с. 87–88). "
           + explain_non(a, b, r[1]))
    return card(level, "V", "complete", "short", src, "условность, интерпретация, дополнение", cond, "; ".join(ans) + ".", sol)


def c_vs_imp(level=7, src="с. 88, гл. 6, § 4"):
    """Сравнение → и ⊃ при данных значениях букв (с. 88)."""
    rows = []
    while len(rows) < 4:
        X, Y = comp(2) or (x, y)
        e = {t: rnd.randint(0, 1) for t in sorted(F.atoms(X) | F.atoms(Y))}
        vx, vy = F.pval(X, e), F.pval(Y, e)
        if (vx, vy) in [(r[3], r[4]) for r in rows] or F.entails([X], Y, F.atoms(X) | F.atoms(Y)) is None:
            continue
        rows.append((X, Y, e, vx, vy))
    cond = (f"{CV} Для каждой пары высказываний и значений букв установите, какие значения может иметь $X \\supset Y$ "
            f"и какие — $X \\rightarrow Y$ по интерпретации § 4 (считая, что о связи $X$ и $Y$ ничего не известно, кроме "
            f"самих высказываний), и объясните расхождение. {INTERP}\n\n" +
            "\n".join(f"{L[i]}) $X = {tex(X)}$, $Y = {tex(Y)}$; {lit_tex(e)}" for i, (X, Y, e, _, _) in enumerate(rows)))
    ans, sol = [], []
    for i, (X, Y, e, vx, vy) in enumerate(rows):
        imp = int(not vx or vy)
        arr = "только 0" if (vx, vy) == (1, 0) else "0 или 1"
        ans.append(f"{L[i]}) $\\supset$: {imp}; $\\rightarrow$: {arr}")
        if (vx, vy) == (1, 0):
            sol.append(f"{L[i]}) $X = 1$, $Y = 0$: $X \\supset Y = 0$; $X \\rightarrow Y$ не может быть 1 — по п. 1 при значении 1 "
                       f"и $X = 1$ было бы $Y = 1$. Здесь операторы сходны (с. 88).")
        else:
            sol.append(f"{L[i]}) $X = {vx}$, $Y = {vy}$: $X \\supset Y = 1$; для $X \\rightarrow Y$ значения букв не "
                       f"решают дела (п. 9): $Y$ не следует из $X$ (при подходящих значениях $X$ истинно, а $Y$ ложно), так "
                       f"что значение 0 возможно (пп. 7–8), а 1 — если связь установлена (п. 5).")
    return card(level, "S", "transfer", "short", src, "условность, материальная импликация", cond, "; ".join(ans) + ".",
                "\n".join(sol) + "\n\nСр. с. 88: $x \\rightarrow y$ может иметь значение 0 при $x = 1$, $y = 1$ и при "
                "$x = 0$, $y = 1$; единственное сходство — случай $x = 1$, $y = 0$.")
