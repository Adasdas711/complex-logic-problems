#!/usr/bin/env python3
"""Серии к гл. 1, § 1 «Система S¹» (с. 15–17): ступени 1–5. Все выводы проверяются s1.check.
Пишет drafts/01.01-gen.md.
"""
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
from s1 import AXIOM_TEXT, C, D, N, V, axiom, check, ftex, instance, tautology, tex  # noqa: E402

rnd = random.Random(1970_15)
x, y, z, u, w = (V(c) for c in "xyzuw")
L = "абвгдежз"
CONV = "Буквы $x, y, z, u, w$ — элементарные высказывания; запись по соглашению книги (с. 15)."
SRC = "с. 15–17, гл. 1, § 1"
POOL = [x, y, z, u, N(x), N(y), C(u, w), D(u, w), N(C(u, w)), N(z)]
SIMPLE = [x, y, z, u, w, N(x), N(y), D(u, w), N(z)]   # без конъюнкций — для схем A5/A6


def card(level, typ, step, form, ans, tags, body, series, cond="def"):
    meta = (f"chapter: 1\nsection: 1\nlevel: {level}\ntype: {typ}\nstep: {step}\ncondition: {cond}\n"
            f"form: {form}\nanswer: {ans}\nsource: \"{SRC}\"\nsystem: \"S^1\"\nseries: {series}\n"
            f"generated: true\ntags: [{tags}]")
    return f"---\n{meta}\n---\n\n{body}\n"


def pick(k, pool=POOL):
    return rnd.sample(pool, k)


def why_text(wh):
    return wh if isinstance(wh, str) else f"{wh[0]}: {wh[1]}, {wh[2]}"


def show(lines, hide_why=(), hide_formula=()):
    out = []
    for n, (a, b, wh) in enumerate(lines, 1):
        f = "…" if n in hide_formula else f"${ftex(a, b)}$"
        out.append(f"{n}. {f} [{'…' if n in hide_why else why_text(wh)}]")
    return "\n".join(out)


# ---------- выводы-шаблоны ----------
def T1(X, Y):   # XY ⊢ Y
    return (C(X, Y), Y), [(C(X, Y), C(Y, X), "A4"), (C(Y, X), Y, "A3"), (C(X, Y), Y, ("R1", 1, 2))]


def T2(X, Y):   # X ⊢ X
    return (X, X), [(X, N(N(X)), "A1"), (N(N(X)), X, "A2"), (X, X, ("R1", 1, 2))]


def T3(X, Y):   # ~~X·Y ⊢ X
    return (C(N(N(X)), Y), X), [(C(N(N(X)), Y), N(N(X)), "A3"), (N(N(X)), X, "A2"), (C(N(N(X)), Y), X, ("R1", 1, 2))]


def T4(X, Y):   # XY ⊢ ~~X
    return (C(X, Y), N(N(X))), [(C(X, Y), X, "A3"), (X, N(N(X)), "A1"), (C(X, Y), N(N(X)), ("R1", 1, 2))]


def T5(X, Y):   # XY ⊢ X·~~Y
    return (C(X, Y), C(X, N(N(Y)))), [
        (C(X, Y), X, "A3"), (C(X, Y), C(Y, X), "A4"), (C(Y, X), Y, "A3"), (C(X, Y), Y, ("R1", 2, 3)),
        (Y, N(N(Y)), "A1"), (C(X, Y), N(N(Y)), ("R1", 4, 5)), (C(X, Y), C(X, N(N(Y))), ("R2", 1, 6))]


def T6(X, Y):   # ~~X·Y ⊢ XY
    return (C(N(N(X)), Y), C(X, Y)), [(N(N(X)), X, "A2"), (X, N(N(X)), "A1"), (C(N(N(X)), Y), C(X, Y), ("R3", 1, 2))]


def T7(X, Y):   # ~~~(X:Y) ⊢ XY : ~X~Y
    a = N(D(X, Y))
    return (N(N(a)), D(C(X, Y), C(N(X), N(Y)))), [(N(N(a)), a, "A2"), (a, D(C(X, Y), C(N(X), N(Y))), "A9"),
                                                  (N(N(a)), D(C(X, Y), C(N(X), N(Y))), ("R1", 1, 2))]


def T8(X, Y):   # XY : ~X~Y ⊢ ~~~(X:Y)
    a = N(D(X, Y))
    b = D(C(X, Y), C(N(X), N(Y)))
    return (b, N(N(a))), [(b, a, "A10"), (a, N(N(a)), "A1"), (b, N(N(a)), ("R1", 1, 2))]


def T9(X, Y):   # ~~~(XY) ⊢ ~XY : X~Y : ~X~Y
    a = N(C(X, Y))
    b = D(C(N(X), Y), C(X, N(Y)), C(N(X), N(Y)))
    return (N(N(a)), b), [(N(N(a)), a, "A2"), (a, b, "A7"), (N(N(a)), b, ("R1", 1, 2))]


def T10(X, Y, Z):   # XYZ ⊢ X
    return (C(X, Y, Z), X), [(C(X, Y, Z), C(C(X, Y), Z), "A5"), (C(C(X, Y), Z), C(X, Y), "A3"),
                             (C(X, Y, Z), C(X, Y), ("R1", 1, 2)), (C(X, Y), X, "A3"), (C(X, Y, Z), X, ("R1", 3, 4))]


def T11(X, Y, Z):   # XYZ ⊢ Z
    return (C(X, Y, Z), Z), [(C(X, Y, Z), C(C(X, Y), Z), "A5"), (C(C(X, Y), Z), C(Z, C(X, Y)), "A4"),
                             (C(X, Y, Z), C(Z, C(X, Y)), ("R1", 1, 2)), (C(Z, C(X, Y)), Z, "A3"),
                             (C(X, Y, Z), Z, ("R1", 3, 4))]


def T12(X, Y):   # ~~(XY) ⊢ Y
    return (N(N(C(X, Y))), Y), [(N(N(C(X, Y))), C(X, Y), "A2"), (C(X, Y), C(Y, X), "A4"),
                                (N(N(C(X, Y))), C(Y, X), ("R1", 1, 2)), (C(Y, X), Y, "A3"),
                                (N(N(C(X, Y))), Y, ("R1", 3, 4))]


TEMPLATES2 = [T1, T2, T3, T4, T5, T6, T7, T8, T9, T12]
TEMPLATES3 = [T10, T11]


def derivation(tpl=None):
    tpl = tpl or rnd.choice(TEMPLATES2 + TEMPLATES3)
    if tpl in TEMPLATES3:
        goal, lines = tpl(*pick(3, SIMPLE))
    else:
        goal, lines = tpl(*pick(2))
    assert not check(lines), (tpl.__name__, check(lines))
    assert tautology(*goal)
    return goal, lines


def corrupt(lines):
    """Портит одно основание или одну формулу; возвращает (новые строки, номер шага, описание правильного)."""
    for _ in range(100):
        k = rnd.randrange(len(lines))
        a, b, wh = lines[k]
        new = list(lines)
        if isinstance(wh, str):
            alt = rnd.choice([n for n in ("A1", "A2", "A3", "A4", "A5", "A7", "A9", "A10") if n != wh])
            new[k] = (a, b, alt)
        else:
            r, i, j = wh
            choice = rnd.choice(["rule", "swap"])
            if choice == "rule":
                new[k] = (a, b, (rnd.choice([q for q in ("R1", "R2", "R3") if q != r]), i, j))
            else:
                new[k] = (a, b, (r, j, i))
        bad = [e for e in check(new)]
        if len(bad) == 1 and bad[0].startswith(f"шаг {k + 1}:"):
            return new, k + 1, why_text(wh)
    return None


# ---------- карточки ----------
def level1():
    import statements as Sx
    import terms as T
    s, p, t, q = T.S("s"), T.P("p"), T.S("t"), T.P("q")
    elem = [Sx.basic(s, p), Sx.wdis(T.X("x"), T.X("y")), Sx.cond(T.X("x"), T.X("y")), Sx.forall(s, Sx.basic(s, p)),
            Sx.basic(t, q, "not"), Sx.exists(t, T.X("y"))]
    compound = [Sx.neg(Sx.basic(s, p)), Sx.conj(Sx.basic(s, p), Sx.basic(t, q)), Sx.sdis(T.X("x"), T.X("y")),
                Sx.neg(Sx.wdis(T.X("x"), T.X("y"))), Sx.conj(Sx.cond(T.X("x"), T.X("y")), T.X("z"))]
    out = []
    for _ in range(4):
        items = rnd.sample(elem, 3) + rnd.sample(compound, 2)
        rnd.shuffle(items)
        ok = [any(Sx.latex(i) == Sx.latex(e) for e in elem) for i in items]
        cond_ = "\n".join(f"{L[k]}) ${Sx.latex(i)}$" for k, i in enumerate(items))
        ans = "; ".join(f"{L[k]}) {'да' if v else 'нет'}" for k, v in enumerate(ok))
        sol = ("D1 § 1 гл. 1 (с. 15): элементарны относительно $S^1$ высказывания, которые нельзя расчленить на "
               "другие высказывания и операторы $\\cdot$, $:$, $\\sim$. Высказывания с главными операторами "
               "$\\leftarrow$, $\\vee$, $\\to$, $\\forall$, $\\exists$ относительно $S^1$ элементарны: их операторы не "
               "входят в $S^1$. Высказывания вида $\\sim x$, $(x \\cdot y)$, $(x : y)$ — нет.\n\n" +
               "\n".join(f"{L[k]}) {'элементарно' if v else 'не элементарно: расчленяется оператором $S^1$'}."
                         for k, v in enumerate(ok)))
        body = (f"## Условие\n\nОбозначения из Введения: $s, t$ — субъекты, $p, q$ — предикаты, $x, y, z$ — "
                f"высказывания. Какие высказывания элементарны относительно $S^1$?\n\n{cond_}\n\n## Ответ\n\n{ans}"
                f"\n\n## Решение\n\n{sol}")
        out.append(card(1, "R", "iso", "sym", "short", "S1, элементарные высказывания", body, "элементарные-S1"))
    return out


def level2():
    out = []
    names = ["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10"]
    for k in range(12):
        n = names[k % len(names)]
        X, Y = pick(2)
        a, b = instance(n, X, Y)
        sub = f"$x$ — ${tex(X)}$" + ("" if n in ("A1", "A2") else f", $y$ — ${tex(Y)}$")
        body = (f"## Условие\n\n{CONV} Подставьте в аксиомную схему {n} (${AXIOM_TEXT[n]}$) вместо {sub} и "
                f"запишите полученную аксиому.\n\n## Ответ\n\n${ftex(a, b)}$\n\n## Решение\n\n"
                f"Схема {n} — с. {15 if n in ('A1', 'A2', 'A3') else 16}. Подставляем и расставляем скобки по "
                "соглашению книги: составной член конъюнкции, если он дизъюнкция или конъюнкция, берётся в скобки; "
                "отрицание составного высказывания — $\\sim(\\dots)$.")
        out.append(card(2, "D", "iso", "sym", "short", "S1, аксиомы", body, "подстановка-в-аксиому"))
    return out


def level3():
    out = []
    bad_makers = [lambda X, Y: (C(X, Y), Y), lambda X, Y: (X, C(X, Y)), lambda X, Y: (N(C(X, Y)), D(N(X), N(Y))),
                  lambda X, Y: (N(D(X, Y)), C(N(X), N(Y))), lambda X, Y: (X, N(X)), lambda X, Y: (N(N(X)), N(X))]
    for _ in range(5):
        items = []
        for _ in range(5):
            X, Y = pick(2)
            if rnd.random() < 0.6:
                n = rnd.choice(["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10"])
                items.append(instance(n, X, Y))
            else:
                items.append(rnd.choice(bad_makers)(X, Y))
        cond_ = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b) in enumerate(items))
        ans = "; ".join(f"{L[k]}) {axiom(a, b) or 'ни одной'}" for k, (a, b) in enumerate(items))
        sol = "\n".join(f"{L[k]}) " + (f"{axiom(a, b)}: ${AXIOM_TEXT[axiom(a, b)]}$" if axiom(a, b) in AXIOM_TEXT
                                       else f"{axiom(a, b)}" if axiom(a, b) else
                                       "не подходит ни под одну из схем A1–A11") for k, (a, b) in enumerate(items))
        body = (f"## Условие\n\n{CONV} Какой аксиомной схеме $S^1$ соответствует каждая формула? Если никакой — "
                f"так и скажите.\n\n{cond_}\n\n## Ответ\n\n{ans}\n\n## Решение\n\nСхемы — с. 15–17.\n\n{sol}")
        out.append(card(3, "C", "iso", "sym", "short", "S1, аксиомы", body, "какая-аксиома"))
    for _ in range(5):
        X, Y, Z = pick(3)
        k = rnd.choice(["R1", "R2", "R3"])
        if k == "R1":
            p1, p2 = (C(X, Y), C(Y, X)), (C(Y, X), Y)
            res = (C(X, Y), Y)
            given = f"(1) ${ftex(*p1)}$ и (2) ${ftex(*p2)}$"
        elif k == "R2":
            p1, p2 = (C(X, Y), X), (C(X, Y), N(N(Y)))
            res = (C(X, Y), C(X, N(N(Y))))
            given = f"(1) ${ftex(*p1)}$ и (2) ${ftex(*p2)}$"
        else:
            p1, p2 = (N(N(X)), X), (X, N(N(X)))
            zf = D(C(N(N(X)), Y), Z)
            res = (zf, D(C(X, Y), Z))
            given = (f"(1) ${ftex(*p1)}$ и (2) ${ftex(*p2)}$; высказывание $z$ — ${tex(zf)}$; замените в нём "
                     f"вхождение ${tex(N(N(X)))}$")
        body = (f"## Условие\n\n{CONV} Какую формулу даёт правило {k}, если даны {given}?\n\n## Ответ\n\n"
                f"${ftex(*res)}$\n\n## Решение\n\nПравила вывода $S^1$ — с. 17: R1 — если $x \\vdash y$ и "
                "$y \\vdash z$, то $x \\vdash z$; R2 — если $x \\vdash y$ и $x \\vdash z$, то $x \\vdash yz$; R3 — "
                "если $x \\vdash y$ и $y \\vdash x$, то $z \\vdash v$, где $v$ получается из $z$ заменой вхождения "
                "$x$ (не обязательно всех) высказыванием $y$.")
        assert not check([(p1[0], p1[1], "A3" if axiom(*p1) == "A3" else axiom(*p1) or "A1"),
                          (p2[0], p2[1], axiom(*p2) or "A1"), (res[0], res[1], (k, 1, 2))]) or k == "R2"
        out.append(card(3, "D", "iso", "sym", "short", "S1, правила вывода", body, "применить-правило"))
    return out


def level4():
    out = []
    tpls = TEMPLATES2 + TEMPLATES3
    for k in range(12):
        goal, lines = derivation(tpls[k % len(tpls)])
        if k % 2 == 0:
            hide = sorted(rnd.sample(range(1, len(lines) + 1), min(2, len(lines))))
            task = "В выводе не указаны основания некоторых шагов. Восстановите их."
            shown = show(lines, hide_why=hide)
            ans = "; ".join(f"{n} — {why_text(lines[n - 1][2])}" for n in hide)
        else:
            rs = [n for n, l in enumerate(lines, 1) if not isinstance(l[2], str)]
            n = rs[-1] if rs else len(lines)
            task = "В выводе пропущена формула одного шага. Восстановите её."
            shown = show(lines, hide_formula=(n,))
            ans = f"шаг {n}: ${ftex(lines[n - 1][0], lines[n - 1][1])}$"
        body = (f"## Условие\n\n{CONV} Вывод в $S^1$ формулы ${ftex(*goal)}$. {task}\n\n{shown}\n\n## Ответ\n\n"
                f"{ans}\n\n## Решение\n\nПолный вывод (аксиомы — с. 15–17, правила — с. 17):\n\n{show(lines)}")
        out.append(card(4, "D", "complete", "sym", "short", "S1, вывод", body, "дополнение-вывода"))
    made = 0
    while made < 6:
        goal, lines = derivation()
        c = corrupt(lines)
        if not c:
            continue
        new, n, right = c
        body = (f"## Условие\n\n{CONV} В выводе формулы ${ftex(*goal)}$ ровно в одном шаге неверно указано "
                f"основание. Найдите шаг и исправьте.\n\n{show(new)}\n\n## Ответ\n\nШаг {n}: верно — {right}.\n\n"
                f"## Решение\n\nПроверяем каждый шаг по аксиомным схемам (с. 15–17) и правилам (с. 17). Верный вывод:"
                f"\n\n{show(lines)}")
        out.append(card(4, "E", "complete", "sym", "short", "S1, вывод, диагностика", body, "ошибка-в-выводе"))
        made += 1
    return out


def level5():
    out = []
    order = TEMPLATES2 + TEMPLATES3 + [T1, T3, T5, T6, T10, T12]
    for tpl in order:
        goal, lines = derivation(tpl)
        body = (f"## Условие\n\n{CONV} Выведите в $S^1$ формулу ${ftex(*goal)}$. Оформите вывод как в книге: шаги "
                f"пронумерованы, в квадратных скобках — аксиомная схема или правило с номерами шагов.\n\n## Ответ\n\n"
                f"Вывод из {len(lines)} шагов (см. решение).\n\n## Решение\n\n{show(lines)}\n\nВозможны и другие выводы; "
                "проверяйте каждый шаг по схемам A1–A14 (с. 15–17) и правилам R1–R3 (с. 17).")
        out.append(card(5, "D", "iso", "sym", "proof", "S1, вывод", body, "вывод"))
    made = 0
    while made < 4:
        goal, lines = derivation(rnd.choice([T5, T10, T11, T12]))
        c = corrupt(lines)
        if not c:
            continue
        new, n, right = c
        body = (f"## Условие\n\n{CONV} Проверьте вывод формулы ${ftex(*goal)}$. Есть ли в нём ошибка? Если есть — "
                f"укажите шаг и исправьте.\n\n{show(new)}\n\n## Ответ\n\nОшибка в шаге {n}: верно — {right}.\n\n"
                f"## Решение\n\nВерный вывод:\n\n{show(lines)}")
        out.append(card(5, "E", "open", "sym", "short", "S1, вывод, диагностика", body, "проверка-вывода"))
        made += 1
    return out


def main():
    cards = level1() + level2() + level3() + level4() + level5()
    (ROOT / "drafts").mkdir(exist_ok=True)
    (ROOT / "drafts" / "01.01-gen.md").write_text("\n=====\n".join(cards), encoding="utf-8")
    print(len(cards))


if __name__ == "__main__":
    main()
