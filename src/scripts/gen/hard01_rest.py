#!/usr/bin/env python3
"""Усложнение оставшейся части гл. 1 (занятия 6–16) по образцу занятия 10.

Заменяет в src/data/zadachi/01.md карточки с теми же номерами (глава и параграф сохраняются):
  § 1 — 001–004: полная скобочная запись по D2 и обратно (с диагностикой двух ошибок), вывод с n-членной
        конъюнкцией; 049–070, 076–102 (короткие выводы и проверки в 3–5 строк) — выводы в 8–12 строк, цепочки
        замен по R3 (A1/A2, A4, A5/A6, A7/A8, A9/A10), дополнение таких выводов, две ошибки в выводе, «исследуйте
        доказуемость» с длинным выводом или опровергающими значениями, «ложные выводы» недоказуемых формул;
        021, 026, 029, 030, 059–062, 082, 086, 090, 094 — метатеоремы ступеней 8–10 (вручную, hard01_rest_hand.py);
  § 3 — сокращения D1, D2: выводы с сокращениями, раскрытие и свёртка длинных формул, диагностика, две
        метатеоремы (★);
  § 4–9 — задачи ступеней 1–3 заменены: MT1 § 4 для длинных формул, значения и обратные задачи § 5, MT1 § 6,
        канонические формы § 7 с тремя буквами, таблицы независимости § 8 для длинных теорем, подстановка в
        длинный вывод § 9.
Все выводы проверяются s1.check (s1.check2 там, где разрешены теоремные схемы § 2), значения и доказуемость —
s1.value / s1.strong_tautology, таблицы — indep.

Карточки 01.01-021 и 01.01-026 раньше давал hard01_01.py — теперь он их пропускает. Порядок запуска:
hard01_01.py, hard01_02.py, hard01_series.py, затем этот генератор.

Запуск: python3 src/scripts/gen/hard01_rest.py
"""
import importlib.util
import itertools
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "gen"))
import indep as IND  # noqa: E402
import s1 as S  # noqa: E402
from s1 import (C, D, IMP, N, V, atoms, check, check2, counterexample, new_atoms, strong_tautology,  # noqa: E402
                tautology, value)
from open_form import test_like  # noqa: E402

x, y, z, u, w = (V(c) for c in "xyzuw")
L = "абвгдежз"
CONV = "Буквы $x, y, z, u, w$ — элементарные высказывания; запись по соглашению книги (с. 15)."
CRIT = ("Критерий: формула доказуема в $S^1$ тогда и только тогда, когда она — сильная тавтология, то есть тавтология, "
        "в заключение которой не входят элементарные высказывания, отсутствующие в посылке (§ 4, MT1, с. 21; § 5, MT1, "
        "с. 22; § 7, MT6, с. 32).")
RULES = ("Правила $S^1$ (с. 17): R1 — если $x \\vdash y$ и $y \\vdash z$, то $x \\vdash z$; R2 — если $x \\vdash y$ и "
         "$x \\vdash z$, то $x \\vdash yz$; R3 — если $x \\vdash y$ и $y \\vdash x$, то $z \\vdash v$, где $v$ получается "
         "из $z$ заменой по крайней мере одного (не обязательно всех) вхождения $x$ высказыванием $y$ (с. 17, 24).")
SCH = ("Схемы (с. 15–16): A1 $x \\vdash \\sim\\sim x$; A2 $\\sim\\sim x \\vdash x$; A3 $xy \\vdash x$; A4 $xy \\vdash yx$; "
       "A5 $x^1 \\ldots x^n \\vdash y$ и A6 $y \\vdash x^1 \\ldots x^n$, где $y$ отличается от $x^1 \\ldots x^n$ лишь "
       "расстановкой скобок; A7 $\\sim(xy) \\vdash \\sim xy : x\\sim y : \\sim x\\sim y$; A8 — обратная к A7; "
       "A9 $\\sim(x : y) \\vdash xy : \\sim x\\sim y$; A10 — обратная к A9.")


def load_h(seed, allow_t):
    """Свежая копия генератора выводов hard01_02 со своим зерном."""
    spec = importlib.util.spec_from_file_location(f"h{seed}", ROOT / "scripts" / "gen" / "hard01_02.py")
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    m.rnd = random.Random(seed)
    m.ALLOW_T = allow_t
    if not allow_t:
        m.check2 = check
        m.WRONG = {"A3": "A4", "A4": "A3", "A1": "A2", "A2": "A1", "A7": "A9", "A9": "A7"}
    return m


h1 = load_h(1970_1101, False)          # § 1: только аксиомные схемы и правила
rnd = random.Random(1970_1100)


def tex(f):
    return S.tex(f)


def ftex(a, b):
    return S.ftex(a, b)


def why_text(wh):
    return wh if isinstance(wh, str) else f"{wh[0]}: {wh[1]}, {wh[2]}"


def show(lines, ft=None):
    ft = ft or ftex
    return "\n".join(f"{n}. ${ft(a, b)}$ [{why_text(wh)}]" for n, (a, b, wh) in enumerate(lines, 1))


def show_hidden(lines, hide_why, hide_f, ft=None):
    ft = ft or ftex
    out = []
    for n, (a, b, wh) in enumerate(lines, 1):
        f = "…" if n in hide_f else f"${ft(a, b)}$"
        out.append(f"{n}. {f} [{'…' if n in hide_why else why_text(wh)}]")
    return "\n".join(out)


def env_t(e):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(e.items()))


def card(level, typ, step, ans_kind, src, tags, cond, ans, sol, form="sym", gen=True, series=None):
    return dict(level=level, type=typ, step=step, form=form, answer=ans_kind, source=src, tags=tags, cond=cond,
                ans=ans, sol=sol, gen=gen, series=series)


# ======================================================================== § 1
SRC1 = "с. 15–17, гл. 1, § 1"


def size(f):
    return len(tex(f))


def paths(f, p=()):
    """Все вхождения (пути) частей формулы."""
    yield p, f
    if f[0] == "neg":
        yield from paths(f[1], p + (1,))
    elif f[0] in ("conj", "dis"):
        for i, c in enumerate(f[1]):
            yield from paths(c, p + (i,))


def put(f, p, val):
    if not p:
        return val
    if f[0] == "neg":
        return N(put(f[1], p[1:], val))
    kids = list(f[1])
    kids[p[0]] = put(kids[p[0]], p[1:], val)
    return (f[0], tuple(kids))


def equiv_moves(s, allow_a1=False):
    """Пары взаимной выводимости по аксиомным схемам: [(s', схема s ⊢ s', схема s' ⊢ s)]."""
    out = []
    if s[0] == "neg" and s[1][0] == "neg":
        out.append((s[1][1], "A2", "A1"))
    if s[0] == "conj" and len(s[1]) == 2:
        a, b = s[1]
        if a != b:
            out.append((C(b, a), "A4", "A4"))
        if a[0] == "conj" and len(a[1]) == 2:
            out.append((C(a[1][0], a[1][1], b), "A6", "A5"))
    if s[0] == "conj" and len(s[1]) == 3:
        a, b, c = s[1]
        out.append((C(C(a, b), c), "A5", "A6"))
        out.append((C(a, C(b, c)), "A5", "A6"))
    if s[0] == "neg" and s[1][0] == "conj" and len(s[1][1]) == 2:
        a, b = s[1][1]
        out.append((D(C(N(a), b), C(a, N(b)), C(N(a), N(b))), "A7", "A8"))
    if s[0] == "neg" and s[1][0] == "dis" and len(s[1][1]) == 2:
        a, b = s[1][1]
        out.append((D(C(a, b), C(N(a), N(b))), "A9", "A10"))
    if s[0] == "dis" and len(s[1]) == 3:
        m = s[1]
        if (m[0][0] == "conj" and len(m[0][1]) == 2 and m[0][1][0][0] == "neg"):
            a, b = m[0][1][0][1], m[0][1][1]
            if m == (C(N(a), b), C(a, N(b)), C(N(a), N(b))):
                out.append((N(C(a, b)), "A8", "A7"))
    if s[0] == "dis" and len(s[1]) == 2:
        m = s[1]
        if m[0][0] == "conj" and len(m[0][1]) == 2:
            a, b = m[0][1]
            if m[1] == C(N(a), N(b)):
                out.append((N(D(a, b)), "A10", "A9"))
    if allow_a1 and s[0] in ("v", "neg") and size(s) <= 4:
        out.append((N(N(s)), "A1", "A2"))
    return out


def r3_chain(steps=3, start=None, maxlen=40):
    """Цепочка замен по R3: z0 ⊢ z1 ⊢ … ; строки — пары схем, R3, R1. Проверяется s1.check."""
    for _ in range(4000):
        z0 = start() if start else r3_start()
        zs, lines, used = [z0], [], set()
        last_r = None
        ok = True
        for k in range(steps):
            zk = zs[-1]
            opts = []
            for p, s in paths(zk):
                for s2, f1, f2 in equiv_moves(s, allow_a1=(rnd.random() < 0.15)):
                    if (s2, s) in used:
                        continue
                    opts.append((p, s, s2, f1, f2))
            if not opts:
                ok = False
                break
            p, s, s2, f1, f2 = rnd.choice(opts)
            occ = [q for q, t in paths(zk) if t == s]
            chosen = occ if (len(occ) > 1 and rnd.random() < 0.5) else [p]
            nz = zk
            for q in chosen:
                nz = put(nz, q, s2)
            if size(nz) > maxlen or nz in zs:
                ok = False
                break
            used.add((s, s2))
            lines.append((s, s2, f1))
            lines.append((s2, s, f2))
            lines.append((zk, nz, ("R3", len(lines) - 1, len(lines))))
            r = len(lines)
            if last_r is not None:
                lines.append((z0, nz, ("R1", last_r, r)))
                r = len(lines)
            last_r = r
            zs.append(nz)
        if ok and not check(lines) and strong_tautology(z0, zs[-1]) and z0 != zs[-1]:
            return lines
    raise RuntimeError("цепочка R3 не построена")


def r3_start():
    X, Y, Z = rnd.sample([x, y, z, N(x), N(y), u, N(z), w], 3)
    return rnd.choice([C(N(N(X)), D(Y, Z)), D(N(C(X, Y)), Z), C(N(D(X, Y)), Z), C(X, Y, N(N(Z))),
                       N(C(C(X, Y), Z)), D(C(X, N(N(Y))), N(D(Y, Z))), C(N(C(X, Y)), N(N(Z))),
                       N(N(C(D(X, Y), Z))), C(D(X, Y), N(C(Y, Z)))])


def r3_deriv_card(level=None):
    lines = r3_chain(3)
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} Выведите в $S^1$ формулу ${ftex(a, b)}$, пользуясь только аксиомными схемами и правилами $S^1$ "
            f"(теоремные схемы § 2 не применять). Указание: посылку надо преобразовывать заменой её частей по R3. "
            f"{SCH} {RULES}")
    ans = f"Например, вывод в {len(lines)} строк (см. решение); последняя строка — ${ftex(a, b)}$ [{why_text(lines[-1][2])}]."
    sol = ("Каждая замена части $s$ на $s'$ требует двух строк $s \\vdash s'$ и $s' \\vdash s$ (пары схем A1/A2, A4/A4, "
           "A5/A6, A7/A8, A9/A10) и строки по R3; цепочку замен соединяет R1.\n\n" + show(lines)
           + "\n\nСхемы — с. 15–16; правила — с. 17.")
    return card(level or (7 if len(lines) >= 10 else 6), "D", "open", "proof", SRC1, "S1, вывод, R3", cond, ans, sol)


def build_deriv_card():
    lines = h1.build_ok(rnd.choice([10, 11, 12]), least=8)
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} Выведите в $S^1$ формулу ${ftex(a, b)}$, пользуясь только аксиомными схемами A1–A14 и правилами "
            f"R1–R3 (теоремные схемы § 2 не применять). {SCH} {RULES}")
    ans = f"Например, вывод в {len(lines)} строк (см. решение); последняя строка — ${ftex(a, b)}$ [{why_text(lines[-1][2])}]."
    sol = show(lines) + "\n\nСхемы — с. 15–16; правила R1, R2 — с. 17."
    assert not check(lines)
    return card(7 if len(lines) >= 10 else 6, "D", "open", "proof", SRC1, "S1, вывод", cond, ans, sol)


def r3_complete_card():
    lines = r3_chain(3)
    n = len(lines)
    r3 = [i for i, (*_, wh) in enumerate(lines, 1) if isinstance(wh, tuple) and wh[0] == "R3"]
    ax = [i for i, (*_, wh) in enumerate(lines, 1) if isinstance(wh, str)]
    r1 = [i for i, (*_, wh) in enumerate(lines, 1) if isinstance(wh, tuple) and wh[0] == "R1"]
    hide_f = {rnd.choice(r3[:-1]), rnd.choice(ax[2:])}
    hide_why = set(rnd.sample([i for i in ax if i not in hide_f], 2)) | {rnd.choice(r1)} | {r3[-1]}
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} В выводе формулы ${ftex(a, b)}$ пропущены формулы некоторых строк и основания некоторых шагов "
            f"(«…»). Восстановите их. {SCH} {RULES}\n\n{show_hidden(lines, hide_why, hide_f)}")
    parts = []
    for k in sorted(hide_why | hide_f):
        la, lb, wh = lines[k - 1]
        s = f"{k} — " + (f"${ftex(la, lb)}$ " if k in hide_f else "") + (f"[{why_text(wh)}]" if k in hide_why else "")
        parts.append(s.strip())
    sol = ("Пропущенную формулу строки по R3 восстанавливаем по строке-результату: в ней посылка — заключение "
           "предыдущего результата, а заключение получается заменой части по паре соседних строк; пропущенную строку "
           "пары — обращением её соседки. Полный вывод:\n\n" + show(lines) + "\n\nСхемы — с. 15–16; правила — с. 17.")
    assert n >= 10
    return card(5, "D", "complete", "build", SRC1, "S1, вывод, R3, дополнение", cond, "; ".join(parts), sol)


R3_WRONG = {"A1": "A2", "A2": "A1", "A7": "A8", "A8": "A7", "A9": "A10", "A10": "A9", "A5": "A6", "A6": "A5"}


def r3_diag_card():
    for _ in range(500):
        lines = r3_chain(3)
        ax = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, str) and wh in R3_WRONG]
        rr = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, tuple)]
        if not ax:
            continue
        i, j = rnd.choice(ax), rnd.choice(rr)
        bad = list(lines)
        a, b, wh = bad[i]
        bad[i] = (a, b, R3_WRONG[wh])
        a2, b2, wh2 = bad[j]
        new_rule = "R1" if wh2[0] == "R3" else "R3"
        bad[j] = (a2, b2, (new_rule, wh2[1], wh2[2]))
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in check(bad)})
        if steps == sorted([i + 1, j + 1]):
            break
    else:
        raise RuntimeError("нет вывода для диагностики")
    exp = []
    for k in sorted([i, j]):
        a, b, wh = lines[k]
        if k == i:
            exp.append(f"Шаг {k + 1}: ${ftex(a, b)}$ — пример схемы {wh}, а не {R3_WRONG[wh]}: посылка и заключение "
                       f"переставлены по сравнению со схемой {R3_WRONG[wh]} (с. 15–16).")
        elif wh[0] == "R3":
            exp.append(f"Шаг {k + 1}: строки {wh[1]} и {wh[2]} — пара $s \\vdash s'$, $s' \\vdash s$, а результат получен "
                       f"заменой вхождения $s$ — это R3; R1 требовал бы, чтобы посылка результата была посылкой строки "
                       f"{wh[1]} (с. 17).")
        else:
            exp.append(f"Шаг {k + 1}: заключение строки {wh[1]} — посылка строки {wh[2]}, результат соединяет посылку "
                       f"первой и заключение второй — это R1; для R3 строки должны быть обращениями друг друга (с. 17).")
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} В выводе формулы ${ftex(a, b)}$ ровно два основания указаны неверно. Найдите их, объясните, "
            f"какое правило или схема нарушены, и исправьте. {SCH} {RULES}\n\n{show(bad)}")
    p, q = sorted([i, j])
    ans = f"Шаг {p + 1}: верно [{why_text(lines[p][2])}]; шаг {q + 1}: верно [{why_text(lines[q][2])}] (с. 15–17)."
    sol = "\n".join(exp) + "\n\nИсправленный вывод:\n\n" + show(lines)
    return card(6, "E", "vary", "text", SRC1, "S1, вывод, R3, диагностика", cond, ans, sol)


def mutate_concl(b):
    """Правдоподобное искажение заключения: отрицание части, перестановка знака."""
    ps = [p for p, s in paths(b) if s[0] in ("v", "conj", "neg")]
    p = rnd.choice(ps)
    s = dict(paths(b))[p]
    s2 = s[1] if s[0] == "neg" else N(s)
    return put(b, p, s2)


def research_card():
    """Исследуйте доказуемость: доказуемая (длинный вывод), нетавтология, тавтология с новой буквой."""
    kind = rnd.choice(["yes", "yes", "non", "new"])
    for _ in range(400):
        lines = r3_chain(3) if rnd.random() < 0.4 else h1.build_ok(rnd.choice([10, 11]), least=8)
        a, b = lines[-1][0], lines[-1][1]
        if kind == "yes":
            break
        if kind == "non":
            b2 = mutate_concl(b)
            if not tautology(a, b2) and size(b2) <= 40:
                b = b2
                break
        else:
            nb = rnd.choice([u, w]) if not ({"u", "w"} <= atoms(a)) else None
            if nb is None or nb[1] in atoms(a):
                continue
            b2 = rnd.choice([D(b, C(nb, N(nb))), C(b, N(C(nb, N(nb))))])
            if tautology(a, b2) and size(b2) <= 44:
                b = b2
                break
    cond = (f"{CONV} Исследуйте доказуемость в $S^1$ формулы ${ftex(a, b)}$: доказуемую выведите (только аксиомные "
            f"схемы и правила $S^1$, без теоремных схем § 2), недоказуемость обоснуйте. {CRIT}")
    if kind == "yes":
        ans = f"Доказуема: вывод в {len(lines)} строк (см. решение)."
        sol = "Доказуема. Вывод:\n\n" + show(lines) + "\n\nСхемы — с. 15–16; правила — с. 17."
        assert strong_tautology(a, b)
    elif kind == "non":
        e = counterexample(a, b)
        ans = f"Недоказуема: при {env_t(e)} посылка — 1, заключение — 0."
        sol = (f"При {env_t(e)} посылка ${tex(a)}$ имеет значение {value(a, e)}, а заключение ${tex(b)}$ — "
               f"{value(b, e)} (главная интерпретация, с. 22). Формула не тавтология, по § 5, MT1 (с. 22) — не теорема "
               "$S^1$. Выводить её бесполезно: любая попытка где-то нарушит схему или правило.")
        assert not tautology(a, b)
    else:
        na = ", ".join(f"${t}$" for t in sorted(new_atoms(a, b)))
        ans = f"Недоказуема: в заключение входит {na}, которого нет в посылке (MT1 § 4, с. 21)."
        sol = (f"Формула — тавтология (заключение принимает значение 1 всякий раз, когда посылка равна 1), но в её "
               f"заключение входит {na}, отсутствующее в посылке. По § 4, MT1 (с. 21) теорема $S^1$ таких букв в "
               "заключении не содержит. Формула недоказуема, хотя и тавтологична: это не сильная тавтология (§ 7, D1, "
               "с. 25).")
        assert tautology(a, b) and new_atoms(a, b)
    return card(6, "C", "open", "proof" if kind == "yes" else "short", "с. 15–17, 21–22, 32, гл. 1, § 1",
                "S1, доказуемость", cond, ans, sol)


NEAR = {"A3": lambda a, b: N(b) if b[0] != "neg" else b[1],
        "A2": lambda a, b: N(b),
        "A4": lambda a, b: C(a[1][1], N(a[1][0])) if a[1][0][0] != "neg" else C(a[1][1], a[1][0][1]),
        "A7": lambda a, b: D(b[1][0], b[1][1], b[1][0]),
        "A9": lambda a, b: D(b[1][0], C(N(a[1][1][0]), a[1][1][1]))}
NEAR_TXT = {"A3": "в заключение A3 входит первый член конъюнкции без изменений",
            "A2": "A2 снимает сразу два знака отрицания",
            "A4": "A4 лишь переставляет члены конъюнкции, не меняя их",
            "A7": "по A7 три члена дизъюнкции различны: $\\sim xy$, $x\\sim y$, $\\sim x\\sim y$",
            "A9": "по A9 второй член — $\\sim x\\sim y$, отрицания стоят перед обоими членами"}


def apply_scheme(name, q):
    """Заключение схемы name при посылке q (или None, если схема к q не применима)."""
    two = q[0] == "conj" and len(q[1]) == 2
    if name == "A1":
        return N(N(q))
    if name == "A2":
        return q[1][1] if q[0] == "neg" and q[1][0] == "neg" else None
    if name == "A3":
        return q[1][0] if two else None
    if name == "T1":
        return q[1][1] if two else None
    if name == "A4":
        return C(q[1][1], q[1][0]) if two else None
    if name in ("A7", "A9"):
        inner = "conj" if name == "A7" else "dis"
        if q[0] == "neg" and q[1][0] == inner and len(q[1][1]) == 2:
            return S.instance(name, *q[1][1])[1]
        return None
    if name == "T6":
        return D(q[1][1], q[1][0]) if q[0] == "dis" and len(q[1]) == 2 else None
    return None


def false_deriv(lines, chk=check):
    """Искажает заключение одной строки-схемы и пересчитывает зависящие строки. Ровно одна ошибка."""
    cand = [i for i, (_, _, wh) in enumerate(lines) if isinstance(wh, str) and wh in NEAR]
    rnd.shuffle(cand)
    for i in cand:
        a, b, wh = lines[i]
        try:
            b2 = NEAR[wh](a, b)
        except (IndexError, TypeError):
            continue
        new = list(lines)
        new[i] = (a, b2, wh)
        changed = {i}
        okk = True
        for k in range(i + 1, len(new)):
            ak, bk, whk = new[k]
            if isinstance(whk, str):
                # строка-схема с посылкой — изменённой формулой: студент применяет ту же схему к новой формуле
                src = [c for c in changed if ak == lines[c][1] and new[c][1] != lines[c][1]]
                if src:
                    na = new[src[0]][1]
                    nb = apply_scheme(whk, na)
                    if nb is None:
                        okk = False
                        break
                    new[k] = (na, nb, whk)
                    changed.add(k)
                continue
            r, p, q = whk
            (a1, b1, _), (a2, b2_, _) = new[p - 1], new[q - 1]
            if r == "R1":
                nf = (a1, b2_, whk)
            elif r == "R2":
                nf = (a1, C(b1, b2_), whk)
            else:
                okk = False
                break
            if nf != new[k]:
                new[k] = nf
                changed.add(k)
        if not okk:
            continue
        errs = chk(new)
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        fa, fb = new[-1][0], new[-1][1]
        if steps == [i + 1] and not tautology(fa, fb) and len(changed) >= 2:
            return new, i
    return None


FALSE_WANT = ["A9", "A3", "A4", "A9", "A3", "A4"]


def false_card():
    want = FALSE_WANT.pop(0) if FALSE_WANT else None
    r = None
    for k in range(600):
        lines = h1.build_ok(rnd.choice([9, 10, 11]), least=8)
        r2 = false_deriv(lines)
        if r2 and (want is None or r2[0][r2[1]][2] == want or k > 200):
            r = r2
            break
    if r is None:
        raise RuntimeError("ложный вывод не построен")
    bad, i = r
    fa, fb = bad[-1][0], bad[-1][1]
    e = counterexample(fa, fb)
    wh = bad[i][2]
    cond = (f"{CONV} Студент утверждает, что вывел в $S^1$ формулу ${ftex(fa, fb)}$:\n\n{show(bad)}\n\nДокажите, что "
            f"формула недоказуема в $S^1$, и найдите шаг, на котором нарушена схема или правило. {SCH} {RULES} {CRIT}")
    ans = (f"Недоказуема: при {env_t(e)} посылка — 1, заключение — 0 (§ 5, MT1, с. 22). Ошибка в шаге {i + 1}: "
           f"${ftex(bad[i][0], bad[i][1])}$ — не пример {wh} (с. 15–16).")
    sol = (f"1. При {env_t(e)} посылка ${tex(fa)}$ равна {value(fa, e)}, заключение ${tex(fb)}$ — {value(fb, e)}: формула "
           f"не тавтология и по § 5, MT1 (с. 22) не может быть теоремой $S^1$. Значит, в выводе есть ошибка.\n"
           f"2. Шаг {i + 1}: ${ftex(bad[i][0], bad[i][1])}$ [{wh}] — не пример схемы {wh}: {NEAR_TXT[wh]} (с. 15–16). "
           f"По схеме должно быть ${ftex(lines_fix(bad, i)[0], lines_fix(bad, i)[1])}$.\n"
           "3. Остальные шаги применены правильно, но опираются на ошибочную строку, и ошибка переходит в "
           "заключение (R1, R2, с. 17).")
    return card(6, "E", "open", "text", "с. 15–17, 22, гл. 1, § 1", "S1, вывод, диагностика", cond, ans, sol)


def lines_fix(bad, i):
    a, b, wh = bad[i]
    out = {"A3": lambda: a[1][0], "A2": lambda: a[1][1], "A4": lambda: C(a[1][1], a[1][0]),
           "A7": lambda: S.instance("A7", *a[1][1])[1], "A9": lambda: S.instance("A9", *a[1][1])[1]}[wh]()
    return a, out


# ---- § 1, 001–004: запись по D2 и соглашению, вывод с n-членной конъюнкцией
def full(f):
    """Полная запись по D2 § 1 (с. 15): все скобки и знаки ·."""
    k = f[0]
    if k == "v":
        return f[1]
    if k == "neg":
        return f"\\sim {full(f[1])}" if f[1][0] in ("v", "neg") else f"\\sim {full(f[1])}"
    sep = " \\cdot " if k == "conj" else " : "
    return "(" + sep.join(full(a) for a in f[1]) + ")"


def rand_tree(depth, letters):
    if depth == 0 or rnd.random() < 0.15:
        a = V(rnd.choice(letters))
        return N(a) if rnd.random() < 0.3 else a
    k = rnd.random()
    if k < 0.15:
        inner = rand_tree(depth - 1, letters)
        return N(inner) if inner[0] in ("conj", "dis") else inner
    n = 3 if rnd.random() < 0.25 else 2
    op = C if k < 0.6 else D
    return op(*[rand_tree(depth - 1, letters) for _ in range(n)])


def dup(f):
    """Одинаковые члены конъюнкции или дизъюнкции, двойное отрицание буквы."""
    if f[0] == "v":
        return False
    if f[0] == "neg":
        return f[1][0] == "neg" or dup(f[1])
    return len(set(f[1])) < len(f[1]) or any(dup(c) for c in f[1])


def rand_ok(depth, letters):
    while True:
        f = rand_tree(depth, letters)
        if not dup(f):
            return f


def ops(f):
    if f[0] == "v":
        return 0
    if f[0] == "neg":
        return 1 + ops(f[1])
    return len(f[1]) - 1 + sum(ops(a) for a in f[1])


def main_op(f):
    return {"neg": "$\\sim$", "conj": "конъюнкция $\\cdot$", "dis": "сильная дизъюнкция $:$"}[f[0]]


def struct_ok(f):
    """Есть и вложенная конъюнкция в конъюнкции, и дизъюнкция-член конъюнкции (где скобки нужны)."""
    s = repr(f)
    return f[0] != "v" and 18 <= len(tex(f)) <= 34 and "dis" in s and "conj" in s


def full_card():
    items = []
    while len(items) < 3:
        f = rand_ok(3, ["x", "y", "z", "u"])
        if struct_ok(f) and f not in items:
            items.append(f)
    body = "\n".join(f"{L[k]}) ${tex(f)}$" for k, f in enumerate(items))
    cond = (f"{CONV} По D2 § 1 (с. 15) высказывания $S^1$ имеют вид $\\sim x$, $(x^1 \\cdot \\ldots \\cdot x^n)$, "
            "$(x^1 : \\ldots : x^n)$ ($n \\geq 2$); по соглашению (с. 15) скобки в ряде случаев опускаются — конъюнкция "
            "связывает сильнее дизъюнкции — и знаки конъюнкции не пишутся. Восстановите для каждого высказывания полную "
            "запись по D2 (все скобки и знаки $\\cdot$), назовите главный оператор и подсчитайте число вхождений "
            f"операторов.\n\n{body}")
    ans = "; ".join(f"{L[k]}) ${full(f)}$, главный — {main_op(f)}, операторов {ops(f)}" for k, f in enumerate(items))
    sol = ("Скобки восстанавливаем от конъюнкций, записанных рядом: они связывают сильнее $:$; член, заключённый в "
           "скобки, — отдельное высказывание; $n$-членная конъюнкция $(x^1 \\cdot \\ldots \\cdot x^n)$ (D2, п. 3) — одно "
           "высказывание, а не вложенные двучленные. В $(x^1 \\cdot \\ldots \\cdot x^n)$ и $(x^1 : \\ldots : x^n)$ "
           "по $n - 1$ вхождений оператора.\n\n" + "\n".join(f"{L[k]}) ${full(f)}$" for k, f in enumerate(items)))
    return card(4, "A", "iso", "build", "с. 15, гл. 1, § 1", "S1, запись, D2", cond, ans, sol)


def drop_mut(f):
    """Ошибка опускания нужных скобок: (x : y)z → x : yz; (xy)z → xyz. Возвращает новое дерево или None."""
    for p, s in paths(f):
        if s[0] == "conj" and s[1][0][0] == "dis" and len(s[1][0][1]) == 2 and len(s[1]) == 2:
            a, b = s[1][0][1]
            return put(f, p, D(a, C(b, s[1][1]))), "dis"
    for p, s in paths(f):
        if s[0] == "conj" and any(c[0] == "conj" for c in s[1]):
            flat = []
            for c in s[1]:
                flat += list(c[1]) if c[0] == "conj" else [c]
            return put(f, p, C(*flat)), "conj"
    return None


def full_diag_card():
    items, kinds = [], []
    while len(items) < 4:
        f = rand_ok(3, ["x", "y", "z"])
        if f[0] == "v" or not (16 <= len(tex(f)) <= 30) or f in items:
            continue
        need = ["dis", "conj", None, None][len(items)]
        if need:
            m = drop_mut(f)
            if not m or m[1] != need or tex(m[0]) == tex(f):
                continue
        items.append(f)
        kinds.append(need)
    order = list(range(4))
    rnd.shuffle(order)
    items = [items[i] for i in order]
    kinds = [kinds[i] for i in order]
    shown = [tex(drop_mut(f)[0]) if k else tex(f) for f, k in zip(items, kinds)]
    body = "\n".join(f"{L[k]}) ${full(f)}$ → ${s}$" for k, (f, s) in enumerate(zip(items, shown)))
    cond = (f"{CONV} Студент записал по соглашению книги (с. 15: конъюнкция связывает сильнее дизъюнкции, знаки "
            "конъюнкции не пишутся) четыре высказывания, данные в полной записи по D2 § 1 (с. 15). Ровно в двух записях "
            f"он изменил строение высказывания. Найдите их, объясните, что нарушено, и запишите верно.\n\n{body}")
    ans, sol = [], []
    for k, (f, kd) in enumerate(zip(items, kinds)):
        if kd == "dis":
            ans.append(f"{L[k]}) верно ${tex(f)}$ (нужны скобки члена-дизъюнкции, соглашение, с. 15)")
            sol.append(f"{L[k]}) Член-дизъюнкцию нельзя оставлять без скобок: конъюнкция связывает сильнее, и "
                       f"${shown[k]}$ читается как другое высказывание (соглашение, с. 15). Верно: ${tex(f)}$.")
        elif kd == "conj":
            ans.append(f"{L[k]}) верно ${tex(f)}$ (изменено число членов конъюнкции, D2, п. 3, с. 15)")
            sol.append(f"{L[k]}) Внутренние скобки конъюнкции опускать нельзя: $(x \\cdot y \\cdot z)$ и "
                       f"$((x \\cdot y) \\cdot z)$ — разные высказывания по D2, п. 3 (с. 15); их связывают лишь схемы "
                       f"A5, A6 (с. 16). Верно: ${tex(f)}$.")
    sol.append("Остальные записи верны.")
    ans.append(", ".join(f"{L[k]})" for k, kd in enumerate(kinds) if not kd) + " — без ошибок")
    return card(4, "E", "vary", "text", "с. 15–16, гл. 1, § 1", "S1, запись, D2, диагностика", cond, "; ".join(ans),
                "\n".join(sol))


def fold_card():
    items = []
    while len(items) < 3:
        f = rand_ok(3, ["x", "y", "z", "u"])
        if struct_ok(f) and f not in items:
            items.append(f)
    body = "\n".join(f"{L[k]}) ${full(f)}$" for k, f in enumerate(items))
    cond = (f"{CONV} Высказывания даны в полной записи по D2 § 1 (с. 15). Запишите каждое по соглашению книги "
            "(конъюнкция связывает сильнее дизъюнкции, знаки конъюнкции опускаются) с наименьшим числом скобок, не "
            f"меняя строения высказывания, и объясните, почему оставшиеся скобки опустить нельзя.\n\n{body}")
    ans = "; ".join(f"{L[k]}) ${tex(f)}$" for k, f in enumerate(items))
    sol = ("Опускаются: внешние скобки, скобки конъюнкции — члена дизъюнкции, знаки $\\cdot$. Остаются: скобки "
           "дизъюнкции — члена конъюнкции или дизъюнкции, скобки конъюнкции — члена конъюнкции (иначе изменится число "
           "членов, D2, п. 3) и скобки после $\\sim$ перед составным высказыванием (с. 15).\n\n" + ans)
    return card(4, "A", "vary", "build", "с. 15, гл. 1, § 1", "S1, запись, D2", cond, ans, sol)


def conj_deriv_card():
    """X¹X²X³ ⊢ двучленная конъюнкция членов: A5, A3, A4, R1, R2."""
    while True:
        X, Y, Z = rnd.sample([D(x, N(y)), D(u, w), N(C(y, z)), N(x), D(x, N(z)), u, N(N(w))], 3)
        P = C(X, Y, Z)
        i, j = rnd.sample(range(3), 2)
        if (i, j) != (0, 1):
            break
    M = [X, Y, Z]
    lines = [(P, C(C(X, Y), Z), "A5")]          # 1

    def get(k):
        if k == 2:
            lines.append((C(C(X, Y), Z), C(Z, C(X, Y)), "A4"))
            lines.append((P, C(Z, C(X, Y)), ("R1", 1, len(lines))))
            lines.append((C(Z, C(X, Y)), Z, "A3"))
            lines.append((P, Z, ("R1", len(lines) - 1, len(lines))))
            return len(lines)
        if not any(b == C(X, Y) and a == P for a, b, _ in lines):
            lines.append((C(C(X, Y), Z), C(X, Y), "A3"))
            lines.append((P, C(X, Y), ("R1", 1, len(lines))))
        r = next(n for n, (a, b, _) in enumerate(lines, 1) if a == P and b == C(X, Y))
        if k == 0:
            lines.append((C(X, Y), X, "A3"))
        else:
            lines.append((C(X, Y), C(Y, X), "A4"))
            lines.append((P, C(Y, X), ("R1", r, len(lines))))
            r = len(lines)
            lines.append((C(Y, X), Y, "A3"))
        lines.append((P, M[k], ("R1", r, len(lines))))
        return len(lines)
    li = get(i)
    lj = get(j)
    lines.append((P, C(M[i], M[j]), ("R2", li, lj)))
    assert not check(lines), check(lines)
    a, b = P, C(M[i], M[j])
    cond = (f"{CONV} Выведите в $S^1$ формулу ${ftex(a, b)}$, пользуясь только схемами A3, A4, A5 и правилами R1, R2 "
            "(с. 15–17). Учтите: в трёхчленной конъюнкции $x^1x^2x^3$ нет вхождения двучленной конъюнкции $x^1x^2$, "
            "поэтому A3 к ней сразу не применяется.")
    ans = f"Например, вывод в {len(lines)} строк (см. решение)."
    sol = ("A3 и A4 — схемы для двучленной конъюнкции; трёхчленную сначала переводим по A5 (с. 16) в $(x^1x^2)x^3$. "
           "Затем выделяем нужные члены и соединяем их по R2.\n\n" + show(lines) + "\n\nСхемы — с. 15–16; правила — с. 17.")
    return card(6 if len(lines) >= 9 else 5, "D", "vary", "proof", SRC1, "S1, вывод, A5", cond, ans, sol)


# ======================================================================== § 3: сокращения D1, D2
SRC3 = "с. 18–20, гл. 1, § 2–3"
CONV3 = (CONV + " Сокращения § 3 (с. 20): $(x \\supset y)$ — для $xy : \\sim xy : \\sim x\\sim y$ (D1); "
         "$(x^1 \\vee \\ldots \\vee x^n)$ — для $\\sim(\\sim x^1 \\ldots \\sim x^n)$ (D2); формула с сокращениями — та же "
         "формула, что и после их раскрытия.")


def OR(*xs):
    """D2 § 3 (с. 20): x¹ ∨ … ∨ xⁿ — сокращение для ∼(∼x¹ … ∼xⁿ)."""
    return N(C(*[N(a) for a in xs]))


def match_imp(f):
    if f[0] == "dis" and len(f[1]) == 3 and f[1][0][0] == "conj" and len(f[1][0][1]) == 2:
        a, b = f[1][0][1]
        if f == IMP(a, b):
            return a, b
    return None


def match_or(f):
    if f[0] == "neg" and f[1][0] == "conj" and all(c[0] == "neg" for c in f[1][1]):
        return [c[1] for c in f[1][1]]
    return None


def abbr(f):
    return f[0] != "v" and (match_imp(f) is not None or match_or(f) is not None)


def tex_ab(f):
    k = f[0]
    if k == "v":
        return f[1]
    m = match_imp(f)
    if m:
        return f"({ab_in(m[0])} \\supset {ab_in(m[1])})"
    m = match_or(f)
    if m:
        return "(" + " \\vee ".join(ab_in(a) for a in m) + ")"
    if k == "neg":
        a = f[1]
        return f"\\sim {tex_ab(a)}" if a[0] in ("v", "neg") or abbr(a) else f"\\sim({tex_ab(a)})"
    if k == "conj":
        return "".join(f"({tex_ab(a)})" if a[0] in ("conj", "dis") and not abbr(a) else tex_ab(a) for a in f[1])
    return " : ".join(f"({tex_ab(a)})" if a[0] == "dis" and not abbr(a) else tex_ab(a) for a in f[1])


def ab_in(a):
    return f"({tex_ab(a)})" if a[0] in ("conj", "dis") and not abbr(a) else tex_ab(a)


def ftex_ab(a, b):
    return f"{tex_ab(a)} \\vdash {tex_ab(b)}"


def has_ab(*fs):
    return any("supset" in tex_ab(f) or "vee" in tex_ab(f) for f in fs)


h3 = load_h(1970_1103, True)
h3.tex = tex_ab
h3.ftex = ftex_ab
h3.CONV = CONV3


def premises3():
    X, Y, Z = rnd.sample([x, y, z, N(x), u, w, N(y)], 3)
    return rnd.choice([C(IMP(X, Y), Z), C(Z, OR(X, Y)), N(OR(X, Y)), C(N(N(Z)), OR(X, Y)), N(N(IMP(X, Y))),
                       C(OR(X, Y), N(Z)), C(N(OR(X, Y)), Z)])


h3.premises = premises3
h3_last = []
_h3_build_ok = h3.build_ok


def _rec_build_ok(want, least=7):
    lines = _h3_build_ok(want, least)
    h3_last[:] = [lines[-1][0], lines[-1][1]]
    return lines


h3.build_ok = _rec_build_ok


def build3(want, least):
    for _ in range(300):
        lines = h3.build_ok(want, least)
        if has_ab(lines[-1][0], lines[-1][1]) and sum(has_ab(a, b) for a, b, _ in lines) >= 3:
            return lines
    raise RuntimeError("нет вывода с сокращениями")


def c3_complete():
    lines = build3(rnd.choice([10, 11]), 9)
    sch = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, str)]
    rul = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, tuple)]
    hide_f = set(rnd.sample(sch[1:], 2))
    hide_why = set(rnd.sample([n for n in sch if n not in hide_f], min(2, len(sch) - 2))) | set(rnd.sample(rul[:-1], 2))
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV3} В выводе формулы ${ftex_ab(a, b)}$ пропущены формулы некоторых строк и основания некоторых шагов "
            f"(«…»). Восстановите их; чтобы опознать схему, раскрывайте сокращения. {h3.REF}\n\n"
            f"{show_hidden(lines, hide_why, hide_f, ftex_ab)}")
    parts = []
    for k in sorted(hide_why | hide_f):
        la, lb, wh = lines[k - 1]
        parts.append((f"{k} — " + (f"${ftex_ab(la, lb)}$ " if k in hide_f else "") +
                      (f"[{why_text(wh)}]" if k in hide_why else "")).strip())
    sol = ("Схемы применяются к раскрытой записи: например, $(x \\vee y)$ — это $\\sim(\\sim x\\sim y)$, отрицание "
           "конъюнкции, к нему применима A7; $\\sim(x \\vee y)$ — это $\\sim\\sim(\\sim x\\sim y)$, к нему применима A2 "
           "(D1, D2, с. 20). Полный вывод:\n\n" + show(lines, ftex_ab) + "\n\nСхемы — с. 15–18; правила — с. 17.")
    return card(4, "D", "complete", "build", SRC3, "S1, сокращения, вывод, дополнение", cond, "; ".join(parts), sol)


def rand_ab(depth, letters):
    if depth == 0:
        a = V(rnd.choice(letters))
        return N(a) if rnd.random() < 0.3 else a
    k = rnd.random()
    sub = lambda: rand_ab(depth - 1, letters)  # noqa: E731
    if k < 0.35:
        return IMP(sub(), sub())
    if k < 0.6:
        return OR(sub(), sub())
    if k < 0.7:
        return OR(sub(), sub(), sub())
    if k < 0.85:
        return C(sub(), sub())
    return N(sub())


def ab_formula(lo=14, hi=34):
    while True:
        f = rand_ab(2, ["x", "y", "z"])
        t = tex_ab(f)
        if lo <= len(t) <= hi and "supset" in t and "vee" in t and not dup(f) and len(tex(f)) <= 90:
            return f


def c3_expand():
    f = ab_formula()
    e = {k: rnd.randint(0, 1) for k in sorted(atoms(f))}
    cond = (f"{CONV3} Раскройте все сокращения в высказывании ${tex_ab(f)}$ и запишите результат по соглашению книги "
            f"(с. 15). Затем вычислите значение высказывания при {env_t(e)} по развёрнутой записи (главная "
            "интерпретация, § 5, с. 22) и объясните, почему оно совпадает со значением, вычисленным по смыслу знаков "
            "$\\supset$ («материальная импликация») и $\\vee$ («по крайней мере одно из»).")
    ans = f"${tex(f)}$; значение {value(f, e)}."
    sol = ("Раскрываем изнутри наружу: сначала внутренние сокращения, затем внешнее; каждое $(a \\supset b)$ заменяем на "
           "$ab : \\sim ab : \\sim a\\sim b$, каждое $(a^1 \\vee \\ldots \\vee a^n)$ — на $\\sim(\\sim a^1 \\ldots \\sim a^n)$ "
           f"(D1, D2, с. 20). Результат: ${tex(f)}$. При {env_t(e)} значение — {value(f, e)}. По D1 из трёх членов "
           "$ab : \\sim ab : \\sim a\\sim b$ при любых значениях истинен не более чем один, и все они ложны лишь при "
           "$a = 1$, $b = 0$ — это и есть материальная импликация; $\\sim(\\sim a^1 \\ldots \\sim a^n)$ ложно лишь при всех "
           "$a^i = 0$ — «по крайней мере одно из» (с. 20, 22).")
    return card(5, "D", "iso", "build", "с. 20, 22, гл. 1, § 3, 5", "S1, сокращения, раскрытие", cond, ans, sol)


def c3_fold():
    f = ab_formula(16, 36)
    cond = (f"{CONV3} Запишите высказывание ${tex(f)}$ как можно короче, свернув по D1 и D2 (с. 20) все его части, "
            "которые являются раскрытыми сокращениями (сворачивайте и вложенные части). Объясните, почему ни одну "
            "другую часть свернуть нельзя.")
    ans = f"${tex_ab(f)}$"
    sol = ("Ищем части вида $ab : \\sim ab : \\sim a\\sim b$ (три члена именно в этом виде — D1) и вида "
           "$\\sim(\\sim a^1 \\ldots \\sim a^n)$ (отрицание конъюнкции, все члены которой — отрицания, — D2); сворачиваем "
           f"сначала внутренние. Результат: ${tex_ab(f)}$. Остальные части под D1 и D2 не подходят: у сильной "
           "дизъюнкции не три члена нужного вида или в конъюнкции под $\\sim$ есть член без отрицания.")
    return card(5, "D", "vary", "build", "с. 20, гл. 1, § 3", "S1, сокращения, свёртка", cond, ans, sol)


def wrong_expand(f, kind):
    """Раскрытие с ошибкой: kind='imp' — второй член D1 как x∼y; kind='or' — внешнее ∼ потеряно у D2."""
    m = match_imp(f)
    if kind == "imp" and m:
        a, b = m
        return D(C(a, b), C(a, N(b)), C(N(a), N(b)))
    m = match_or(f)
    if kind == "or" and m:
        return C(*[N(a) for a in m])
    if f[0] == "v":
        return None
    if f[0] == "neg":
        r = wrong_expand(f[1], kind)
        return N(r) if r else None
    kids = list(f[1])
    for i, c in enumerate(kids):
        r = wrong_expand(c, kind)
        if r:
            kids[i] = r
            return (f[0], tuple(kids))
    return None


def c3_exp_diag():
    items, kinds = [], ["imp", "or", None, None]
    while len(items) < 4:
        f = ab_formula(12, 26)
        k = kinds[len(items)]
        if k and (wrong_expand(f, k) is None or tautology(f, wrong_expand(f, k)) and tautology(wrong_expand(f, k), f)):
            continue
        items.append(f)
    order = list(range(4))
    rnd.shuffle(order)
    items = [items[i] for i in order]
    kinds = [kinds[i] for i in order]
    shown = [wrong_expand(f, k) if k else f for f, k in zip(items, kinds)]
    body = "\n".join(f"{L[i]}) ${tex_ab(f)}$ → ${tex(s)}$" for i, (f, s) in enumerate(zip(items, shown)))
    cond = (f"{CONV3} Студент раскрыл сокращения в четырёх высказываниях. Ровно в двух раскрытиях есть ошибка. "
            "Найдите их, назовите нарушенное определение, исправьте и покажите значениями, что запись студента не "
            f"равнозначна исходному высказыванию.\n\n{body}")
    ans, sol = [], []
    for i, (f, k, s) in enumerate(zip(items, kinds, shown)):
        if not k:
            continue
        e = next(ev for ev in (dict(zip(sorted(atoms(f)), vs)) for vs in itertools.product((0, 1), repeat=len(atoms(f))))
                 if value(f, ev) != value(s, ev))
        rule = ("D1 (с. 20): второй член — $\\sim xy$, а не $x\\sim y$" if k == "imp" else
                "D2 (с. 20): $x \\vee y$ — это $\\sim(\\sim x\\sim y)$, внешнее отрицание потеряно")
        ans.append(f"{L[i]}) нарушено {rule.split(' (')[0]}, с. 20")
        sol.append(f"{L[i]}) Нарушено {rule}. Верно: ${tex(f)}$. При {env_t(e)} исходное высказывание равно "
                   f"{value(f, e)}, запись студента — {value(s, e)} (с. 22).")
    sol.append("Остальные раскрытия верны.")
    ans.append(", ".join(f"{L[i]})" for i, k in enumerate(kinds) if not k) + " — без ошибок")
    return card(5, "E", "vary", "text", "с. 20, 22, гл. 1, § 3", "S1, сокращения, диагностика", cond, "; ".join(ans),
                "\n".join(sol))


def c3_diag2():
    for _ in range(200):
        c = h3.diag_card(0)[1]
        if has_ab(*[f for f in h3_last]):
            break
    cond = c["cond"].replace("Найдите их,", "Найдите их (схемы опознавайте по раскрытой записи),")
    cond = cond.replace("исправьте.\n\n1.", f"исправьте. {h3.REF}\n\n1.", 1)
    return card(6, "E", "vary", "text", SRC3, "S1, сокращения, вывод, диагностика", cond, c["ans"], c["sol"])


def c3_deriv():
    lines = build3(rnd.choice([11, 12]), 10)
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV3} Выведите в $S^1$ формулу ${ftex_ab(a, b)}$, пользуясь аксиомными схемами, теоремными схемами § 2 "
            f"и правилами $S^1$. {h3.REF}")
    ans = f"Например, вывод в {len(lines)} строк (см. решение); последняя строка — ${ftex_ab(a, b)}$ [{why_text(lines[-1][2])}]."
    sol = ("Раскрываем сокращения и применяем схемы к раскрытой записи (D1, D2, с. 20).\n\n" + show(lines, ftex_ab) +
           "\n\nСхемы — с. 15–18; правила — с. 17.")
    return card(7, "D", "open", "proof", SRC3, "S1, сокращения, вывод", cond, ans, sol)


def c3_false():
    for _ in range(500):
        lines = build3(rnd.choice([9, 10]), 8)
        r = false_deriv(lines, check2)
        if r and has_ab(r[0][-1][0], r[0][-1][1]):
            break
    else:
        raise RuntimeError("ложный вывод с сокращениями не построен")
    bad, i = r
    fa, fb = bad[-1][0], bad[-1][1]
    e = counterexample(fa, fb)
    wh = bad[i][2]
    fx = lines_fix(bad, i)
    cond = (f"{CONV3} Студент утверждает, что вывел в $S^1$ формулу ${ftex_ab(fa, fb)}$:\n\n{show(bad, ftex_ab)}\n\n"
            f"Докажите, что формула недоказуема в $S^1$, и найдите шаг, на котором нарушена схема или правило. "
            f"{h3.REF} {CRIT}")
    ans = (f"Недоказуема: при {env_t(e)} посылка — 1, заключение — 0 (§ 5, MT1, с. 22). Ошибка в шаге {i + 1}: формула — "
           f"не пример {wh} (с. 15–16).")
    sol = (f"1. Значения считаем по раскрытой записи (D1, D2, с. 20). При {env_t(e)} посылка равна {value(fa, e)}, "
           f"заключение — {value(fb, e)}: формула не тавтология и по § 5, MT1 (с. 22) не теорема $S^1$.\n"
           f"2. Шаг {i + 1}: ${ftex_ab(bad[i][0], bad[i][1])}$ [{wh}] — не пример схемы {wh}: {NEAR_TXT[wh]} "
           f"(с. 15–16). По схеме — ${ftex_ab(fx[0], fx[1])}$.\n3. Остальные шаги верны, но ошибка переходит в заключение "
           "по R1, R2 (с. 17).")
    return card(6, "E", "open", "text", SRC3, "S1, сокращения, вывод, диагностика", cond, ans, sol)


# ======================================================================== § 4
h4 = load_h(1970_1104, True)
SRC4 = "с. 21, гл. 1, § 4"


def binary_only(f):
    if f[0] == "v":
        return True
    if f[0] == "neg":
        return binary_only(f[1])
    return (f[0] != "conj" or len(f[1]) == 2) and all(binary_only(c) for c in f[1])


def theorem4(want=6, least=4, binary=False):
    for _ in range(500):
        lines = h4.build_ok(want, least)
        a, b = lines[-1][0], lines[-1][1]
        if not binary or (binary_only(a) and binary_only(b) and all(binary_only(p) and binary_only(q)
                                                                     for p, q, _ in lines)):
            return lines
    raise RuntimeError


def with_new_letter(b):
    ps = [p for p, s in paths(b) if s[0] == "v"]
    p = rnd.choice(ps)
    s = dict(paths(b))[p]
    return put(b, p, rnd.choice([C(s, u), D(s, N(u)), C(N(u), s)]))


def c4_series():
    kinds = ["new", "new", "yes", "yes"]
    rnd.shuffle(kinds)
    items, ders = [], []
    for kd in kinds:
        while True:
            lines = theorem4(rnd.choice([5, 6]), 4)
            a, b = lines[-1][0], lines[-1][1]
            if "u" in atoms(a):
                continue
            if kd == "new":
                b = with_new_letter(b)
            if len(tex(a)) + len(tex(b)) <= 46:
                break
        items.append((a, b))
        ders.append(lines if kd == "yes" else None)
    body = "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items))
    cond = (f"{CONV} MT1 § 4 (с. 21): если $x \\vdash y$ — теорема $S^1$, то в $y$ не входят элементарные высказывания, "
            "не входящие в $x$. Для каждой формулы: если MT1 позволяет установить её недоказуемость, назовите "
            "элементарные высказывания, нарушающие условие; если не позволяет — исследуйте доказуемость сами и "
            f"доказуемую выведите (схемы и теоремные схемы § 2, правила R1–R3).\n\n{body}")
    ans, sol = [], []
    for i, ((a, b), lines) in enumerate(zip(items, ders)):
        if lines is None:
            na = ", ".join(f"${t}$" for t in sorted(new_atoms(a, b)))
            ans.append(f"{L[i]}) недоказуема: {na} нет в посылке (MT1)")
            sol.append(f"{L[i]}) В заключение входит {na}, которого нет в посылке; по MT1 § 4 (с. 21) формула не "
                       "теорема $S^1$.")
        else:
            ans.append(f"{L[i]}) MT1 не решает; доказуема")
            sol.append(f"{L[i]}) Новых элементарных высказываний нет — MT1 ничего не даёт (условие MT1 необходимое, а не "
                       f"достаточное). Формула доказуема:\n\n{show(lines)}\n")
    return card(6, "C", "iso", "proof", SRC4, "S1, непарадоксальность, MT1", cond, "; ".join(ans), "\n".join(sol))


def hidden_occ(a):
    """Буква, входящая в посылку только внутри отрицания составной части или дизъюнкции."""
    out = set()
    for p, s in paths(a):
        if s[0] == "neg" and s[1][0] in ("conj", "dis") or s[0] == "dis":
            out |= atoms(s)
    top = {s[1] for p, s in paths(a) if s[0] == "v" and all(
        dict(paths(a))[p[:k]][0] == "conj" for k in range(len(p)))}
    return sorted(out - top)


def c4_diag():
    rows = []
    # (формула, утверждение студента, верно ли, пояснение)
    while True:
        lines = theorem4(5, 4)
        a, b = lines[-1][0], lines[-1][1]
        hid = [t for t in hidden_occ(a) if t in atoms(b)]
        if hid and "u" not in atoms(a) and len(tex(a)) + len(tex(b)) <= 44:
            break
    t = hid[0]
    rows.append(((a, b), f"недоказуема по MT1: ${t}$ входит в посылку только внутри "
                         f"{'дизъюнкции' if any(s[0] == 'dis' and t in atoms(s) for _, s in paths(a)) else 'отрицания'}, "
                         "значит, в посылку не входит", False, "B", lines))
    while True:
        lines = theorem4(5, 4)
        a, b = lines[-1][0], lines[-1][1]
        b2 = mutate_concl(b)
        if not tautology(a, b2) and not new_atoms(a, b2) and len(tex(a)) + len(tex(b2)) <= 44:
            break
    rows.append(((a, b2), "доказуема по MT1: новых элементарных высказываний в заключении нет", False, "A", None))
    while True:
        lines = theorem4(5, 4)
        a, b = lines[-1][0], lines[-1][1]
        if "u" not in atoms(a) and len(tex(a)) + len(tex(b)) <= 40:
            break
    rows.append(((a, with_new_letter(b)), "недоказуема по MT1: в заключение входит $u$, которого нет в посылке", True,
                 None, None))
    while True:
        lines = theorem4(5, 4)
        a, b = lines[-1][0], lines[-1][1]
        if len(tex(a)) + len(tex(b)) <= 40:
            break
    rows.append(((a, b), "MT1 о доказуемости ничего не говорит: новых элементарных высказываний нет", True, None, None))
    rnd.shuffle(rows)
    body = "\n".join(f"{L[i]}) ${ftex(a, b)}$ — «{cl}»" for i, ((a, b), cl, *_r) in enumerate(rows))
    cond = (f"{CONV} MT1 § 4 (с. 21): если $x \\vdash y$ — теорема $S^1$, то в $y$ не входят элементарные высказывания, "
            "не входящие в $x$. Студент применил MT1 к четырём формулам. Ровно два его вывода ошибочны. Найдите их, "
            f"объясните ошибку и установите, доказуема ли формула на самом деле. {CRIT}\n\n{body}")
    ans, sol = [], []
    for i, ((a, b), cl, ok, kd, lines) in enumerate(rows):
        if ok:
            continue
        if kd == "B":
            ans.append(f"{L[i]}) ошибка: вхождение — любое, и внутри отрицания или дизъюнкции тоже (MT1, с. 21); формула доказуема")
            sol.append(f"{L[i]}) Высказывание входит в посылку, где бы ни стояло его вхождение (Введение, § 7, с. 9–10); "
                       "условие MT1 выполнено, и MT1 недоказуемости не даёт. Формула доказуема:\n\n" + show(lines) + "\n")
        else:
            e = counterexample(a, b)
            ans.append(f"{L[i]}) ошибка: MT1 — необходимое условие, а не достаточное (с. 21); недоказуема: {env_t(e)}")
            sol.append(f"{L[i]}) MT1 говорит лишь, что у теоремы нет новых букв в заключении; обратного она не "
                       f"утверждает. При {env_t(e)} посылка — 1, заключение — 0: не тавтология, по § 5, MT1 (с. 22) — "
                       "недоказуема.")
    sol.append("Остальные выводы студента верны.")
    ans.append(", ".join(f"{L[i]})" for i, r in enumerate(rows) if r[2]) + " — верно")
    return card(6, "E", "vary", "text", "с. 9–10, 21–22, гл. 1, § 4", "S1, непарадоксальность, MT1, диагностика", cond,
                "; ".join(ans), "\n".join(sol))


# ======================================================================== § 5
SRC5 = "с. 22–24, гл. 1, § 5"
INTERP = ("Главная интерпретация (с. 22): $\\sim x$ имеет значение 1, если и только если $x$ имеет значение 0; "
          "$x^1 \\ldots x^n$ — 1, если все $x^i$ имеют значение 1; $x^1 : \\ldots : x^n$ — 1, если одно и только одно "
          "из $x^i$ имеет значение 1; $x \\vdash y$ — 0, если и только если $x$ имеет значение 1, а $y$ — 0.")


def envs(names):
    for vs in itertools.product((0, 1), repeat=len(names)):
        yield dict(zip(names, vs))


def long3(lo=16, hi=30, letters="xyz"):
    while True:
        f = rand_ok(3, list(letters))
        if lo <= len(tex(f)) <= hi and len(atoms(f)) == 3:
            return f


def kind(f):
    vs = {value(f, e) for e in envs(sorted(atoms(f)))}
    return "тавтология" if vs == {1} else "противоречие" if vs == {0} else "ни тавтология, ни противоречие"


def c5_table_fill():
    while True:
        f = long3(18, 30)
        if f[0] in ("conj", "dis") and len(f[1]) == 2 and kind(f) != "противоречие" and all(
                c[0] != "v" and kind(c).startswith("ни") for c in f[1]):
            break
    A, B = f[1]
    names = sorted(atoms(f))
    rows = [(e, value(A, e), value(B, e), value(f, e)) for e in envs(names)]
    hide = set(rnd.sample(range(8 * 3), 9))
    head = (f"| ${names[0]}$ | ${names[1]}$ | ${names[2]}$ | ${tex(A)}$ | ${tex(B)}$ | ${tex(f)}$ |\n"
            "|---|---|---|---|---|---|\n")

    def cell(i, j, v):
        return "?" if 3 * i + j in hide else str(v)
    body = "".join(f"| {e[names[0]]} | {e[names[1]]} | {e[names[2]]} | {cell(i, 0, va)} | {cell(i, 1, vb)} | "
                   f"{cell(i, 2, vf)} |\n" for i, (e, va, vb, vf) in enumerate(rows))
    cond = (f"{CONV} {INTERP} Заполните пропуски «?» в таблице значений высказывания ${tex(f)}$ и его двух главных "
            f"частей, а затем определите по D2, D3 § 5 (с. 22), тавтология ли оно, противоречие или ни то ни другое.\n\n"
            f"{head}{body}")
    filled = []
    for i, (e, va, vb, vf) in enumerate(rows):
        miss = [str(v) for j, v in enumerate((va, vb, vf)) if 3 * i + j in hide]
        if miss:
            filled.append(f"строка {i + 1}: " + ", ".join(miss))
    ans = "; ".join(filled) + f"; {kind(f)}"
    sol = (f"Главный оператор — {'конъюнкция' if f[0] == 'conj' else 'сильная дизъюнкция'} (п. {3 if f[0] == 'conj' else 4} "
           "главной интерпретации, с. 22). Полная таблица:\n\n" + head + "".join(
               f"| {e[names[0]]} | {e[names[1]]} | {e[names[2]]} | {va} | {vb} | {vf} |\n" for e, va, vb, vf in rows) +
           f"\nИтог: {kind(f)} (D2, D3, с. 22).")
    return card(4, "V", "complete", "build", SRC5, "главная интерпретация, таблица", cond, ans, sol)


def c5_zero_sets():
    want_none = rnd.random() < 0.3
    while True:
        a, b = rand_ok(2, list("xyz")), rand_ok(2, list("xyz"))
        if (len(atoms(a) | atoms(b)) < 3 or not (18 <= len(tex(a)) + len(tex(b)) <= 34) or not kind(a).startswith("ни")
                or min(len(tex(a)), len(tex(b))) < 6):
            continue
        zs = [e for e in envs(sorted(atoms(a) | atoms(b))) if value(a, e) == 1 and value(b, e) == 0]
        if (not zs) == want_none and len(zs) <= 3:
            break
    cond = (f"{CONV} {INTERP} Найдите все наборы значений элементарных высказываний, при которых формула следования "
            f"${ftex(a, b)}$ принимает значение 0. Если таких наборов нет, докажите, что формула — тавтология (D1 § 5, "
            "с. 22), не перебирая вслепую все восемь наборов: начните с наборов, где посылка равна 1.")
    pos = [e for e in envs(sorted(atoms(a) | atoms(b))) if value(a, e) == 1]
    if zs:
        ans = "; ".join(env_t(e) for e in zs)
    else:
        ans = "Таких наборов нет — тавтология."
    sol = (f"По п. 5 (с. 22) формула равна 0 только при посылке 1 и заключении 0. Посылка ${tex(a)}$ равна 1 при "
           + "; ".join(env_t(e) for e in pos) + ". Заключение в этих наборах: "
           + "; ".join(f"{value(b, e)}" for e in pos) + ". " +
           (f"Значение 0 — при {'; '.join(env_t(e) for e in zs)}." if zs else "Везде 1 — формула тавтология (D1)."))
    return card(5, "V", "open", "short", SRC5, "главная интерпретация, тавтология", cond, ans, sol)


def c5_joint():
    want = rnd.random() < 0.65
    while True:
        fs = [rand_ok(2, list("xyz")) for _ in range(3)]
        need = [1, 0, 1]
        if any(len(tex(f)) < 6 for f in fs) or len(set(fs)) < 3:
            continue
        names = sorted(set().union(*(atoms(f) for f in fs)))
        if len(names) < 3:
            continue
        sols = [e for e in envs(names) if [value(f, e) for f in fs] == need]
        if bool(sols) == want and len(sols) <= 2:
            break
    cond = (f"{CONV} {INTERP} Подберите значения $x, y, z$, при которых одновременно ${tex(fs[0])}$ имеет значение 1, "
            f"${tex(fs[1])}$ — значение 0 и ${tex(fs[2])}$ — значение 1, или докажите, что таких значений нет. Найдите "
            "все решения.")
    if sols:
        ans = "; ".join(env_t(e) for e in sols)
        sol = "Перебор по условиям (с. 22): " + "; ".join(
            f"при {env_t(e)} значения — 1, 0, 1" for e in sols) + ". В остальных наборах хотя бы одно условие нарушено."
    else:
        ans = "Таких значений нет."
        rows = []
        for e in envs(names):
            vs = [value(f, e) for f in fs]
            bad = next(i for i in range(3) if vs[i] != need[i])
            rows.append(f"{env_t(e)}: {'первое' if bad == 0 else 'второе' if bad == 1 else 'третье'} высказывание "
                        f"равно {vs[bad]}")
        sol = "Ни в одном из восьми наборов условия не выполняются вместе (с. 22):\n\n" + "\n".join(f"- {r}" for r in rows)
    return card(5, "V", "vary", "short", SRC5, "главная интерпретация, обратная задача", cond, ans, sol)


def c5_mt3():
    for _ in range(500):
        lines = theorem4(rnd.choice([5, 6]), 4)
        a, b = lines[-1][0], lines[-1][1]
        names = sorted(atoms(a))
        z0 = [e for e in envs(names) if value(b, e) == 0]
        z1 = [e for e in envs(names) if value(b, e) == 1 and value(a, e) == 0]
        if z0 and len(tex(a)) + len(tex(b)) <= 44:
            break
    e = rnd.choice(z0)
    cond = (f"{CONV} {INTERP} Формула ${ftex(a, b)}$ — теорема $S^1$ (её вывод в {len(lines)} строк приведён в "
            f"решении). При {env_t(e)} заключение имеет значение 0. Найдите значение посылки при этих значениях, опираясь "
            "на MT3 § 5 (с. 24: если $x \\vdash y$ — теорема $S^1$ и $y$ имеет значение 0, то $x$ имеет значение 0), и "
            "проверьте вычислением. Затем найдите набор, при котором заключение равно 1, а посылка 0, или докажите, что "
            "его нет, и объясните, почему ответ не противоречит MT2 § 5.")
    if z1:
        ans = f"Посылка — 0; набор есть: {env_t(z1[0])}."
        part = (f"При {env_t(z1[0])} заключение — 1, посылка — 0. MT2 (с. 24) утверждает лишь: если посылка теоремы "
                "равна 1, то и заключение равно 1; об обратном она ничего не говорит.")
    else:
        ans = "Посылка — 0; такого набора нет."
        part = ("Такого набора нет: во всех наборах, где заключение равно 1, посылка тоже 1 (перебор). Это не следует из "
                "MT2 — так получилось для данной формулы.")
    sol = (f"1. По MT3 § 5 посылка равна 0. Проверка: ${tex(a)}$ при {env_t(e)} равно {value(a, e)} (с. 22).\n"
           f"2. {part}\n\nВывод теоремы:\n\n{show(lines)}")
    assert value(a, e) == 0
    return card(5, "V", "vary", "short", SRC5, "главная интерпретация, MT2, MT3", cond, ans, sol)


def c5_equal():
    kd = rnd.choice(["same", "extra", "diff"])
    for _ in range(300):
        lines = r3_chain(2, maxlen=30)
        a, b = lines[-1][0], lines[-1][1]
        if kd == "extra":
            nb = u if "u" not in atoms(a) else w
            b = C(b, D(nb, N(nb))) if rnd.random() < .5 else D(C(b, D(nb, N(nb))), C(nb, N(nb)))
        elif kd == "diff":
            b = mutate_concl(b)
            if tautology(a, b) and tautology(b, a):
                continue
        if len(tex(a)) + len(tex(b)) <= 46:
            break
    names = sorted(atoms(a) | atoms(b))
    cond = (f"{CONV} {INTERP} По MT4 § 5 (с. 24) если $x \\vdash y$ и $y \\vdash x$ — теоремы $S^1$, то $x$ и $y$ "
            "равнозначны: принимают одно и то же значение при каждой комбинации значений входящих в них элементарных "
            f"высказываний. Исследуйте, равнозначны ли ${tex(a)}$ и ${tex(b)}$; затем исследуйте доказуемость формул "
            f"${ftex(a, b)}$ и ${ftex(b, a)}$ и объясните, согласуется ли результат с MT4. {CRIT}")
    if kd == "diff":
        e = next(ev for ev in envs(names) if value(a, ev) != value(b, ev))
        pa, pb = strong_tautology(a, b), strong_tautology(b, a)
        ans = (f"Не равнозначны: при {env_t(e)} — {value(a, e)} и {value(b, e)}; доказуема "
               + ("первая" if pa else "вторая" if pb else "ни одна") + ".")
        sol = (f"При {env_t(e)} первое высказывание равно {value(a, e)}, второе — {value(b, e)}. Значит, по MT4 обе "
               "формулы теоремами быть не могут. " + ("Первая — сильная тавтология, доказуема; вторая — нет." if pa else
                                                       "Вторая — сильная тавтология, доказуема; первая — нет." if pb else
                                                       "Ни одна не тавтология — обе недоказуемы (§ 5, MT1)."))
    elif kd == "same":
        ans = "Равнозначны; обе формулы доказуемы."
        sol = ("Высказывания равнозначны: вторая получена из первой заменой частей на взаимно выводимые (выводы — ниже), "
               "и значения совпадают во всех наборах. Элементарные высказывания одни и те же, поэтому обе формулы — "
               "сильные тавтологии и доказуемы. Вывод первой:\n\n" + show(lines) + "\n\nВторая выводится теми же "
               "заменами в обратном порядке (R3 по тем же парам, R1). Согласуется с MT4.")
    else:
        na = ", ".join(f"${t}$" for t in sorted(atoms(b) - atoms(a)))
        ans = f"Равнозначны; доказуема только вторая (в первой в заключении {na})."
        sol = (f"Добавленная часть с {na} при любых значениях не меняет значения (с. 22), поэтому высказывания "
               f"равнозначны. Но в заключение ${ftex(a, b)}$ входит {na}, которого нет в посылке, — по MT1 § 4 (с. 21) "
               "она недоказуема; обратная — сильная тавтология и доказуема. MT4 не нарушена: она выводит "
               "равнозначность из доказуемости, а не наоборот.")
    return card(6, "C", "open", "short", SRC5, "главная интерпретация, MT4", cond, ans, sol)


def c5_calc_diag():
    for _ in range(2000):
        f = long3(20, 32)
        e = {k: rnd.randint(0, 1) for k in sorted(atoms(f))}
        nodes = []
        for p, s in sorted(paths(f), key=lambda t: -len(t[0])):
            if s[0] != "v" and s not in nodes:
                nodes.append(s)
        if not (6 <= len(nodes) <= 9):
            continue
        dis_err = [s for s in nodes if s[0] == "dis" and sum(value(c, e) for c in s[1]) >= 2]
        oth_err = [s for s in nodes if s[0] in ("conj", "neg") and s not in dis_err]
        if not dis_err or not oth_err:
            continue
        e1, e2 = rnd.choice(dis_err), rnd.choice(oth_err)
        stv = {}

        def sv(s):
            if s[0] == "v":
                return e[s[1]]
            return stv[s]
        for s in nodes:
            if s[0] == "neg":
                v = 1 - sv(s[1])
            elif s[0] == "conj":
                v = int(all(sv(c) for c in s[1]))
            else:
                v = int(sum(sv(c) for c in s[1]) == 1)
            if s == e1:
                v = int(any(sv(c) for c in s[1]))
            elif s == e2:
                v = 1 - v
            stv[s] = v
        right = {}
        for s in nodes:
            if s[0] == "neg":
                r = 1 - sv(s[1])
            elif s[0] == "conj":
                r = int(all(sv(c) for c in s[1]))
            else:
                r = int(sum(sv(c) for c in s[1]) == 1)
            right[s] = r
        wrong = [s for s in nodes if right[s] != stv[s]]
        if wrong == [s for s in nodes if s in (e1, e2)] and len(wrong) == 2:
            break
    body = "\n".join(f"{i + 1}. ${tex(s)}$ = {stv[s]}" for i, s in enumerate(nodes))
    cond = (f"{CONV} {INTERP} Студент вычислил значение высказывания ${tex(f)}$ при {env_t(e)}, двигаясь от частей к "
            f"целому. Ровно на двух шагах он неверно применил пункт главной интерпретации (значения частей он берёт из "
            f"своих же предыдущих шагов). Найдите эти шаги, назовите нарушенный пункт и найдите верное значение "
            f"высказывания.\n\n{body}")
    idx = {s: i + 1 for i, s in enumerate(nodes)}
    pts = {"neg": "п. 2", "conj": "п. 3", "dis": "п. 4"}
    ans = "; ".join(f"шаг {idx[s]}: {pts[s[0]]} (с. 22)" for s in wrong) + f"; верно — {value(f, e)}"
    sol = []
    for s in wrong:
        if s == e1:
            sol.append(f"Шаг {idx[s]}: в сильной дизъюнкции истинны по меньшей мере два члена, а по п. 4 (с. 22) она "
                       "истинна, только когда истинен один и только один член; студент прочёл $:$ как «хотя бы одно из».")
        else:
            sol.append(f"Шаг {idx[s]}: по {pts[s[0]]} (с. 22) при этих значениях частей должно быть {right[s]}.")
    sol.append("Верное вычисление:\n\n" + "\n".join(f"{i + 1}. ${tex(s)}$ = {value(s, e)}" for i, s in enumerate(nodes)))
    return card(5, "E", "vary", "text", SRC5, "главная интерпретация, диагностика", cond, ans, "\n".join(sol))


def c5_mt_diag():
    for _ in range(500):
        lines = theorem4(5, 4)
        a, b = lines[-1][0], lines[-1][1]
        names = sorted(atoms(a))
        z1 = [e for e in envs(names) if value(b, e) == 1 and value(a, e) == 0]
        z0 = [e for e in envs(names) if value(b, e) == 0]
        if z1 and z0 and len(tex(a)) + len(tex(b)) <= 44:
            break
    e1, e0 = z1[0], z0[0]
    claims = [(f"при {env_t(e0)} заключение равно 0, значит, по MT3 посылка равна 0", True),
              (f"при {env_t(e1)} заключение равно 1, значит, по MT2 посылка равна 1", False)]
    rnd.shuffle(claims)
    cond = (f"{CONV} {INTERP} MT2 § 5 (с. 24): если $x \\vdash y$ — теорема $S^1$ и $x$ имеет значение 1, то $y$ имеет "
            "значение 1; MT3: если $x \\vdash y$ — теорема и $y$ имеет значение 0, то $x$ имеет значение 0. Формула "
            f"${ftex(a, b)}$ — теорема $S^1$ (вывод — в решении). Студент делает два вывода: (1) {claims[0][0]}; "
            f"(2) {claims[1][0]}. Проверьте оба вывода вычислением и назовите ошибку в рассуждении.")
    k = 1 if not claims[0][1] else 2
    ans = (f"Ошибочен вывод ({k}): MT2 (с. 24) идёт от посылки к заключению, обращать её нельзя; при {env_t(e1)} посылка "
           "равна 0.")
    sol = (f"При {env_t(e0)}: заключение {value(b, e0)}, посылка {value(a, e0)} — вывод по MT3 верен. При {env_t(e1)}: "
           f"заключение {value(b, e1)}, посылка {value(a, e1)} — студент обратил MT2, а она утверждает лишь «посылка 1 ⇒ "
           "заключение 1» (с. 24).\n\nВывод теоремы:\n\n" + show(lines))
    return card(5, "E", "vary", "text", SRC5, "главная интерпретация, MT2, диагностика", cond, ans, sol)


def c5_a9_diag():
    P = N(D(x, y, z))
    good = D(C(x, y, z), C(N(x), y, z), C(x, N(y), z), C(x, y, N(z)), C(N(x), N(y), N(z)))
    bad = D(C(x, y, z), C(N(x), N(y), z), C(N(x), y, N(z)), C(x, N(y), N(z)))
    assert tautology(P, good) and not tautology(P, bad)
    e = counterexample(P, bad)
    cond = (f"{CONV} Схема A9 в общем виде (с. 16): $\\sim(x^1 : \\ldots : x^n) \\vdash y^1 : \\ldots : y^m$, где "
            "$y^1, \\ldots, y^m$ — попарно различные высказывания, в которые входят $x^1 \\ldots x^n$ и все "
            "высказывания, отличающиеся от него наличием одного и только одного оператора отрицания перед всеми "
            "$x^1, \\ldots, x^n$ или перед $i$ из них, где $1 \\leq i \\leq n - 2$. Студент выписал пример A9 при $n = 3$: "
            f"${ftex(P, bad)}$. Найдите в его записи все ошибки, запишите пример A9 при $n = 3$ верно и, рассуждая как в "
            "доказательстве MT1 § 5 (с. 23), покажите значениями, что формула студента не тавтология, а верная — "
            "тавтология.")
    ans = (f"Две ошибки: взяты члены с двумя отрицаниями ($i = 2 > n - 2$) и пропущен член $\\sim x\\sim y\\sim z$. Верно: "
           f"${ftex(P, good)}$. Формула студента ложна при {env_t(e)}.")
    sol = ("1. При $n = 3$ допустимо лишь $i = 1$ (с. 16): члены $xyz$, $\\sim xyz$, $x\\sim yz$, $xy\\sim z$ и член с "
           "отрицаниями перед всеми — $\\sim x\\sim y\\sim z$. Студент взял $i = 2$ и забыл отрицание перед всеми.\n"
           f"2. При {env_t(e)} $x : y : z = 0$, посылка — 1, а все члены заключения студента — 0: формула равна 0 (с. 22).\n"
           "3. Верная формула: посылка равна 1, когда истинны ни одного, два или три из $x, y, z$. Ни одного — истинен "
           "только $\\sim x\\sim y\\sim z$; три — только $xyz$; два — только тот член с одним отрицанием, где отрицание "
           "стоит перед ложным. Ровно один член истинен — заключение 1, как в доказательстве MT1 (с. 23).")
    return card(6, "E", "transfer", "text", "с. 16, 22–23, гл. 1, § 5", "главная интерпретация, A9, диагностика", cond,
                ans, sol)


# ======================================================================== § 6
SRC6 = "с. 22, 25, гл. 1, § 5–6"


def c6_series():
    kinds = ["both", "first", "second", "none"]
    rnd.shuffle(kinds)
    items = []
    for kd in kinds:
        for _ in range(20000):
            lt = rnd.sample("xyz", rnd.choice([2, 3]))
            p, q = rand_ok(2, lt), rand_ok(2, lt)
            if not (atoms(q) <= atoms(p)) or not (14 <= len(tex(p)) + len(tex(q)) <= 30) or q[0] == "neg":
                continue
            s1_, s2_ = strong_tautology(p, q), strong_tautology(p, N(q))
            got = "both" if s1_ and s2_ else "first" if s1_ else "second" if s2_ else "none"
            if got == kd and (p, q) not in items:
                items.append((p, q))
                break
    body = "\n".join(f"{L[i]}) $X$ = ${tex(p)}$, $Y$ = ${tex(q)}$" for i, (p, q) in enumerate(items))
    cond = (f"{CONV} MT1 § 6 (с. 25): если $x \\vdash y$ — теорема $S^1$ и $x$ не противоречие, то $x \\vdash \\sim y$ не "
            "теорема. Ниже $X$, $Y$ — обозначения данных высказываний. Для каждой пары исследуйте доказуемость формул $X \\vdash Y$ и $X \\vdash \\sim Y$ и объясните "
            f"результат через MT1 § 6: если доказуемы обе — покажите, что $X$ противоречие (D3 § 5, с. 22). {CRIT}"
            f"\n\n{body}")
    names = {"both": "доказуемы обе", "first": "доказуема только $X \\vdash Y$",
             "second": "доказуема только $X \\vdash \\sim Y$", "none": "ни одна не доказуема"}
    ans, sol = [], []
    for i, (p, q) in enumerate(items):
        kd = kinds[i]
        ans.append(f"{L[i]}) {names[kd]}")
        if kd == "both":
            sol.append(f"{L[i]}) $X$ равно 0 при всех значениях — противоречие; поэтому обе формулы тавтологии, новых букв "
                       "нет — обе доказуемы. MT1 § 6 не нарушена: её условие «$X$ не противоречие» не выполнено.")
        else:
            parts = []
            for qq, nm in ((q, "$X \\vdash Y$"), (N(q), "$X \\vdash \\sim Y$")):
                ce = counterexample(p, qq)
                parts.append(f"{nm} — сильная тавтология" if ce is None else f"{nm} ложна при {env_t(ce)}")
            sol.append(f"{L[i]}) " + "; ".join(parts) + ". $X$ не противоречие, и обе вместе быть теоремами не могут (MT1 § 6).")
    return card(5, "C", "iso", "short", SRC6, "S1, непротиворечивость, MT1", cond, "; ".join(ans), "\n".join(sol))


# ======================================================================== § 7
SRC7 = "с. 25–26, гл. 1, § 7"
a_, b_, c_ = V("a"), V("b"), V("c")


def mt_tex(e, names):
    return "".join(n if e[n] else f"\\sim {n}" for n in names)


def c7_canon():
    while True:
        f = rand_ok(3, ["a", "b", "c"])
        if len(atoms(f)) == 3 and 16 <= len(tex(f)) <= 30 and kind(f).startswith("ни"):
            sat = [e for e in envs(["a", "b", "c"]) if value(f, e)]
            if 2 <= len(sat) <= 5:
                break
    mems = [mt_tex(e, ["a", "b", "c"]) for e in sat]
    cond = ("Буквы $a, b, c$ — элементарные высказывания в алфавитном порядке $a, b, c$. Каноническая форма (D2 § 7, "
            "с. 25–26): $x^1 : \\ldots : x^n$, где каждый $x^i$ — конъюнкция элементарных высказываний с отрицанием или "
            "без; в каждом члене они попарно различны и идут по алфавиту (при одном и том же высказывании — сначала без "
            "отрицания); все члены попарно различны. Каноническая форма для $x$ (D3) — высказывание $y$ в канонической "
            f"форме, для которого $x \\vdash y$ и $y \\vdash x$ — теоремы $S^1$. Найдите для ${tex(f)}$ каноническую форму, "
            "каждый член которой содержит все три буквы, и обоснуйте D3 по критерию. " + CRIT)
    ans = " : ".join(f"${m}$" for m in mems) + " (порядок членов любой)"
    sol = ("1. Перебираем 8 наборов (с. 22); высказывание равно 1 при " + "; ".join(env_t(e) for e in sat) + ".\n"
           "2. Каждому такому набору сопоставляем конъюнкцию трёх букв (с отрицанием там, где значение 0), по алфавиту — "
           "D2, п. 2a, 2b; члены различны — п. 2c.\n"
           "3. Полученная дизъюнкция $y$ истинна ровно в тех же наборах (в каждом наборе истинен не более чем один член), "
           "и в $x$, $y$ одни и те же буквы; значит, $x \\vdash y$ и $y \\vdash x$ — сильные тавтологии и по MT6 § 7 "
           "(с. 32) теоремы. По D3 $y$ — каноническая форма для $x$.\n\nОтвет: " + ans)
    return card(5, "A", "iso", "build", SRC7, "S1, каноническая форма", cond, ans, sol)


def c7_canon_diag():
    while True:
        f = rand_ok(3, ["a", "b", "c"])
        if len(atoms(f)) == 3 and 16 <= len(tex(f)) <= 30:
            sat = [e for e in envs(["a", "b", "c"]) if value(f, e)]
            if 3 <= len(sat) <= 5:
                break
    names = ["a", "b", "c"]
    miss = rnd.choice(sat)
    rest = [e for e in sat if e != miss]
    wro = rnd.choice(rest)
    order = rnd.choice([["b", "a", "c"], ["a", "c", "b"], ["c", "a", "b"]])
    stud = [(mt_tex(e, order) if e == wro else mt_tex(e, names)) for e in rest]
    cond = ("Буквы $a, b, c$ — элементарные высказывания в алфавитном порядке $a, b, c$. Каноническая форма (D2 § 7, "
            "с. 25–26): $x^1 : \\ldots : x^n$, где каждый $x^i$ — конъюнкция элементарных высказываний с отрицанием или "
            "без; в каждом члене они попарно различны и упорядочены по алфавиту (при одном и том же высказывании — "
            "сначала без отрицания); все члены попарно различны. Каноническая форма для $x$ (D3) — $y$ в канонической "
            f"форме, для которого $x \\vdash y$ и $y \\vdash x$ — теоремы $S^1$. Студент нашёл для ${tex(f)}$ каноническую "
            f"форму из членов с тремя буквами: ${' : '.join(stud)}$. Найдите все ошибки, назовите нарушенные условия и "
            "исправьте.")
    good = " : ".join(f"${mt_tex(e, names)}$" for e in sat)
    ans = (f"Две ошибки: член ${mt_tex(wro, order)}$ нарушает порядок D2, п. 2b (с. 26) — верно ${mt_tex(wro, names)}$; "
           f"пропущен член ${mt_tex(miss, names)}$ (D3: иначе $x \\vdash y$ не теорема). Верно: {good}.")
    sol = (f"1. ${mt_tex(wro, order)}$: элементарные высказывания не по алфавиту — нарушено D2, п. 2b (с. 26).\n"
           f"2. При {env_t(miss)} исходное высказывание равно 1, а в записи студента ни один член не истинен — "
           "заключение 0. Формула $x \\vdash y$ не тавтология и по § 5, MT1 (с. 22) не теорема; по D3 (с. 26) запись "
           f"студента — не каноническая форма для $x$. Нужен член ${mt_tex(miss, names)}$.\n"
           f"3. Верно: {good} — по MT6 § 7 (с. 32) обе формулы следования доказуемы.")
    return card(6, "E", "vary", "text", SRC7, "S1, каноническая форма, диагностика", cond, ans, sol)


# ======================================================================== § 8
SRC8 = "с. 33–35, гл. 1, § 8"
TT = {"A1": "$\\sim x = 0$; $x^1 : \\ldots : x^n = x^1 \\cdot \\ldots \\cdot x^n$",
      "A2": "$\\sim x = 1$; $x^1 : \\ldots : x^n = x^1 \\vee \\ldots \\vee x^n$ (равно 0, если и только если все $x^i$ "
            "равны 0)",
      "A3": "$\\sim x = x$; $xy = 1$; $x^1 : \\ldots : x^n = 1$",
      "A4": "$\\sim x = x$; $xy = x$; $x^1 : \\ldots : x^n = x^1$",
      "A7": "$\\sim x = x$; $x^1 : \\ldots : x^n = 0$",
      "A9": "$\\sim x = x$; $x^1 : \\ldots : x^n = x^1 \\vee \\ldots \\vee x^n$ (равно 0, если и только если все $x^i$ "
            "равны 0)",
      "A10": "$x^1 : \\ldots : x^n = x^1 \\vee \\ldots \\vee x^n$ (равно 0, если и только если все $x^i$ равны 0)"}


def ttext(tn):
    return (f"Таблица для {tn} (§ 8, с. 33): значения 1 и 0, отмеченное значение 1; {TT[tn]}; остальные операторы и "
            "$\\vdash$ — как при главной интерпретации (§ 5, с. 22)")


def tv(f, e, t):
    return IND.val(f, e, t)


def theorem8(binary=True):
    while True:
        lines = theorem4(rnd.choice([5, 6]), 4, binary=binary)
        a, b = lines[-1][0], lines[-1][1]
        if a != b and len(tex(a)) + len(tex(b)) >= 14:
            return a, b


def c8_table():
    tn = rnd.choice(["A1", "A2", "A3", "A4", "A7", "A9", "A10"])
    t = IND.TABLES[tn]
    items = []
    for _ in range(20000):
        if len(items) == 4:
            break
        a, b = theorem8()
        ok, env = IND.valid(a, b, t)
        want_bad = len(items) in (0, 2)
        if ok == (not want_bad) and len(tex(a)) + len(tex(b)) <= 40 and (a, b) not in items:
            items.append((a, b))
    if len(items) < 4:
        return c8_table()
    rnd.shuffle(items)
    ans, sol = [], []
    for k, (a, b) in enumerate(items):
        ok, e = IND.valid(a, b, t)
        if ok:
            ans.append(f"{L[k]}) тавтологична")
            sol.append(f"{L[k]}) При всех наборах значений формула получает отмеченное значение 1.")
        else:
            ans.append(f"{L[k]}) не тавтологична: {env_t(e)}")
            sol.append(f"{L[k]}) При {env_t(e)} посылка по таблице равна {tv(a, e, t)}, заключение — {tv(b, e, t)}; формула "
                       "равна 0. Значит, эту теорему нельзя вывести без схемы " + tn + ".")
    body = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b) in enumerate(items))
    cond = (f"{CONV} {ttext(tn)}. В этой таблице все аксиомные схемы, кроме {tn}, тавтологичны, а правила сохраняют "
            "тавтологичность (с. 33–35). Все формулы ниже — теоремы $S^1$. Для каждой установите, тавтологична ли она в "
            "таблице; для нетавтологичной укажите значения и вычислите при них посылку и заключение, и объясните, что "
            f"отсюда следует о её выводах.\n\n{body}")
    return card(5, "V", "iso", "short", SRC8, "S1, независимость, таблицы", cond, "; ".join(ans),
                f"{ttext(tn)}.\n\n" + "\n".join(sol) + "\n\nТавтологичность в таблице переходит от аксиом к теоремам, "
                "выведенным без " + tn + "; поэтому нетавтологичная теорема требует " + tn + ".")


def c8_fill():
    tn = rnd.choice(["A1", "A2", "A4", "A9", "A10"])
    t = IND.TABLES[tn]
    for _ in range(5000):
        a, b = theorem8()
        names = sorted(atoms(a) | atoms(b))
        if len(names) == 3 and len(tex(a)) + len(tex(b)) <= 34:
            rows = [(e, tv(a, e, t), tv(b, e, t), t["ent"](tv(a, e, t), tv(b, e, t))) for e in envs(names)]
            if len({r[1] for r in rows}) > 1:
                break
    hide = set(rnd.sample(range(24), 10))

    def cell(i, j, v):
        return "?" if 3 * i + j in hide else str(v)
    head = f"| ${names[0]}$ | ${names[1]}$ | ${names[2]}$ | посылка | заключение | формула |\n|---|---|---|---|---|---|\n"
    body = "".join(f"| {e[names[0]]} | {e[names[1]]} | {e[names[2]]} | {cell(i, 0, va)} | {cell(i, 1, vb)} | "
                   f"{cell(i, 2, f)} |\n" for i, (e, va, vb, f) in enumerate(rows))
    bad = [i + 1 for i, r in enumerate(rows) if r[3] != 1]
    cond = (f"{CONV} {ttext(tn)}. Заполните пропуски «?» в таблице значений теоремы $S^1$ ${ftex(a, b)}$ по этой таблице "
            f"и установите, тавтологична ли она в ней.\n\n{head}{body}")
    filled = []
    for i, (e, va, vb, f) in enumerate(rows):
        miss = [str(v) for j, v in enumerate((va, vb, f)) if 3 * i + j in hide]
        if miss:
            filled.append(f"строка {i + 1}: " + ", ".join(miss))
    ans = "; ".join(filled) + ("; тавтологична" if not bad else f"; не тавтологична (строки {', '.join(map(str, bad))})")
    sol = f"{ttext(tn)}. Полная таблица:\n\n" + head + "".join(
        f"| {e[names[0]]} | {e[names[1]]} | {e[names[2]]} | {va} | {vb} | {f} |\n" for e, va, vb, f in rows)
    return card(5, "V", "complete", "build", SRC8, "S1, независимость, таблицы", cond, ans, sol)


def c8_diag():
    tn = rnd.choice(["A1", "A2", "A3", "A4", "A7", "A9", "A10"])
    t = IND.TABLES[tn]
    while True:
        rows = []
        while len(rows) < 4:
            a, b = theorem8()
            if len(tex(a)) + len(tex(b)) <= 38 and all((a, b) != r[:2] for r in rows):
                rows.append((a, b, IND.valid(a, b, t)[0]))
        if 1 <= sum(not r[2] for r in rows) <= 3:
            break
    flip = rnd.sample(range(4), 2)
    claim = [(not ok) if i in flip else ok for i, (_, _, ok) in enumerate(rows)]
    body = "\n".join(f"{n + 1}. ${ftex(a, b)}$ — {'тавтологична' if c else 'не тавтологична'}"
                     for n, ((a, b, _), c) in enumerate(zip(rows, claim)))
    cond = (f"{CONV} {ttext(tn)}. Студент проверил в этой таблице четыре теоремы $S^1$. Ровно в двух выводах он ошибся. "
            f"Найдите их и обоснуйте значениями.\n\n{body}")
    ans, sol = [], []
    for n, (a, b, ok) in enumerate(rows):
        if n not in flip:
            continue
        if ok:
            ans.append(f"строка {n + 1}: тавтологична")
            sol.append(f"Строка {n + 1}: при всех наборах формула получает отмеченное значение — тавтологична.")
        else:
            e = IND.valid(a, b, t)[1]
            ans.append(f"строка {n + 1}: не тавтологична ({env_t(e)})")
            sol.append(f"Строка {n + 1}: при {env_t(e)} посылка — {tv(a, e, t)}, заключение — {tv(b, e, t)}; формула "
                       "равна 0.")
    return card(6, "E", "vary", "text", SRC8, "S1, независимость, таблицы, диагностика", cond, "; ".join(ans) +
                f" (таблица для {tn}, с. 33)", "\n".join(sol) + f"\n\nОстальные выводы верны ({ttext(tn)}).")


# ======================================================================== § 9
def subst(f, b, a):
    if f == b:
        return a
    if f[0] == "v":
        return f
    if f[0] == "neg":
        return N(subst(f[1], b, a))
    return (f[0], tuple(subst(c, b, a) for c in f[1]))


def c9_subst():
    for _ in range(500):
        lines = theorem4(rnd.choice([7, 8]), 6)
        letters = sorted(set().union(*(atoms(p) | atoms(q) for p, q, _ in lines)))
        bl = rnd.choice(letters)
        A = rnd.choice([N(D(y, z)), C(x, N(w)), D(u, N(x)), N(C(z, u))])
        new = [(subst(p, V(bl), A), subst(q, V(bl), A), wh) for p, q, wh in lines]
        if not check2(new) and max(len(tex(p)) + len(tex(q)) for p, q, _ in new) <= 58:
            break
    a, b = lines[-1][0], lines[-1][1]
    na, nb = new[-1][0], new[-1][1]
    cond = (f"{CONV} MT1 § 9 (с. 35): если $x \\vdash y$ доказуема в $S^1$, то доказуема и формула, получающаяся "
            "подстановкой высказывания $a$ на место элементарного высказывания $b$ везде, где $b$ входит. Дан вывод "
            f"теоремы ${ftex(a, b)}$:\n\n{show(lines)}\n\nПодставьте ${tex(A)}$ на место ${bl}$ во всех строках, проверьте, "
            "что каждая строка нового списка — снова пример той же схемы или получена по тому же правилу из тех же строк, "
            "и запишите полученную теорему. Объясните, почему так будет для любого вывода в $S^1$.")
    ans = f"${ftex(na, nb)}$; вывод после подстановки — в решении."
    sol = ("Схемы $S^1$ заданы метапеременными (Введение, § 10, с. 14): подстановка в пример схемы даёт пример той же "
           "схемы; R1, R2, R3 связывают строки по их виду, и подстановка во все строки этот вид сохраняет. Поэтому "
           "подстановка в каждую строку вывода даёт вывод (MT1 § 9, с. 35):\n\n" + show(new))
    return card(6, "D", "transfer", "proof", "с. 14, 35, гл. 1, § 9", "S1, правило подстановки", cond, ans, sol)


# ======================================================================== сборка
def plan():
    P = {"01.01-001": full_card, "01.01-002": full_diag_card, "01.01-003": fold_card, "01.01-004": conj_deriv_card}
    one = {49: r3_deriv_card, 50: build_deriv_card, 51: r3_complete_card, 52: build_deriv_card, 53: r3_deriv_card,
           54: r3_complete_card, 55: build_deriv_card, 56: r3_deriv_card, 57: build_deriv_card, 58: r3_deriv_card,
           63: r3_deriv_card, 64: build_deriv_card, 65: research_card, 66: research_card,
           67: r3_diag_card, 68: r3_diag_card, 69: r3_diag_card, 70: r3_diag_card,
           76: r3_complete_card, 77: build_deriv_card,
           79: research_card, 80: research_card, 81: research_card, 83: research_card, 84: research_card,
           85: research_card, 87: r3_deriv_card, 88: research_card, 89: research_card, 91: r3_deriv_card,
           92: research_card, 93: r3_deriv_card,
           95: false_card, 96: false_card, 97: r3_diag_card, 98: false_card, 99: false_card, 100: r3_diag_card,
           101: false_card, 102: false_card}
    P.update({f"01.01-{n:03d}": fn for n, fn in one.items()})
    P.update({"01.03-001": c3_complete, "01.03-002": c3_expand, "01.03-003": c3_fold, "01.03-004": c3_exp_diag,
              "01.03-005": c3_diag2, "01.03-006": c3_deriv, "01.03-007": c3_false,
              "01.04-001": c4_series, "01.04-002": c4_diag,
              "01.05-001": c5_table_fill, "01.05-003": c5_zero_sets, "01.05-004": c5_joint, "01.05-005": c5_mt3,
              "01.05-006": c5_equal, "01.05-007": c5_calc_diag, "01.05-015": c5_mt_diag, "01.05-016": c5_a9_diag,
              "01.06-001": c6_series, "01.07-004": c7_canon, "01.07-005": c7_canon_diag,
              "01.08-001": c8_table, "01.08-002": c8_fill, "01.08-003": c8_diag, "01.09-001": c9_subst})
    return P


def render(cid, c):
    sec = int(cid[3:5])
    extra = ('generated: true\n' if c.get("gen") else "") + (f'series: {c["series"]}\n' if c.get("series") else "")
    return (f'---\nid: "{cid}"\nchapter: 1\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\nstep: {c["step"]}\n'
            f'condition: def\nform: {c["form"]}\nanswer: {c["answer"]}\nsource: "{c["source"]}"\nsystem: "S^1"\n'
            f'{extra}tags: [{c["tags"]}]\n---\n\n## Условие\n\n{c["cond"]}\n\n## Ответ\n\n{c["ans"]}\n\n'
            f'## Решение\n\n{c["sol"]}\n')


def main():
    from hard01_rest_hand import HAND, HAND3
    cards = {cid: fn() for cid, fn in plan().items()}
    cards.update(HAND)
    cards.update(HAND3)
    for cid, c in cards.items():
        assert not test_like(c["cond"]), (cid, c["cond"][:120])
    path = ROOT / "data" / "zadachi" / "01.md"
    parts = re.split(r"(\n=====\n)", path.read_text(encoding="utf-8"))
    done = set()
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(01\.\d\d-\d{3})"', chunk, re.M)
        if m and m.group(1) in cards:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            parts[i] = lead + render(m.group(1), cards[m.group(1)]).rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
            done.add(m.group(1))
    assert done == set(cards), sorted(set(cards) - done)
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {len(done)}")


if __name__ == "__main__":
    main()
