#!/usr/bin/env python3
"""Усложнение гл. 4 «Другие формы следования» (занятия 25–29) по образцу занятия 10.

Заменяет в src/data/zadachi/04.md сгенерированные карточки (в тех же id) трудными:
  § 1 (S³, S₃, Sᵐ) — выводы в S₃ и S³ в 8–12 строк с ограничением A3 (с. 59, 61), дополнение длинных выводов,
        выводы с двумя ошибками (A3 без ограничения и неверное основание), составные замены и почти-примеры A3
        (ограничение книги и ограничение Г. А. Смирнова), серии длинных формул по критерию Sᵐ, сравнение систем,
        «постройте или докажите, что нельзя», трёхзначные таблицы независимости S₃* (с. 62), обычный язык;
  § 2 (S⁴, S₄, S₄*, Sᶜ) — выводы с A15 (язык S¹) и с A12 (язык S₁), выводы в S₄* с A**12 и R*5, дополнение,
        две ошибки (в том числе A3 без ограничения и R*5 без условия), почти-примеры A15, A12, A**12, серии по
        критерию Sᶜ, контрапозиция Sˢ ↔ Sᶜ, сравнение систем, построения, обычный язык;
  § 3 (S⁵) — выводы формул ⊢ x (A^d1, R^d1–R^d3 и схемы S₁), дополнение, две ошибки, почти-примеры A^d1, серии
        формул вырожденного следования, R^d1 и сильное следование, ⊢ ∼(x∼y) и x ⊢ y, правило подстановки MT7;
  § 4 (S⁶) — выводы «парадоксальных» для Sˢ формул через R^k1, дополнение, две ошибки, построение z для R^k1,
        серии по критерию S⁶, сравнение систем, доказательство MT3 (с. 71) с пропусками.
Ручные задачи ступеней 8–10 — hard04_hand.py. Выводы проверяются sys4.check по схемам и правилам параграфа,
строки и ответы — критериями систем (гл. 4, § 1–4; гл. 5, § 2, с. 72–73).

Запуск: python3 src/scripts/gen/hard04.py
"""
import re
import sys
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(HERE))
import hard04_lib as H  # noqa: E402
from hard04_lib import rnd, x, y, z, u, w, size, rule_count, derivation, deg_derivation, q_derivation, all_ok  # noqa
import sys4 as S4  # noqa: E402
import systems as SY  # noqa: E402
from s1 import C, D, N, V, atoms  # noqa: E402
from s1w import W  # noqa: E402
from open_form import test_like  # noqa: E402
from hard04_hand import HAND  # noqa: E402

L = "абвгдежз"


def T(f, lang="w"):
    return S4.tex(f, lang)


def FT(a, b, lang="w"):
    return S4.ltex(a, b, lang)


def cap(s):
    return s[:1].upper() + s[1:]


def enters(s):
    """(«входит», «которого») или («входят», «которых») — по числу элементарных высказываний."""
    return ("входят", "которых") if len(s) > 1 else ("входит", "которого")


def lst(s):
    return ", ".join(f"${t}$" for t in sorted(s))


def env_t(e):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(e.items()))


CONV_W = ("Буквы $p, q, r, s, t$ — элементарные высказывания; $\\vee$ — соединительная дизъюнкция («по крайней мере "
          "одно из», гл. 2, § 1, с. 36); запись — по соглашению книги.")
CONV_C = ("Буквы $p, q, r, s, t$ — элементарные высказывания; «$:$» — сильная дизъюнкция («одно и только одно из», "
          "с. 22); запись — по соглашению книги (с. 15).")
SYSN = {"S_3": "$S_3$", "S^3": "$S^3$", "S_4": "$S_4$", "S_4*": "$S_4^*$", "S^4": "$S^4$", "S^5": "$S^5$",
        "S^6": "$S^6$"}


def LANG(s):
    return S4.SYSTEMS[s]["lang"]


def CONV(s):
    return CONV_W if LANG(s) == "w" else CONV_C


RULES12 = ("Правила (гл. 1, § 1, с. 17): R1 — если $x \\vdash y$ и $y \\vdash z$, то $x \\vdash z$; R2 — если "
           "$x \\vdash y$ и $x \\vdash z$, то $x \\vdash yz$; R3 — замена вхождения на взаимно выводимое.")
SCH_W = ("Схемы $S_1$ (гл. 2, § 1, с. 36): A1 $\\sim\\sim x \\vdash x$; A2 $x \\vdash \\sim\\sim x$; A3 $xy \\vdash x$; "
         "A4 $xy \\vdash yx$; A5, A6 — расстановка и снятие скобок в конъюнкции; A7 $(x \\vee y)z \\vdash xz \\vee y$; "
         "A8 $xz \\vee yz \\vdash (x \\vee y)z$; A9 $\\sim(x^1 \\ldots x^n) \\vdash \\sim x^1 \\vee \\ldots \\vee \\sim x^n$; "
         "A10 — обратная к A9; A11 $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$. " + RULES12)
SCH_C = ("Схемы $S^1$ (гл. 1, § 1, с. 15–16): A1 $x \\vdash \\sim\\sim x$; A2 $\\sim\\sim x \\vdash x$; A3 $xy \\vdash x$; "
         "A4 $xy \\vdash yx$; A5, A6 — расстановка и снятие скобок в конъюнкции; A7 $\\sim(xy) \\vdash \\sim xy : x\\sim y "
         ": \\sim x\\sim y$; A8 — обратная к A7; A9 $\\sim(x : y) \\vdash xy : \\sim x\\sim y$; A10 — обратная к A9. "
         + RULES12)
R3TXT = (" $S_3$ образуется из $S_1$ ограничением A3: в $y$ входят только те элементарные высказывания, которые входят в "
         "$x$ (гл. 4, § 1, с. 59, 61).")
SCH = {
    "S_3": SCH_W + R3TXT,
    "S_4": SCH_W + R3TXT + " $S_4$ получается из $S_3$ добавлением схемы A12 $x \\vdash x \\vee y$ (§ 2, с. 65).",
    "S^3": SCH_C + " $S^3$ получается из $S^1$ ограничением A3: в $y$ входят только те элементарные высказывания, "
                   "которые входят в $x$ (гл. 4, § 1, с. 59).",
}
SCH["S_4*"] = SCH["S_4"] + (" $S_4^*$ получается из $S_4$ заменой A3, A8 и A11 схемой $A^{**}12$ $x \\vdash x(y \\vee "
                            "\\sim y)$ и правилом $R^*5$: если $x \\vdash z$ и в $y$ не входят элементарные высказывания, "
                            "отсутствующие в $z$, то $xy \\vdash z$ (с. 66).")
SCH["S^4"] = SCH["S^3"] + " $S^4$ получается из $S^3$ добавлением A15 $\\sim x \\vdash \\sim(xy)$ (§ 2, с. 62)."
SCH["S^5"] = SCH_W + (" $S^5$ (гл. 4, § 3, с. 67, 70) получается принятием $S^s$ (здесь — $S_1$) и дополнений: "
                      "$\\vdash x$ — формула вырожденного следования (D1); $A^d1$ $\\vdash \\sim(\\sim xx)$; $R^d1$ — если "
                      "$x \\vdash y$ и $\\vdash x$, то $\\vdash y$; $R^d2$ — если $x \\vdash y$ и $\\vdash \\sim y$, то "
                      "$\\vdash \\sim x$; $R^d3$ — если $\\vdash x$ и $\\vdash y$, то $\\vdash xy$.")
SCH["S^6"] = SCH["S^5"] + (" $S^6$ получается из $S^5$ присоединением $R^k1$: если $xz \\vdash y$ и $\\vdash z$, то "
                           "$x \\vdash y$ (§ 4, с. 70).")
NOTE = {
    "S_3": ("Проверка: каждая строка — тавтология, и множества элементарных высказываний посылки и заключения совпадают, "
            "как требует MT1 § 1 (с. 59; $S_3$ эквивалентна $S^3$, с. 61); в каждом применении A3 ограничение выполнено."),
    "S^3": ("Проверка: каждая строка — тавтология, и множества элементарных высказываний посылки и заключения совпадают "
            "(MT1 § 1, с. 59); в каждом применении A3 ограничение выполнено."),
    "S_4": ("Проверка: каждая строка — теорема $S^c$: тавтология, и в посылку не входят элементарные высказывания, "
            "отсутствующие в заключении (MT1 § 2, с. 63; $S_4$ эквивалентна $S^4$, с. 65). Новые элементарные "
            "высказывания в заключение вводит только A12."),
    "S^4": ("Проверка: каждая строка — теорема $S^c$: тавтология, и в посылку не входят элементарные высказывания, "
            "отсутствующие в заключении (MT1 § 2, с. 63). Новые элементарные высказывания в заключение вводит только "
            "A15."),
    "S_4*": ("Проверка: каждая строка — теорема $S^c$: тавтология, и в посылку не входят элементарные высказывания, "
             "отсутствующие в заключении ($S_4^*$ эквивалентна $S_4$, с. 66; MT1 § 2, с. 63)."),
    "S^5": ("Проверка: строки вида $x \\vdash y$ — теоремы $S_1$ (сильные тавтологии), строки вида $\\vdash x$ — "
            "тавтологии (MT1 § 3, с. 67)."),
    "S^6": ("Проверка: строки до $R^k1$ — теоремы $S^5$; последняя строка — тавтология (MT1 § 4, с. 70), но в её "
            "заключение входят элементарные высказывания, отсутствующие в посылке, поэтому без $R^k1$ (в $S^s$) она "
            "недоказуема."),
}
CRIT = {
    "s": ("$S^s$ — тавтология, и в заключение не входят элементарные высказывания, отсутствующие в посылке (гл. 5, § 2, "
          "MT1, с. 72)"),
    "m": ("$S^m$ — тавтология, и множества элементарных высказываний посылки и заключения совпадают (гл. 4, § 1, MT1, "
          "MT5, с. 59–61; гл. 5, § 2, MT2, с. 73)"),
    "c": ("$S^c$ — тавтология, и в посылку не входят элементарные высказывания, отсутствующие в заключении (гл. 4, § 2, "
          "MT1, MT5, с. 63–65; гл. 5, § 2, MT4, с. 73)"),
    "q": "$S^6$ — тавтология; условий на элементарные высказывания нет (гл. 4, § 4, MT1, MT2, с. 70; гл. 5, § 2, MT6, с. 73)",
}
CRIT_D = ("формула $\\vdash x$ доказуема в $S^5$ тогда и только тогда, когда $x$ — тавтология (гл. 4, § 3, MT1, MT4, "
          "с. 67, 69)")
SK = {"s": "$S^s$", "m": "$S^m$", "c": "$S^c$", "q": "$S^6$"}


def card(level, typ, step, ans_kind, src, tags, cond, ans, sol, form="sym", system=None):
    return dict(level=level, type=typ, step=step, form=form, answer=ans_kind, source=src, tags=tags, cond=cond,
                ans=ans, sol=sol, system=system)


SRC = {1: "с. 59–62, гл. 4, § 1", 2: "с. 62–67, гл. 4, § 2", 3: "с. 67–70, гл. 4, § 3", 4: "с. 70–71, гл. 4, § 4"}
TAG = {"S_3": "S3, максимальное следование", "S^3": "S3, максимальное следование", "S_4": "S4, конверсное следование",
       "S^4": "S4, конверсное следование", "S_4*": "S4, конверсное следование", "S^5": "S5, вырожденное следование",
       "S^6": "S6, квазиследование"}
SEC = {"S_3": 1, "S^3": 1, "S_4": 2, "S^4": 2, "S_4*": 2, "S^5": 3, "S^6": 4}


# ---------- построение выводов ----------
def pick2(pool):
    return rnd.sample(pool, 2)


def prem3():
    X, Y = pick2([x, y, z, N(x), N(y)])
    return rnd.choice([C(W(X, Y), X), C(X, W(X, Y)), C(N(N(X)), X), C(W(X, Y), C(Y, X)), C(X, Y, X),
                       W(C(X, Y), C(Y, X)), C(W(X, N(Y)), Y), C(N(C(X, Y)), X, Y)])


def premc3():
    X, Y = pick2([x, y, z, N(x), N(y)])
    return rnd.choice([C(N(C(X, Y)), X), C(D(X, Y), X), C(X, N(N(X))), C(N(D(X, Y)), Y), C(N(C(X, Y)), C(Y, X)),
                       C(D(X, Y), C(X, Y))])


def premc4():
    X, Y = pick2([x, y, N(x), N(y), z])
    return rnd.choice([N(C(X, Y)), N(X), N(D(X, Y)), C(N(X), X), N(N(C(X, Y))), C(N(C(X, Y)), Y)])


def prem4():
    X, Y = pick2([x, y, N(x), N(y), z])
    return rnd.choice([C(W(X, Y), X), N(C(X, Y)), C(X, Y, X), W(X, N(Y)), C(N(N(X)), X), C(X, W(Y, X))])


def prem4s():
    X, Y = pick2([x, y, N(x), N(y)])
    return rnd.choice([N(C(X, Y)), W(N(X), N(Y)), C(W(X, Y), X), N(N(X)), C(X, Y)])


def gen(sysname, want, least):
    lang = LANG(sysname)
    if sysname == "S_3":
        return derivation("S_3", prem3, want, least,
                          accept=lambda ls: rule_count(ls, "A3") >= 1 and 10 <= size(ls[-1][1]) <= 36)
    if sysname == "S^3":
        return derivation("S^3", premc3, want, least, lim=44,
                          accept=lambda ls: rule_count(ls, "A3") >= 1 and 10 <= size(ls[-1][1], "c") <= 44)
    if sysname == "S_4":
        return derivation("S_4", prem4, want, least,
                          accept=lambda ls: rule_count(ls, "A12") >= 1 and not SY.provable("s", ls[-1][0], ls[-1][1]))
    if sysname == "S^4":
        return derivation("S^4", premc4, want, least, lim=44,
                          accept=lambda ls: rule_count(ls, "A15") >= 1 and not SY.provable("s", ls[-1][0], ls[-1][1]))
    if sysname == "S_4*":
        for _ in range(200):
            ls = derivation("S_4*", prem4s, want - 1, least - 1,
                            accept=lambda ls: rule_count(ls, "A12") + rule_count(ls, "A**12") >= 1)
            P, b = ls[-1][0], ls[-1][1]
            ys = [t for t in [x, y, z, u, N(x), N(y)] if atoms(t) <= atoms(b) and t != P]
            if not ys:
                continue
            Y = rnd.choice(ys)
            ls2 = ls + [(C(P, Y), b, ("R*5", len(ls)))]
            if all_ok("S_4*", ls2):
                return ls2
        raise RuntimeError("S_4*")
    if sysname == "S^5":
        return deg_derivation(want, least, need=rnd.choice([("Rd1", "Rd3"), ("Rd1", "Rd2"), ("Rd1",)]))
    if sysname == "S^6":
        return q_derivation(want, least)
    raise ValueError(sysname)


# ---------- вывод ----------
def c_deriv(sysname):
    lang = LANG(sysname)
    lines = gen(sysname, rnd.choice([10, 11]), 9)
    a, b = lines[-1][0], lines[-1][1]
    goal = FT(a, b, lang)
    cond = f"{CONV(sysname)} Выведите в {SYSN[sysname]} формулу ${goal}$. {SCH[sysname]}"
    ans = f"Например, вывод в {len(lines)} строк (см. решение); последняя строка — ${goal}$ [{S4.why_text(lines[-1][2])}]."
    sol = S4.show(lines, lang) + "\n\n" + NOTE[sysname]
    return card(7 if len(lines) >= 10 else 6, "D", "open", "proof", SRC[SEC[sysname]], TAG[sysname] + ", вывод", cond,
                ans, sol, system=sysname)


def c_complete(sysname):
    lang = LANG(sysname)
    lines = gen(sysname, rnd.choice([10, 11]), 10)
    n = len(lines)
    sl = [k for k, (*_, wh) in enumerate(lines, 1) if isinstance(wh, str) and 1 < k < n]
    rl = [k for k, (*_, wh) in enumerate(lines, 1) if not isinstance(wh, str) and k < n]
    hide_f = set(rnd.sample(sl, min(2, max(1, len(sl) - 1))))
    rest = [k for k in sl if k not in hide_f]
    hide_why = set(rnd.sample(rest, min(2, len(rest)))) | set(rnd.sample(rl, min(2, len(rl))))
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV(sysname)} В выводе в {SYSN[sysname]} формулы ${FT(a, b, lang)}$ пропущены основания некоторых шагов "
            f"и формулы некоторых строк («…»). Восстановите их и проверьте каждый восстановленный шаг по схемам и "
            f"правилам системы.\n\n{S4.show(lines, lang, hide_why, hide_f)}\n\n{SCH[sysname]}")
    parts = []
    for k in sorted(hide_why | hide_f):
        la, lb, wh = lines[k - 1]
        parts.append((f"{k} — " + (f"${FT(la, lb, lang)}$ " if k in hide_f else "") +
                      (f"[{S4.why_text(wh)}]" if k in hide_why else "")).strip())
    sol = ("Формулу строки восстанавливаем по соседним: в R1 заключение одной строки — посылка другой, в R2 обе строки "
           "имеют общую посылку, в правилах для $\\vdash x$ формула строки входит в результат; основание — по виду "
           "формулы.\n\n" + S4.show(lines, lang) + "\n\n" + NOTE[sysname])
    return card(5, "D", "complete", "build", SRC[SEC[sysname]], TAG[sysname] + ", вывод, дополнение", cond,
                "; ".join(parts), sol, system=sysname)


# ---------- две ошибки ----------
WRONG = {"w": {"A1": "A2", "A2": "A1", "A3": "A4", "A4": "A3", "A9": "A10", "A10": "A9", "A7": "A8", "A8": "A7",
               "A5": "A6", "A6": "A5", "A11": "A7", "A**12": "A12"},
         "c": {"A1": "A2", "A2": "A1", "A3": "A4", "A4": "A3", "A7": "A8", "A8": "A7", "A9": "A10", "A10": "A9",
               "A15": "A3", "A5": "A6", "A6": "A5"}}
WHY = {"w": {"A1": "в $S_1$ A1 — $\\sim\\sim x \\vdash x$ (снятие двойного отрицания), A2 — $x \\vdash \\sim\\sim x$ (с. 36)",
             "A2": "в $S_1$ A2 — $x \\vdash \\sim\\sim x$ (введение двойного отрицания), A1 — обратная (с. 36)",
             "A3": "A3 $xy \\vdash x$ оставляет первый член конъюнкции, A4 переставляет члены (с. 36)",
             "A4": "A4 $xy \\vdash yx$ переставляет члены конъюнкции, A3 оставляет первый член (с. 36)",
             "A9": "A9 раскрывает отрицание конъюнкции в дизъюнкцию отрицаний, A10 — обратный переход (с. 36)",
             "A10": "A10 собирает дизъюнкцию отрицаний в отрицание конъюнкции, A9 — обратный переход (с. 36)",
             "A7": "A7 — $(x \\vee y)z \\vdash xz \\vee y$, A8 — $xz \\vee yz \\vdash (x \\vee y)z$ (с. 36)",
             "A8": "A8 — $xz \\vee yz \\vdash (x \\vee y)z$, A7 — $(x \\vee y)z \\vdash xz \\vee y$ (с. 36)",
             "A5": "A5 расставляет скобки в конъюнкции без скобок, A6 снимает их (с. 16, 36)",
             "A6": "A6 снимает скобки в конъюнкции, A5 расставляет их (с. 16, 36)",
             "A11": "A11 — $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$, A7 — $(x \\vee y)z \\vdash xz \\vee y$ (с. 36)",
             "A**12": ("A12 — $x \\vdash x \\vee y$ (с. 65); здесь к посылке присоединено конъюнктивно $y \\vee \\sim y$: "
                       "это $A^{**}12$ $x \\vdash x(y \\vee \\sim y)$ (с. 66)")},
       "c": {"A1": "в $S^1$ A1 — $x \\vdash \\sim\\sim x$ (введение двойного отрицания), A2 — обратная (с. 15)",
             "A2": "в $S^1$ A2 — $\\sim\\sim x \\vdash x$ (снятие двойного отрицания), A1 — обратная (с. 15)",
             "A3": "A3 $xy \\vdash x$ оставляет первый член конъюнкции, A4 переставляет члены (с. 15–16)",
             "A4": "A4 $xy \\vdash yx$ переставляет члены конъюнкции, A3 оставляет первый член (с. 15–16)",
             "A7": "A7 раскрывает $\\sim(xy)$ в $\\sim xy : x\\sim y : \\sim x\\sim y$, A8 — обратный переход (с. 16)",
             "A8": "A8 собирает $\\sim xy : x\\sim y : \\sim x\\sim y$ в $\\sim(xy)$, A7 — обратный переход (с. 16)",
             "A9": "A9 раскрывает $\\sim(x : y)$ в $xy : \\sim x\\sim y$, A10 — обратный переход (с. 16)",
             "A10": "A10 собирает $xy : \\sim x\\sim y$ в $\\sim(x : y)$, A9 — обратный переход (с. 16)",
             "A5": "A5 расставляет скобки в конъюнкции без скобок, A6 снимает их (с. 16)",
             "A6": "A6 снимает скобки в конъюнкции, A5 расставляет их (с. 16)",
             "A15": ("A3 $xy \\vdash x$ отбрасывает член конъюнкции; здесь из $\\sim x$ получено $\\sim(xy)$ — это A15 "
                     "$S^4$ $\\sim x \\vdash \\sim(xy)$ (с. 62)")}}
RWRONG = {"R1": "R2", "Rd1": "R1", "Rd3": "R2", "Rd2": "Rd1", "Rk1": "Rd1"}
RWHY = {"R1": "R2 соединяет в конъюнкцию заключения двух строк с общей посылкой, а здесь заключение строки {i} — посылка "
              "строки {j}: это R1 (с. 17)",
        "Rd1": "R1 связывает две формулы следования, а строка {j} — формула вырожденного следования; из $x \\vdash y$ "
               "(строка {i}) и $\\vdash x$ (строка {j}) получаем $\\vdash y$ по $R^d1$ (с. 67)",
        "Rd3": "R2 применяется к формулам $x \\vdash y$ и $x \\vdash z$ с общей посылкой, а строки {i} и {j} — формулы "
               "вырожденного следования; $\\vdash xy$ из $\\vdash x$ и $\\vdash y$ — это $R^d3$ (с. 70)",
        "Rd2": "по $R^d1$ из $x \\vdash y$ и $\\vdash x$ получается $\\vdash y$; здесь даны $x \\vdash y$ (строка {i}) и "
               "$\\vdash \\sim y$ (строка {j}), а получено $\\vdash \\sim x$ — это $R^d2$ (с. 70)",
        "Rk1": "$R^d1$ даёт формулу вырожденного следования $\\vdash y$, а здесь из $xz \\vdash y$ (строка {i}) и "
               "$\\vdash z$ (строка {j}) получена формула $x \\vdash y$ — это $R^k1$ (с. 70)"}
RNAME = {"R1": "R1", "R2": "R2", "Rd1": "$R^d1$", "Rd2": "$R^d2$", "Rd3": "$R^d3$", "Rk1": "$R^k1$"}


def wname(s):
    return S4.why_text(s)


def c_diag2(sysname):
    """Два неверно названных основания (схема и правило)."""
    lang = LANG(sysname)
    for _ in range(400):
        lines = gen(sysname, rnd.choice([8, 9, 10]), 7)
        cand = [k for k, (*_, wh) in enumerate(lines) if isinstance(wh, str) and wh in WRONG[lang]]
        cand = [k for k in cand if lines[k][2] in ("A15", "A**12")] or cand
        rs = [k for k, (*_, wh) in enumerate(lines) if not isinstance(wh, str) and wh[0] in RWRONG]
        if not cand or not rs:
            continue
        pri = [k for k in rs if lines[k][2][0] != "R1"] or rs
        i, j = rnd.choice(cand), rnd.choice(pri)
        bad = list(lines)
        a, b, wh = bad[i]
        bad[i] = (a, b, WRONG[lang][wh])
        a2, b2, wh2 = bad[j]
        bad[j] = (a2, b2, (RWRONG[wh2[0]], *wh2[1:]))
        errs = S4.check(sysname, bad)
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        if steps == sorted([i + 1, j + 1]):
            break
    else:
        raise RuntimeError("нет вывода для диагностики")
    p, q = sorted([i, j])
    cond = (f"{CONV(sysname)} В выводе в {SYSN[sysname]} формулы ${FT(lines[-1][0], lines[-1][1], lang)}$ ровно два "
            f"основания указаны неверно. Найдите их, объясните, почему каждое неверно, и исправьте.\n\n"
            f"{S4.show(bad, lang)}\n\n{SCH[sysname]}")
    ans, exp = [], []
    for k in (p, q):
        a, b, wh = lines[k]
        if k == i:
            ans.append(f"шаг {k + 1}: {wname(wh)}, а не {wname(WRONG[lang][wh])}")
            exp.append(f"Шаг {k + 1}: ${FT(a, b, lang)}$ — пример {wname(wh)}: {WHY[lang][wh]}.")
        else:
            ans.append(f"шаг {k + 1}: {RNAME[wh[0]]}, а не {RNAME[RWRONG[wh[0]]]}")
            exp.append(f"Шаг {k + 1}: " + RWHY[wh[0]].format(i=wh[1], j=wh[2]) + ".")
    ans_t = cap("; ".join(ans)) + " (страницы — в решении)."
    sol = "\n".join(exp) + "\n\nИсправленный вывод:\n\n" + S4.show(lines, lang)
    return card(6, "E", "vary", "text", SRC[SEC[sysname]], TAG[sysname] + ", вывод, диагностика", cond, ans_t, sol,
                system=sysname)


def premF():
    X, Y, Z = rnd.sample([x, y, z, N(x), N(y), u], 3)
    return rnd.choice([C(W(X, Y), Z), C(X, Y, Z), C(X, W(Y, Z)), N(C(X, Y)), W(C(X, Z), C(Y, Z)), C(X, Y)])


def bad_a3(ls):
    return [k for k, (a, b, wh) in enumerate(ls) if wh == "A3" and not S4.a3_restricted(a, b)]


def c_diag_fatal(sysname):
    """A3 без ограничения (S_3, S_4) или R*5 без условия (S_4*) — и одно неверно названное основание."""
    lang = "w"
    key = "m" if sysname == "S_3" else "c"
    for _ in range(400):
        if sysname in ("S_3", "S_4"):
            base = "S_1" if sysname == "S_3" else "S_1A12"
            acc = (lambda ls: len(bad_a3(ls)) == 1) if sysname == "S_3" else \
                (lambda ls: len(bad_a3(ls)) == 1 and rule_count(ls, "A12") >= 1)
            try:
                lines = derivation(base, premF, rnd.choice([8, 9]), 7, accept=acc)
            except RuntimeError:
                continue
            f = bad_a3(lines)[0]
        else:
            lines = derivation("S_4*", prem4s, 7, 6,
                               accept=lambda ls: rule_count(ls, "A12") + rule_count(ls, "A**12") >= 1)
            P, b = lines[-1][0], lines[-1][1]
            ys = [t for t in [u, w, N(u), C(u, w)] if not atoms(t) <= atoms(b) and not atoms(t) <= atoms(P)]
            lines = lines + [(C(P, rnd.choice(ys)), b, ("R*5", len(lines)))]
            f = len(lines) - 1
        if [int(re.match(r"шаг (\d+)", e).group(1)) for e in S4.check(sysname, lines)] != [f + 1]:
            continue
        cand = [k for k, (*_, wh) in enumerate(lines) if k != f and
                ((isinstance(wh, str) and wh in WRONG[lang] and wh != "A3") or (not isinstance(wh, str) and wh[0] == "R1"))]
        if not cand:
            continue
        m = rnd.choice(cand)
        bad = list(lines)
        a, b, wh = bad[m]
        bad[m] = (a, b, WRONG[lang][wh] if isinstance(wh, str) else ("R2", *wh[1:]))
        errs = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in S4.check(sysname, bad)})
        if errs == sorted([f + 1, m + 1]):
            break
    else:
        raise RuntimeError("нет вывода с ошибкой")
    a, b = lines[-1][0], lines[-1][1]
    fa, fb, fwh = lines[f]
    if fwh == "A3":
        X, Y = fa[1]
        miss = atoms(Y) - atoms(X)
        e1 = (f"шаг {f + 1}: не аксиома {SYSN[sysname]} — нарушено ограничение A3 (с. 59, 61)")
        x1 = (f"Шаг {f + 1}: ${FT(fa, fb)}$ — пример A3 $S_1$ ($x$ := ${T(X)}$, $y$ := ${T(Y)}$), но во второй член "
              f"конъюнкции {enters(miss)[0]} {lst(miss)}, {enters(miss)[1]} нет в первом. В {SYSN[sysname]} A3 ограничена: в $y$ входят "
              f"только элементарные высказывания, которые входят в $x$ (с. 59, 61). Другие схемы и правила эту строку "
              f"тоже не дают: по MT1 {'§ 1 (с. 59)' if sysname == 'S_3' else '§ 2 (с. 63)'} в каждой теореме "
              + ("множества элементарных высказываний посылки и заключения совпадают." if sysname == "S_3" else
                 "в посылку не входят элементарные высказывания, отсутствующие в заключении."))
    else:
        Y = fa[1][1]
        miss = atoms(Y) - atoms(fb)
        e1 = f"шаг {f + 1}: $R^*5$ неприменимо — нарушено его условие (с. 66)"
        x1 = (f"Шаг {f + 1}: по $R^*5$ из $x \\vdash z$ получаем $xy \\vdash z$, только если в $y$ не входят элементарные "
              f"высказывания, отсутствующие в $z$ (с. 66). Здесь в $y$ = ${T(Y)}$ {enters(miss)[0]} {lst(miss)}, "
              f"{enters(miss)[1]} нет в $z$ = ${T(fb)}$. Шаг не обоснован.")
    ma, mb, mwh = lines[m]
    if isinstance(mwh, str):
        e2 = f"шаг {m + 1}: {wname(mwh)}, а не {wname(WRONG[lang][mwh])}"
        x2 = f"Шаг {m + 1}: ${FT(ma, mb)}$ — пример {wname(mwh)}: {WHY[lang][mwh]}."
    else:
        e2 = f"шаг {m + 1}: R1, а не R2"
        x2 = f"Шаг {m + 1}: " + RWHY["R1"].format(i=mwh[1], j=mwh[2]) + "."
    prov = SY.provable(key, a, b)
    if prov:
        fin = (f"Заключительная формула тем не менее доказуема в {SYSN[sysname]} (другим выводом): она удовлетворяет "
               f"критерию {CRIT[key]}.")
        fin_s = "заключительная формула доказуема другим выводом"
    else:
        fin = (f"Заключительная формула в {SYSN[sysname]} недоказуема: {SY.reason(key, a, b, T)}. Критерий "
               f"{CRIT[key]}.")
        fin_s = "заключительная формула недоказуема"
    cond = (f"{CONV_W} Студент построил вывод в {SYSN[sysname]} формулы ${FT(a, b)}$. В нём ровно две ошибки. Найдите "
            f"их, объясните и исследуйте доказуемость заключительной формулы в {SYSN[sysname]}: если вывод нельзя "
            f"исправить, докажите, что формула недоказуема.\n\n{S4.show(bad)}\n\n{SCH[sysname]}")
    ans = cap("; ".join([e1, e2] if f < m else [e2, e1])) + f"; {fin_s}."
    sol = "\n".join([x1, x2] if f < m else [x2, x1]) + "\n\n" + fin
    return card(6, "E", "vary", "text", SRC[SEC[sysname]], TAG[sysname] + ", вывод, диагностика", cond, ans, sol,
                system=sysname)


# ---------- формулы ----------
def rnd_form(names, depth, lang="w"):
    dis = "wdis" if lang == "w" else "dis"
    if depth == 0 or rnd.random() < 0.22:
        v = V(rnd.choice(names))
        return N(v) if rnd.random() < 0.35 else v
    k = rnd.random()
    if k < 0.16:
        s_ = rnd_form(names, depth - 1, lang)
        return N(s_) if s_[0] != "neg" else s_
    op = "conj" if k < 0.58 else dis
    a, b = rnd_form(names, depth - 1, lang), rnd_form(names, depth - 1, lang)
    return (op, (a, b)) if a != b else a


FSEEN = set()


def find(pred, na="pqr", nb="pqr", depth=2, lang="w", lo=16, hi=46, tries=20000):
    for _ in range(tries):
        a, b = rnd_form(na, depth, lang), rnd_form(nb, depth, lang)
        s = size(a, lang) + size(b, lang)
        if lo <= s <= hi and a != b and (a, b) not in FSEEN and pred(a, b):
            FSEEN.add((a, b))
            return a, b
    raise RuntimeError("формула не найдена")


def kind_pred(k, kind):
    if kind == "yes":
        return lambda a, b: SY.provable(k, a, b) and (k != "q" or not SY.cond("s", a, b))
    if kind == "cond":
        return lambda a, b: SY.taut(a, b) and not SY.cond(k, a, b)
    if kind == "taut":
        return lambda a, b: SY.cond(k, a, b) and not SY.taut(a, b)
    if kind == "strong":
        return lambda a, b: SY.provable("s", a, b)
    if kind == "no":
        return lambda a, b: not SY.taut(a, b)
    raise ValueError(kind)


def verdict(k, a, b):
    return "доказуема" if SY.provable(k, a, b) else "недоказуема"


def why(k, a, b):
    r = SY.reason(k, a, b, T)
    return r[0].upper() + r[1:]


def c_series(k, lang, sec, level=6):
    kinds = {"m": ["yes", "cond", "taut", rnd.choice(["yes", "cond"])],
             "c": ["yes", "cond", "taut", rnd.choice(["yes", "cond"])],
             "q": ["yes", "yes", "no", rnd.choice(["strong", "no"])]}[k]
    rnd.shuffle(kinds)
    nb = "pqr" if k != "c" else "pqrs"
    items = [find(kind_pred(k, kd), na="pqr", nb=nb, depth=rnd.choice([2, 3]), lang=lang, lo=20, hi=48)
             for kd in kinds]
    conv = CONV_W if lang == "w" else CONV_C
    cond = (f"{conv} Исследуйте доказуемость в {SK[k]} каждой формулы и обоснуйте: для доказуемой — по критерию, для "
            f"недоказуемой — набором значений, при котором посылка 1, а заключение 0, или элементарным высказыванием, "
            f"нарушающим условие системы. Критерий {CRIT[k]}.\n\n" +
            "\n".join(f"{L[i]}) ${FT(a, b, lang)}$" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {verdict(k, a, b)}" for i, (a, b) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {why(k, a, b)}: {verdict(k, a, b)}." for i, (a, b) in enumerate(items))
    sol += f"\n\nКритерий {CRIT[k]}."
    return card(level, "C", "open", "short", SRC[sec], {"m": "Sm", "c": "Sc", "q": "S6"}[k] + ", доказуемость", cond,
                ans, sol)


def claim_for(k, a, b, wrong):
    """Утверждение студента о формуле (верное или неверное)."""
    taut = SY.taut(a, b)
    prov = SY.provable(k, a, b)
    if not wrong:
        if prov:
            return "доказуема: тавтология, и условие системы выполнено"
        if not taut:
            return f"недоказуема: при {env_t(SY.counter(a, b))} посылка 1, заключение 0"
        return "недоказуема: тавтология, но условие системы на элементарные высказывания нарушено"
    if prov:
        return rnd.choice(["недоказуема: в заключении больше элементарных высказываний, чем нужно",
                           "недоказуема: посылка и заключение имеют разный вид"])
    if taut:
        return "доказуема: это тавтология"
    return "доказуема: условие системы на элементарные высказывания выполнено"


def c_series_diag(k, lang, sec, level=6):
    kinds = {"m": ["yes", "cond", "taut", "yes"], "c": ["yes", "cond", "taut", "yes"],
             "q": ["yes", "no", "strong", "no"]}[k]
    rnd.shuffle(kinds)
    items = [find(kind_pred(k, kd), na="pqr", nb="pqrs" if k == "c" else "pqr", depth=2, lang=lang, lo=18, hi=44)
             for kd in kinds]
    wrong = rnd.sample(range(4), 2)
    conv = CONV_W if lang == "w" else CONV_C
    rows = "\n".join(f"{i + 1}. ${FT(a, b, lang)}$ — {claim_for(k, a, b, i in wrong)}." for i, (a, b) in enumerate(items))
    cond = (f"{conv} Студент исследовал доказуемость четырёх формул в {SK[k]}:\n\n{rows}\n\nРовно два вывода неверны. "
            f"Найдите их, объясните ошибку и дайте верный ответ с обоснованием. Критерий {CRIT[k]}.")
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        if i in wrong:
            ans.append(f"{i + 1}: {verdict(k, a, b)}")
            sol.append(f"{i + 1}. Неверно. {why(k, a, b)}: формула {verdict(k, a, b)}.")
    page = {"m": "гл. 4, § 1, MT1, MT5, с. 59–61", "c": "гл. 4, § 2, MT1, MT5, с. 63–65", "q": "гл. 4, § 4, MT1, MT2, с. 70"}[k]
    return card(level, "E", "vary", "text", SRC[sec], {"m": "Sm", "c": "Sc", "q": "S6"}[k] + ", доказуемость, диагностика",
                cond, "Неверны выводы " + "; ".join(ans) + f" (критерий: {page}).", "\n".join(sol) + "\n\nОстальные выводы верны.")


# ---------- сравнение систем ----------
def sys_row(a, b):
    return ", ".join(f"{SK[k]} — {'да' if SY.provable(k, a, b) else 'нет'}" for k in "smcq")


def c_compare(sec, lang="w", level=7):
    preds = [lambda a, b: SY.taut(a, b) and atoms(b) < atoms(a),
             lambda a, b: SY.taut(a, b) and atoms(a) < atoms(b),
             lambda a, b: SY.taut(a, b) and not (atoms(a) <= atoms(b)) and not (atoms(b) <= atoms(a)),
             lambda a, b: SY.taut(a, b) and atoms(a) == atoms(b),
             lambda a, b: not SY.taut(a, b) and atoms(a) == atoms(b)]
    ch = rnd.sample(range(5), 3)
    items = [find(preds[i], na="pqr", nb="pqrs", depth=2, lang=lang, lo=16, hi=40) for i in ch]
    conv = CONV_W if lang == "w" else CONV_C
    cond = (f"{conv} Для каждой формулы исследуйте доказуемость в $S^s$, $S^m$, $S^c$ и $S^6$ и обоснуйте по "
            f"критериям: {CRIT['s']}; {CRIT['m']}; {CRIT['c']}; {CRIT['q']}.\n\n" +
            "\n".join(f"{L[i]}) ${FT(a, b, lang)}$" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {sys_row(a, b)}" for i, (a, b) in enumerate(items))
    sol = []
    for i, (a, b) in enumerate(items):
        if SY.taut(a, b):
            t = "тавтология"
        else:
            t = f"не тавтология: при {env_t(SY.counter(a, b))} посылка 1, заключение 0 — недоказуема ни в одной системе"
        sol.append(f"{L[i]}) {t[0].upper() + t[1:]}. Элементарные высказывания посылки: {lst(atoms(a))}; заключения: "
                   f"{lst(atoms(b))}. Итог: {sys_row(a, b)}.")
    return card(level, "S", "transfer", "short", "с. 59–73, гл. 4, § 1–4; гл. 5, § 2", "системы, сравнение", cond, ans,
                "\n".join(sol))


def c_compare_diag(sec, lang="w", level=6):
    a, b = find(lambda a, b: SY.taut(a, b) and atoms(a) != atoms(b) and bool(atoms(a) & atoms(b)), na="pqr", nb="pqrs",
                depth=2, lang=lang, lo=18, hi=40)
    truth = {k: SY.provable(k, a, b) for k in "smcq"}
    flip = rnd.sample("smc", 2)
    claim = {k: (not v) if k in flip else v for k, v in truth.items()}
    reasons = {True: "доказуема", False: "недоказуема"}
    conv = CONV_W if lang == "w" else CONV_C
    rows = "\n".join(f"- {SK[k]}: {reasons[claim[k]]}" for k in "smcq")
    cond = (f"{conv} Студент исследовал формулу ${FT(a, b, lang)}$ в четырёх системах и пришёл к выводам:\n\n{rows}\n\n"
            f"Ровно два вывода неверны. Найдите их и обоснуйте верный ответ. Критерии: {CRIT['s']}; {CRIT['m']}; "
            f"{CRIT['c']}; {CRIT['q']}.")
    pg = {"s": "гл. 5, § 2, MT1, с. 72", "m": "гл. 4, § 1, MT1, MT5; гл. 5, § 2, MT2", "c": "гл. 4, § 2, MT1, MT5; гл. 5, § 2, MT4"}
    ans = "; ".join(f"{SK[k]} — {reasons[truth[k]]} ({pg[k]})" for k in "smc" if k in flip)
    sol = (f"Формула — тавтология. Элементарные высказывания посылки: {lst(atoms(a))}; заключения: {lst(atoms(b))}.\n" +
           "\n".join(f"{SK[k]}: {SY.reason(k, a, b, T)} — {reasons[truth[k]]}." for k in "smcq"))
    return card(level, "E", "vary", "text", "с. 59–73, гл. 4, § 1–4; гл. 5, § 2", "системы, сравнение, диагностика",
                cond, "Неверны выводы: " + ans + ".", sol)


# ---------- постройте или докажите, что нельзя ----------
def ex_find(pred, lang="w"):
    for _ in range(40000):
        a, b = rnd_form("pqr", 2, lang), rnd_form("pqrs", 2, lang)
        bins = sum(repr(t).count(op) for t in (a, b) for op in ("'conj'", "'wdis'", "'dis'"))
        if bins >= 3 and len(atoms(a) | atoms(b)) >= 3 and pred(a, b) and (a, b) not in FSEEN:
            FSEEN.add((a, b))
            return a, b
    raise RuntimeError


def nontriv(a, b):
    """Посылка — не противоречие, заключение — не тавтология."""
    return any(SY.value(a, e) for e in SY.rows(a)) and not SY.is_taut(b)


BUILD = {
    "c-not-s": ("доказуемую в $S^c$, но недоказуемую в $S^s$", True,
                lambda a, b: SY.provable("c", a, b) and not SY.provable("s", a, b) and nontriv(a, b)),
    "s-not-m": ("доказуемую в $S^s$, но недоказуемую в $S^m$", True,
                lambda a, b: SY.provable("s", a, b) and not SY.provable("m", a, b) and nontriv(a, b)),
    "q-not-sc": ("доказуемую в $S^6$, но недоказуемую ни в $S^s$, ни в $S^c$", True,
                 lambda a, b: SY.provable("q", a, b) and not SY.provable("s", a, b) and not SY.provable("c", a, b)
                 and nontriv(a, b)),
    "m-not-s": ("доказуемую в $S^m$, но недоказуемую в $S^s$", False,
                "Такой формулы нет. По критерию $S^m$ формула — тавтология, и множества элементарных высказываний "
                "посылки и заключения совпадают. Тогда в заключение не входят элементарные высказывания, отсутствующие "
                "в посылке, — выполнен и критерий $S^s$, и формула доказуема в $S^s$."),
    "sc-not-m": ("доказуемую и в $S^s$, и в $S^c$, но недоказуемую в $S^m$", False,
                 "Такой формулы нет. Из доказуемости в $S^s$: формула — тавтология, и множество элементарных "
                 "высказываний заключения содержится в множестве посылки; из доказуемости в $S^c$: множество посылки "
                 "содержится в множестве заключения. Два множества, каждое из которых содержится в другом, совпадают — "
                 "выполнен критерий $S^m$, и формула доказуема в $S^m$."),
    "c-not-q": ("доказуемую в $S^c$, но недоказуемую в $S^6$", False,
                "Такой формулы нет. Доказуемая в $S^c$ формула — тавтология (критерий $S^c$), а по MT2 § 4 (с. 70) "
                "всякая тавтология $x \\vdash y$ доказуема в $S^6$."),
    "m-not-c": ("доказуемую в $S^m$, но недоказуемую в $S^c$", False,
                "Такой формулы нет. Доказуемая в $S^m$ формула — тавтология с совпадающими множествами элементарных "
                "высказываний посылки и заключения; тогда в посылку не входят элементарные высказывания, отсутствующие "
                "в заключении, — выполнен критерий $S^c$."),
}


def c_build(combo, sec, level=7):
    what, exists, rule = BUILD[combo]
    req = ("в формуле не меньше трёх бинарных операторов и не меньше трёх элементарных высказываний, посылка — не "
           "противоречие, заключение — не тавтология")
    cond = (f"{CONV_W} Постройте формулу следования {what}, у которой {req}, или докажите, что такой формулы нет. "
            f"Критерии: {CRIT['s']}; {CRIT['m']}; {CRIT['c']}; {CRIT['q']}.")
    if exists:
        a, b = ex_find(rule)
        ans = f"Например, ${FT(a, b)}$ (возможны и другие)."
        sol = (f"Проверка примера ${FT(a, b)}$. Формула — тавтология (нет набора значений, при котором посылка 1, а "
               f"заключение 0); посылка истинна, например, при {env_t(next(e for e in SY.rows(a) if SY.value(a, e)))}; "
               f"заключение ложно при {env_t(next(e for e in SY.rows(b) if not SY.value(b, e)))}. Элементарные "
               f"высказывания посылки: {lst(atoms(a))}; заключения: {lst(atoms(b))}.\n" +
               "\n".join(f"{SK[k]}: {SY.reason(k, a, b, T)} — {verdict(k, a, b)}." for k in "smcq"))
        typ = "P" if combo == "q-not-sc" else "C"
    else:
        ans = "Такой формулы нет (см. доказательство)."
        sol = rule
        typ = "M"
    return card(level, typ, "open", "build", "с. 59–73, гл. 4, § 1–4; гл. 5, § 2", "системы, построение", cond, ans, sol)


# ---------- обычный язык ----------
PH = {"p": ("идёт дождь", "дождь не идёт"), "q": ("дует ветер", "ветер не дует"), "r": ("холодно", "не холодно"),
      "s": ("светит солнце", "солнце не светит")}


def lit_nl(f):
    return PH[f[1]][0] if f[0] == "v" else PH[f[1][1]][1]


def is_lit(f):
    return f[0] == "v" or (f[0] == "neg" and f[1][0] == "v")


def small_nl(f):
    if is_lit(f):
        return lit_nl(f)
    if f[0] == "neg":
        return "неверно, что " + small_nl(f[1])
    parts = [lit_nl(t) for t in f[1]]
    return " и ".join(parts) if f[0] == "conj" else " или ".join(parts) + " (или то и другое)"


def nl(f):
    if is_lit(f) or all(is_lit(t) for t in f[1] if f[0] != "neg") and f[0] != "neg":
        return small_nl(f)
    if f[0] == "neg":
        return "неверно, что " + small_nl(f[1])
    parts = [small_nl(t) for t in f[1]]
    if f[0] == "conj":
        return "верно и то, что " + ", и то, что ".join(parts)
    return "верно по крайней мере одно из двух: " + "; ".join(parts)


def nat_side(names):
    def lit():
        v = V(rnd.choice(names))
        return N(v) if rnd.random() < 0.3 else v

    def small():
        if rnd.random() < 0.4:
            return lit()
        a, b = lit(), lit()
        while atoms(a) == atoms(b):
            b = lit()
        return (rnd.choice(["conj", "wdis"]), (a, b))
    k = rnd.random()
    if k < 0.15:
        s_ = small()
        return N(s_) if s_[0] in ("conj", "wdis") else s_
    a, b = small(), small()
    if a == b or (is_lit(a) and is_lit(b) and atoms(a) == atoms(b)):
        return a
    return (rnd.choice(["conj", "wdis"]), (a, b))


def c_nat(sec, level=6):
    for _ in range(20000):
        a, b = nat_side(list("pqr")), nat_side(list("pqrs"))
        if (a, b) in FSEEN or a == b or size(a) + size(b) < 14:
            continue
        pv = [SY.provable(k, a, b) for k in "smcq"]
        if SY.taut(a, b) and len(set(pv)) == 2 and rnd.random() < 0.8 or (not SY.taut(a, b) and rnd.random() < 0.08):
            FSEEN.add((a, b))
            break
    arg = f"{nl(a)[0].upper() + nl(a)[1:]}; следовательно, {nl(b)}."
    cond = ("Обозначим: $p$ — «идёт дождь», $q$ — «дует ветер», $r$ — «холодно», $s$ — «светит солнце»; «или» — "
            "соединительное ($\\vee$, гл. 2, § 1, с. 36). Запишите рассуждение формулой следования и исследуйте, будет "
            "ли оно следованием в смысле $S^s$, $S^m$, $S^c$ и $S^6$; обоснуйте значениями и множествами элементарных "
            f"высказываний. Критерии: {CRIT['s']}; {CRIT['m']}; {CRIT['c']}; {CRIT['q']}.\n\n> {arg}")
    ans = f"${FT(a, b)}$; {sys_row(a, b)}."
    t = ("тавтология" if SY.taut(a, b) else
         f"не тавтология: при {env_t(SY.counter(a, b))} посылка 1, заключение 0")
    sol = (f"Формула: ${FT(a, b)}$. Она — {t}. Элементарные высказывания посылки: {lst(atoms(a))}; заключения: "
           f"{lst(atoms(b))}.\n" + "\n".join(f"{SK[k]}: {SY.reason(k, a, b, T)} — {verdict(k, a, b)}." for k in "smcq"))
    return card(level, "F", "vary", "short", "с. 59–73, гл. 4, § 1–4; гл. 5, § 2", "обычный язык, системы", cond, ans,
                sol, form="nat")


# ---------- § 1: A3 с ограничением ----------
def cpool():
    return rnd.choice([x, y, N(x), C(x, y), W(x, z), N(C(y, z)), C(N(x), z), W(y, N(z)), C(x, N(x)), N(N(y))])


def a3_item(kind):
    for _ in range(5000):
        X, Y, Z = cpool(), cpool(), cpool()
        if len({X, Y, Z}) < 3:
            continue
        if kind == "sub" and atoms(Y) < atoms(X):
            return C(X, Y), X
        if kind == "eq" and atoms(Y) == atoms(X):
            return C(X, Y), X
        if kind == "new" and not atoms(Y) <= atoms(X):
            return C(X, Y), X
        if kind == "nest" and atoms(Z) <= atoms(X) | atoms(Y):
            return C(C(X, Y), Z), X
        if kind == "second" and atoms(Y) != atoms(X):
            return C(X, Y), Y
        if kind == "inner" and atoms(Y) | atoms(Z) <= atoms(X):
            return C(X, C(Y, Z)), X
    raise RuntimeError(kind)


def a3_desc(a, b, smirnov):
    if S4.a3_shape(a, b):
        X, Y = a[1]
        sub_t = f"$x$ := ${T(X)}$, $y$ := ${T(Y)}$"
        main = atoms(Y) <= atoms(X)
        s = f"пример A3 $S_1$ ({sub_t}); "
        s += ("ограничение $S_3$ выполнено — аксиома $S_3$" if main else
              f"ограничение $S_3$ нарушено ({lst(atoms(Y) - atoms(X))} есть в $y$, но не в $x$) — не аксиома $S_3$")
        if smirnov:
            sm = atoms(X) == atoms(Y)
            s += "; по Смирнову — " + ("аксиома" if sm else "не аксиома: множества $x$ и $y$ различны")
        return s, main
    if a[0] == "conj" and len(a[1]) == 2 and b == a[1][1]:
        return "не пример A3: заключение — второй, а не первый член конъюнкции", False
    if a[0] == "conj" and len(a[1]) == 2 and a[1][0][0] == "conj" and a[1][0][1][0] == b:
        return f"не пример A3: первый член конъюнкции — ${T(a[1][0])}$, а не ${T(b)}$", False
    return "не пример A3", False


def c_a3_series(smirnov):
    kinds = ["sub", "eq", "new", rnd.choice(["nest", "second"]), "inner"] if smirnov else \
        ["new", "eq", rnd.choice(["nest", "second"]), "inner", "new"]
    rnd.shuffle(kinds)
    items = [a3_item(k) for k in kinds]
    extra = (" Проверьте также ограничение Г. А. Смирнова (с. 59): в $x$ и $y$ входят одинаковые элементарные "
             "высказывания.") if smirnov else ""
    cond = (f"{CONV_W} Для каждой формулы установите, получается ли она из схемы A3 $xy \\vdash x$ заменой букв "
            f"высказываниями (одинаковые — одинаково); если получается — укажите замену и проверьте ограничение $S_3$: в "
            f"$y$ входят только те элементарные высказывания, которые входят в $x$ (гл. 4, § 1, с. 59, 61); если нет — "
            f"назовите, что мешает.{extra} Для формул, не являющихся аксиомами $S_3$, исследуйте доказуемость в $S^m$. "
            f"Критерий {CRIT['m']}.\n\n" + "\n".join(f"{L[i]}) ${FT(a, b)}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        d, ax = a3_desc(a, b, smirnov)
        tail = "" if ax else f"; в $S^m$ {verdict('m', a, b)}"
        ans.append(f"{L[i]}) {d}{tail}")
        sol.append(f"{L[i]}) {d}." + ("" if ax else f" {why('m', a, b)}: в $S^m$ {verdict('m', a, b)}."))
    return card(5, "A", "vary", "short", "с. 59–61, гл. 4, § 1", "S3, A3, ограничение, почти-пример", cond,
                "; ".join(ans), "\n".join(sol), system="S_3")


# ---------- почти-примеры схем § 2–3 ----------
def cpool_c():
    return rnd.choice([x, y, N(x), C(x, y), D(x, z), N(C(y, z)), C(N(x), z), D(y, N(z))])


def a15_item(kind):
    for _ in range(3000):
        X, Y, Z = cpool_c(), cpool_c(), cpool_c()
        if len({X, Y, Z}) < 3:
            continue
        if kind == "yes" and not atoms(Y) <= atoms(X):
            return N(X), N(C(X, Y))
        if kind == "order":
            return N(X), N(C(Y, X))
        if kind == "noneg":
            return N(X), C(N(X), Y)
        if kind == "dneg":
            return N(N(X)), N(C(N(X), Y))
        if kind == "flat" and X[0] != "conj" and Y[0] != "conj" and Z[0] != "conj":
            return N(C(X, Y)), N(C(X, Y, Z))
        if kind == "nested" and X[0] != "conj":
            return N(C(X, Y)), N(C(C(X, Y), Z))
    raise RuntimeError(kind)


def a15_desc(a, b):
    if S4.is_c_inst("A15", a, b):
        return f"пример A15: $x$ := ${T(a[1], 'c')}$, $y$ := ${T(b[1][1][1], 'c')}$", True
    if b[0] == "neg" and b[1][0] == "conj" and len(b[1][1]) == 2 and b[1][1][1] == a[1]:
        return "не пример: в A15 $x$ — первый член конъюнкции под отрицанием, а здесь — второй", False
    if b[0] == "conj":
        return "не пример: в A15 отрицание стоит перед всей конъюнкцией $\\sim(xy)$, а здесь — только перед первым членом", False
    if b[0] == "neg" and b[1][0] == "conj" and len(b[1][1]) == 3:
        return ("не пример: A15 даёт двучленную конъюнкцию $\\sim((\\ldots)z)$, а здесь трёхчленная без скобок "
                "(нужны A5, A6)"), False
    return "не пример A15", False


def ent_reason_c(a, b, lang):
    return f"{why('c', a, b)}: в $S^c$ {verdict('c', a, b)}"


def c_a15_series():
    kinds = ["yes", "order", "noneg", "dneg", rnd.choice(["flat", "nested"])]
    rnd.shuffle(kinds)
    items = [a15_item(k) for k in kinds]
    cond = (f"{CONV_C} Для каждой формулы установите, получается ли она из схемы A15 $\\sim x \\vdash \\sim(xy)$ "
            f"системы $S^4$ (гл. 4, § 2, с. 62) заменой букв высказываниями (одинаковые — одинаково); если получается — "
            f"укажите замену, если нет — назовите, что мешает, и исследуйте доказуемость формулы в $S^c$. Критерий "
            f"{CRIT['c']}.\n\n" + "\n".join(f"{L[i]}) ${FT(a, b, 'c')}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        d, ok = a15_desc(a, b)
        ans.append(f"{L[i]}) {d}" + ("" if ok else f"; в $S^c$ {verdict('c', a, b)}"))
        sol.append(f"{L[i]}) {d}." + (" Как пример аксиомной схемы формула доказуема в $S^4$ (тавтология, в посылку не "
                                      "входят элементарные высказывания, отсутствующие в заключении)." if ok else
                                      f" {ent_reason_c(a, b, 'c')}."))
    return card(5, "A", "vary", "short", "с. 62–65, гл. 4, § 2", "S4, A15, почти-пример", cond, "; ".join(ans),
                "\n".join(sol), system="S^4")


def a12_item(kind):
    for _ in range(3000):
        X, Y, Z = cpool(), cpool(), cpool()
        if len({X, Y, Z}) < 3:
            continue
        if kind == "yes" and not atoms(Y) <= atoms(X):
            return X, W(X, Y)
        if kind == "order":
            return X, W(Y, X)
        if kind == "flat" and X[0] != "wdis" and Y[0] != "wdis" and Z[0] != "wdis":
            return X, W(X, Y, Z)
        if kind == "conj" and X[0] != "conj":
            return C(X, Y), W(X, Y)
        if kind == "starstar":
            t = rnd.choice([u, w, z])
            return X, C(X, W(t, N(t)))
        if kind == "starbad":
            t = rnd.choice([u, w, z])
            return X, C(X, W(t, N(X)))
        if kind == "back":
            return W(X, Y), X
    raise RuntimeError(kind)


def a12_desc(a, b):
    if S4.is_w_inst("A12", a, b):
        return f"пример A12: $x$ := ${T(a)}$, $y$ := ${T(b[1][1])}$", True
    if S4.is_w_inst("A**12", a, b):
        return f"пример $A^{{**}}12$: $x$ := ${T(a)}$, $y$ := ${T(b[1][1][1][0])}$", True
    if b[0] == "wdis" and len(b[1]) == 2 and b[1][1] == a:
        return "не пример: в A12 посылка — первый член дизъюнкции, а здесь — второй", False
    if b[0] == "wdis" and len(b[1]) == 3:
        return "не пример: A12 даёт двучленную дизъюнкцию, а здесь трёхчленная", False
    if b[0] == "wdis" and a[0] == "conj":
        return "не пример: в A12 первый член дизъюнкции совпадает со всей посылкой, а здесь посылка — конъюнкция", False
    if b[0] == "conj":
        return ("не пример: в $A^{**}12$ второй множитель — $y \\vee \\sim y$ с одним и тем же $y$, а здесь члены "
                "дизъюнкции не таковы"), False
    return "не пример ни A12, ни $A^{**}12$", False


def c_a12_series():
    kinds = ["yes", "order", rnd.choice(["flat", "conj"]), "starstar", rnd.choice(["starbad", "back"])]
    rnd.shuffle(kinds)
    items = [a12_item(k) for k in kinds]
    cond = (f"{CONV_W} Для каждой формулы установите, получается ли она заменой букв высказываниями (одинаковые — "
            f"одинаково) из схемы A12 $x \\vdash x \\vee y$ системы $S_4$ (с. 65) или из схемы $A^{{**}}12$ "
            f"$x \\vdash x(y \\vee \\sim y)$ системы $S_4^*$ (с. 66); если получается — укажите схему и замену, если нет — "
            f"назовите, что мешает, и исследуйте доказуемость формулы в $S^c$. Критерий {CRIT['c']}.\n\n" +
            "\n".join(f"{L[i]}) ${FT(a, b)}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        d, ok = a12_desc(a, b)
        ans.append(f"{L[i]}) {d}" + ("" if ok else f"; в $S^c$ {verdict('c', a, b)}"))
        sol.append(f"{L[i]}) {d}." + ("" if ok else f" {ent_reason_c(a, b, 'w')}."))
    return card(5, "A", "vary", "short", "с. 65–66, гл. 4, § 2", "S4, A12, почти-пример", cond, "; ".join(ans),
                "\n".join(sol), system="S_4")


def ad1_item(kind):
    for _ in range(3000):
        X, Y = cpool(), cpool()
        if X == Y:
            continue
        if kind == "yes":
            return N(C(N(X), X))
        if kind == "order":
            return N(C(X, N(X)))
        if kind == "other" and not SY.is_taut(N(C(N(X), Y))):
            return N(C(N(X), Y))
        if kind == "dneg":
            return N(C(N(N(X)), N(X)))
        if kind == "outer":
            return N(N(C(N(X), X)))
        if kind == "wdis":
            return W(N(C(N(X), X)), Y)
    raise RuntimeError(kind)


def ad1_desc(f):
    if S4.is_w_inst("Ad1", None, f):
        return f"пример $A^d1$: $x$ := ${T(f[1][1][1])}$", True
    g = f[1] if f[0] == "neg" else None
    if g is not None and g[0] == "conj" and len(g[1]) == 2 and g[1][0] == N(N(g[1][1])):
        pass
    if g is not None and g[0] == "conj" and len(g[1]) == 2 and g[1][1] == N(g[1][0]):
        return "не пример: в $A^d1$ первым стоит отрицание, $\\sim(\\sim xx)$, а здесь порядок членов обратный", False
    if g is not None and g[0] == "conj":
        return "не пример: члены конъюнкции под отрицанием — не $\\sim x$ и $x$ с одним и тем же $x$", False
    if g is not None and g[0] == "neg":
        return "не пример: под знаком $\\sim$ стоит не конъюнкция $\\sim xx$, а её отрицание", False
    return "не пример: формула — дизъюнкция, а не $\\sim(\\sim xx)$", False


def c_ad1_series():
    kinds = ["yes", "order", "other", "dneg", rnd.choice(["outer", "wdis"])]
    rnd.shuffle(kinds)
    items = [ad1_item(k) for k in kinds]
    cond = (f"{CONV_W} Для каждой формулы вырожденного следования установите, получается ли она из схемы $A^d1$ "
            f"$\\vdash \\sim(\\sim xx)$ системы $S^5$ (с. 67) заменой $x$ высказыванием; если получается — укажите "
            f"замену, если нет — назовите, что мешает, и исследуйте доказуемость формулы в $S^5$: {CRIT_D}.\n\n" +
            "\n".join(f"{L[i]}) $\\vdash {T(f)}$" for i, f in enumerate(items)))
    ans, sol = [], []
    for i, f in enumerate(items):
        d, ok = ad1_desc(f)
        if ok:
            ans.append(f"{L[i]}) {d}")
            sol.append(f"{L[i]}) {d}.")
            continue
        if SY.is_taut(f):
            r = "тавтология — доказуема в $S^5$ (MT4, с. 69)"
        else:
            e = next(e for e in SY.rows(f) if not SY.value(f, e))
            r = f"при {env_t(e)} значение 0 — не тавтология, недоказуема (MT1, с. 67)"
        ans.append(f"{L[i]}) {d}; {'доказуема' if SY.is_taut(f) else 'недоказуема'}")
        sol.append(f"{L[i]}) {d}; {r}.")
    return card(5, "A", "vary", "short", "с. 67–69, гл. 4, § 3", "S5, A^d1, почти-пример", cond, "; ".join(ans),
                "\n".join(sol), system="S^5")


NEAR = {"A3": (a3_item, ["sub", "new", "nest", "second", "eq", "inner"], "w", "S_3"),
        "A15": (a15_item, ["yes", "order", "noneg", "dneg", "flat", "nested"], "c", "S^4"),
        "A12": (a12_item, ["yes", "order", "flat", "conj", "starstar", "starbad"], "w", "S_4"),
        "Ad1": (ad1_item, ["yes", "order", "other", "dneg", "outer", "wdis"], "w", "S^5")}
NEAR_RULE = {"A3": "A3 и ограничение $S_3$ (с. 59, 61)", "A15": "A15 (с. 62)", "A12": "A12 (с. 65), $A^{**}12$ (с. 66)",
             "Ad1": "$A^d1$ (с. 67)"}
NEAR_SCH = {"A3": ("из схемы A3 $xy \\vdash x$ и выполнено ли для неё ограничение $S_3$: в $y$ входят только "
                  "элементарные высказывания, которые входят в $x$ (с. 59, 61)"),
            "A15": "из схемы A15 $\\sim x \\vdash \\sim(xy)$ (с. 62)",
            "A12": ("из схемы A12 $x \\vdash x \\vee y$ (с. 65) или из схемы $A^{**}12$ $x \\vdash x(y \\vee \\sim y)$ "
                    "(с. 66)"),
            "Ad1": "из схемы $A^d1$ $\\vdash \\sim(\\sim xx)$ (с. 67)"}


def near_info(sch, it):
    if sch == "A3":
        a, b = it
        d, ok = a3_desc(a, b, False)
        return FT(a, b), d, ok
    if sch == "A15":
        a, b = it
        d, ok = a15_desc(a, b)
        return FT(a, b, "c"), d, ok
    if sch == "A12":
        a, b = it
        d, ok = a12_desc(a, b)
        return FT(a, b), d, ok
    d, ok = ad1_desc(it)
    return f"\\vdash {T(it)}", d, ok


def c_near_diag(sch):
    fn, kinds, lang, sysn = NEAR[sch]
    ks = rnd.sample(kinds, 4)
    items = [near_info(sch, fn(k)) for k in ks]
    wrong = rnd.sample(range(4), 2)
    yes, no = ("аксиома $S_3$", "не аксиома $S_3$") if sch == "A3" else ("получается", "не получается")
    rows = "\n".join(f"{i + 1}. ${f}$ — " + (yes if ok != (i in wrong) else no) for i, (f, d, ok) in enumerate(items))
    conv = CONV_W if lang == "w" else CONV_C
    cond = (f"{conv} Студент проверил для каждой формулы ниже, получается ли она заменой букв высказываниями "
            f"(одинаковые — одинаково) {NEAR_SCH[sch]}.\n\n{rows}\n\nРовно два вывода неверны. Найдите их и объясните, что упустил студент.")
    ans = "; ".join(f"{i + 1}: {d}" for i, (f, d, ok) in enumerate(items) if i in wrong)
    sol = "\n".join(f"{i + 1}. {d}." for i, (f, d, ok) in enumerate(items)) + f"\n\nСхема — {NEAR_RULE[sch]}."
    return card(5, "E", "vary", "text", {"A3": SRC[1], "A15": SRC[2], "A12": SRC[2], "Ad1": SRC[3]}[sch],
                f"{TAG[sysn]}, почти-пример, диагностика", cond, f"Неверны выводы о строках {ans} ({NEAR_RULE[sch]}).",
                sol, system=sysn)


# ---------- § 1: таблицы независимости S_3* (с. 62) ----------
TT = {"A3": ("значения 1, 2, 3, отмечено 1; $xy = 2$, когда $x$ или $y$ равно 2, и $xy = \\max(x, y)$ в остальных "
             "случаях; $x \\vee y = 2$, когда $x$ или $y$ равно 2, и $x \\vee y = \\min(x, y)$ в остальных случаях; "
             "$\\sim x = 2$ при $x = 3$ и $\\sim x = 3$ в остальных случаях; $x \\vdash y$ принимает неотмеченное значение "
             "только при значении $x$, равном 1 или 2, и значении $y$, равном 3"),
      "A*12": ("значения 1, 2, 3; $xy = 1$ при $x = y = 1$ и $xy = 3$ в остальных случаях; $x \\vee y = 3$ при $x = y = 3$ "
               "и $x \\vee y = 1$ в остальных случаях; $\\sim x = 4 - x$; значение $x \\vdash y$ равно 1 (отмечено) "
               "тогда и только тогда, когда значение $x$ больше или равно значению $y$"),
      "R*3": ("значения 1, 2, 3, отмечено 1; $xy = \\max(x, y)$; $x \\vee y = 2$, когда $x$ и $y$ равны 2, $x \\vee y = 3$, "
              "когда $x$ и $y$ равны 3, и $x \\vee y = 1$ в остальных случаях; $\\sim x = 3$ при $x = 1$ и $\\sim x = 1$ в "
              "остальных случаях; $x \\vdash y$ принимает неотмеченное значение только при значении $x$, равном 1, и "
              "значении $y$, равном 2 или 3")}
TWHAT = {"A3": "независимости A3 в $S_3^*$", "A*12": "независимости $A^*12$ $x \\vee x \\vdash x$",
         "R*3": "независимости правила $R^*3$"}
BOOKEX = {"A3": (C(N(x), x), x), "A*12": (W(x, x), x), "R*3": (W(x, y), W(N(N(x)), y))}


def c_table(tn, level=6):
    t = S4.TABLES[tn]
    items = [BOOKEX[tn]]
    while len(items) < 4:
        a, b = rnd_form("pq", 2), rnd_form("pq", 2)
        if a == b or (a, b) in items or not 10 <= size(a) + size(b) <= 30:
            continue
        ok, _ = S4.tcheck(a, b, t)
        need_bad = len(items) == 1
        if ok != need_bad:
            items.append((a, b))
    rnd.shuffle(items)
    cond = (f"{CONV_W} Таблица для доказательства {TWHAT[tn]} (гл. 4, § 1, с. 62): {TT[tn]}. Для каждой формулы "
            f"исследуйте, получает ли она отмеченное значение при всех значениях входящих в неё элементарных "
            f"высказываний; если нет — укажите такие значения и вычислите при них посылку и заключение.\n\n" +
            "\n".join(f"{L[i]}) ${FT(a, b)}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        ok, e = S4.tcheck(a, b, t)
        if ok:
            ans.append(f"{L[i]}) отмеченное при всех значениях")
            sol.append(f"{L[i]}) Перебор всех значений (1, 2, 3 для каждой буквы) даёт отмеченное значение.")
        else:
            va, vb = S4.tval(a, e, t), S4.tval(b, e, t)
            ans.append(f"{L[i]}) неотмеченное при {env_t(e)}")
            sol.append(f"{L[i]}) При {env_t(e)} посылка имеет значение {va}, заключение — {vb}; значение формулы "
                       "неотмеченное.")
    a0, b0 = BOOKEX[tn]
    e0 = S4.tcheck(a0, b0, t)[1]
    sol.append(f"Формула ${FT(a0, b0)}$ — та, что приведена на с. 62: при {env_t(e0)} посылка — {S4.tval(a0, e0, t)}, "
               f"заключение — {S4.tval(b0, e0, t)}, значение неотмеченное.")
    return card(level, "C", "iso", "short", "с. 61–62, гл. 4, § 1", "S3*, независимость, таблицы", cond, "; ".join(ans),
                "\n".join(sol), system="S_3^*")


def c_table_diag(tn, level=6):
    t = S4.TABLES[tn]
    rows = []
    while len(rows) < 4:
        a, b = rnd_form("pq", 2), rnd_form("pq", 2)
        if a == b or any((a, b) == (r[0], r[1]) for r in rows) or not 10 <= size(a) + size(b) <= 30:
            continue
        ok, e = S4.tcheck(a, b, t)
        if ok == (len(rows) % 2 == 0):
            rows.append((a, b, ok, e))
    rnd.shuffle(rows)
    flip = rnd.sample(range(4), 2)
    body = "\n".join(f"{n + 1}. ${FT(a, b)}$ — " + ("отмеченное при всех значениях" if (ok != (n in flip)) else
                                                    "при некоторых значениях неотмеченное") for n, (a, b, ok, e) in enumerate(rows))
    cond = (f"{CONV_W} Таблица для доказательства {TWHAT[tn]} (гл. 4, § 1, с. 62): {TT[tn]}. Студент проверил в этой "
            f"таблице четыре формулы. Ровно в двух выводах он ошибся. Найдите их и обоснуйте значениями.\n\n{body}")
    ans, sol = [], []
    for n, (a, b, ok, e) in enumerate(rows):
        if n not in flip:
            continue
        if ok:
            ans.append(f"строка {n + 1}: отмеченное при всех значениях")
            sol.append(f"Строка {n + 1}: перебор всех значений даёт отмеченное значение.")
        else:
            ans.append(f"строка {n + 1}: неотмеченное при {env_t(e)}")
            sol.append(f"Строка {n + 1}: при {env_t(e)} посылка — {S4.tval(a, e, t)}, заключение — {S4.tval(b, e, t)}; "
                       "значение неотмеченное.")
    return card(level, "E", "vary", "text", "с. 61–62, гл. 4, § 1", "S3*, независимость, таблицы, диагностика", cond,
                cap("; ".join(ans)) + f" (таблица с. 62).", "\n".join(sol) + "\n\nОстальные выводы верны.",
                system="S_3^*")


# ---------- § 2: контрапозиция ----------
def c_contra(level=6):
    items = []
    kinds = ["sub", "sub", "eq", rnd.choice(["sub", "eq"])]
    for kd in kinds:
        items.append(find(lambda a, b, kd=kd: SY.provable("s", a, b) and ((atoms(b) < atoms(a)) if kd == "sub" else
                                                                        atoms(a) == atoms(b)),
                          na="pqr", nb="pqr", depth=2, lo=14, hi=36))
    rnd.shuffle(items)
    cond = (f"{CONV_W} Каждая формула $x \\vdash y$ ниже доказуема в $S^s$. Для каждой запишите формулу "
            f"$\\sim y \\vdash \\sim x$ и исследуйте её доказуемость в $S^s$ и в $S^c$; обоснуйте значениями и "
            f"множествами элементарных высказываний. Критерии: {CRIT['s']}; {CRIT['c']}.\n\n" +
            "\n".join(f"{L[i]}) ${FT(a, b)}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        A, B = N(b), N(a)
        ans.append(f"{L[i]}) ${FT(A, B)}$: $S^s$ — {'да' if SY.provable('s', A, B) else 'нет'}, $S^c$ — "
                   f"{'да' if SY.provable('c', A, B) else 'нет'}")
        assert SY.taut(A, B)
        sol.append(f"{L[i]}) ${FT(A, B)}$ — тавтология: она принимает значение 0 только при $\\sim y = 1$, $\\sim x = 0$, "
                   f"то есть при $y = 0$, $x = 1$, а таких значений нет, раз ${FT(a, b)}$ — тавтология. Элементарные "
                   f"высказывания посылки: {lst(atoms(A))}; заключения: {lst(atoms(B))}. $S^s$: "
                   f"{SY.reason('s', A, B, T)}; $S^c$: {SY.reason('c', A, B, T)}.")
    return card(level, "S", "transfer", "short", "с. 62–67, гл. 4, § 2; гл. 5, § 2", "S4, Sc, контрапозиция", cond,
                "; ".join(ans), "\n".join(sol))


def c_contra_diag(level=6):
    items = [find(lambda a, b: SY.provable("s", a, b) and atoms(b) < atoms(a), na="pqr", nb="pqr", depth=2, lo=14, hi=34)
             for _ in range(3)]
    errs = rnd.sample(range(3), 2)
    kinds = rnd.sample(["order", "verdict"], 2)
    rows, ans, sol = [], [], []
    for i, (a, b) in enumerate(items):
        A, B = N(b), N(a)
        if i in errs and kinds[errs.index(i)] == "order":
            rows.append(f"{i + 1}. ${FT(a, b)}$ ⟹ ${FT(N(a), N(b))}$, доказуема в $S^c$.")
            ans.append(f"{i + 1}: перевёрнут порядок — надо ${FT(A, B)}$")
            sol.append(f"{i + 1}. Студент записал $\\sim x \\vdash \\sim y$ вместо $\\sim y \\vdash \\sim x$. Его формула "
                       f"${FT(N(a), N(b))}$ — {SY.reason('c', N(a), N(b), T)}. Верная контрапозиция ${FT(A, B)}$: "
                       f"{SY.reason('c', A, B, T)} — доказуема в $S^c$ (MT4 гл. 5, § 2, с. 73).")
        elif i in errs:
            rows.append(f"{i + 1}. ${FT(a, b)}$ ⟹ ${FT(A, B)}$, доказуема в $S^s$.")
            ans.append(f"{i + 1}: в $S^s$ недоказуема (новое элементарное высказывание), доказуема в $S^c$")
            sol.append(f"{i + 1}. Запись верна, но ${FT(A, B)}$ в $S^s$ недоказуема: {SY.reason('s', A, B, T)} (MT1 "
                       f"гл. 5, § 2, с. 72); в $S^c$ доказуема: {SY.reason('c', A, B, T)}.")
        else:
            rows.append(f"{i + 1}. ${FT(a, b)}$ ⟹ ${FT(A, B)}$, доказуема в $S^c$.")
    cond = (f"{CONV_W} Каждая формула слева доказуема в $S^s$. Студент записал её контрапозицию "
            f"$\\sim y \\vdash \\sim x$ и указал систему, в которой та доказуема:\n\n" + "\n".join(rows) +
            f"\n\nРовно в двух строках есть ошибки. Найдите их, объясните и исправьте. Критерии: {CRIT['s']}; "
            f"{CRIT['c']}.")
    return card(level, "E", "vary", "text", "с. 62–67, гл. 4, § 2; гл. 5, § 2", "S4, Sc, контрапозиция, диагностика",
                cond, cap("; ".join(ans)) + " (гл. 5, § 2, MT1, MT4, с. 72–73).",
                "\n".join(sol) + "\n\nОстальная строка верна.")


# ---------- § 3: R^d1, ⊢ ∼(x∼y), MT7 ----------
def deg_form(taut, lo=10, hi=30, names="pqr"):
    for _ in range(20000):
        f = rnd_form(names, rnd.choice([2, 3]))
        if lo <= size(f) <= hi and SY.is_taut(f) == taut and f not in FSEEN and len(atoms(f)) >= 2:
            FSEEN.add(f)
            return f
    raise RuntimeError


def c_deg_series(level=6):
    kinds = [True, True, False, False]
    rnd.shuffle(kinds)
    items = []
    for k in kinds:
        if k and rnd.random() < 0.5:
            ls = deg_derivation(6, 3, need=("Rd1",))
            items.append(ls[-1][1])
        else:
            items.append(deg_form(k, 14, 34))
    cond = (f"{CONV_W} Исследуйте доказуемость в $S^5$ каждой формулы вырожденного следования и обоснуйте: для "
            f"недоказуемой — набором значений, при котором высказывание ложно; для доказуемой — тавтологичностью. "
            f"Критерий: {CRIT_D}.\n\n" + "\n".join(f"{L[i]}) $\\vdash {T(f)}$" for i, f in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {'доказуема' if SY.is_taut(f) else 'недоказуема'}" for i, f in enumerate(items))
    sol = []
    for i, f in enumerate(items):
        if SY.is_taut(f):
            sol.append(f"{L[i]}) При всех значениях {lst(atoms(f))} высказывание истинно — тавтология; по MT4 (с. 69) "
                       "доказуема.")
        else:
            e = next(e for e in SY.rows(f) if not SY.value(f, e))
            sol.append(f"{L[i]}) При {env_t(e)} высказывание ложно — не тавтология; по MT1 (с. 67) недоказуема.")
    return card(level, "C", "open", "short", "с. 67–69, гл. 4, § 3", "S5, доказуемость", cond, ans, "\n".join(sol),
                system="S^5")


def c_deg_series_diag(level=6):
    items = [deg_form(t, 14, 32) for t in rnd.sample([True, True, False, False], 4)]
    wrong = rnd.sample(range(4), 2)
    claims = {True: ["доказуема: тавтология (MT4)", "доказуема: истинна при всех значениях"],
              False: ["недоказуема: ложна при некоторых значениях", "недоказуема: не тавтология (MT1)"]}
    fake = {True: ["недоказуема: в формуле вырожденного следования нет посылки, условие непарадоксальности нарушено",
                   "недоказуема: высказывание не имеет вида $\\sim(\\sim xx)$, а других аксиом для $\\vdash x$ нет"],
            False: ["доказуема: она получается по $R^d1$ из $A^d1$", "доказуема: в неё входят и $x$, и $\\sim x$"]}
    rows, ans, sol = [], [], []
    for i, f in enumerate(items):
        t = SY.is_taut(f)
        rows.append(f"{i + 1}. $\\vdash {T(f)}$ — " + (rnd.choice(fake[t]) if i in wrong else rnd.choice(claims[t])) + ".")
        if i in wrong:
            if t:
                ans.append(f"{i + 1}: доказуема (тавтология, MT4, с. 69)")
                sol.append(f"{i + 1}. Неверно: высказывание — тавтология, и по MT4 (с. 69) $\\vdash x$ доказуема. Для "
                           "$\\vdash x$ условий на элементарные высказывания нет; доказуемы не только примеры $A^d1$, "
                           "но и всё, что из них выводится по $R^d1$–$R^d3$.")
            else:
                e = next(e for e in SY.rows(f) if not SY.value(f, e))
                ans.append(f"{i + 1}: недоказуема (MT1, с. 67)")
                sol.append(f"{i + 1}. Неверно: при {env_t(e)} высказывание ложно; по MT1 (с. 67) доказуемы только "
                           "тавтологии.")
    cond = (f"{CONV_W} Студент исследовал доказуемость в $S^5$ четырёх формул вырожденного следования:\n\n" +
            "\n".join(rows) + f"\n\nРовно два вывода неверны. Найдите их и обоснуйте верный ответ. Критерий: {CRIT_D}.")
    return card(level, "E", "vary", "text", "с. 67–69, гл. 4, § 3", "S5, доказуемость, диагностика", cond,
                cap("; ".join(ans)) + ".", "\n".join(sol) + "\n\nОстальные выводы верны.", system="S^5")


def c_rd1_items(level=6):
    X0 = rnd.choice([x, y, C(x, y), N(x)])
    X = N(C(N(X0), X0))
    targets = []
    want = ["ok", "new", "non", rnd.choice(["ok", "new"])]
    rnd.shuffle(want)
    for kd in want:
        for _ in range(20000):
            Y = rnd_form(sorted(atoms(X) | ({"r"} if kd == "new" else set())), 2)
            if size(Y) < 8 or Y in targets or Y == X:
                continue
            if kd == "ok" and SY.provable("s", X, Y):
                break
            if kd == "new" and SY.is_taut(Y) and not atoms(Y) <= atoms(X):
                break
            if kd == "non" and not SY.is_taut(Y) and atoms(Y) <= atoms(X):
                break
        targets.append(Y)
    cond = (f"{CONV_W} В $S^5$ доказуема $\\vdash {T(X)}$ (пример $A^d1$). Для каждой формулы $\\vdash y$ ниже установите, "
            f"можно ли получить её одним применением $R^d1$ (если $x \\vdash y$ и $\\vdash x$, то $\\vdash y$, с. 67) из "
            f"$\\vdash {T(X)}$ и формулы ${T(X)} \\vdash y$, доказуемой в $S^s$; если нельзя — объясните почему и "
            f"исследуйте доказуемость $\\vdash y$ в $S^5$. Критерии: {CRIT['s']}; {CRIT_D}.\n\n" +
            "\n".join(f"{L[i]}) $\\vdash {T(Y)}$" for i, Y in enumerate(targets)))
    ans, sol = [], []
    for i, Y in enumerate(targets):
        if SY.provable("s", X, Y):
            ans.append(f"{L[i]}) можно")
            sol.append(f"{L[i]}) ${FT(X, Y)}$ — сильная тавтология (тавтология, новых элементарных высказываний в "
                       f"заключении нет), доказуема в $S^s$; по $R^d1$ получаем $\\vdash {T(Y)}$.")
        elif SY.is_taut(Y):
            ans.append(f"{L[i]}) нельзя (новое элементарное высказывание), но формула доказуема")
            sol.append(f"{L[i]}) В ${T(Y)}$ входит {lst(atoms(Y) - atoms(X))}, которого нет в ${T(X)}$: формула "
                       f"${FT(X, Y)}$ в $S^s$ недоказуема (непарадоксальность). Но ${T(Y)}$ — тавтология, и по MT4 "
                       f"(с. 69) $\\vdash {T(Y)}$ доказуема — другим выводом.")
        else:
            e = next(e for e in SY.rows(Y) if not SY.value(Y, e))
            ans.append(f"{L[i]}) нельзя; формула недоказуема")
            sol.append(f"{L[i]}) При {env_t(e)} ${T(Y)}$ ложно, а ${T(X)}$ истинно: ${FT(X, Y)}$ — не тавтология и в "
                       f"$S^s$ недоказуема; по MT1 (с. 67) $\\vdash {T(Y)}$ недоказуема.")
    return card(level, "C", "open", "short", "с. 67–70, гл. 4, § 3", "S5, R^d1", cond, "; ".join(ans), "\n".join(sol),
                system="S^5")


def c_deg_vs_ent(level=7):
    preds = [lambda a, b: SY.provable("s", a, b), lambda a, b: SY.taut(a, b) and not SY.cond("s", a, b),
             lambda a, b: not SY.taut(a, b)]
    items = [find(p, na="pqr", nb="pqrs", depth=2, lo=12, hi=30) for p in preds]
    rnd.shuffle(items)
    cond = (f"{CONV_W} Для каждой формулы $x \\vdash y$ исследуйте её доказуемость в $S^s$ и доказуемость формулы "
            f"вырожденного следования $\\vdash \\sim(x\\sim y)$ в $S^5$; объясните, почему результаты могут расходиться. "
            f"Критерии: {CRIT['s']}; {CRIT_D}.\n\n" + "\n".join(f"{L[i]}) ${FT(a, b)}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        f = N(C(a, N(b)))
        ans.append(f"{L[i]}) $S^s$ — {'да' if SY.provable('s', a, b) else 'нет'}; $\\vdash {T(f)}$ — "
                   f"{'доказуема' if SY.is_taut(f) else 'недоказуема'}")
        assert SY.is_taut(f) == SY.taut(a, b)
        sol.append(f"{L[i]}) $\\sim(x\\sim y)$ ложно ровно тогда, когда $x = 1$, $y = 0$, поэтому оно тавтология тогда и "
                   f"только тогда, когда ${FT(a, b)}$ — тавтология. $S^s$: {SY.reason('s', a, b, T)}; $S^5$: "
                   + ("тавтология — доказуема (MT4, с. 69)" if SY.is_taut(f) else
                      f"при {env_t(SY.counter(a, b))} значение 0 — недоказуема (MT1, с. 67)") + ".")
    sol.append("Расхождение возможно только из-за условия $S^s$ на элементарные высказывания: для $\\vdash x$ такого "
               "условия нет.")
    return card(level, "S", "transfer", "short", "с. 67–70, гл. 4, § 3; гл. 5, § 2", "S5, Ss, сравнение", cond,
                "; ".join(ans), "\n".join(sol))


def subst_all(f, v, Z):
    if f[0] == "v":
        return Z if f[1] == v else f
    if f[0] == "neg":
        return N(subst_all(f[1], v, Z))
    return (f[0], tuple(subst_all(t, v, Z) for t in f[1]))


def occ(f, v):
    if f[0] == "v":
        return int(f[1] == v)
    if f[0] == "neg":
        return occ(f[1], v)
    return sum(occ(t, v) for t in f[1])


def subst_first(f, v, Z, done=None):
    done = done if done is not None else [False]
    if f[0] == "v":
        if f[1] == v and not done[0]:
            done[0] = True
            return Z
        return f
    if f[0] == "neg":
        return N(subst_first(f[1], v, Z, done))
    return (f[0], tuple(subst_first(t, v, Z, done) for t in f[1]))


def c_mt7(level=5):
    items = []
    while len(items) < 3:
        f = deg_form(True, 10, 24, names="pq")
        if occ(f, "p") < 2:
            continue
        Z = rnd.choice([C(y, z), W(N(y), z), N(C(x, z)), C(N(z), y), W(z, u)])
        g = subst_all(f, "p", Z)
        if size(g) <= 44:
            items.append((f, Z, g))
    cond = (f"{CONV_W} Каждая формула ниже доказуема в $S^5$. Выполните подстановку высказывания вместо $p$ всюду, где "
            f"$p$ входит, и проверьте значениями, что результат — тавтология; сошлитесь на правило подстановки MT7 "
            f"(с. 70): если $\\vdash x$ доказуема, то доказуема $\\vdash y$, где $y$ получено подстановкой высказывания "
            f"$z$ на место элементарного высказывания $v$ везде, где $v$ входит в $x$.\n\n" +
            "\n".join(f"{L[i]}) $\\vdash {T(f)}$, вместо $p$ — ${T(Z)}$" for i, (f, Z, g) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) $\\vdash {T(g)}$" for i, (f, Z, g) in enumerate(items))
    sol = "\n".join(f"{L[i]}) $\\vdash {T(g)}$: при любых значениях {lst(atoms(g))} подставленное ${T(Z)}$ получает "
                    f"значение 0 или 1, и $\\vdash {T(f)}$ при этом значении $p$ истинна; значит, результат — "
                    f"тавтология и по MT7 (или MT4, с. 69) доказуем." for i, (f, Z, g) in enumerate(items))
    return card(level, "A", "iso", "short", "с. 69–70, гл. 4, § 3", "S5, подстановка", cond, ans, sol, system="S^5")


def c_mt7_diag(level=6):
    for _ in range(5000):
        f = deg_form(True, 10, 26, names="pq")
        Z = rnd.choice([C(y, z), N(y), W(N(y), z), C(z, N(z)), N(C(y, z))])
        g = subst_first(f, "p", Z)
        if occ(f, "p") >= 2 and not SY.is_taut(g) and size(g) <= 40:
            break
    good = subst_all(f, "p", Z)
    e = next(e for e in SY.rows(g) if not SY.value(g, e))
    cond = (f"{CONV_W} В $S^5$ доказуема $\\vdash {T(f)}$. Студент, ссылаясь на правило подстановки MT7 (с. 70), "
            f"подставил ${T(Z)}$ вместо $p$ и получил $\\vdash {T(g)}$, которую объявил доказуемой. Найдите ошибку, "
            f"докажите значениями, что полученная формула недоказуема, и дайте верный результат подстановки.")
    ans = (f"Подстановка выполнена не во все вхождения $p$ (MT7 требует замены везде, с. 70): при {env_t(e)} "
           f"${T(g)}$ ложно. Верно: $\\vdash {T(good)}$.")
    sol = (f"1. MT7 (с. 70): $z$ подставляется на место $v$ везде, где $v$ входит в $x$. В $\\vdash {T(f)}$ буква $p$ "
           f"входит {occ(f, 'p')} раза, а студент заменил только первое вхождение.\n"
           f"2. При {env_t(e)} высказывание ${T(g)}$ ложно — оно не тавтология и по MT1 (с. 67) недоказуемо.\n"
           f"3. Верная подстановка: $\\vdash {T(good)}$ — тавтология, доказуема по MT7.")
    return card(level, "E", "vary", "text", "с. 69–70, гл. 4, § 3", "S5, подстановка, диагностика", cond, ans, sol,
                system="S^5")


# ---------- § 4: R^k1 ----------
def taut_all(names):
    fs = [W(V(p), N(V(p))) for p in sorted(names)]
    return fs[0] if len(fs) == 1 else C(*fs)


def c_rk1_build(level=7):
    want = ["new", "new", "non"]
    rnd.shuffle(want)
    items = []
    for kd in want:
        items.append(find((lambda a, b: SY.taut(a, b) and not SY.cond("s", a, b)) if kd == "new" else
                          (lambda a, b: not SY.taut(a, b) and not SY.cond("s", a, b)),
                          na="pq", nb="pqr", depth=2, lo=10, hi=28))
    cond = (f"{CONV_W} Для каждой формулы $x \\vdash y$ найдите высказывание $z$, для которого $xz \\vdash y$ доказуема в "
            f"$S^s$, а $\\vdash z$ — в $S^5$ (тогда по $R^k1$, с. 70, $x \\vdash y$ доказуема в $S^6$), или докажите, что "
            f"такого $z$ нет. Критерии: {CRIT['s']}; {CRIT_D}.\n\n" +
            "\n".join(f"{L[i]}) ${FT(a, b)}$" for i, (a, b) in enumerate(items)))
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        if SY.taut(a, b):
            Z = taut_all(atoms(b) - atoms(a))
            assert SY.provable("s", C(a, Z), b) and SY.is_taut(Z)
            ans.append(f"{L[i]}) например, $z$ = ${T(Z)}$")
            sol.append(f"{L[i]}) $z$ = ${T(Z)}$ — тавтология, $\\vdash z$ доказуема (MT4 § 3, с. 69). Формула "
                       f"${FT(C(a, Z), b)}$ — тавтология (множитель $z$ всегда истинен, посылка равнозначна ${T(a)}$), и "
                       f"все элементарные высказывания заключения входят в посылку: сильная тавтология, доказуема в $S^s$. "
                       f"Так устроен случай 3 доказательства MT2 § 4 (с. 71).")
        else:
            e = SY.counter(a, b)
            ans.append(f"{L[i]}) такого $z$ нет")
            sol.append(f"{L[i]}) Пусть $xz \\vdash y$ доказуема в $S^s$ и $\\vdash z$ — в $S^5$. Тогда $z$ — тавтология "
                       f"(MT1 § 3), $xz \\vdash y$ — тавтология, и при любых значениях из $x = 1$ следует $xz = 1$, то есть "
                       f"$y = 1$: ${FT(a, b)}$ была бы тавтологией. Но при {env_t(e)} посылка 1, заключение 0. Значит, "
                       f"$z$ нет (и по MT1 § 4, с. 70, формула в $S^6$ недоказуема).")
    return card(level, "P", "open", "build", "с. 70–71, гл. 4, § 4", "S6, R^k1, построение", cond, "; ".join(ans),
                "\n".join(sol), system="S^6")


def c_rk1_diag(level=6):
    a, b = find(lambda a, b: SY.taut(a, b) and not SY.cond("s", a, b), na="pq", nb="pqr", depth=2, lo=10, hi=26)
    newl = sorted(atoms(b) - atoms(a))
    p = newl[0]
    badZ = V(p)                                  # не тавтология
    good = taut_all(atoms(b) - atoms(a))
    cond = (f"{CONV_W} Студент доказывает в $S^6$ формулу ${FT(a, b)}$ так:\n\n"
            f"1. ${FT(C(a, badZ), b)}$ — доказуема в $S^s$, так как это сильная тавтология.\n"
            f"2. $\\vdash {p}$ — доказуема в $S^5$, так как ${p}$ — элементарное высказывание.\n"
            f"3. Значит, по $R^k1$ (если $xz \\vdash y$ и $\\vdash z$, то $x \\vdash y$, с. 70) доказуема ${FT(a, b)}$.\n\n"
            f"Найдите все ошибки и исправьте доказательство. Критерии: {CRIT['s']}; {CRIT_D}.")
    st1 = SY.provable("s", C(a, badZ), b)
    err1 = (f"шаг 1 верен: ${FT(C(a, badZ), b)}$ — сильная тавтология" if st1 else
            f"шаг 1 неверен: ${FT(C(a, badZ), b)}$ — {SY.reason('s', C(a, badZ), b, T)}")
    ans = (f"Шаг 2 неверен: $\\vdash {p}$ недоказуема — ${p}$ не тавтология (MT1 § 3, с. 67); " +
           ("" if st1 else "шаг 1 тоже неверен — формула не сильная тавтология (гл. 5, § 2, MT1, с. 72); ") +
           f"верно взять $z$ = ${T(good)}$ (случай 3 доказательства MT2 § 4, с. 71).")
    sol = (f"1. {err1[0].upper() + err1[1:]}.\n"
           f"2. Шаг 2: по MT1 § 3 (с. 67) доказуемы только формулы $\\vdash x$ с тавтологией $x$; ${p}$ при ${p} = 0$ "
           f"ложно — $\\vdash {p}$ недоказуема, и $R^k1$ применить нельзя.\n"
           f"3. Исправление: $z$ = ${T(good)}$ — тавтология, $\\vdash z$ доказуема (MT4 § 3, с. 69); "
           f"${FT(C(a, good), b)}$ — сильная тавтология, доказуема в $S^s$; по $R^k1$ — ${FT(a, b)}$.")
    return card(level, "E", "vary", "text", "с. 70–71, гл. 4, § 4", "S6, R^k1, диагностика", cond, ans, sol,
                system="S^6")


S6MT3 = [("x(y \\vee \\sim y) \\vdash x", "A3"), ("x \\vdash zy \\vee x", "A12, R1, $a \\vee b \\vdash b \\vee a$"),
         ("zy \\vee x \\vdash (zy \\vee x)(y \\vee \\sim y)", "A11"), ("zy \\vee x \\vdash y \\vee \\sim y", "A3, R1"),
         ("x \\vdash y \\vee \\sim y", "2, 3, 4, R1"), ("x \\vdash x", "A1, A2, R1"),
         ("x \\vdash x(y \\vee \\sim y)", "5, 6, R2"), ("x \\dashv\\vdash x(y \\vee \\sim y)", "1, 7")]


def c_book_s6mt3():
    hide_f, hide_w = {4, 7}, {2, 5, 8}
    shown = "\n".join(f"{i}. {'…' if i in hide_f else '$' + f + '$'} [{'…' if i in hide_w else b}]"
                      for i, (f, b) in enumerate(S6MT3, 1))
    cond = (f"{CONV_W} Система $S^{{*6}}$ получается из $S_2$ снятием ограничения на R2 (гл. 4, § 4, с. 71). Ниже — "
            f"начало доказательства MT3 (если $x \\supset y$ — тавтология, то $x \\vdash y$ доказуема в $S^{{*6}}$) с "
            f"пропусками («…»): пропущены формулы двух строк и основания трёх. Восстановите их, а затем объясните, как "
            f"из строки 8 и полноты $S^s$ получается $x \\vdash y$ для тавтологии $x \\vdash y$, в $y$ которой входят "
            f"элементарные высказывания $p^1, \\ldots, p^n$, отсутствующие в $x$.\n\n{shown}")
    ans = ("4 — $zy \\vee x \\vdash y \\vee \\sim y$; 7 — $x \\vdash x(y \\vee \\sim y)$; 2 — [A12, R1, "
           "$a \\vee b \\vdash b \\vee a$]; 5 — [2, 3, 4, R1]; 8 — [1, 7]; далее: $x \\vdash x(p^1 \\vee \\sim p^1) \\ldots "
           "(p^n \\vee \\sim p^n)$ и R1.")
    sol = ("Строки (с. 71):\n\n" + "\n".join(f"{i}. ${f}$ [{b}]" for i, (f, b) in enumerate(S6MT3, 1)) +
           "\n\nСтрока 4 получается из строки 3 по A3 и R1 (отбрасываем первый член конъюнкции), строка 7 — из 5 и 6 по "
           "R2: обе строки имеют посылку $x$; строка 8 — сокращение для строк 1 и 7.\n\nДалее (с. 71): если "
           "$x(p^1 \\vee \\sim p^1) \\ldots (p^n \\vee \\sim p^n) \\vdash y$ — тавтология, то она доказуема в $S^s$ (все "
           "элементарные высказывания $y$ входят в посылку), а значит, и в $S^{*6}$. По строке 8 (применённой $n$ раз) "
           "доказуема $x \\vdash x(p^1 \\vee \\sim p^1) \\ldots (p^n \\vee \\sim p^n)$; по R1 — $x \\vdash y$.")
    return card(5, "D", "complete", "build", "с. 71, гл. 4, § 4", "S6, S*6, вывод, дополнение", cond, ans, sol,
                system="S^{*6}")


# ---------- план ----------
def ids(sec, nums):
    return [f"04.{sec:02d}-{n:03d}" for n in nums]


def order(kinds):
    """Лестница: по ступени (дополнение и почти-примеры раньше, перенос и построения позже)."""
    return sorted(kinds, key=lambda k: k[0])


def plan():
    out = {}
    # § 1: все задачи — в занятии 25; 031, 032 — ручные (ступени 8, 9)
    k1 = [(6, lambda: c_deriv("S_3"))] * 4 + [(6, lambda: c_deriv("S^3"))] + [(5, lambda: c_complete("S_3"))] * 3 + \
         [(6, lambda: c_diag_fatal("S_3"))] * 2 + [(6, lambda: c_diag2("S^3"))] + \
         [(5, lambda: c_a3_series(True)), (5, lambda: c_a3_series(False)), (5, lambda: c_near_diag("A3"))] + \
         [(6, lambda: c_series("m", "w", 1)), (6, lambda: c_series("m", "c", 1))] + \
         [(6, lambda: c_series_diag("m", "w", 1)), (6, lambda: c_series_diag("m", "c", 1))] + \
         [(7, lambda: c_compare(1)), (7, lambda: c_compare(1, "c"))] + \
         [(7, lambda: c_build("m-not-s", 1)), (7, lambda: c_build("sc-not-m", 1)), (7, lambda: c_build("s-not-m", 1))] + \
         [(6, lambda: c_table("A3")), (6, lambda: c_table("A*12")), (6, lambda: c_table("R*3"))] + \
         [(6, lambda: c_table_diag("A3")), (6, lambda: c_table_diag("R*3"))] + [(6, lambda: c_nat(1))] * 2
    s1 = ids(1, range(1, 31))
    assert len(k1) == len(s1), (len(k1), len(s1))
    rnd.shuffle(k1)
    out.update(zip(s1, [f for _, f in order(k1)]))
    # § 2: 001 — занятие 25; 002–035 — 26; 036–053 — 27. Ручные: 012, 020, 028, 034, 051–053
    k2 = [(6, lambda: c_deriv("S^4"))] * 5 + [(6, lambda: c_deriv("S_4"))] * 4 + [(6, lambda: c_deriv("S_4*"))] * 2 + \
         [(5, lambda: c_complete("S^4"))] * 2 + [(5, lambda: c_complete("S_4"))] * 2 + [(5, lambda: c_complete("S_4*"))] + \
         [(6, lambda: c_diag2("S^4"))] * 4 + [(6, lambda: c_diag_fatal("S_4"))] * 2 + [(6, lambda: c_diag_fatal("S_4*"))] + \
         [(5, c_a15_series)] * 2 + [(5, c_a12_series)] + [(5, lambda: c_near_diag("A15")), (5, lambda: c_near_diag("A12"))] + \
         [(6, lambda: c_series("c", "w", 2))] * 3 + [(6, lambda: c_series("c", "c", 2))] * 2 + \
         [(6, lambda: c_series_diag("c", "w", 2)), (6, lambda: c_series_diag("c", "c", 2))] + \
         [(7, lambda: c_compare(2)), (7, lambda: c_compare(2, "c")), (6, lambda: c_compare_diag(2))] + \
         [(7, lambda: c_build("c-not-s", 2)), (7, lambda: c_build("m-not-c", 2)), (7, lambda: c_build("c-not-q", 2))] + \
         [(6, lambda: c_nat(2))] * 2 + [(6, c_contra)] * 2 + [(6, c_contra_diag)]
    s2 = ids(2, [n for n in range(1, 51) if n not in (12, 20, 28, 34)])
    assert len(k2) == len(s2), (len(k2), len(s2))
    rnd.shuffle(k2)
    a_part, b_part = k2[:31], k2[31:]
    out.update(zip(s2, [f for _, f in order(a_part)] + [f for _, f in order(b_part)]))
    # § 3: 001–016 — занятие 27 (ручная 012); 017–032 — 28 (ручные 031, 032)
    k3 = [(6, lambda: c_deriv("S^5"))] * 5 + [(5, lambda: c_complete("S^5"))] * 3 + [(6, lambda: c_diag2("S^5"))] * 4 + \
         [(5, c_ad1_series)] * 2 + [(5, lambda: c_near_diag("Ad1"))] + [(6, c_deg_series)] * 3 + \
         [(6, c_deg_series_diag)] * 2 + [(6, c_rd1_items)] * 2 + [(7, c_deg_vs_ent)] * 2 + [(5, c_mt7), (6, c_mt7_diag)] + \
         [(6, lambda: c_nat3())] + [(7, lambda: c_build_deg("deg-imp")), (7, lambda: c_build_deg("deg-new"))]
    s3 = ids(3, [n for n in range(1, 31) if n != 12])
    assert len(k3) == len(s3), (len(k3), len(s3))
    rnd.shuffle(k3)
    out.update(zip(s3, [f for _, f in order(k3[:15])] + [f for _, f in order(k3[15:])]))
    # § 4: 001–018 — занятие 28 (ручные 010, 016); 019 — 29 (ступень 7); 020 (ручная), 021 (ручная) — 29
    k4 = [(6, lambda: c_deriv("S^6"))] * 3 + [(5, lambda: c_complete("S^6"))] * 2 + [(6, lambda: c_diag2("S^6"))] * 2 + \
         [(7, c_rk1_build)] + [(6, c_rk1_diag)] + [(6, lambda: c_series("q", "w", 4))] + \
         [(6, lambda: c_series_diag("q", "w", 4))] + [(7, lambda: c_compare(4)), (6, lambda: c_compare_diag(4))] + \
         [(5, c_book_s6mt3)] + \
         [(6, lambda: c_nat(4))] + [(7, lambda: c_build("q-not-sc", 4))]
    s4 = ids(4, [n for n in range(1, 19) if n not in (10, 16)])
    assert len(k4) == len(s4), (len(k4), len(s4))
    rnd.shuffle(k4)
    out.update(zip(s4, [f for _, f in order(k4)]))
    out["04.04-019"] = lambda: c_compare(4, "c")
    return out


def c_nat3(level=6):
    """Обычный язык: «логически истинное» высказывание (⊢ x в S⁵)."""
    for _ in range(20000):
        f = nat_side(list("pqr"))
        g = nat_side(list("pqr"))
        h = rnd.choice([W(f, g), W(f, N(f)) if False else W(f, g), C(W(f, N(g)), W(g, N(g)))])
        if h in FSEEN or size(h) < 14 or size(h) > 40:
            continue
        if f[0] in ("conj", "wdis") and g[0] in ("conj", "wdis"):
            continue
        FSEEN.add(h)
        break
    taut = SY.is_taut(h)
    parts = []
    if h[0] == "wdis":
        text = "верно по крайней мере одно из двух: " + "; ".join(nl(t) for t in h[1])
    else:
        text = "верно и то, что " + ", и то, что ".join("верно по крайней мере одно из двух: " + "; ".join(nl(s_) for s_ in t[1])
                                                     for t in h[1])
    cond = ("Обозначим: $p$ — «идёт дождь», $q$ — «дует ветер», $r$ — «холодно»; «или» — соединительное ($\\vee$, "
            "гл. 2, § 1, с. 36). Запишите высказывание формулой и исследуйте, доказуема ли в $S^5$ формула $\\vdash x$ "
            f"для него (то есть утверждается ли оно «без посылок»); обоснуйте значениями. Критерий: {CRIT_D}.\n\n"
            f"> {text[0].upper() + text[1:]}.").replace("исследуйте, доказуема ли в $S^5$ формула",
                                                        "исследуйте доказуемость в $S^5$ формулы")
    if taut:
        just = "тавтология — доказуема (MT4, с. 69)"
    else:
        e = next(e for e in SY.rows(h) if not SY.value(h, e))
        just = f"при {env_t(e)} ложно — не тавтология, недоказуема (MT1, с. 67)"
    ans = f"$\\vdash {T(h)}$; {'доказуема' if taut else 'недоказуема'}."
    sol = f"Формула: $\\vdash {T(h)}$; {just}."
    return card(level, "F", "vary", "short", "с. 67–69, гл. 4, § 3", "S5, обычный язык", cond, ans, sol, form="nat",
                system="S^5")


def c_build_deg(kind, level=7):
    if kind == "deg-imp":
        cond = (f"{CONV_W} Постройте высказывания $x$ и $y$, для которых в $S^5$ доказуемы $\\vdash x$ и $x \\vdash y$, "
                f"но недоказуема $\\vdash y$, или докажите, что таких нет. Затем ответьте на тот же вопрос для "
                f"доказуемых $x \\vdash y$ и $\\vdash \\sim y$ и недоказуемой $\\vdash \\sim x$. Критерий: {CRIT_D}.")
        ans = "Ни в одном случае таких высказываний нет (MT1, MT4, $R^d1$, MT5)."
        sol = ("1. Пусть $\\vdash x$ и $x \\vdash y$ доказуемы. По $R^d1$ (с. 67) доказуема и $\\vdash y$ — требуемой пары "
               "нет. То же семантически: по MT1 (с. 67) $x$ — тавтология; $x \\vdash y$ — теорема $S^s$ и тавтология (с. 22); тогда $y = 1$ при "
               "всех значениях, и по MT4 (с. 69) $\\vdash y$ доказуема.\n"
               "2. Пусть $x \\vdash y$ и $\\vdash \\sim y$ доказуемы. По $R^d2$ (с. 70) — или по MT5 (с. 69) — доказуема "
               "$\\vdash \\sim x$. Семантически: $y = 0$ всегда, а из $x = 1$ следовало бы $y = 1$; значит, $x = 0$ "
               "всегда, и $\\sim x$ — тавтология.\nТаких высказываний нет.")
        return card(level, "M", "open", "build", "с. 67–70, гл. 4, § 3", "S5, построение", cond, ans, sol, system="S^5")
    for _ in range(20000):
        a, b = deg_form(True, 8, 22, "pq"), deg_form(True, 8, 22, "pqr")
        if not atoms(b) <= atoms(a) and len(atoms(a) | atoms(b)) >= 3:
            break
    cond = (f"{CONV_W} Постройте высказывания $x$ и $y$, в каждом из которых не меньше двух бинарных операторов, такие, "
            f"что в $S^5$ доказуемы $\\vdash x$ и $\\vdash y$, но формула $x \\vdash y$ недоказуема (ни в $S^s$, ни в "
            f"$S^5$), — или докажите, что таких нет. Критерии: {CRIT_D}; {CRIT['s']}; формулы $x \\vdash y$ доказуемы в "
            "$S^5$ так же, как в $S^s$ (с. 67).")
    ans = f"Например, $x$ = ${T(a)}$, $y$ = ${T(b)}$ (возможны и другие)."
    sol = (f"$\\vdash {T(a)}$ и $\\vdash {T(b)}$ — тавтологии, доказуемы по MT4 (с. 69). Но в ${T(b)}$ входит "
           f"{lst(atoms(b) - atoms(a))}, которого нет в ${T(a)}$: формула ${FT(a, b)}$, хотя и тавтология, в $S^s$ "
           "недоказуема (непарадоксальность). Дополнения $S^5$ (с. 67) дают только формулы вида $\\vdash x$, поэтому "
           "и в $S^5$ она недоказуема.")
    return card(level, "C", "open", "build", "с. 67–70, гл. 4, § 3", "S5, построение", cond, ans, sol, system="S^5")


def render(cid, c):
    sec = int(cid.split(".")[1].split("-")[0])
    sysl = f'system: "{c["system"]}"\n' if c.get("system") else ""
    return (f'---\nid: "{cid}"\nchapter: 4\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\n'
            f'step: {c["step"]}\ncondition: def\nform: {c["form"]}\nanswer: {c["answer"]}\nsource: "{c["source"]}"\n'
            f'{sysl}generated: true\ntags: [{c["tags"]}]\n---\n\n## Условие\n\n{c["cond"]}\n\n## Ответ\n\n{c["ans"]}\n\n'
            f'## Решение\n\n{c["sol"]}\n')


def main():
    cards = {cid: fn() for cid, fn in plan().items()}
    hand = {k: v for k, v in HAND.items()}
    assert not set(cards) & set(hand)
    cards.update(hand)
    for cid, c in cards.items():
        assert not test_like(c["cond"]), (cid, c["cond"][:160])
    path = ROOT / "data" / "zadachi" / "04.md"
    parts = re.split(r"(\n=====\n)", path.read_text(encoding="utf-8"))
    done = set()
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(04\.\d\d-\d{3})"', chunk, re.M)
        if m and m.group(1) in cards:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            text = render(m.group(1), cards[m.group(1)])
            if cards[m.group(1)].get("hand"):
                text = text.replace("generated: true\n", "")
            parts[i] = lead + text.rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
            done.add(m.group(1))
    assert done == set(cards), sorted(set(cards) - done)
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {len(done)}")


if __name__ == "__main__":
    main()
