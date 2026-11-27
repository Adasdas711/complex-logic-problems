#!/usr/bin/env python3
"""Усложнение гл. 5 «Общая теория дедукции» (занятия 29–33) по образцу занятия 10.

Заменяет в src/data/zadachi/05.md карточки в тех же id (глава и параграф сохраняются):
  § 1–2 — длинные формулы по критериям MT1–MT4, MT6 (с. 72–73) для S^s, S^w, S^m, S^c, S^6 с обоснованием значениями
          и множествами элементарных высказываний; диагностика с двумя ошибками; построения «формула, доказуемая в одних
          системах и недоказуемая в других, или докажите, что нельзя»; выводы в S₁ (8–12 строк) с переносом на другие
          системы, дополнение выводов, выводы с двумя неверными основаниями; формализация рассуждений;
  § 3   — выводы «парадоксов» в S⁶ по R^k1 (гл. 4, § 4), подстановки в формулы вида B, формулы вида A и B;
  § 4   — формулы интуиционистского списка книги (с. 75) как формулы следования; выводы ⊢ X ∨ ∼X в S⁵;
  § 5   — выводы в S^s_n с A^n1–A^n6 (с. 76), классический случай с A^n7, серии формул в трёх состояниях;
  § 6   — расширение числа возможностей (D1, MT1–MT6, с. 77–78), отношения D2, D3 (с. 79);
  § 7   — системы S^i_n: что исключают MT1 и MT2 § 5;
  § 8   — интерпретация знака следования § 8 (с. 79–80);
  § 9   — операция замены отрицаний (с. 81), S₂¹.
Выводы проверяются logic/ded5.check, ответы — критериями systems.py и перебором значений.

Запуск: python3 src/scripts/gen/hard05.py
"""
import importlib.util
import random
import re
import sys
from itertools import combinations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts"))
import ded5 as K  # noqa: E402
import systems as SY  # noqa: E402
from ded5 import NN, QQ, check, ftex, show, show_hidden, tex, why_tex  # noqa: E402
from s1 import C, D, N, V  # noqa: E402
from s1w import W  # noqa: E402
from open_form import test_like  # noqa: E402

_spec = importlib.util.spec_from_file_location("hard02_lib", ROOT / "scripts" / "gen" / "hard02.py")
H = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(H)

rnd = random.Random(1970_0500)
H.rnd.seed(1970_0501)
x, y, z, u = (V(c) for c in "xyzu")
L = "абвгдежз"
KS = ["s", "w", "m", "c", "q"]
ST = {"s": "$S^s$", "w": "$S^w$", "m": "$S^m$", "c": "$S^c$", "q": "$S^6$"}
MTN = {"s": "MT1", "m": "MT2", "w": "MT3", "c": "MT4", "q": "MT6"}

CONV = ("Буквы $x, y, z, u$ — элементарные высказывания; «$\\vee$» — соединительная дизъюнкция («по крайней мере одно "
        "из»), «$:$» — сильная («одно и только одно из»); запись — по соглашению книги.")
CRIT = ("Критерии (гл. 5, § 2, с. 72–73): формула следования доказуема в $S^s$ (MT1) тогда и только тогда, когда "
        "импликация «посылка $\\supset$ заключение» доказуема в классическом пропозициональном исчислении и в заключение не "
        "входят элементарные высказывания, отсутствующие в посылке; в $S^m$ (MT2) — импликация доказуема и в посылку и "
        "заключение входят одинаковые элементарные высказывания; в $S^w$ (MT3) — импликация доказуема и в посылке и "
        "заключении есть по крайней мере одно одинаковое элементарное высказывание; в $S^c$ (MT4) — импликация доказуема и в "
        "посылку не входят элементарные высказывания, отсутствующие в заключении; в $S^6$ (MT6) — импликация доказуема. "
        "Импликация доказуема классически тогда и только тогда, когда формула следования — тавтология (с. 72).")
SRC2 = "с. 72–73, гл. 5, § 2"


def card(level, typ, step, ans_kind, src, tags, cond, ans, sol, form="sym", system=None, case=None, condition="def"):
    return dict(level=level, type=typ, step=step, form=form, answer=ans_kind, source=src, tags=tags, cond=cond,
                ans=ans, sol=sol, system=system, case=case, condition=condition)


# ---------- формулы ----------
def rnd_f(names, depth, dis=0.15):
    if depth == 0 or rnd.random() < 0.18:
        v = V(rnd.choice(names))
        return N(v) if rnd.random() < 0.35 else v
    k = rnd.random()
    if k < 0.17:
        return N(rnd_f(names, depth - 1, dis))
    a, b = rnd_f(names, depth - 1, dis), rnd_f(names, depth - 1, dis)
    if a == b:
        return a
    if k < 0.55:
        return C(a, b)
    return D(a, b) if rnd.random() < dis else W(a, b)


def size(f):
    return len(tex(f)) if f is not None else 0


def atoms(f):
    return K.atoms(f)


def lst(s):
    s = sorted(s)
    return "\\{" + ", ".join(s) + "\\}" if s else "\\varnothing"


def env_t(e):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(e.items()))


def pattern(a, b):
    if not K.taut2(a, b):
        return "non"
    A, B = atoms(a), atoms(b)
    if A == B:
        return "eq"
    if B < A:
        return "sub"
    if A < B:
        return "sup"
    return "over" if A & B else "disj"


PROV = {"eq": set(KS), "sub": {"s", "w", "q"}, "sup": {"c", "w", "q"}, "over": {"w", "q"}, "disj": {"q"}, "non": set()}


def provset(a, b):
    out = {k for k in KS if SY.provable(k, a, b)}
    assert out == PROV[pattern(a, b)], (ftex(a, b), out, pattern(a, b))
    return out


def sys_list(ks):
    ks = [k for k in KS if k in ks]
    return ", ".join(ST[k] for k in ks) if ks else "ни в одной"


SEEN = set()


def sample(pat, lo=16, hi=40, dis=0.15, depth=3):
    for _ in range(40000):
        if pat == "eq":
            la = lb = rnd.sample("xyz", rnd.choice([2, 2, 3]))
        elif pat == "sub":
            lb = rnd.sample("xyz", 2)
            la = lb + [rnd.choice([c for c in "xyzu" if c not in lb])]
        elif pat == "sup":
            la = rnd.sample("xyz", 2)
            lb = la + [rnd.choice([c for c in "xyzu" if c not in la])]
        elif pat == "over":
            la = ["x", "y"]
            lb = ["y", "z"]
        elif pat == "disj":
            la, lb = ["x", "y"], ["z", "u"]
            if rnd.random() < 0.5:
                la, lb = ["x"], ["y", "z"]
        else:
            la = rnd.sample("xyz", 2)
            lb = rnd.sample("xyz", 2)
        a, b = rnd_f(la, depth, dis), rnd_f(lb, depth, dis)
        if a == b or not (lo <= size(a) + size(b) <= hi) or size(a) < 4 or size(b) < 4:
            continue
        if pattern(a, b) != pat or (a, b) in SEEN:
            continue
        SEEN.add((a, b))
        return a, b
    raise RuntimeError(pat)


def why_sys(a, b, k):
    """Обоснование для одной системы."""
    A, B = atoms(a), atoms(b)
    if not K.taut2(a, b):
        return f"не тавтология (при {env_t(K.counter2(a, b))} посылка 1, заключение 0) — по {MTN[k]} недоказуема"
    ok = SY.cond(k, a, b)
    detail = {"s": f"$B \\subseteq A$ {'выполнено' if ok else 'нарушено'}",
              "c": f"$A \\subseteq B$ {'выполнено' if ok else 'нарушено'}",
              "m": f"$A = B$ {'выполнено' if ok else 'нарушено'}",
              "w": f"$A \\cap B \\neq \\varnothing$ {'выполнено' if ok else 'нарушено'}",
              "q": "условия на элементарные высказывания нет"}[k]
    return f"тавтология, {detail} — по {MTN[k]} {'доказуема' if ok else 'недоказуема'}"


def explain(a, b):
    A, B = atoms(a), atoms(b)
    head = f"$A = {lst(A)}$, $B = {lst(B)}$. "
    if not K.taut2(a, b):
        e = K.counter2(a, b)
        return head + (f"При {env_t(e)} посылка 1, заключение 0: формула не тавтология, импликация классически недоказуема — "
                       "по MT1–MT4, MT6 формула недоказуема ни в одной системе.")
    ks = provset(a, b)
    rel = {"eq": "$A = B$", "sub": "$B \\subset A$, $A \\neq B$", "sup": "$A \\subset B$, $A \\neq B$",
           "over": "$A \\cap B \\neq \\varnothing$, но ни одно множество не входит в другое",
           "disj": "$A \\cap B = \\varnothing$"}[pattern(a, b)]
    return head + (f"Наборов, где посылка 1, а заключение 0, нет (перебор {2 ** len(A | B)} наборов) — тавтология. {rel}. "
                   f"Доказуема в: {sys_list(ks)}.")


# ---------- § 1–2: серии ----------
def c_crit_series(src=SRC2, level=6, sec_tags="общая теория дедукции, критерии"):
    pats = rnd.sample(["eq", "sub", "sup", "over", "disj", "non"], 4)
    items = [sample(p) for p in pats]
    ans = "; ".join(f"{L[i]}) {sys_list(provset(a, b))}" for i, (a, b) in enumerate(items))
    cond = (f"{CONV} Для каждой формулы найдите все системы из $S^s$, $S^w$, $S^m$, $S^c$, $S^6$, в которых она доказуема, и "
            "обоснуйте: для нетавтологии — набором значений, при котором посылка 1, а заключение 0; для тавтологии — "
            f"множествами $A$ (элементарные высказывания посылки) и $B$ (заключения). {CRIT}\n\n"
            + "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    sol = "\n".join(f"{L[i]}) {explain(a, b)}" for i, (a, b) in enumerate(items))
    return card(level, "C", "open", "short", src, sec_tags, cond, ans, sol)


def c_crit_one(src=SRC2, level=7):
    pat = rnd.choice(["sub", "sup", "over", "disj", "non", "eq"])
    a, b = sample(pat, lo=24, hi=44)
    ks = provset(a, b)
    taut = K.taut2(a, b)
    ans = (f"Классически — {'доказуема' if taut else 'недоказуема'}; " +
           "; ".join(f"{ST[k]} — {'да' if k in ks else 'нет'}" for k in KS))
    cond = (f"{CONV} Исследуйте доказуемость импликации ${tex(a)} \\supset {tex(b)}$ в классическом пропозициональном "
            f"исчислении и формулы ${ftex(a, b)}$ в каждой из систем $S^s$, $S^w$, $S^m$, $S^c$, $S^6$. {CRIT}")
    sol = (explain(a, b) + "\n\n" + "\n".join(f"{ST[k]}: {why_sys(a, b, k)} (с. 72–73)." for k in KS))
    return card(level, "S", "transfer", "short", src, "классическая логика, критерии", cond, ans, sol)


# ошибки ученика при применении критериев
def wrong_claim(a, b, k):
    """Правдоподобный неверный вывод ученика для системы k и его разбор (claim, fix, why)."""
    A, B = atoms(a), atoms(b)
    good = SY.provable(k, a, b)
    taut = K.taut2(a, b)
    if good:
        if k == "s":
            bad = sorted(A - B)
            if bad:
                return (f"недоказуема: в посылку входит ${bad[0]}$, которого нет в заключении",
                        "это условие $S^c$ (MT4); по MT1 (с. 72) для $S^s$ важно лишь, чтобы в заключение не входили "
                        "элементарные высказывания, отсутствующие в посылке")
        if k == "c":
            bad = sorted(B - A)
            if bad:
                return (f"недоказуема: в заключение входит ${bad[0]}$, которого нет в посылке",
                        "это условие $S^s$ (MT1); по MT4 (с. 73) для $S^c$ важно, чтобы в посылку не входили "
                        "элементарные высказывания, отсутствующие в заключении")
        if k == "w" and A != B:
            return ("недоказуема: множества элементарных высказываний посылки и заключения различны",
                    "это условие $S^m$ (MT2); по MT3 (с. 73) для $S^w$ достаточно одного общего элементарного высказывания")
        if k == "q" and not (A & B):
            return ("недоказуема: у посылки и заключения нет общих элементарных высказываний",
                    "по MT6 (с. 73) в $S^6$ условий на элементарные высказывания нет — достаточно тавтологичности")
        return None
    if not taut:
        if SY.cond(k, a, b):
            e = K.counter2(a, b)
            return ("доказуема: условие на элементарные высказывания выполнено",
                    f"условия мало: при {env_t(e)} посылка 1, заключение 0 — импликация классически недоказуема, а "
                    f"{MTN[k]} (с. 72–73) требует её доказуемости")
        return None
    if k == "m" and A & B:
        return ("доказуема: тавтология, и у посылки и заключения есть общие элементарные высказывания",
                f"общего элементарного высказывания достаточно для $S^w$ (MT3), а по MT2 (с. 73) для $S^m$ множества "
                f"должны совпадать: ${lst(A)}$ и ${lst(B)}$")
    if k == "s" and A <= B:
        return ("доказуема: тавтология, и в посылку не входят элементарные высказывания, отсутствующие в заключении",
                f"это условие $S^c$ (MT4); по MT1 (с. 72) в заключение не должны входить новые элементарные высказывания, "
                f"а входит ${sorted(B - A)[0]}$")
    if k == "c" and B <= A:
        return ("доказуема: тавтология, и в заключение не входят элементарные высказывания, отсутствующие в посылке",
                f"это условие $S^s$ (MT1); по MT4 (с. 73) в посылку не должны входить элементарные высказывания, "
                f"отсутствующие в заключении, а входит ${sorted(A - B)[0]}$")
    return ("доказуема: это тавтология",
            f"тавтологичности мало: по {MTN[k]} (с. 72–73) нужно ещё условие на элементарные высказывания, а оно нарушено "
            f"($A = {lst(A)}$, $B = {lst(B)}$)")


def right_claim(a, b, k):
    if SY.provable(k, a, b):
        return "доказуема: тавтология, и условие системы выполнено"
    if not K.taut2(a, b):
        return f"недоказуема: при {env_t(K.counter2(a, b))} посылка 1, заключение 0"
    return "недоказуема: тавтология, но условие системы нарушено"


def c_crit_diag(src=SRC2, level=6):
    for _ in range(2000):
        rows = []
        for k in rnd.sample(KS, 4):
            pat = rnd.choice(["eq", "sub", "sup", "over", "disj", "non"])
            a, b = sample(pat, lo=14, hi=34)
            rows.append((k, a, b))
        wrong = rnd.sample(range(4), 2)
        claims = []
        ok = True
        for i, (k, a, b) in enumerate(rows):
            if i in wrong:
                w = wrong_claim(a, b, k)
                if not w:
                    ok = False
                    break
                claims.append(w)
            else:
                claims.append(None)
        if ok:
            break
    lines, ans, sol = [], [], []
    for i, (k, a, b) in enumerate(rows):
        if i in wrong:
            claim, why = claims[i]
            verdict = "доказуема" if SY.provable(k, a, b) else "недоказуема"
            ans.append(f"{i + 1}: в {ST[k]} {verdict} ({MTN[k]} § 2, с. {72 if k == 's' else 73})")
            sol.append(f"{i + 1}. Неверно: {why}. Верно: {why_sys(a, b, k)}.")
        else:
            claim = right_claim(a, b, k)
        lines.append(f"{i + 1}. ${ftex(a, b)}$ в {ST[k]} — {claim}.")
    cond = (f"{CONV} Студент исследовал доказуемость четырёх формул, каждой — в своей системе:\n\n" + "\n".join(lines) +
            f"\n\nРовно два вывода неверны. Найдите их, назовите нарушенную метатеорему и дайте верный ответ с обоснованием. {CRIT}")
    return card(level, "E", "vary", "text", src, "критерии, диагностика", cond, "; ".join(ans),
                "\n".join(sol) + "\n\nОстальные выводы верны.")


# ---------- построения ----------
REL = ["eq", "sub", "sup", "over", "disj", "non"]
REL_TEXT = {"eq": "$A = B$", "sub": "$B \\subset A$, $A \\neq B$", "sup": "$A \\subset B$, $A \\neq B$",
            "over": "$A \\cap B \\neq \\varnothing$ и ни одно из множеств не входит в другое", "disj": "$A \\cap B = \\varnothing$",
            "non": "не тавтология"}


def requests_pool():
    out = []
    for inn in range(1, 4):
        for ins in combinations(KS, inn):
            for outn in range(1, 3):
                for outs in combinations([k for k in KS if k not in ins], outn):
                    out.append((ins, outs))
    return out


def feasible(ins, outs):
    return [r for r in REL if set(ins) <= PROV[r] and not (set(outs) & PROV[r])]


IMPOSS = {
    ("s", "c", "m"): "из $B \\subseteq A$ (MT1) и $A \\subseteq B$ (MT4) следует $A = B$ — условие MT2",
    ("m", "s"): "из $A = B$ (MT2) следует $B \\subseteq A$ (MT1)", ("m", "c"): "из $A = B$ (MT2) следует $A \\subseteq B$ (MT4)",
    ("m", "w"): "из $A = B$ следует $A \\cap B = A \\neq \\varnothing$: в каждом высказывании есть элементарные",
    ("s", "w"): "из $B \\subseteq A$ и $B \\neq \\varnothing$ следует $A \\cap B \\neq \\varnothing$",
    ("c", "w"): "из $A \\subseteq B$ и $A \\neq \\varnothing$ следует $A \\cap B \\neq \\varnothing$",
    ("any", "q"): "во всех системах первое условие — доказуемость импликации, а в $S^6$ других условий нет (MT6)",
}


def why_impossible(ins, outs):
    ins, outs = set(ins), set(outs)
    if "q" in outs:
        return IMPOSS[("any", "q")]
    if {"s", "c"} <= ins and "m" in outs:
        return IMPOSS[("s", "c", "m")]
    for a in [k for k in KS if k in ins]:
        for b in [k for k in KS if k in outs]:
            if (a, b) in IMPOSS:
                return IMPOSS[(a, b)]
    raise ValueError((ins, outs))


def req_text(ins, outs):
    return f"доказуемую в {', '.join(ST[k] for k in ins)} и недоказуемую в {', '.join(ST[k] for k in outs)}"


def c_construct(src=SRC2, level=8):
    pool = requests_pool()
    for _ in range(5000):
        reqs = rnd.sample(pool, 3)
        feas = [bool(feasible(*r)) for r in reqs]
        if sum(feas) in (1, 2) and all(feas[i] or why_impossible(*reqs[i]) for i in range(3)):
            break
    ans, sol = [], []
    for i, (ins, outs) in enumerate(reqs):
        fr = feasible(ins, outs)
        if fr:
            r = rnd.choice([q for q in fr if q != "non"] or fr)
            a, b = sample(r, lo=10, hi=26, depth=2)
            got = provset(a, b)
            assert set(ins) <= got and not (set(outs) & got)
            ans.append(f"{L[i]}) например, ${ftex(a, b)}$")
            sol.append(f"{L[i]}) Нужно {REL_TEXT[r]}" + (" при тавтологичности" if r != "non" else "") +
                       f". Пример ${ftex(a, b)}$: {explain(a, b)}")
        else:
            ans.append(f"{L[i]}) нельзя")
            sol.append(f"{L[i]}) Нельзя: {why_impossible(ins, outs)}. По MT1–MT4, MT6 (с. 72–73) доказуемость в каждой "
                       "системе определяется тавтологичностью и отношением множеств $A$, $B$, так что требование "
                       "противоречиво.")
    cond = (f"{CONV} Для каждого требования постройте формулу следования, ему удовлетворяющую, или докажите, что такой "
            f"формулы нет. Пусть $A$ и $B$ — множества элементарных высказываний посылки и заключения. {CRIT}\n\n" +
            "\n".join(f"{L[i]}) формулу, {req_text(*r)};" for i, r in enumerate(reqs)))
    return card(level, "S", "transfer", "build", src, "критерии, построение", cond, "; ".join(ans), "\n".join(sol),
                form="meta")


def c_separate(src=SRC2, level=7):
    """Разделяющие формулы для пары систем с длинными формулами."""
    pairs = [("s", "c"), ("c", "s"), ("w", "s"), ("w", "c"), ("q", "w"), ("s", "m"), ("c", "m"), ("w", "m")]
    p1, p2 = rnd.sample(pairs, 2)
    ans, sol, items = [], [], []
    for i, (k1, k2) in enumerate((p1, p2)):
        r = rnd.choice(feasible((k1,), (k2,)))
        a, b = sample(r, lo=20, hi=36)
        got = provset(a, b)
        assert k1 in got and k2 not in got
        items.append((k1, k2))
        ans.append(f"{L[i]}) например, ${ftex(a, b)}$")
        sol.append(f"{L[i]}) ${ftex(a, b)}$: {explain(a, b)} В {ST[k1]}: {why_sys(a, b, k1)}; в {ST[k2]}: "
                   f"{why_sys(a, b, k2)}.")
    cond = (f"{CONV} Постройте формулы следования, в которых посылка и заключение содержат не меньше двух операторов "
            f"каждая: а) доказуемую в {ST[p1[0]]}, но не в {ST[p1[1]]}; б) доказуемую в {ST[p2[0]]}, но не в {ST[p2[1]]}. "
            f"Обоснуйте ответ значениями и множествами элементарных высказываний. {CRIT}")
    return card(level, "S", "transfer", "build", src, "критерии, разделяющие формулы", cond, "; ".join(ans), "\n".join(sol))


# ---------- обычный язык ----------
TOPICS = [
    [("идёт дождь", "дождь не идёт"), ("дует ветер", "ветер не дует"), ("холодно", "не холодно"),
     ("светит солнце", "солнце не светит")],
    [("ключ замкнут", "ключ не замкнут"), ("лампа горит", "лампа не горит"), ("по цепи течёт ток", "по цепи не течёт ток"),
     ("предохранитель цел", "предохранитель не цел")],
    [("договор подписан", "договор не подписан"), ("сделка зарегистрирована", "сделка не зарегистрирована"),
     ("срок истёк", "срок не истёк"), ("стороны пришли к соглашению", "стороны не пришли к соглашению")],
    [("число $n$ делится на 2", "число $n$ не делится на 2"), ("число $n$ делится на 3", "число $n$ не делится на 3"),
     ("число $n$ больше 10", "число $n$ не больше 10"), ("число $n$ простое", "число $n$ не простое")],
    [("у пациента жар", "у пациента нет жара"), ("анализ положителен", "анализ не положителен"),
     ("пациент принимает лекарство", "пациент не принимает лекарство"), ("пациент здоров", "пациент не здоров")],
    [("поезд опаздывает", "поезд не опаздывает"), ("рейс отменён", "рейс не отменён"),
     ("билеты проданы", "билеты не проданы"), ("касса открыта", "касса закрыта")],
]


def nl(f, ph, inner=False):
    k = f[0]
    if k == "v":
        return ph[f[1]][0]
    if k == "neg" and f[1][0] == "v":
        return ph[f[1][1]][1]
    if k == "neg":
        return f"неверно, что {nl(f[1], ph, True)}"
    parts = [nl(a, ph, True) if a[0] in ("v", "neg") else f"({nl(a, ph, True)})" for a in f[1]]
    if k == "conj":
        return " и ".join(parts)
    if k == "wdis":
        s = " или ".join(parts) + " (по крайней мере одно)"
    else:
        s = "либо " + ", либо ".join(parts) + " (одно и только одно)"
    return s


def phrases():
    t = rnd.choice(TOPICS)
    return {c: t[i] for i, c in enumerate("xyzu")}


def dict_text(ph, names):
    return "; ".join(f"${c}$ — «{ph[c][0]}»" for c in sorted(names))


def cap(s):
    return s[0].upper() + s[1:] if s and s[0] != "$" else s


def c_nat(src=SRC2, level=6, pat=None):
    pat = pat or rnd.choice(["sub", "sup", "over", "disj", "non", "eq"])
    a, b = sample(pat, lo=12, hi=30, dis=0.2)
    ph = phrases()
    names = atoms(a) | atoms(b)
    ks = provset(a, b)
    cond = (f"Рассуждение: «{cap(nl(a, ph))}; следовательно, {nl(b, ph)}». Обозначения: {dict_text(ph, names)}; «или … (по "
            "крайней мере одно)» — $\\vee$, «либо …, либо … (одно и только одно)» — $:$, «неверно, что» и «не» — $\\sim$. "
            "Запишите рассуждение формулой следования и исследуйте, в каких из систем $S^s$, $S^w$, $S^m$, $S^c$, $S^6$ оно "
            f"принимается как следование; обоснуйте значениями. {CRIT}")
    ans = f"${ftex(a, b)}$; {sys_list(ks)}."
    sol = f"Формула: ${ftex(a, b)}$.\n\n{explain(a, b)}"
    return card(level, "F", "vary", "short", src, "формализация, критерии", cond, ans, sol, form="nat")


# ---------- выводы в S₁ (= S^s) ----------
S1CONV = ("$S_1$ — система сильного следования $S^s$ (гл. 2, § 5, с. 45). Её схемы (с. 36): A1 $\\sim\\sim x \\vdash x$; "
          "A2 $x \\vdash \\sim\\sim x$; A3 $xy \\vdash x$; A4 $xy \\vdash yx$; A5, A6 — расстановка скобок в конъюнкции; "
          "A7 $(x \\vee y)z \\vdash xz \\vee y$; A8 $xz \\vee yz \\vdash (x \\vee y)z$; A9 $\\sim(x^1 \\ldots x^n) \\vdash "
          "\\sim x^1 \\vee \\ldots \\vee \\sim x^n$; A10 — обратная к A9; A11 $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$; "
          "правила (с. 17): R1 — из $x \\vdash y$ и $y \\vdash z$ получить $x \\vdash z$; R2 — из $x \\vdash y$ и $x \\vdash z$ "
          "получить $x \\vdash yz$; R3 — из $x \\vdash y$ и $y \\vdash x$ получить $z \\vdash v$, где $v$ получено из $z$ "
          "заменой вхождений $x$ на $y$.")
S1SRC = "с. 17, 36, 45, 72–73, гл. 1, § 1; гл. 2, § 1, 5; гл. 5, § 2"


def s1_lines(want, least):
    return H.build_ok(want, least)


def other_sys(a, b):
    ks = provset(a, b)
    return "; ".join(f"{ST[k]} — {'да' if k in ks else 'нет'}" for k in ["w", "m", "c", "q"])


def c_s1_deriv(level=7, src=S1SRC):
    lines = s1_lines(rnd.choice([9, 10, 11]), least=8)
    assert not check(lines, "S1")
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} {S1CONV} Выведите в $S_1$ формулу ${ftex(a, b)}$, а затем, не строя других выводов, установите по "
            f"MT2–MT4, MT6 § 2 гл. 5, в каких из систем $S^w$, $S^m$, $S^c$, $S^6$ она доказуема. {CRIT}")
    ans = f"Вывод в {len(lines)} строк (см. решение); {other_sys(a, b)}."
    sol = (show(lines) + "\n\nВыведенная формула — теорема $S^s$, значит, тавтология (MT1, с. 72). " + explain(a, b) +
           " " + " ".join(f"{ST[k]}: {why_sys(a, b, k)}." for k in ["w", "m", "c", "q"]))
    return card(level, "D", "transfer", "proof", src, "вывод, S1, перенос", cond, ans, sol, system="S^s")


def c_s1_complete(level=5, src=S1SRC):
    lines = s1_lines(rnd.choice([10, 11]), least=9)
    sl = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, str)]
    rl = [n for n, (*_, wh) in enumerate(lines, 1) if isinstance(wh, tuple)]
    hide_f = set(rnd.sample(sl[1:] or sl, min(2, max(1, len(sl) - 1))))
    hide_why = set(rnd.sample([n for n in sl if n not in hide_f], min(2, len(sl) - len(hide_f))))
    hide_why |= set(rnd.sample(rl[:-1], min(2, len(rl) - 1)))
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} {S1CONV} В выводе в $S_1$ формулы ${ftex(a, b)}$ пропущены формулы некоторых строк и основания "
            f"некоторых шагов («…»). Восстановите их и установите, в каких из $S^m$ и $S^c$ доказуема выведенная формула "
            f"(MT2, MT4 § 2 гл. 5, с. 73).\n\n{show_hidden(lines, hide_why, hide_f)}")
    parts = []
    for n in sorted(hide_why | hide_f):
        la, lb, wh = lines[n - 1]
        parts.append(f"{n} — " + (f"${ftex(la, lb)}$ " if n in hide_f else "") + (f"[{why_tex(wh)}]" if n in hide_why else ""))
    ks = provset(a, b)
    parts.append(f"$S^m$ — {'да' if 'm' in ks else 'нет'}, $S^c$ — {'да' if 'c' in ks else 'нет'}")
    sol = ("Формулу строки восстанавливаем по соседним: в R1 заключение одной строки — посылка другой, в R2 обе строки "
           "имеют общую посылку; основание — по виду формулы.\n\n" + show(lines) + "\n\n" + explain(a, b))
    return card(level, "D", "complete", "build", src, "вывод, S1, дополнение", cond, "; ".join(p.strip() for p in parts),
                sol, system="S^s")


def c_s1_diag(level=6, src=S1SRC):
    for _ in range(400):
        lines = s1_lines(rnd.choice([9, 10]), least=8)
        cand = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, str) and wh in H.WRONG]
        rs = [i for i, (*_, wh) in enumerate(lines) if isinstance(wh, tuple) and wh[0] == "R1"]
        if not cand or not rs:
            continue
        i, j = rnd.choice(cand), rnd.choice(rs)
        bad = list(lines)
        a, b, wh = bad[i]
        bad[i] = (a, b, H.WRONG[wh])
        a2, b2, wh2 = bad[j]
        bad[j] = (a2, b2, ("R2", wh2[1], wh2[2]))
        errs = check(bad, "S1")
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        if steps == sorted([i + 1, j + 1]):
            break
    else:
        raise RuntimeError("diag")
    p, q = sorted([i, j])
    fix = {i: lines[i][2], j: lines[j][2]}
    fa, fb = lines[-1][0], lines[-1][1]
    cond = (f"{CONV} {S1CONV} В выводе в $S_1$ формулы ${ftex(fa, fb)}$ ровно два основания указаны неверно. Найдите их, "
            f"объясните, почему каждое неверно, исправьте и установите, в каких из $S^w$, $S^m$, $S^c$, $S^6$ доказуема "
            f"выведенная формула.\n\n{show(bad)}")
    ans = f"Шаг {p + 1}: [{why_tex(fix[p])}]; шаг {q + 1}: [{why_tex(fix[q])}]; {other_sys(fa, fb)}."
    exp = []
    for k in (p, q):
        a, b, _ = lines[k]
        if k == i:
            exp.append(f"Шаг {k + 1}: ${ftex(a, b)}$ — пример {fix[k]}, а не {H.WRONG[fix[k]]}: {H.WHY[fix[k]]} (с. 36).")
        else:
            exp.append(f"Шаг {k + 1}: R2 соединяет в конъюнкцию заключения двух строк с общей посылкой, а здесь "
                       f"заключение строки {fix[k][1]} — посылка строки {fix[k][2]}: это R1 (с. 17).")
    sol = "\n".join(exp) + "\n\nИсправленный вывод:\n\n" + show(lines) + "\n\n" + explain(fa, fb)
    return card(level, "E", "vary", "text", src, "вывод, S1, диагностика", cond, ans, sol, system="S^s")


def c_imp_diag(src=SRC2, level=5):
    """Не каждой классически доказуемой импликации соответствует формула следования (с. 73)."""
    a, b = sample(rnd.choice(["sub", "sup", "over", "disj"]), lo=10, hi=22, depth=2)
    nested = rnd.choice([f"({tex(a)} \\vdash ({tex(b)} \\vdash {tex(a)}))",
                         f"({tex(a)} \\vdash {tex(b)})({tex(b)} \\vdash {tex(a)}) \\vdash ({tex(a)} \\vdash {tex(a)})"])
    cond = (f"{CONV} Студент рассуждает: «Импликация, соответствующая выражению ${nested}$, доказуема в классическом "
            "пропозициональном исчислении, значит, по MT6 это выражение доказуемо в $S^6$; а поскольку $S^6$ — классическая "
            f"логика, то и формула ${ftex(a, b)}$ доказуема во всех системах $S^s$, $S^w$, $S^m$, $S^c$». Найдите все ошибки "
            f"и дайте верные ответы. {CRIT}")
    ks = provset(a, b)
    ans = ("1) Выражение с двумя и более знаками $\\vdash$ — не формула следования систем общей теории дедукции (с. 73), MT6 "
           "к нему неприменима; 2) $S^6$ не совпадает с классическим исчислением (с. 73); 3) для формулы: " +
           sys_list(ks) + ".")
    sol = ("1. По определениям формулы следования выражения вида $(x \\vdash (y \\vdash x))$, $(x \\vdash y)(y \\vdash z) "
           "\\vdash (x \\vdash z)$, содержащие два или более знака следования, не являются формулами следования в системах "
           "общей теории дедукции (с. 73). MT6 говорит только о формулах $x \\vdash y$.\n"
           "2. Поэтому не каждой формуле классического исчисления вида $x \\supset y$ соответствует формула $x \\vdash y$; "
           "даже $S^6$ не совпадает с классическим исчислением (с. 73).\n"
           f"3. Формула ${ftex(a, b)}$: {explain(a, b)}")
    return card(level, "E", "vary", "text", src, "классическая логика, диагностика", cond, ans, sol, form="meta")


# ---------- построитель выводов ----------
class B:
    def __init__(self):
        self.lines = []

    def add(self, a, b, why):
        self.lines.append((a, b, why))
        return len(self.lines)


def derive_excl(bd, X, swap=False):
    """⊢ X ∨ ∼X (или ⊢ ∼X ∨ X) в S⁵: A^d1, A9, A1, A2, A4, R3, R^d1."""
    i1 = bd.add(None, N(C(N(X), X)), "Ad1")
    if swap:
        j1 = bd.add(C(N(X), X), C(X, N(X)), "A4")
        j2 = bd.add(C(X, N(X)), C(N(X), X), "A4")
        j3 = bd.add(N(C(N(X), X)), N(C(X, N(X))), ("R3", j1, j2))
        i1 = bd.add(None, N(C(X, N(X))), ("Rd1", j3, i1))
        i2 = bd.add(N(C(X, N(X))), W(N(X), N(N(X))), "A9")
        i3 = bd.add(None, W(N(X), N(N(X))), ("Rd1", i2, i1))
        i4 = bd.add(N(N(X)), X, "A1")
        i5 = bd.add(X, N(N(X)), "A2")
        i6 = bd.add(W(N(X), N(N(X))), W(N(X), X), ("R3", i4, i5))
        return bd.add(None, W(N(X), X), ("Rd1", i6, i3))
    i2 = bd.add(N(C(N(X), X)), W(N(N(X)), N(X)), "A9")
    i3 = bd.add(None, W(N(N(X)), N(X)), ("Rd1", i2, i1))
    i4 = bd.add(N(N(X)), X, "A1")
    i5 = bd.add(X, N(N(X)), "A2")
    i6 = bd.add(W(N(N(X)), N(X)), W(X, N(X)), ("R3", i4, i5))
    return bd.add(None, W(X, N(X)), ("Rd1", i6, i3))


S5CONV = ("$S^5$ получается из $S^s$ присоединением формул $\\vdash x$, схемы $A^d1$ $\\vdash \\sim(\\sim xx)$ и правила "
          "$R^d1$: если $x \\vdash y$ и $\\vdash x$, то $\\vdash y$ (гл. 4, § 3, с. 67); там же приняты $R^d2$ (если "
          "$x \\vdash y$ и $\\vdash \\sim y$, то $\\vdash \\sim x$) и $R^d3$ (если $\\vdash x$ и $\\vdash y$, то $\\vdash xy$, "
          "с. 70). $S^s$ берём в форме $S_1$ (схемы A1–A11, правила R1–R3, гл. 2, § 1, с. 36; гл. 1, § 1, с. 17). "
          "Основание [$S^s$] — строка есть теорема $S^s$: тавтология, в заключение которой не входят элементарные "
          "высказывания, отсутствующие в посылке (MT1 § 2 гл. 5, с. 72).")
S6CONV = ("$S^6$ получается из $S^5$ присоединением правила $R^k1$: если $xz \\vdash y$ и $\\vdash z$, то $x \\vdash y$ "
          "(гл. 4, § 4, с. 70). " + S5CONV)
SCH1 = ("Схемы $S_1$ (с. 36): A1 $\\sim\\sim x \\vdash x$; A2 $x \\vdash \\sim\\sim x$; A3 $xy \\vdash x$; A4 $xy \\vdash yx$; "
        "A9 $\\sim(xy) \\vdash \\sim x \\vee \\sim y$; A10 $\\sim x \\vee \\sim y \\vdash \\sim(xy)$; R1–R3 — с. 17.")
SRC_S6 = "с. 67, 70, 72–74, гл. 4, § 3–4; гл. 5, § 2–3"


def new_conj(names):
    return V(names[0]) if len(names) == 1 else C(*(V(n) for n in names))


def s6_paradox(a, b):
    """Вывод a ⊢ b в S⁶ по образцу доказательства MT2 § 4 гл. 4 (с. 70–71)."""
    new = sorted(atoms(b) - atoms(a))
    Z = new_conj(new)
    bd = B()
    swap = rnd.random() < 0.3 and len(new) == 1
    k = derive_excl(bd, Z, swap=swap)
    T = bd.lines[-1][1]
    if b == T:
        i = bd.add(C(a, T), C(T, a), "A4")
        j = bd.add(C(T, a), T, "A3")
        m = bd.add(C(a, T), T, ("R1", i, j))
    else:
        m = bd.add(C(a, T), b, "Ts")
    bd.add(a, b, ("Rk1", m, k))
    assert not check(bd.lines, "S6"), check(bd.lines, "S6")
    return bd.lines


def sample_par():
    for _ in range(20000):
        kind = rnd.random()
        if kind < 0.3:
            Y = rnd_f(["y"] if rnd.random() < 0.6 else ["y", "z"], 2)
            a = rnd_f(["x"], 2) if rnd.random() < 0.5 else rnd_f(["x", "y"], 2)
            b = W(Y, N(Y)) if rnd.random() < 0.5 else rnd_f(["x", "y", "z"], 2)
        elif kind < 0.6:
            X = rnd_f(["x"], 1)
            a = C(N(X), X) if rnd.random() < 0.5 else C(X, rnd_f(["x", "y"], 1), N(X))
            b = rnd_f(["y", "z"], 2)
        else:
            a, b = rnd_f(["x", "y"], 2), rnd_f(["x", "y", "z"], 2)
        if not atoms(b) - atoms(a) or not K.taut2(a, b) or not (8 <= size(a) + size(b) <= 30) or (a, b) in SEEN:
            continue
        if len(atoms(b) - atoms(a)) > 2:
            continue
        SEEN.add((a, b))
        return a, b
    raise RuntimeError


def c_s6_deriv(level=7, src=SRC_S6, sec="парадоксы следования"):
    a, b = sample_par()
    lines = s6_paradox(a, b)
    new = sorted(atoms(b) - atoms(a))
    cond = (f"{CONV} {S6CONV} Выведите в $S^6$ формулу ${ftex(a, b)}$ и объясните, почему в $S^s$ она недоказуема.")
    ans = (f"Вывод в {len(lines)} строк: $\\vdash {tex(lines[-3][1]) if lines[-2][2] == 'Ts' else tex(lines[-2][1])}$… "
           f"затем $R^k1$ (см. решение); в $S^s$ недоказуема: в заключение входит " +
           ", ".join(f"${n}$" for n in new) + ", которого нет в посылке (MT1, с. 72).")
    ans = (f"Вывод в {len(lines)} строк (см. решение), последний шаг — $R^k1$; в $S^s$ недоказуема: в заключение входит "
           + ", ".join(f"${n}$" for n in new) + f", отсутствующ{'ее' if len(new) == 1 else 'ие'} в посылке (MT1, с. 72).")
    sol = (show(lines) + "\n\nИдея — как в доказательстве MT2 § 4 гл. 4 (с. 70–71): к посылке присоединяется тавтология из "
           "новых элементарных высказываний; формула с такой посылкой — теорема $S^s$, а сама тавтология выводится в "
           "$S^5$ из $A^d1$. Формула — тавтология, поэтому по MT6 § 2 гл. 5 она и должна быть доказуема в $S^6$; в $S^s$ "
           "её исключает MT1 (с. 72): формулы такого рода — «парадоксы», которых системы $S^s$, $S^w$, $S^m$, $S^c$ "
           "не допускают (с. 73).")
    return card(level, "D", "transfer", "proof", src, f"{sec}, S6, вывод", cond, ans, sol, system="S^6")


def hide_lines(lines, nf=2, nw=3):
    sl = [n for n, (_, _, wh) in enumerate(lines, 1) if isinstance(wh, str)]
    rl = [n for n, (_, _, wh) in enumerate(lines, 1) if isinstance(wh, tuple)]
    hide_f = set(rnd.sample(sl[1:] or sl, min(nf, max(1, len(sl) - 1))))
    rest = [n for n in sl if n not in hide_f]
    hide_why = set(rnd.sample(rest, min(nw - 1, len(rest))))
    hide_why |= set(rnd.sample(rl[:-1] or rl, min(2, len(rl[:-1] or rl))))
    hf2 = set(rnd.sample([n for n in rl[:-1] if n not in hide_why] or [], min(1, len([n for n in rl[:-1] if n not in hide_why]))))
    return hide_why, hide_f | hf2


def complete_answer(lines, hide_why, hide_f):
    parts = []
    for n in sorted(hide_why | hide_f):
        la, lb, wh = lines[n - 1]
        parts.append((f"{n} — " + (f"${ftex(la, lb)}$ " if n in hide_f else "") +
                      (f"[{why_tex(wh)}]" if n in hide_why else "")).strip())
    return "; ".join(parts)


def c_s6_complete(level=5, src=SRC_S6, sec="парадоксы следования"):
    a, b = sample_par()
    lines = s6_paradox(a, b)
    hw, hf = hide_lines(lines)
    cond = (f"{CONV} {S6CONV} {SCH1} В выводе в $S^6$ формулы ${ftex(a, b)}$ пропущены формулы некоторых строк и основания "
            f"некоторых шагов («…»). Восстановите их.\n\n{show_hidden(lines, hw, hf)}")
    sol = ("Строку восстанавливаем по правилу, которое на неё ссылается: $R^d1$ берёт $x \\vdash y$ и $\\vdash x$ и даёт "
           "$\\vdash y$; R3 заменяет вхождения по паре $x \\vdash y$, $y \\vdash x$; $R^k1$ из $xz \\vdash y$ и $\\vdash z$ "
           "даёт $x \\vdash y$ (с. 17, 67, 70).\n\n" + show(lines))
    return card(level, "D", "complete", "build", src, f"{sec}, S6, дополнение", cond, complete_answer(lines, hw, hf), sol,
                system="S^6")


WRONG5 = {"A1": "A2", "A2": "A1", "A3": "A4", "A4": "A3", "A9": "A10", "A10": "A9", "Rd1": "R1", "Rk1": "Rd1",
          "R1": "R2", "An1": "An2", "An2": "An1", "An3": "An4", "An4": "An3", "An5": "An6", "An6": "An5", "Ts": "A3"}
AN_P = "с. 76"


def why_wrong(name, line, wrong):
    a, b, w = line
    if name in H.WHY:
        return f"${ftex(a, b)}$ — пример {name}, а не {wrong}: {H.WHY[name]} (с. 36)"
    if name == "Rd1":
        return ("R1 соединяет две формулы следования $x \\vdash y$ и $y \\vdash z$, а здесь одна из строк — формула "
                "вырожденного следования $\\vdash x$, и получается $\\vdash y$: это $R^d1$ (с. 67)")
    if name == "Rk1":
        return ("$R^d1$ даёт формулу вырожденного следования $\\vdash y$, а здесь из $xz \\vdash y$ и $\\vdash z$ получена "
                "$x \\vdash y$: это $R^k1$ (гл. 4, § 4, с. 70)")
    if name == "R1":
        return (f"R2 соединяет в конъюнкцию заключения двух строк с общей посылкой, а здесь заключение строки {w[1]} — "
                f"посылка строки {w[2]}: это R1 (с. 17)")
    if name.startswith("An"):
        return (f"${ftex(a, b)}$ — пример $A^n{name[2:]}$ (${K.AN_TEXT[name]}$), а $A^n{wrong[2:]}$ — обратная схема "
                f"${K.AN_TEXT[wrong]}$ ({AN_P})")
    if name == "Ts":
        return ("A3 ($xy \\vdash x$) оставляет первый член конъюнкции, а здесь посылка — не конъюнкция с таким первым "
                "членом; строка — теорема $S^s$ (MT1 § 2, с. 72: тавтология без новых элементарных высказываний в "
                "заключении)")
    raise KeyError(name)


def corrupt(lines, system, k=2, prefer=()):
    for _ in range(500):
        cand = [i for i, (_, _, wh) in enumerate(lines)
                if (wh if isinstance(wh, str) else wh[0]) in WRONG5]
        if len(cand) < k:
            return None
        pri = [i for i in cand if (lines[i][2] if isinstance(lines[i][2], str) else lines[i][2][0]) in prefer]
        pick = set()
        if pri:
            pick.add(rnd.choice(pri))
        while len(pick) < k:
            pick.add(rnd.choice(cand))
        bad = list(lines)
        for i in pick:
            a, b, wh = bad[i]
            bad[i] = (a, b, WRONG5[wh] if isinstance(wh, str) else (WRONG5[wh[0]], wh[1], wh[2]))
        errs = check(bad, system)
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        if steps == sorted(i + 1 for i in pick):
            return bad, sorted(pick)
    return None


def c_diag2(lines, system, cond_head, src, tags, level=6, sys_tex=None, extra_ans="", extra_sol="", prefer=()):
    res = corrupt(lines, system, prefer=prefer)
    if res is None:
        return None
    bad, pick = res
    fa, fb = lines[-1][0], lines[-1][1]
    cond = (f"{cond_head} В выводе формулы ${ftex(fa, fb)}$ ровно два основания указаны неверно. Найдите их, объясните, "
            f"почему каждое неверно, и исправьте.\n\n{show(bad)}")
    ans = "; ".join(f"шаг {i + 1}: [{why_tex(lines[i][2])}]" for i in pick) + extra_ans
    sol = "\n".join(f"Шаг {i + 1}: " + why_wrong(lines[i][2] if isinstance(lines[i][2], str) else lines[i][2][0],
                                                lines[i], bad[i][2] if isinstance(bad[i][2], str) else bad[i][2][0]) + "."
                    for i in pick)
    sol += "\n\nИсправленный вывод:\n\n" + show(lines) + extra_sol
    return card(level, "E", "vary", "text", src, tags, cond, ans, sol, system=sys_tex)


def c_s6_diag(level=6, src=SRC_S6, sec="парадоксы следования"):
    for _ in range(50):
        a, b = sample_par()
        c = c_diag2(s6_paradox(a, b), "S6", f"{CONV} {S6CONV} {SCH1}", src, f"{sec}, S6, диагностика", level, "S^6",
                    prefer=("Rk1", "Rd1"))
        if c:
            return c
    raise RuntimeError


# ---------- § 3: формулы вида A и B ----------
SCH_A = [("x \\vdash x : \\sim x", lambda X: (X, D(X, N(X)))), ("x \\vdash x \\vee \\sim x", lambda X: (X, W(X, N(X)))),
         ("\\sim xx \\vdash x", lambda X: (C(N(X), X), X))]
SCH_B = [("x \\vdash y : \\sim y", lambda X, Y: (X, D(Y, N(Y)))), ("x \\vdash y \\vee \\sim y", lambda X, Y: (X, W(Y, N(Y)))),
         ("\\sim xx \\vdash y", lambda X, Y: (C(N(X), X), Y))]
ABTXT = ("Формулы вида A (с. 74): $x \\vdash x : \\sim x$, $x \\vdash x \\vee \\sim x$, $\\sim xx \\vdash x$; вида B: "
         "$x \\vdash y : \\sim y$, $x \\vdash y \\vee \\sim y$, $\\sim xx \\vdash y$.")
SRC3 = "с. 35, 72–74, гл. 1, § 9; гл. 5, § 2–3"


def comp(names, d=1):
    for _ in range(100):
        f = rnd_f(names, d + 1)
        if f[0] not in ("v",) and 3 <= size(f) <= 12:
            return f
    return rnd_f(names, d)


def c_subst_B(level=6, src=SRC3):
    items = []
    while len(items) < 4:
        si = rnd.randrange(3)
        X = comp(["x", "y"])
        Y = comp(rnd.choice([["x"], ["y"], ["x", "y"], ["y", "z"], ["z"]]))
        a, b = SCH_B[si][1](X, Y)
        if any(a == p and b == q for _, _, p, q in items):
            continue
        items.append((si, (X, Y), a, b))
    want = {"s", "w", "m", "c"}
    ans, sol = [], []
    for i, (si, (X, Y), a, b) in enumerate(items):
        ks = provset(a, b) & want
        ans.append(f"{L[i]}) ${ftex(a, b)}$ — {sys_list(ks)}")
        sol.append(f"{L[i]}) Подстановка $x := {tex(X)}$, $y := {tex(Y)}$ в ${SCH_B[si][0]}$ даёт ${ftex(a, b)}$. "
                   + explain(a, b))
    cond = (f"{CONV} {ABTXT} В $S^s$ формулы вида B недоказуемы (с. 74). Выполните подстановки в формулы вида B и для каждой "
            f"полученной формулы найдите все системы из $S^s$, $S^w$, $S^m$, $S^c$, где она доказуема; обоснуйте значениями и "
            f"множествами $A$, $B$ элементарных высказываний посылки и заключения. {CRIT}\n\n" +
            "\n".join(f"{L[i]}) ${SCH_B[si][0]}$; $x := {tex(X)}$, $y := {tex(Y)}$" for i, (si, (X, Y), _, _) in enumerate(items)))
    sol.append("Вывод: подстановка в недоказуемую формулу может дать и доказуемую, и недоказуемую формулу — правило "
               "подстановки (MT1 § 9 гл. 1, с. 35) переносит только доказуемость (с. 74).")
    return card(level, "P", "vary", "short", src, "парадоксы следования, подстановка", cond, "; ".join(ans), "\n".join(sol),
                system="S^s")


def ab_kind(a, b):
    for nm, f in SCH_A:
        for X in [a, b, *(a[1] if a[0] == "conj" else ())]:
            if f(X) == (a, b):
                return "A", nm, X
    return None


def c_ab(level=6, src=SRC3):
    items = []
    kinds = rnd.sample(["A", "A", "Bin", "Bout", "near"], 4)
    for k in kinds:
        for _ in range(500):
            X = comp(["x", "y"])
            if k == "A":
                nm, f = rnd.choice(SCH_A)
                a, b = f(X)
            elif k in ("Bin", "Bout"):
                Y = comp(["x", "y"] if k == "Bin" else ["z", "y"])
                if Y == X or (k == "Bin" and not atoms(Y) <= atoms(X)) or (k == "Bout" and atoms(Y) <= atoms(X)):
                    continue
                nm, f = rnd.choice(SCH_B)
                a, b = f(X, Y)
            else:
                Y = comp(["x", "y"])
                if Y == X:
                    continue
                a, b = rnd.choice([(X, W(X, N(Y))), (C(N(X), Y), X), (X, D(Y, N(X)))])
            if (a, b) not in [(p, q) for p, q in items]:
                items.append((a, b))
                break
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        r = ab_kind(a, b)
        sp = SY.provable("s", a, b)
        ans.append(f"{L[i]}) " + (f"вида A ($x := {tex(r[2])}$)" if r else "не вида A") + f", в $S^s$ {'доказуема' if sp else 'недоказуема'}")
        why = SY.reason("s", a, b, tex)
        sol.append(f"{L[i]}) " + (f"Получается из ${r[1]}$ подстановкой $x := {tex(r[2])}$. " if r else
                                  "Ни из одной формулы вида A подстановкой не получается: одинаковые буквы схемы требуют "
                                  "одинаковых высказываний, а здесь соответствующие места заняты разными. ") +
                   f"В $S^s$: {why} (MT1, с. 72).")
    cond = (f"{CONV} {ABTXT} Для каждой формулы установите, получается ли она подстановкой (одинаковые буквы — одинаковыми "
            f"высказываниями) из формулы вида A, и исследуйте её доказуемость в $S^s$ по MT1 § 2 (с. 72): тавтология, в "
            f"заключение которой не входят элементарные высказывания, отсутствующие в посылке.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    sol.append("Формулы, которые не получаются из формул вида A, тоже могут быть доказуемы: важны тавтологичность и условие "
               "MT1, а не внешний вид (с. 74).")
    return card(level, "P", "iso", "short", src, "парадоксы следования, почти-примеры", cond, "; ".join(ans), "\n".join(sol),
                system="S^s")


def c_par_student(level=5, src=SRC3):
    for _ in range(500):
        X = comp(["x", "y"])
        Y = comp(["x", "y"])
        if Y != X and atoms(Y) <= atoms(X):
            break
    si = rnd.randrange(3)
    a, b = SCH_B[si][1](X, Y)
    Y2 = comp(["z"] if rnd.random() < 0.5 else ["y", "z"])
    sj = rnd.randrange(3)
    a2, b2 = SCH_B[sj][1](X, Y2)
    assert SY.provable("s", a, b) and not SY.provable("s", a2, b2)
    cond = (f"{CONV} {ABTXT} Студент рассуждает: «Формула ${ftex(a, b)}$ получается из формулы вида B ${SCH_B[si][0]}$ "
            f"подстановкой $x := {tex(X)}$, $y := {tex(Y)}$; формулы вида B в $S^s$ недоказуемы, значит, недоказуема и она. "
            f"А формула ${ftex(a2, b2)}$ — тавтология, поэтому в $S^s$ она доказуема». Найдите все ошибки, назовите "
            "нарушенные правила и дайте верные ответы.")
    ans = (f"1) Правило подстановки (MT1 § 9 гл. 1, с. 35) переносит только доказуемость; ${ftex(a, b)}$ — сильная тавтология, "
           f"по MT1 § 2 (с. 72) доказуема. 2) Тавтологичности мало: в ${ftex(a2, b2)}$ в заключение входит "
           + ", ".join(f"${n}$" for n in sorted(atoms(b2) - atoms(a2))) + ", которого нет в посылке, — по MT1 недоказуема.")
    sol = (f"1. Правило подстановки (MT1 § 9 гл. 1, с. 35): если формула доказуема, то доказуем и результат подстановки. О "
           f"подстановках в недоказуемые формулы оно ничего не говорит. Книга подчёркивает: формулы вида A получаются не из "
           f"формул вида B (с. 74). Здесь ${ftex(a, b)}$: {SY.reason('s', a, b, tex)} — по MT1 § 2 доказуема в $S^s$.\n"
           f"2. ${ftex(a2, b2)}$: {SY.reason('s', a2, b2, tex)} — по MT1 § 2 недоказуема; в $S^s$ такие «парадоксы» исключены "
           "(с. 73).")
    return card(level, "E", "vary", "text", src, "парадоксы следования, диагностика", cond, ans, sol, system="S^s")


def c_par_nat(level=6, src=SRC3):
    ph = phrases()
    xx, yy = ph["x"], ph["y"]
    cond = (f"Студент разбирает два рассуждения. Первое: «{cap(xx[0])} и {xx[1]}; следовательно, {yy[0]}» — «это следование в "
            f"смысле $S^s$, ведь посылка никогда не бывает истинной». Второе: «{cap(xx[0])}; следовательно, либо {yy[0]}, либо "
            f"{yy[1]} (одно и только одно)» — «в $S^6$ это не следование: у посылки и заключения нет общего». Обозначения: "
            f"$x$ — «{xx[0]}», $y$ — «{yy[0]}». Запишите рассуждения формулами, найдите ошибки студента, назовите нарушенные "
            f"метатеоремы и дайте верные ответы для $S^s$, $S^w$, $S^6$. {CRIT}")
    f1, f2 = (C(x, N(x)), y), (x, D(y, N(y)))
    for f in (f1, f2):
        assert provset(*f) == {"q"}
    ans = ("$x\\sim x \\vdash y$ и $x \\vdash y : \\sim y$ — тавтологии без общих элементарных высказываний: обе доказуемы "
           "только в $S^6$. Ошибка 1 — против MT1 (с. 72): в заключение входит $y$, которого нет в посылке. Ошибка 2 — против "
           "MT6 (с. 73): в $S^6$ условий на элементарные высказывания нет.")
    sol = ("1. $x\\sim x \\vdash y$: посылка ложна при всех значениях — тавтология; $A = \\{x\\}$, $B = \\{y\\}$. По MT1 "
           "(с. 72) в $S^s$ недоказуема (в заключение входит $y$), по MT3 — и в $S^w$ (общих нет); по MT6 доказуема в $S^6$.\n"
           "2. $x \\vdash y : \\sim y$: заключение истинно всегда (ровно одно из $y$, $\\sim y$ истинно) — тавтология; "
           "$A \\cap B = \\varnothing$. В $S^s$, $S^w$ недоказуема (MT1, MT3), в $S^6$ доказуема (MT6, с. 73).\n"
           "Обе формулы — «парадоксы» вида B (с. 74), которые системы $S^s$, $S^w$, $S^m$, $S^c$ исключают (с. 73).")
    return card(level, "E", "vary", "text", src, "парадоксы следования, обычный язык, диагностика", cond, ans, sol, form="nat")


# ---------- § 4: интуиционистская логика ----------
SRC4 = "с. 72–75, гл. 5, § 2, 4"
INTU = ("В интуиционистском пропозициональном исчислении (с. 75) доказуемы $x \\supset (y \\supset x)$, "
        "$x \\supset (\\sim x \\supset y)$, $\\sim xx \\supset y$, $y \\supset x \\vee \\sim x$ и недоказуемы "
        "$\\sim\\sim x \\supset x$ и $\\sim x \\vee x$.")
INTU_S = [("\\sim xx \\vdash y", lambda X, Y: (C(N(X), X), Y)), ("y \\vdash x \\vee \\sim x", lambda X, Y: (Y, W(X, N(X)))),
          ("\\sim\\sim x \\vdash x", lambda X, Y: (N(N(X)), X)), ("\\sim xx \\vdash y", lambda X, Y: (C(N(X), X), Y))]


def c_intu_inst(level=7, src=SRC4):
    items = []
    order = rnd.sample(range(4), 4)
    for si in order:
        for _ in range(200):
            X = comp(["x", "y"])
            Y = comp(rnd.choice([["x"], ["y", "z"], ["z"], ["x", "y"]]))
            a, b = INTU_S[si][1](X, Y)
            if Y != X:
                break
        items.append((si, X, Y, a, b))
    ans, sol = [], []
    for i, (si, X, Y, a, b) in enumerate(items):
        ans.append(f"{L[i]}) {sys_list(provset(a, b))}")
        sol.append(f"{L[i]}) ${ftex(a, b)}$ (образец ${INTU_S[si][0]}$). " + explain(a, b))
    cond = (f"{CONV} {INTU} При интерпретации этого исчисления как системы следования знак $\\supset$ перед заключением "
            "заменяется знаком $\\vdash$. Для каждой формулы следования, полученной подстановкой в образец, найдите все системы "
            f"из $S^s$, $S^w$, $S^m$, $S^c$, $S^6$, где она доказуема, и обоснуйте значениями и множествами элементарных "
            f"высказываний. {CRIT}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (si, X, Y, a, b) in enumerate(items)))
    sol.append("Формулы по образцу $\\sim\\sim x \\vdash x$ доказуемы во всех системах ($A = B$), хотя $\\sim\\sim x \\supset x$ "
               "интуиционистски недоказуема; «парадоксальные» образцы $\\sim xx \\vdash y$, $y \\vdash x \\vee \\sim x$ дают "
               "формулы, доказуемые лишь там, где выполнено условие на элементарные высказывания (с. 73, 75).")
    return card(level, "S", "transfer", "short", src, "интуиционистская логика, критерии", cond, "; ".join(ans),
                "\n".join(sol))


def s5_excl_lines(X=None):
    X = X or comp(["x", "y"])
    bd = B()
    derive_excl(bd, X, swap=rnd.random() < 0.5)
    assert not check(bd.lines, "S5")
    return bd.lines


def c_s5_excl(level=7, src="с. 36, 67, 73, 75, гл. 2, § 1; гл. 4, § 3; гл. 5, § 2, 4"):
    lines = s5_excl_lines()
    b = lines[-1][1]
    cond = (f"{CONV} {S5CONV} {SCH1} Выведите в $S^5$ формулу ${ftex(None, b)}$ (она имеет вид $\\vdash \\sim x \\vee x$ или "
            "$\\vdash x \\vee \\sim x$, недоказуемый в интуиционистском исчислении, с. 75) и объясните, почему её доказуемость "
            "согласуется с MT5 § 2 гл. 5 (с. 73).")
    ans = f"Вывод в {len(lines)} строк от $A^d1$ (см. решение); формула — тавтология, а по MT5 $\\vdash x$ доказуема в $S^5$ тогда и только тогда, когда $x$ доказуема классически."
    sol = (show(lines) + "\n\nMT5 § 2 (с. 73): $\\vdash x$ доказуема в $S^5$ тогда и только тогда, когда $x$ доказуема в "
           "классическом исчислении. Дизъюнкция высказывания и его отрицания истинна при всех значениях, так что вывод "
           "согласуется с MT5. Интуиционистская недоказуемость $\\sim x \\vee x$ — ограничение, которое на уровне общей "
           "теории дедукции автор считает бессмысленным (с. 75).")
    return card(level, "D", "transfer", "proof", src, "интуиционистская логика, S5, вывод", cond, ans, sol, system="S^5")


def s5_random(want=10):
    """Случайный вывод в S⁵ от A^d1: шаги S₁ с R^d1, замены по R3, R^d3."""
    for _ in range(3000):
        bd = B()
        X = comp(["x", "y"]) if rnd.random() < 0.5 else V(rnd.choice("xy"))
        i0 = bd.add(None, N(C(N(X), X)), "Ad1")
        facts = [(bd.lines[-1][1], i0)]
        tries = 0
        while len(bd.lines) < want and tries < 40:
            tries += 1
            q, i = facts[-1] if rnd.random() < 0.75 else rnd.choice(facts)
            r = rnd.random()
            if r < 0.25:
                dn = [s for s in subs(q) if s[0] == "neg" and s[1][0] == "neg"]
                sw = [s for s in subs(q) if s[0] == "conj" and len(s[1]) == 2 and s[1][0] != s[1][1]]
                if dn and rnd.random() < 0.6:
                    s = rnd.choice(dn)
                    j1 = bd.add(s, s[1][1], "A1")
                    j2 = bd.add(s[1][1], s, "A2")
                    q2 = repl(q, s, s[1][1])
                    j3 = bd.add(q, q2, ("R3", j1, j2))
                elif sw:
                    s = rnd.choice(sw)
                    t = C(s[1][1], s[1][0])
                    j1 = bd.add(s, t, "A4")
                    j2 = bd.add(t, s, "A4")
                    q2 = repl(q, s, t)
                    j3 = bd.add(q, q2, ("R3", j1, j2))
                else:
                    continue
                if q2 in [f for f, _ in facts]:
                    del bd.lines[j1 - 1:]
                    continue
                k = bd.add(None, q2, ("Rd1", j3, i))
                facts.append((q2, k))
                continue
            if r < 0.33 and len(facts) >= 2:
                (q1, i1), (q2, i2) = rnd.sample(facts, 2)
                if size(C(q1, q2)) <= 30:
                    k = bd.add(None, C(q1, q2), ("Rd3", i1, i2))
                    facts.append((C(q1, q2), k))
                continue
            opts = [(n, rr) for n, rr in H.moves(q) if size(rr) <= 30 and rr not in [f for f, _ in facts]]
            if not opts:
                continue
            n, rr = rnd.choice(opts)
            j = bd.add(q, rr, n)
            k = bd.add(None, rr, ("Rd1", j, i))
            facts.append((rr, k))
        lines = prune(bd.lines)
        nrd = sum(1 for *_, w in lines if isinstance(w, tuple) and w[0] == "Rd1")
        names = {w for *_, w in lines if isinstance(w, str)}
        if (8 <= len(lines) <= 12 and nrd >= 3 and not check(lines, "S5") and size(lines[-1][1]) >= 12
                and len(names - {"Ad1"}) >= 3):
            key_ = lines[-1][1]
            if key_ in SEEN:
                continue
            SEEN.add(key_)
            return lines
    raise RuntimeError("s5")


def subs(f):
    out = [f]
    if f[0] == "neg":
        out += subs(f[1])
    elif f[0] in ("conj", "wdis", "dis"):
        for a in f[1]:
            out += subs(a)
    return out


def repl(f, s, t):
    if f == s:
        return t
    if f[0] in ("v", "nn", "qq"):
        return f
    if f[0] == "neg":
        return N(repl(f[1], s, t))
    return (f[0], tuple(repl(a, s, t) for a in f[1]))


def prune(lines):
    need, stack = set(), [len(lines)]
    while stack:
        n = stack.pop()
        if n in need:
            continue
        need.add(n)
        wh = lines[n - 1][2]
        if isinstance(wh, tuple):
            stack += [wh[1], wh[2]]
    keep = sorted(need)
    new = {old: i for i, old in enumerate(keep, 1)}
    return [(a, b, wh if isinstance(wh, str) else (wh[0], new[wh[1]], new[wh[2]])) for a, b, wh in
            (lines[o - 1] for o in keep)]


SCH_FULL = ("Схемы $S_1$ (с. 36): A1 $\\sim\\sim x \\vdash x$; A2 $x \\vdash \\sim\\sim x$; A3 $xy \\vdash x$; A4 "
            "$xy \\vdash yx$; A5, A6 — расстановка скобок в конъюнкции; A7 $(x \\vee y)z \\vdash xz \\vee y$; A8 "
            "$xz \\vee yz \\vdash (x \\vee y)z$; A9 $\\sim(x^1 \\ldots x^n) \\vdash \\sim x^1 \\vee \\ldots \\vee \\sim x^n$; A10 — "
            "обратная к A9; A11 $xy \\vee z \\vdash (xy \\vee z)(y \\vee \\sim y)$; R1–R3 — с. 17.")
SRC5D = "с. 17, 36, 67, 70, 73, гл. 1, § 1; гл. 2, § 1; гл. 4, § 3; гл. 5, § 2"


def c_s5_deriv(level=7, src=SRC5D, tags="S5, вывод"):
    lines = s5_random(rnd.choice([10, 11, 12]))
    b = lines[-1][1]
    cond = (f"{CONV} {S5CONV} {SCH_FULL} Выведите в $S^5$ формулу ${ftex(None, b)}$ и проверьте значениями, что это согласуется "
            "с MT5 § 2 гл. 5 (с. 73): $\\vdash x$ доказуема в $S^5$ тогда и только тогда, когда $x$ доказуема в классическом "
            "исчислении.")
    ans = f"Вывод в {len(lines)} строк от $A^d1$ (см. решение); ${tex(b)}$ истинно при всех значениях."
    sol = (show(lines) + f"\n\nПроверка: ${tex(b)}$ принимает значение 1 при всех {2 ** len(atoms(b))} наборах значений — "
           "тавтология, т. е. формула, доказуемая классически (с. 72); по MT5 (с. 73) так и должно быть.")
    assert K.taut2(None, b)
    return card(level, "D", "open", "proof", src, tags, cond, ans, sol, system="S^5")


def c_s5_complete(level=5, src=SRC5D, tags="S5, вывод, дополнение"):
    lines = s5_random(rnd.choice([10, 11, 12]))
    hw, hf = hide_lines(lines)
    b = lines[-1][1]
    cond = (f"{CONV} {S5CONV} {SCH_FULL} В выводе в $S^5$ формулы ${ftex(None, b)}$ пропущены формулы некоторых строк и "
            f"основания некоторых шагов («…»). Восстановите их.\n\n{show_hidden(lines, hw, hf)}")
    sol = ("$R^d1$ берёт строку $x \\vdash y$ и строку $\\vdash x$ и даёт $\\vdash y$ (с. 67); $R^d3$ соединяет $\\vdash x$ и "
           "$\\vdash y$ в $\\vdash xy$ (с. 70); R3 заменяет вхождения по паре $x \\vdash y$, $y \\vdash x$ (с. 17).\n\n" + show(lines))
    return card(level, "D", "complete", "build", src, tags, cond, complete_answer(lines, hw, hf), sol, system="S^5")


def c_s5_diag(level=6, src=SRC5D, tags="S5, вывод, диагностика"):
    for _ in range(80):
        lines = s5_random(rnd.choice([10, 11, 12]))
        c = c_diag2(lines, "S5", f"{CONV} {S5CONV} {SCH_FULL}", src, tags, level, "S^5", prefer=("Rd1",))
        if c:
            return c
    raise RuntimeError


def c_intu_student(level=5, src=SRC4):
    X = comp(["x", "y"])
    Y = comp(["z"] if rnd.random() < 0.5 else ["y", "z"])
    a1, b1 = N(N(X)), X
    a2, b2 = C(N(X), X), Y
    cond = (f"{CONV} {INTU} Студент рассуждает: «Раз $\\sim\\sim x \\supset x$ интуиционистски недоказуема, формула "
            f"${ftex(a1, b1)}$ недоказуема в $S^s$; а ${ftex(a2, b2)}$ доказуема в $S^s$, потому что доказуема "
            f"$\\sim xx \\supset y$». Найдите все ошибки и дайте верные ответы с обоснованием по MT1 § 2 (с. 72).")
    ans = (f"1) ${ftex(a1, b1)}$ доказуема в $S^s$: это пример A1 $S_1$ (с. 36), сильная тавтология (MT1); "
           f"2) ${ftex(a2, b2)}$ недоказуема: в заключение входит " + ", ".join(f"${n}$" for n in sorted(atoms(b2) - atoms(a2))) +
           ", которого нет в посылке (MT1, с. 72).")
    sol = ("Интуиционистское исчисление — не система общей теории дедукции; его интерпретация как системы следования даёт "
           "неполную систему с парадоксальными следствиями (с. 75). Доказуемость в $S^s$ решает MT1 § 2.\n"
           f"1. ${ftex(a1, b1)}$: тавтология, $A = B = {lst(atoms(X))}$ — доказуема в $S^s$ (MT1); это и пример схемы A1 "
           "$S_1$ (с. 36).\n"
           f"2. ${ftex(a2, b2)}$: посылка ложна при всех значениях — тавтология, но $B = {lst(atoms(Y))}$, $A = {lst(atoms(X))}$: условие $B \\subseteq A$ нарушено — по MT1 недоказуема: такие «парадоксы» системы $S^s$ исключают (с. 73).")
    return card(level, "E", "vary", "text", src, "интуиционистская логика, диагностика", cond, ans, sol, system="S^s")


def c_intu_nat(level=6, src=SRC4):
    ph = phrases()
    xx, yy = ph["x"], ph["y"]
    f1 = (N(N(x)), x)
    f2 = (C(x, N(x)), y)
    f3 = (y, W(x, N(x)))
    cond = (f"Обозначения: $x$ — «{xx[0]}», $y$ — «{yy[0]}». Рассуждения: 1) «Неверно, что {xx[1]}; следовательно, {xx[0]}»; "
            f"2) «{cap(xx[0])} и {xx[1]}; следовательно, {yy[0]}»; 3) «{cap(yy[0])}; следовательно, {xx[0]} или {xx[1]} (по "
            f"крайней мере одно)». {INTU} Запишите рассуждения формулами следования, укажите, какой формуле интуиционистского "
            f"списка каждое соответствует, и исследуйте их доказуемость в $S^s$, $S^w$, $S^m$, $S^c$, $S^6$. {CRIT}")
    ans = ("1) $\\sim\\sim x \\vdash x$ — во всех пяти системах (интуиционистски $\\sim\\sim x \\supset x$ недоказуема); "
           "2) $x\\sim x \\vdash y$ и 3) $y \\vdash x \\vee \\sim x$ — только в $S^6$ (интуиционистски доказуемы).")
    for f in (f1,):
        assert provset(*f) == set(KS)
    for f in (f2, f3):
        assert provset(*f) == {"q"}
    sol = ("1. $\\sim\\sim x \\vdash x$: тавтология, $A = B = \\{x\\}$ — доказуема во всех пяти системах (MT1–MT4, MT6, "
           "с. 72–73).\n2. $x\\sim x \\vdash y$: посылка ложна всегда — тавтология; $A \\cap B = \\varnothing$ — доказуема только "
           "в $S^6$.\n3. $y \\vdash x \\vee \\sim x$: заключение истинно всегда — тавтология; $A \\cap B = \\varnothing$ — только "
           "в $S^6$.\nИнтерпретация интуиционистского исчисления как системы следования дала бы обратную картину: 1 "
           "отвергалось бы, 2 и 3 принимались бы — «неполная система, да к тому же с парадоксальными следствиями» (с. 75).")
    return card(level, "F", "transfer", "short", src, "интуиционистская логика, обычный язык", cond, ans, sol, form="nat")


def c_intu_six(level=7, src="с. 20, 72–75, гл. 1, § 3; гл. 5, § 2, 4"):
    from s1 import IMP
    rows = [(x, IMP(y, x), "x \\vdash y \\supset x"), (x, IMP(N(x), y), "x \\vdash \\sim x \\supset y"),
            (C(N(x), x), y, "\\sim xx \\vdash y"), (y, W(x, N(x)), "y \\vdash x \\vee \\sim x"),
            (N(N(x)), x, "\\sim\\sim x \\vdash x")]
    got = [provset(a, b) for a, b, _ in rows]
    assert got == [{"c", "w", "q"}, {"c", "w", "q"}, {"q"}, {"q"}, set(KS)], got
    assert K.taut2(None, W(N(x), x))
    cond = (f"{INTU} Для каждой из шести формул запишите соответствующую формулу систем общей теории дедукции, заменив "
            "главный знак $\\supset$ знаком $\\vdash$ (внутренний $\\supset$ остаётся сокращением по D1 § 3 гл. 1, с. 20: "
            "$x \\supset y$ есть $xy : \\sim xy : \\sim x\\sim y$; для формулы без $\\supset$ — формулу $\\vdash x$), и "
            "найдите все системы из $S^s$, $S^w$, $S^m$, $S^c$, $S^6$, где она доказуема (для $\\vdash x$ — исследуйте "
            f"доказуемость в $S^5$ по MT5 § 2). {CRIT}")
    ans = ("$x \\vdash y \\supset x$ и $x \\vdash \\sim x \\supset y$ — $S^w$, $S^c$, $S^6$; $\\sim xx \\vdash y$ и "
           "$y \\vdash x \\vee \\sim x$ — только $S^6$; $\\sim\\sim x \\vdash x$ — все пять; $\\vdash \\sim x \\vee x$ — "
           "доказуема в $S^5$.")
    sol = ("1. $x \\vdash y \\supset x$: при $x = 1$ импликация $y \\supset x$ истинна — тавтология; $A = \\{x\\}$, "
           "$B = \\{x, y\\}$: $A \\subset B$, $A \\neq B$ — по MT4, MT3, MT6 доказуема в $S^c$, $S^w$, $S^6$, по "
           "MT1, MT2 недоказуема в $S^s$, $S^m$.\n"
           "2. $x \\vdash \\sim x \\supset y$: при $x = 1$ посылка импликации $\\sim x$ ложна, импликация истинна — "
           "тавтология; множества те же — $S^c$, $S^w$, $S^6$.\n"
           "3. $\\sim xx \\vdash y$: посылка ложна всегда — тавтология; $A \\cap B = \\varnothing$ — только $S^6$ (MT6).\n"
           "4. $y \\vdash x \\vee \\sim x$: заключение истинно всегда — тавтология; $A \\cap B = \\varnothing$ — только $S^6$.\n"
           "5. $\\sim\\sim x \\vdash x$: тавтология с $A = B$ — доказуема во всех пяти.\n"
           "6. $\\vdash \\sim x \\vee x$: $\\sim x \\vee x$ истинно при обоих значениях $x$, по MT5 (с. 73) доказуема в $S^5$.\n"
           "Итог: из того, что интуиционист принимает, в $S^s$ не проходит ничего, а то, что он отвергает (5, 6), "
           "доказуемо — «неполная система, да к тому же с парадоксальными следствиями» (с. 75).")
    return card(level, "S", "transfer", "short", src, "интуиционистская логика, классическая логика", cond, ans, sol,
                form="meta")


# ---------- § 5: неклассический случай ----------
SRC5 = "с. 17, 36, 72, 75–77, гл. 1, § 1; гл. 2, § 1; гл. 5, § 2, 5"
NCONV = ("Буквы $x, y$ — высказывания с главным оператором $\\leftarrow$, $\\forall$, $\\exists$ или $\\rightarrow$ (например, "
         "$a \\leftarrow b$), не содержащие $\\urcorner$ и $?$; $\\urcorner x$ и $?x$ образованы из $x$ помещением этих "
         "операторов перед главным оператором (дополнение к определению высказывания, гл. 5, § 5, с. 76), так что "
         "элементарные высказывания в них те же, что в $x$.")
ANLIST = ("Схемы § 5 (с. 76): $A^n1$ $\\sim x \\vdash \\urcorner x \\vee ?x$; $A^n2$ $\\urcorner x \\vee ?x \\vdash \\sim x$; "
          "$A^n3$ $\\sim\\urcorner x \\vdash x \\vee ?x$; $A^n4$ $x \\vee ?x \\vdash \\sim\\urcorner x$; $A^n5$ $\\sim ?x \\vdash "
          "x \\vee \\urcorner x$; $A^n6$ $x \\vee \\urcorner x \\vdash \\sim ?x$.")
SEM3 = ("Главная семантическая интерпретация (с. 76): $x$ и $\\urcorner x$ не бывают истинны вместе, могут быть оба ложны, "
        "$?x$ равнозначно $\\sim x\\sim\\urcorner x$; значит, у каждой буквы три состояния — истинно $x$, истинно "
        "$\\urcorner x$, истинно $?x$. В классическом случае, где принята $A^n7$ $\\sim x \\vdash \\urcorner x$ (с. 77), "
        "состояния «истинно $?x$» нет.")
SNCONV = (f"{NCONV} $S^s_n$ — система $S^s$ (в форме $S_1$) с дополнительными схемами $A^n1$–$A^n6$ (с. 75–76). {ANLIST} "
          "Основание [$S^s$] — строка получается подстановкой высказываний (в том числе $\\urcorner x$, $?x$) в теорему "
          "$S^s$, то есть в тавтологию, в заключение которой не входят элементарные высказывания, отсутствующие в посылке "
          "(MT1 § 2, с. 72; правило подстановки MT1 § 9 гл. 1, с. 35).")
LET3 = {"p": lambda n: V(n), "n": NN, "q": QQ}


def sn_to_conj(bd, S, n):
    p, q, r = V(n), NN(n), QQ(n)
    base, (a0, a1), (A, Bq) = {"p": (p, ("An1", "An2"), (q, r)), "n": (q, ("An3", "An4"), (p, r)),
                               "q": (r, ("An5", "An6"), (p, q))}[S]
    i1 = bd.add(N(base), W(A, Bq), a0)
    i2 = bd.add(W(A, Bq), N(base), a1)
    i3 = bd.add(base, N(N(base)), "A2")
    i4 = bd.add(N(N(base)), N(W(A, Bq)), ("R3", i1, i2))
    i5 = bd.add(base, N(W(A, Bq)), ("R1", i3, i4))
    i6 = bd.add(N(W(A, Bq)), C(N(A), N(Bq)), "Ts")
    return bd.add(base, C(N(A), N(Bq)), ("R1", i5, i6)), base, A, Bq


def sn_from_conj(bd, S, n):
    p, q, r = V(n), NN(n), QQ(n)
    base, A, Bq = {"p": (p, q, r), "n": (q, p, r), "q": (r, p, q)}[S]
    axA = {"v": "An1", "nn": "An3", "qq": "An5"}[A[0]]
    Dd = K.an_inst(axA, n)[1]
    P = C(N(A), N(Bq))
    j1 = bd.add(P, N(A), "A3")
    j2 = bd.add(N(A), Dd, axA)
    j3 = bd.add(P, Dd, ("R1", j1, j2))
    j4 = bd.add(P, C(N(Bq), N(A)), "A4")
    j5 = bd.add(C(N(Bq), N(A)), N(Bq), "A3")
    j6 = bd.add(P, N(Bq), ("R1", j4, j5))
    j7 = bd.add(P, C(Dd, N(Bq)), ("R2", j3, j6))
    j8 = bd.add(C(Dd, N(Bq)), base, "Ts")
    return bd.add(P, base, ("R1", j7, j8))


def sn_lines(kind=None, n="x", prefix=None):
    bd = B()
    kind = kind or rnd.choice(["to", "first", "second", "swap", "from"])
    S = rnd.choice("pnq")
    if kind == "from":
        sn_from_conj(bd, S, n)
    else:
        k, base, A, Bq = sn_to_conj(bd, S, n)
        Cn = C(N(A), N(Bq))
        if kind == "first":
            m = bd.add(Cn, N(A), "A3")
            bd.add(base, N(A), ("R1", k, m))
        elif kind == "second":
            m1 = bd.add(Cn, C(N(Bq), N(A)), "A4")
            m2 = bd.add(C(N(Bq), N(A)), N(Bq), "A3")
            k2 = bd.add(base, C(N(Bq), N(A)), ("R1", k, m1))
            bd.add(base, N(Bq), ("R1", k2, m2))
        elif kind == "swap":
            m1 = bd.add(Cn, C(N(Bq), N(A)), "A4")
            bd.add(base, C(N(Bq), N(A)), ("R1", k, m1))
    if prefix:
        a0 = bd.lines[-1][0]
        other = prefix
        last = len(bd.lines)
        if rnd.random() < 0.5:
            P = C(a0, other)
            j = bd.add(P, a0, "A3")
        else:
            P = C(other, a0)
            j1 = bd.add(P, C(a0, other), "A4")
            j2 = bd.add(C(a0, other), a0, "A3")
            j = bd.add(P, a0, ("R1", j1, j2))
        bd.add(P, bd.lines[last - 1][1], ("R1", j, last))
    assert not check(bd.lines, "Sn"), (check(bd.lines, "Sn"), show(bd.lines))
    return bd.lines


def rnd_other(n="y"):
    return rnd.choice([V(n), NN(n), QQ(n), N(V(n)), N(NN(n))])


def tname(lines):
    a, b = lines[-1][0], lines[-1][1]
    for nm, (p, q) in TSCH.items():
        if (p, q) == (a, b):
            return nm
    return None


xv, xn, xq = V("x"), NN("x"), QQ("x")
TSCH = {"T2": (xv, N(xn)), "T3": (xv, N(xq)), "T5": (xn, N(xv)), "T6": (xn, N(xq)), "T8": (xq, N(xv)), "T9": (xq, N(xn))}


def c_sn_deriv(level=7, src=SRC5, kind=None, prefix=None):
    n = rnd.choice("xy")
    pre = rnd_other("y" if n == "x" else "x") if prefix else None
    lines = sn_lines(kind, n, pre)
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{SNCONV} {SCH1} Выведите в $S^s_n$ формулу ${ftex(a, b)}$.")
    ans = f"Вывод в {len(lines)} строк (см. решение)."
    sol = (show(lines) + "\n\nКлюч: пары $A^n1$/$A^n2$, $A^n3$/$A^n4$, $A^n5$/$A^n6$ дают равнозначность, по которой R3 "
           "заменяет отрицание буквы дизъюнкцией двух других её состояний (с. 17, 76). Проверка по главной интерпретации "
           "(с. 76): формула истинна во всех трёх состояниях — как и должно быть по MT1 § 5.")
    assert K.taut3(a, b)
    return card(level, "D", "open", "proof", src, "неклассический случай, вывод", cond, ans, sol, system="S^s_n",
                case="nonclassical")


def c_sn_complete(level=5, src=SRC5):
    lines = sn_lines(rnd.choice(["first", "second", "from"]), rnd.choice("xy"))
    hw, hf = hide_lines(lines)
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{SNCONV} {SCH1} В выводе в $S^s_n$ формулы ${ftex(a, b)}$ пропущены формулы некоторых строк и основания "
            f"некоторых шагов («…»). Восстановите их.\n\n{show_hidden(lines, hw, hf)}")
    sol = ("Формула строки, на которую ссылается R1, R2 или R3, восстанавливается по виду правила (с. 17); основание "
           "аксиомы — по виду формулы: схемы $A^n$ — с. 76, схемы $S_1$ — с. 36.\n\n" + show(lines))
    return card(level, "D", "complete", "build", src, "неклассический случай, вывод, дополнение", cond,
                complete_answer(lines, hw, hf), sol, system="S^s_n", case="nonclassical")


def c_sn_diag(level=6, src=SRC5):
    for _ in range(80):
        lines = sn_lines(rnd.choice(["first", "second", "from", "swap"]), rnd.choice("xy"),
                         rnd_other() if rnd.random() < 0.3 else None)
        lines = lines if lines[-1][0] is not None else lines
        c = c_diag2(lines, "Sn", f"{SNCONV} {SCH1}", src, "неклассический случай, вывод, диагностика", level, "S^s_n",
                    prefer=("An1", "An2", "An3", "An4", "An5", "An6"))
        if c:
            c["case"] = "nonclassical"
            return c
    raise RuntimeError


def sn7_lines(n="x"):
    bd = B()
    k, base, A, Bq = sn_to_conj(bd, "n", n)          # ⌝x ⊢ ∼x∼?x
    m = bd.add(C(N(A), N(Bq)), N(A), "A3")
    t5 = bd.add(base, N(A), ("R1", k, m))            # ⌝x ⊢ ∼x  (T5)
    a7 = bd.add(N(V(n)), NN(n), "An7")
    r = bd.add(N(NN(n)), N(N(V(n))), ("R3", t5, a7))
    a1 = bd.add(N(N(V(n))), V(n), "A1")
    bd.add(N(NN(n)), V(n), ("R1", r, a1))
    assert not check(bd.lines, "Sn7"), check(bd.lines, "Sn7")
    return bd.lines


def c_sn7_deriv(level=7, src=SRC5):
    n = rnd.choice("xy")
    lines = sn7_lines(n)
    a, b = lines[-1][0], lines[-1][1]
    cond = (f"{SNCONV} {SCH1} Классический случай получается присоединением схемы $A^n7$ $\\sim x \\vdash \\urcorner x$ "
            f"(с. 77). Выведите в $S^s_n$ с $A^n7$ формулу ${ftex(a, b)}$ и объясните, почему без $A^n7$ она недоказуема.")
    st = K.counter3(a, b)
    ans = (f"Вывод в {len(lines)} строк: сначала $\\urcorner {n} \\vdash \\sim {n}$ (T5), затем R3 по ней и $A^n7$, A1, R1; "
           f"без $A^n7$ — по MT3 § 5 (с. 76): при {K.st_text(st)} посылка 1, заключение 0.")
    sol = (show(lines) + f"\n\nБез $A^n7$: по главной интерпретации (с. 76) при {K.st_text(st)} посылка ${tex(a)}$ истинна, "
           f"а ${tex(b)}$ ложно — формула не тавтология и по MT1 § 5 недоказуема (это MT3, с. 76: недоказуемость закона "
           "снятия двойного отрицания, с. 76–77). С $A^n7$ доказуемы $\\sim x \\dashv\\vdash \\urcorner x$, "
           "$\\sim\\urcorner x \\vdash x$ и другие формулы, делающие излишними оператор неопределённости и различение двух "
           "отрицаний (с. 77).")
    assert not K.taut3(a, b) and K.taut3(a, b, classical=True)
    return card(level, "D", "transfer", "proof", src, "классический случай, вывод", cond, ans, sol, system="S^s_n",
                case="classical")


def c_sn7_misuse(level=7, src=SRC5):
    for _ in range(200):
        n = rnd.choice("xy")
        lines = sn7_lines(n)
        cand = [i for i, (_, _, w) in enumerate(lines) if isinstance(w, str) and w in WRONG5 and w != "An7"]
        i = rnd.choice(cand)
        bad = list(lines)
        a, b, w = bad[i]
        bad[i] = (a, b, WRONG5[w])
        errs = check(bad, "Sn")
        steps = sorted({int(re.match(r"шаг (\d+)", e).group(1)) for e in errs})
        j = next(k for k, (_, _, w) in enumerate(lines) if w == "An7")
        if steps == sorted([i + 1, j + 1]):
            break
    fa, fb = lines[-1][0], lines[-1][1]
    st = K.counter3(fa, fb)
    cond = (f"{SNCONV} {SCH1} Студент выводит в $S^s_n$ (неклассический случай) формулу ${ftex(fa, fb)}$:\n\n{show(bad)}\n\n"
            "В выводе ровно два нарушения. Найдите их, назовите нарушенное правило со страницей и объясните, можно ли "
            "исправить вывод.")
    p, q = sorted([i, j])
    ans = (f"Шаг {i + 1}: [{why_tex(lines[i][2])}], а не [{why_tex(WRONG5[lines[i][2]])}]; шаг {j + 1}: $A^n7$ принимается "
           f"только в классическом случае (с. 77). Исправить нельзя: по MT3 § 5 (с. 76) формула недоказуема в $S^s_n$ "
           f"(при {K.st_text(st)} она ложна).")
    sol = (f"Шаг {i + 1}: " + why_wrong(lines[i][2], lines[i], WRONG5[lines[i][2]]) + ".\n"
           f"Шаг {j + 1}: $\\sim {n} \\vdash \\urcorner {n}$ — схема $A^n7$; её присоединяют, чтобы получить классический "
           "случай (с. 77), в неклассической $S^s_n$ её нет. По главной интерпретации она не тавтология: при истинном "
           f"$?{n}$ посылка истинна, а $\\urcorner {n}$ ложно.\n"
           f"Сама формула ${ftex(fa, fb)}$ при {K.st_text(st)} имеет истинную посылку и ложное заключение, по MT1 § 5 "
           "(с. 76) она недоказуема в $S^s_n$ — это MT3 § 5. В классическом случае (с $A^n7$) вывод верен после исправления "
           f"шага {i + 1}.")
    return card(level, "E", "vary", "text", src, "неклассический случай, диагностика", cond, ans, sol, system="S^s_n",
                case="nonclassical")


def rnd_n(names, depth):
    if depth == 0 or rnd.random() < 0.25:
        n = rnd.choice(names)
        leaf = rnd.choice([V(n), NN(n), QQ(n)])
        return N(leaf) if rnd.random() < 0.35 else leaf
    k = rnd.random()
    if k < 0.15:
        return N(rnd_n(names, depth - 1))
    a, b = rnd_n(names, depth - 1), rnd_n(names, depth - 1)
    if a == b:
        return a
    return C(a, b) if k < 0.55 else W(a, b)


def has_n(f):
    return "nn" in repr(f) or "qq" in repr(f)


def sample_n(cat, names=("x",), lo=10, hi=30, depth=2):
    for _ in range(30000):
        a, b = rnd_n(list(names), depth), rnd_n(list(names), depth)
        if a == b or not (lo <= size(a) + size(b) <= hi) or not has_n((a, b)) or (a, b) in SEEN:
            continue
        t3, t2 = K.taut3(a, b), K.taut3(a, b, classical=True)
        c = "both" if t3 else ("cl" if t2 else "none")
        if c == cat:
            SEEN.add((a, b))
            return a, b
    raise RuntimeError(cat)


def n_verdict(a, b):
    t3, t2 = K.taut3(a, b), K.taut3(a, b, classical=True)
    return f"{'тавтология' if t3 else 'не тавтология'} / {'тавтология' if t2 else 'не тавтология'}"


def n_explain(a, b):
    out = []
    if K.taut3(a, b):
        out.append(f"во всех {3 ** len(atoms(a) | atoms(b))} состояниях, где посылка истинна, истинно и заключение — тавтология "
                   "(значит, и в классическом случае)")
    else:
        st = K.counter3(a, b)
        out.append(f"при {K.st_text(st)} посылка 1, заключение 0 — не тавтология, по MT1 § 5 (с. 76) недоказуема ни в "
                   "одной $S^i_n$")
        if K.taut3(a, b, classical=True):
            out.append("в классическом случае состояния с истинным $?$ нет, и в оставшихся формула тавтологична")
        else:
            st2 = K.counter3(a, b, classical=True)
            out.append(f"и в классическом случае: при {K.st_text(st2)} посылка 1, заключение 0")
    return "; ".join(out)


def c_sn_series(level=6, src="с. 76–77, гл. 5, § 5", names=("x",)):
    cats = rnd.sample(["both", "cl", "none", rnd.choice(["both", "cl"])], 4)
    items = [sample_n(c, names, lo=12 if len(names) == 1 else 16, hi=30 if len(names) == 1 else 36,
                      depth=2 if len(names) == 1 else 3) for c in cats]
    cond = (f"{NCONV} {SEM3} Проверьте тавтологичность каждой формулы в неклассическом и в классическом случае; для "
            "нетавтологии укажите состояние букв, при котором посылка истинна, а заключение ложно, и сделайте вывод о "
            "доказуемости в системах $S^i_n$ по MT1 § 5 (с. 76): все доказуемые в $S^i_n$ формулы — тавтологии.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {n_verdict(a, b)}" for i, (a, b) in enumerate(items)) + " (неклассический / классический)"
    sol = "\n".join(f"{L[i]}) {n_explain(a, b)}." for i, (a, b) in enumerate(items))
    return card(level, "C", "iso", "short", src, "неклассический случай, тавтологии", cond, ans, sol, system="S^i_n")


def c_an_rec(level=5, src="с. 76–77, гл. 5, § 5"):
    n = rnd.choice("xy")
    p, q, r = V(n), NN(n), QQ(n)
    m = "y" if n == "x" else "x"
    good = rnd.sample(["An1", "An2", "An3", "An4", "An5", "An6"], 2)
    pool = [K.an_inst(g, n) for g in good]
    nears = [(N(q), W(r, p), "в $A^n3$ члены дизъюнкции идут в порядке $x \\vee ?x$, а схема задаёт запись точно"),
             (N(p), W(q, QQ(m)), "в схеме все три вхождения — одно и то же $x$, а здесь разные буквы"),
             (W(p, r), N(r), "посылка как в $A^n4$, но заключение должно быть $\\sim\\urcorner x$, а не $\\sim ?x$"),
             (N(r), W(p, N(p)), "в $A^n5$ заключение $x \\vee \\urcorner x$: внутреннее отрицание $\\urcorner$, а не $\\sim$"),
             (W(q, r), N(q), "посылка как в $A^n2$, но заключение $A^n2$ — $\\sim x$")]
    near = rnd.sample(nears, 2)
    a7 = K.an_inst("An7", n)
    items = [(a, b, None) for a, b in pool] + [(a, b, w) for a, b, w in near] + [(a7[0], a7[1], "a7")]
    rnd.shuffle(items)
    ans, sol = [], []
    for i, (a, b, w) in enumerate(items):
        nm = K.an_axiom(a, b)
        if w is None:
            ans.append(f"{L[i]}) $A^n{nm[2:]}$")
            sol.append(f"{L[i]}) Пример $A^n{nm[2:]}$ (${K.AN_TEXT[nm]}$) при $x := {n}$.")
        elif w == "a7":
            ans.append(f"{L[i]}) $A^n7$ — только классический случай")
            sol.append(f"{L[i]}) Это $A^n7$ $\\sim x \\vdash \\urcorner x$ (с. 77): её принимают, чтобы получить классический "
                       f"случай; в неклассическом она не тавтология (при истинном $?{n}$ посылка 1, заключение 0).")
        else:
            assert nm is None
            ans.append(f"{L[i]}) ни одной")
            sol.append(f"{L[i]}) Не пример ни одной схемы: {w}.")
    cond = (f"{NCONV} {ANLIST} Классический случай получается присоединением $A^n7$ $\\sim x \\vdash \\urcorner x$ (с. 77). "
            "Для каждой формулы найдите схему из $A^n1$–$A^n7$, примером которой она является (подстановкой буквы вместо "
            "$x$); если такой нет — назовите место, которое мешает.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b, _) in enumerate(items)))
    return card(level, "A", "iso", "short", src, "неклассический случай, схемы, почти-примеры", cond, "; ".join(ans),
                "\n".join(sol), system="S^s_n")


def c_sn_student(level=5, src="с. 75–76, гл. 5, § 5"):
    n, m = rnd.sample("xyz", 2)
    comp_ = rnd.choice([(f"{n}{m}", "конъюнкции «$\\cdot$»"), (f"{n} \\vee {m}", "дизъюнкции «$\\vee$»"),
                        (f"\\sim {n}", "отрицания «$\\sim$»"), (f"{n} : {m}", "сильной дизъюнкции «$:$»")])
    X, op = comp_
    T = rnd.choice([("T2", f"{n} \\vdash \\sim\\urcorner {n}", f"\\sim\\urcorner {n} \\vdash {n}"),
                    ("T8", f"?{n} \\vdash \\sim {n}", f"\\sim {n} \\vdash ?{n}"),
                    ("T5", f"\\urcorner {n} \\vdash \\sim {n}", f"\\sim {n} \\vdash \\urcorner {n}")])
    conv = {"T2": (N(NN(n)), V(n)), "T8": (N(V(n)), QQ(n)), "T5": (N(V(n)), NN(n))}[T[0]]
    st = K.counter3(*conv)
    cond = (f"{NCONV} {ANLIST} Студент пишет: «1) Подставив $x := {X}$ в $A^n1$, получаем теорему $\\sim({X}) \\vdash "
            f"\\urcorner({X}) \\vee ?({X})$. 2) Раз ${T[1]}$ — теорема $S^s_n$ ({T[0]}, с. 77), то и обратная формула "
            f"${T[2]}$ доказуема в $S^s_n$». Найдите все ошибки, назовите нарушенные положения книги со страницами.")
    ans = (f"1) $\\urcorner$ и $?$ ставятся только перед высказыванием с главным оператором $\\leftarrow$, $\\forall$, $\\exists$, "
           f"$\\rightarrow$ (дополнение к определению высказывания, с. 76); перед оператором {op} они стоять не могут "
           f"(с. 75) — выражение не высказывание. 2) Обращение теоремы — не правило; ${T[2]}$ не тавтология (при "
           f"{K.st_text(st)} посылка 1, заключение 0), по MT1 § 5 (с. 76) недоказуема.")
    sol = (f"1. Дополнение к определению высказывания (с. 76): если $x$ — высказывание с главным оператором $\\forall$, "
           f"$\\exists$, $\\leftarrow$ или $\\rightarrow$, не содержащее $\\urcorner$ и $?$, то $\\urcorner x$ и $?x$ — "
           f"высказывания. У ${X}$ главный оператор — оператор {op}; перед операторами общей теории дедукции "
           f"($\\cdot$, $:$, $\\vee$, $\\sim$) операторы $\\urcorner$ и $?$ стоять не могут (с. 75). Значит, в $A^n1$ на место "
           f"$x$ такое высказывание подставлять нельзя.\n"
           f"2. Правила вывода (с. 17) не позволяют обращать формулы. Проверка по главной интерпретации (с. 76): при "
           f"{K.st_text(st)} посылка ${T[2].split(' \\vdash ')[0]}$ истинна, а заключение ложно — формула не тавтология, "
           f"по MT1 § 5 (все теоремы $S^i_n$ — тавтологии) недоказуема.")
    return card(level, "E", "vary", "text", src, "неклассический случай, диагностика", cond, ans, sol, system="S^s_n",
                case="nonclassical")


SUBJ = [("эта руда", "примесь золота"), ("пациент", "аллергию на пенициллин"), ("слиток", "примесь меди"),
        ("картина", "подпись автора"), ("договор", "юридическую силу"), ("образец", "радиоактивность")]


def nl_n(f, sp, inner=False):
    a, b = sp
    k = f[0]
    if k == "v":
        return f"{a} имеет {b}"
    if k == "nn":
        return f"{a} не имеет {b}"
    if k == "qq":
        return f"{a} неопределённо имеет {b}"
    if k == "neg":
        return f"неверно, что {nl_n(f[1], sp, True)}" if f[1][0] in LEAF5 else f"неверно, что ({nl_n(f[1], sp, True)})"
    parts = [nl_n(t, sp, True) if t[0] in LEAF5 + ("neg",) else f"({nl_n(t, sp, True)})" for t in f[1]]
    return " и ".join(parts) if k == "conj" else " или ".join(parts) + " (по крайней мере одно)"


LEAF5 = ("v", "nn", "qq")


def c_sn_nat(level=6, src="с. 75–77, гл. 5, § 5"):
    sp = rnd.choice(SUBJ)
    pool = [(N(xv), xn), (xn, N(xv)), (N(xn), xv), (C(N(xv), N(xn)), xq), (N(xq), W(xv, xn)), (N(xv), W(xn, xq)),
            (W(xn, xq), N(xv)), (xq, N(xn)), (C(N(xv), N(xq)), xn), (N(xq), xv)]
    items = rnd.sample(pool, 3)
    while all(K.taut3(*it) == K.taut3(*it, classical=True) for it in items):
        items = rnd.sample(pool, 3)
    cond = (f"Пусть $x$ — высказывание «{sp[0]} имеет {sp[1]}» (вида $a \\leftarrow b$); тогда $\\urcorner x$ — «{sp[0]} не "
            f"имеет {sp[1]}», $?x$ — «{sp[0]} неопределённо имеет {sp[1]}» (с. 76), «неверно, что» — $\\sim$. {SEM3} Запишите "
            "каждое рассуждение формулой следования и исследуйте, тавтологично ли оно в неклассическом и в классическом "
            "случае; для нетавтологии укажите состояние.\n\n" +
            "\n".join(f"{i + 1}) «{cap(nl_n(a, sp))}; следовательно, {nl_n(b, sp)}»." for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{i + 1}) ${ftex(a, b)}$ — {n_verdict(a, b)}" for i, (a, b) in enumerate(items)) + \
        " (неклассический / классический)"
    sol = "\n".join(f"{i + 1}) ${ftex(a, b)}$: {n_explain(a, b)}." for i, (a, b) in enumerate(items))
    sol += ("\n\nРассуждения, которые проходят только в классическом случае, опираются на $A^n7$ ($\\sim x \\vdash "
            "\\urcorner x$) и её следствия (с. 77).")
    return card(level, "F", "transfer", "short", src, "неклассический случай, обычный язык", cond, ans, sol, form="nat")


def c_sn_table(level=5, src="с. 76–77, гл. 5, § 5"):
    a, b = sample_n(rnd.choice(["both", "cl", "none"]), ("x", "y"), lo=14, hi=28, depth=2)
    names = sorted(atoms(a) | atoms(b))
    sts = list(K.states(names))
    rows = [(st, K.val3(a, st), K.val3(b, st)) for st in sts]
    hide = set(rnd.sample(range(len(rows)), min(5, len(rows))))
    lab = {"a": "{0}", "n": "\\urcorner {0}", "q": "?{0}"}
    head = "| " + " | ".join(f"истинно у ${n}$" for n in names) + " | посылка | заключение |\n|" + "---|" * (len(names) + 2) + "\n"
    body = "".join("| " + " | ".join(f"${lab[st[n]].format(n)}$" for n in names) +
                   f" | {'?' if i in hide else va} | {'?' if i in hide else vb} |\n" for i, (st, va, vb) in enumerate(rows))
    bad = [i + 1 for i, (_, va, vb) in enumerate(rows) if va and not vb]
    cond = (f"{NCONV} {SEM3} Заполните пропуски «?» в таблице значений посылки и заключения формулы ${ftex(a, b)}$ по всем "
            "состояниям букв и сделайте вывод о её тавтологичности в неклассическом и в классическом случае (в классическом "
            f"— только строки без $?$).\n\n{head}{body}")
    ans = ("; ".join(f"строка {i + 1}: {rows[i][1]}, {rows[i][2]}" for i in sorted(hide)) + "; " + n_verdict(a, b) +
           " (неклассический / классический)")
    sol = ("Значения: $x$ — 1 только в состоянии «истинно $x$», $\\urcorner x$ — только в «истинно $\\urcorner x$», $?x$ — "
           "только в «истинно $?x$» (с. 76); $\\sim$, конъюнкция, $\\vee$ — как обычно.\n\n" + head + "".join(
               "| " + " | ".join(f"${lab[st[n]].format(n)}$" for n in names) + f" | {va} | {vb} |\n" for st, va, vb in rows) +
           "\n" + (f"Строки с посылкой 1 и заключением 0: {', '.join(map(str, bad))}." if bad else
                   "Строк с посылкой 1 и заключением 0 нет."))
    return card(level, "C", "complete", "build", src, "неклассический случай, значения", cond, ans, sol)


# ---------- § 6: расширение числа возможностей, отношения ----------
SRC6 = "с. 72–73, 77–79, гл. 5, § 2, 6"
D1TXT = ("D1 (с. 77): $y^1, \\ldots, y^m$ не расширяют числа возможностей по $x^1, \\ldots, x^n$, если и только если доказуема "
         "$\\vdash \\sim(x^1 : \\ldots : x^n : y^1 : \\ldots : y^m)$ или $x^1 : \\ldots : x^n : y^1 : \\ldots : y^m \\vdash "
         "x_1 : \\ldots : x_k$, где $x_1, \\ldots, x_k$ — высказывания из $x^1, \\ldots, x^n$ или их отрицания "
         "($1 \\leqslant k \\leqslant n$; каждое $x^i$ входит не более одного раза — само или с отрицанием). Формулы проверяются в $S^5$: по MT5 § 2 (с. 73) $\\vdash x$ доказуема в $S^5$ тогда "
         "и только тогда, когда $x$ — тавтология, а $x \\vdash y$ в $S^5$ — теоремы $S^s$ (MT1 § 2, с. 72).")


def cands(base):
    out = []
    for k in range(1, len(base) + 1):
        for idx in combinations(range(len(base)), k):
            for signs in product((0, 1), repeat=k):
                ts = [base[i] if s == 0 else N(base[i]) for i, s in zip(idx, signs)]
                out.append(ts[0] if k == 1 else D(*ts))
    return out


def poss(base, zs):
    F = D(*(base + zs))
    if K.taut2(None, N(F)):
        return ("contr", None)
    for t in cands(base):
        if K.taut2(F, t):
            return ("wit", t)
    return ("ext", None)


def true_rows(F, names):
    out = []
    for bits in product((0, 1), repeat=len(names)):
        e = dict(zip(names, bits))
        if K.val(F, e):
            out.append("(" + ", ".join(map(str, bits)) + ")")
    return out


def poss_text(base, zs, verdict):
    F = D(*(base + zs))
    names = sorted(atoms(F))
    rows = true_rows(F, names)
    head = f"$({', '.join(names)})$"
    if verdict[0] == "contr":
        return (f"${tex(F)}$ ложна при всех значениях: $\\vdash {tex(N(F))}$ — тавтология, доказуема в $S^5$ (MT5 § 2) — по D1 "
                "не расширяет")
    if verdict[0] == "wit":
        return (f"${tex(F)}$ истинна при {head} $\\in \\{{{', '.join(rows)}\\}}$, и при всех этих наборах истинно "
                f"${tex(verdict[1])}$: ${tex(F)} \\vdash {tex(verdict[1])}$ — сильная тавтология, теорема $S^s$ и $S^5$ — по D1 "
                "не расширяет")
    return (f"${tex(F)}$ истинна при {head} $\\in \\{{{', '.join(rows)}\\}}$ — не противоречие; каждое $x_1 : \\ldots : x_k$ "
            "(одно из высказываний или их отрицаний, или сильная дизъюнкция таких высказываний с разными буквами) ложно "
            "хотя бы при одном из этих наборов (проверка перебором) — по D1 расширяет")


EXT_POOL = [N(W(x, y)), C(N(x), N(y)), W(C(x, y), C(N(x), N(y))), N(C(W(x, y), N(C(x, y)))), C(N(y), N(x)),
            N(W(y, x)), W(C(N(x), N(y)), C(x, y)), N(D(x, y))]


def sample_z(cat, names=("x", "y")):
    for _ in range(20000):
        if cat == "ext" and len(names) == 2 and rnd.random() < 0.7:
            zf = rnd.choice(EXT_POOL)
        else:
            zf = rnd_f(list(names), 2)
        if not (3 <= size(zf) <= 16) or zf in SEEN:
            continue
        base = [V(n) for n in names]
        v = poss(base, [zf])
        if (v[0] == "ext") == (cat == "ext") and (cat != "contr" or v[0] == "contr"):
            SEEN.add(zf)
            return zf, v
    raise RuntimeError(cat)


def v_short(v):
    return {"contr": "не расширяет (противоречие)", "ext": "расширяет"}.get(v[0]) or f"не расширяет (${tex(v[1])}$)"


def c_poss_series(level=6, src=SRC6):
    cats = rnd.sample(["ext", "wit", "wit", "contr", "ext"], 4)
    items = [sample_z(c) for c in cats]
    base = [x, y]
    cond = (f"{CONV} {D1TXT} Для каждого высказывания $z$ установите, расширяет ли оно число возможностей по $x$ и $y$; "
            "обоснуйте значениями: для нерасширяющего укажите доказуемую формулу D1, для расширяющего покажите, что ни одна "
            "такая формула не доказуема.\n\n" + "\n".join(f"{L[i]}) $z = {tex(zf)}$" for i, (zf, _) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {v_short(v)}" for i, (zf, v) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {poss_text(base, [zf], v)}." for i, (zf, v) in enumerate(items))
    sol += "\n\nСр. MT2, MT4 § 6 (с. 78): $xy$, $\\sim xy$, $x\\sim y$, $x$, $y$, $\\sim x$, $\\sim y$ не расширяют, $\\sim x\\sim y$ расширяет."
    return card(level, "C", "iso", "short", src, "расширение возможностей", cond, ans, sol, system="S^5")


def c_poss3(level=7, src=SRC6):
    items = []
    while len(items) < 4:
        cat = "ext" if len(items) < 1 or (len(items) == 2 and rnd.random() < 0.5) else "wit"
        for _ in range(4000):
            if cat == "ext":
                zf = rnd.choice([C(N(x), N(y), N(z)), N(W(x, y, z)), N(W(W(x, y), z)), C(N(W(x, y)), N(z))])
            else:
                lits = [rnd.choice([V(n), N(V(n))]) for n in rnd.sample("xyz", rnd.choice([1, 2, 2, 3]))]
                zf = lits[0] if len(lits) == 1 else C(*lits)
                if rnd.random() < 0.3:
                    zf = rnd_f(["x", "y", "z"], 2)
            v = poss([x, y, z], [zf])
            if (v[0] == "ext") == (cat == "ext") and zf not in [q for q, _ in items] and size(zf) <= 24:
                items.append((zf, v))
                break
    rnd.shuffle(items)
    cond = (f"{CONV} {D1TXT} Для каждого высказывания $w$ установите, расширяет ли оно число возможностей по $x$, $y$, $z$ "
            "(здесь $n = 3$, так что $k \\leqslant 3$); обоснуйте значениями.\n\n" +
            "\n".join(f"{L[i]}) $w = {tex(zf)}$" for i, (zf, _) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {v_short(v)}" for i, (zf, v) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {poss_text([x, y, z], [zf], v)}." for i, (zf, v) in enumerate(items))
    return card(level, "C", "transfer", "short", src, "расширение возможностей", cond, ans, sol, system="S^5")


def c_poss_diag(level=6, src=SRC6):
    for _ in range(500):
        cats = rnd.sample(["ext", "wit", "wit", "contr", "ext", "wit"], 4)
        items = [sample_z(c) for c in cats]
        wrong = rnd.sample(range(4), 2)
        claims, ok = [], True
        for i, (zf, v) in enumerate(items):
            F = D(x, y, zf)
            if i not in wrong:
                claims.append(v_short(v))
                continue
            if v[0] == "ext":
                bads = [t for t in cands([x, y]) if not K.taut2(F, t)]
                t = rnd.choice(bads)
                claims.append(f"не расширяет, так как доказуема ${tex(F)} \\vdash {tex(t)}$")
            else:
                claims.append("расширяет, так как $" + tex(F) + "$ не противоречие")
        if ok:
            break
    lines, ans, sol = [], [], []
    for i, (zf, v) in enumerate(items):
        lines.append(f"{i + 1}. $z = {tex(zf)}$ — {claims[i]}.")
        if i in wrong:
            F = D(x, y, zf)
            if v[0] == "ext":
                t = re.search(r"\\vdash (.+)\$$", claims[i])
                tt = [q for q in cands([x, y]) if tex(q) == t.group(1)][0]
                e = K.counter2(F, tt)
                ans.append(f"{i + 1}: расширяет (D1, с. 77)")
                sol.append(f"{i + 1}. Неверно: при {env_t(e)} посылка ${tex(F)}$ истинна, а ${tex(tt)}$ ложно — формула не "
                           f"тавтология и не доказуема в $S^5$ (MT1 § 2, с. 72). {poss_text([x, y], [zf], v)}.")
            else:
                ans.append(f"{i + 1}: {v_short(v)} (D1, с. 77)")
                sol.append(f"{i + 1}. Неверно: того, что $x : y : z$ не противоречие, мало — D1 допускает и формулу "
                           f"$x : y : z \\vdash x_1 : \\ldots : x_k$. {poss_text([x, y], [zf], v)}.")
    cond = (f"{CONV} {D1TXT} Студент исследовал, расширяют ли высказывания $z$ число возможностей по $x$ и $y$:\n\n" +
            "\n".join(lines) + "\n\nРовно два вывода неверны. Найдите их, объясните ошибку и дайте верный ответ.")
    return card(level, "E", "vary", "text", src, "расширение возможностей, диагностика", cond, "; ".join(ans),
                "\n".join(sol) + "\n\nОстальные выводы верны.", system="S^5")


def c_poss_table(level=5, src=SRC6):
    zf, v = sample_z(rnd.choice(["ext", "wit"]))
    F = D(x, y, zf)
    rows = []
    for bits in product((0, 1), repeat=2):
        e = {"x": bits[0], "y": bits[1]}
        rows.append((bits, K.val(zf, e), K.val(F, e)))
    hide = set(rnd.sample(range(4), 3))
    head = "| $x$ | $y$ | $z$ | $x : y : z$ |\n|---|---|---|---|\n"
    body = "".join(f"| {b[0]} | {b[1]} | {'?' if i in hide else vz} | {'?' if i in hide else vf} |\n"
                   for i, (b, vz, vf) in enumerate(rows))
    cond = (f"{CONV} {D1TXT} Для $z = {tex(zf)}$ заполните пропуски «?» в таблице и по ней установите, расширяет ли $z$ число "
            f"возможностей по $x$ и $y$; для нерасширяющего $z$ укажите формулу D1.\n\n{head}{body}")
    ans = "; ".join(f"строка {i + 1}: {rows[i][1]}, {rows[i][2]}" for i in sorted(hide)) + f"; {v_short(v)}"
    sol = (head + "".join(f"| {b[0]} | {b[1]} | {vz} | {vf} |\n" for b, vz, vf in rows) + "\n" +
           "$x : y : z$ истинна, когда истинно ровно одно из $x$, $y$, $z$ (с. 22). " + poss_text([x, y], [zf], v) + ".")
    return card(level, "V", "complete", "build", src, "расширение возможностей, значения", cond, ans, sol, system="S^5")


D23 = ("D2 (с. 79): $x$ и $y$ находятся в классическом отношении, если и только если доказуема $\\vdash x : y$; D3: в "
       "неклассическом, если и только если доказуема $\\vdash x : y : \\sim x\\sim y$, но недоказуема $\\vdash x : y$. "
       "Формулы $\\vdash x$ проверяются в $S^5$: по MT5 § 2 (с. 73) $\\vdash x$ доказуема тогда и только тогда, когда $x$ — "
       "тавтология.")


def rel(P, Q):
    if K.taut2(None, D(P, Q)):
        return "классическое"
    if K.taut2(None, D(P, Q, C(N(P), N(Q)))):
        return "неклассическое"
    return "ни то, ни другое"


def rel_why(P, Q):
    r = rel(P, Q)
    if r == "классическое":
        return f"${tex(D(P, Q))}$ истинна при всех значениях — тавтология, $\\vdash {tex(D(P, Q))}$ доказуема в $S^5$: классическое (D2)"
    e = K.counter2(None, D(P, Q))
    s1_ = f"при {env_t(e)} ${tex(D(P, Q))}$ ложна — $\\vdash x : y$ недоказуема"
    if r == "неклассическое":
        return s1_ + (f"; ${tex(D(P, Q, C(N(P), N(Q))))}$ истинна при всех значениях (оба сразу не истинны) — доказуема: "
                      "неклассическое (D3)")
    e2 = K.counter2(None, D(P, Q, C(N(P), N(Q))))
    return s1_ + f"; при {env_t(e2)} ложна и ${tex(D(P, Q, C(N(P), N(Q))))}$ (оба истинны): ни D2, ни D3"


def sample_pair(cat):
    for _ in range(20000):
        P, Q = rnd_f(["x", "y"], 2), rnd_f(["x", "y"], 2)
        if P == Q or not (2 <= size(P) <= 12 and 2 <= size(Q) <= 12) or (P, Q) in SEEN:
            continue
        if K.taut2(None, N(P)) or K.taut2(None, N(Q)) or K.taut2(None, P) or K.taut2(None, Q):
            continue
        if rel(P, Q) == cat:
            SEEN.add((P, Q))
            return P, Q
    raise RuntimeError(cat)


def c_rel_series(level=6, src="с. 73, 79, гл. 5, § 2, 6"):
    cats = rnd.sample(["классическое", "неклассическое", "неклассическое", "ни то, ни другое", "классическое"], 4)
    items = [sample_pair(c) for c in cats]
    cond = (f"{CONV} {D23} Для каждой пары высказываний установите по D2, D3, в каком отношении они находятся, и обоснуйте "
            "значениями.\n\n" + "\n".join(f"{L[i]}) ${tex(P)}$ и ${tex(Q)}$" for i, (P, Q) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {rel(P, Q)}" for i, (P, Q) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {rel_why(P, Q)}." for i, (P, Q) in enumerate(items))
    return card(level, "C", "iso", "short", src, "классические и неклассические отношения", cond, ans, sol, system="S^5")


def c_rel_diag(level=6, src="с. 73, 79, гл. 5, § 2, 6"):
    cats = rnd.sample(["классическое", "неклассическое", "неклассическое", "ни то, ни другое"], 4)
    items = [sample_pair(c) for c in cats]
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, (P, Q) in enumerate(items):
        r = rel(P, Q)
        if i in wrong:
            claim = {"классическое": "неклассическое: они не бывают истинны вместе",
                     "неклассическое": "классическое: они не бывают истинны вместе",
                     "ни то, ни другое": "неклассическое: они не бывают ложны вместе"}[r]
            ans.append(f"{i + 1}: {r} (D2, D3, с. 79)")
            sol.append(f"{i + 1}. Неверно: {rel_why(P, Q)}. Несовместимость даёт лишь $\\vdash x : y : \\sim x\\sim y$; для "
                       "классического отношения нужно ещё, чтобы одно из двух всегда было истинно.")
        else:
            claim = r
        lines.append(f"{i + 1}. ${tex(P)}$ и ${tex(Q)}$ — {claim}.")
    cond = (f"{CONV} {D23} Студент определил отношения четырёх пар:\n\n" + "\n".join(lines) +
            "\n\nРовно два ответа неверны. Найдите их, назовите нарушенное определение и обоснуйте верный ответ значениями.")
    return card(level, "E", "vary", "text", src, "классические и неклассические отношения, диагностика", cond,
                "; ".join(ans), "\n".join(sol) + "\n\nОстальные ответы верны.", system="S^5")


def c_rel_nat(level=6, src="с. 73, 79, гл. 5, § 2, 6"):
    ph = phrases()
    cats = rnd.sample(["классическое", "неклассическое", "ни то, ни другое"], 3)
    items = [sample_pair(c) for c in cats]
    cond = (f"Обозначения: {dict_text(ph, 'xy')}. {D23} Запишите каждую пару высказываний формулами и установите по D2, D3, в "
            "каком отношении они находятся.\n\n" +
            "\n".join(f"{i + 1}) «{cap(nl(P, ph))}» и «{nl(Q, ph)}»." for i, (P, Q) in enumerate(items)))
    ans = "; ".join(f"{i + 1}) ${tex(P)}$, ${tex(Q)}$ — {rel(P, Q)}" for i, (P, Q) in enumerate(items))
    sol = "\n".join(f"{i + 1}) {rel_why(P, Q)}." for i, (P, Q) in enumerate(items))
    return card(level, "T", "vary", "short", src, "классические и неклассические отношения, обычный язык", cond, ans, sol,
                form="nat")


def c_s5_series(level=6, src="с. 73, 78, гл. 5, § 2, 6"):
    items = []
    while len(items) < 4:
        zf = rnd_f(["x", "y"], 2)
        if not 3 <= size(zf) <= 12:
            continue
        a = D(x, y, zf)
        b = rnd.choice(cands([x, y]) + [D(x, y, rnd_f(["x", "y"], 1))])
        want = len(items) % 2 == 0
        if SY.provable("s", a, b) == want and (a, b) not in items and not K.taut2(None, N(a)):
            items.append((a, b))
    rnd.shuffle(items)
    cond = (f"{CONV} Исследуйте доказуемость в $S^5$ каждой формулы (формулы $x \\vdash y$ в $S^5$ — теоремы $S^s$, критерий "
            "MT1 § 2, с. 72: тавтология, в заключение которой не входят элементарные высказывания, отсутствующие в посылке); "
            "для недоказуемой укажите набор значений, при котором посылка 1, а заключение 0.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {'доказуема' if SY.provable('s', a, b) else 'недоказуема'}" for i, (a, b) in enumerate(items))
    sol = "\n".join(f"{L[i]}) " + (f"тавтология, $B \\subseteq A$ — доказуема" if SY.provable("s", a, b) else
                                    f"при {env_t(K.counter2(a, b))} посылка 1, заключение 0 — недоказуема") + "."
                    for i, (a, b) in enumerate(items))
    sol += "\n\nТакие формулы служат свидетелями в D1 § 6 (ср. списки MT2 и MT4, с. 78)."
    return card(level, "C", "iso", "short", src, "расширение возможностей, S5", cond, ans, sol, system="S^5")


def c_poss_construct(level=7, src="с. 77–79, гл. 5, § 6"):
    e1 = rnd.choice([W(C(x, y), C(N(x), N(y))), N(W(x, y)), N(C(W(x, y), N(C(x, y))))])
    e3 = rnd.choice([C(N(x), N(y), N(z)), N(W(x, y, z))])
    assert poss([x, y], [e1])[0] == "ext" and poss([x, y, z], [e3])[0] == "ext"
    cond = (f"{CONV} {D1TXT} Для каждого случая постройте высказывание, расширяющее число возможностей, или докажите, что "
            "такого нет: а) по $x$ и $y$ — высказывание, отличное по записи от $\\sim x\\sim y$; б) по $x$ и $\\sim x$ — "
            "высказывание, построенное из $x$; в) по $x$, $y$, $z$.")
    ans = (f"а) например, ${tex(e1)}$; б) нельзя (MT7 § 6, с. 79); в) например, ${tex(e3)}$.")
    sol = (f"а) {poss_text([x, y], [e1], poss([x, y], [e1]))}.\n"
           "б) Высказывание $z$, построенное из $x$, равнозначно $x$, $\\sim x$, противоречию или тавтологии. Если $z$ "
           "равнозначно $x$, то $x : \\sim x : z$ равнозначна $\\sim x$ и доказуема $x : \\sim x : z \\vdash \\sim x$; если "
           "$\\sim x$ — доказуема $x : \\sim x : z \\vdash x$; если противоречие — $x : \\sim x : z \\vdash x : \\sim x$; если "
           "тавтология — $\\vdash \\sim(x : \\sim x : z)$. Все эти формулы — тавтологии, по MT1, MT5 § 2 доказуемы; по D1 "
           "$z$ не расширяет. Это MT7 (с. 79).\n"
           f"в) {poss_text([x, y, z], [e3], poss([x, y, z], [e3]))}.")
    return card(level, "S", "transfer", "build", src, "расширение возможностей, построение", cond, ans, sol, system="S^5")


# ---------- § 7: расширения общей теории дедукции ----------
SRC7 = "с. 72–73, 75–77, 79, гл. 5, § 2, 5, 7"
KSN = ["s", "w", "m", "c"]
STN = {"s": "$S^s_n$", "w": "$S^w_n$", "m": "$S^m_n$", "c": "$S^c_n$"}
EXTTXT = ("По § 7 (с. 79) разделы логики строятся присоединением дополнений к выбранной системе общей теории дедукции, "
          "как в § 5; присоединив $A^n1$–$A^n6$ к $S^s$, $S^w$, $S^m$, $S^c$, получаем $S^s_n$, $S^w_n$, $S^m_n$, $S^c_n$ "
          "(с. 75). MT1 § 5 (с. 76): все доказуемые в $S^i_n$ формулы — тавтологии (по главной интерпретации). MT2 § 5: если "
          "$x \\vdash y$ доказуема в $S^s_n$, то в $y$ не входят элементарные высказывания, отсутствующие в $x$; для $S^w_n$, "
          "$S^m_n$, $S^c_n$ имеют силу соответствующие теоремы непарадоксальности (условия MT3, MT2, MT4 § 2).")


def cond_n(k, a, b):
    A, Bs = K.atoms(a), K.atoms(b)
    return {"s": Bs <= A, "w": bool(A & Bs), "m": A == Bs, "c": A <= Bs}[k]


def excl(a, b, k):
    if not K.taut3(a, b):
        return "MT1"
    if not cond_n(k, a, b):
        return "MT2"
    return "prov" if not has_n((a, b)) else "open"


EXW = {"MT1": "исключена (MT1)", "MT2": "исключена (MT2)", "prov": "доказуема", "open": "не исключена"}


def excl_ans(a, b):
    groups = {}
    for k in KSN:
        groups.setdefault(excl(a, b, k), []).append(STN[k])
    return "; ".join(f"{', '.join(v)} — {EXW[g]}" for g, v in groups.items())


def excl_sol(a, b):
    A, Bs = K.atoms(a), K.atoms(b)
    if not K.taut3(a, b):
        return (f"при {K.st_text(K.counter3(a, b))} посылка истинна, заключение ложно — не тавтология, по MT1 § 5 "
                "недоказуема во всех $S^i_n$")
    head = f"тавтология (проверка по всем состояниям); $A = {lst(A)}$, $B = {lst(Bs)}$"
    parts = []
    for k in KSN:
        e = excl(a, b, k)
        parts.append(f"{STN[k]}: " + {"MT2": "условие нарушено — исключена по MT2 § 5",
                                      "prov": f"формула без $\\urcorner$ и $?$ — теорема $S^{k}$ по {MTN[k]} § 2, а значит, "
                                              f"и {STN[k]}",
                                      "open": "условие выполнено — MT1 и MT2 её не исключают"}[e])
    return head + "; " + "; ".join(parts)


def sample_nrel(rel, names=("x", "y", "z")):
    for _ in range(40000):
        if rel == "eq":
            la = lb = list(rnd.sample(names, 2))
        elif rel == "sub":
            lb = list(rnd.sample(names, 1))
            la = lb + [rnd.choice([c for c in names if c not in lb])]
        elif rel == "sup":
            la = list(rnd.sample(names, 1))
            lb = la + [rnd.choice([c for c in names if c not in la])]
        elif rel == "over":
            la, lb = ["x", "y"], ["y", "z"]
        else:
            la, lb = ["x"], ["y"]
        a, b = rnd_n(la, 2), rnd_n(lb, 2)
        if a == b or not has_n((a, b)) or not (10 <= size(a) + size(b) <= 30) or (a, b) in SEEN:
            continue
        if not K.taut3(a, b):
            if rel == "non":
                SEEN.add((a, b))
                return a, b
            continue
        A, Bs = K.atoms(a), K.atoms(b)
        r = "eq" if A == Bs else "sub" if Bs < A else "sup" if A < Bs else "over" if A & Bs else "disj"
        if r == rel:
            SEEN.add((a, b))
            return a, b
    raise RuntimeError(rel)


def c_excl_series(level=6, src=SRC7, classical=False):
    if classical:
        items = [sample(p, lo=12, hi=30) for p in rnd.sample(["eq", "sub", "sup", "over", "non"], 4)]
    else:
        items = [sample_nrel(r) for r in rnd.sample(["eq", "sub", "sup", "over", "non"], 3)]
        items.insert(rnd.randrange(4), sample(rnd.choice(["sub", "sup"]), lo=12, hi=28))
    cond = (f"{NCONV} {CONV.split(';')[1].strip().capitalize()}. {EXTTXT} {SEM3} Для каждой формулы и каждой из систем "
            "$S^s_n$, $S^w_n$, $S^m_n$, $S^c_n$ установите, исключают ли её доказуемость MT1 или MT2 § 5; для формулы без "
            "$\\urcorner$ и $?$ решите вопрос о доказуемости полностью. Обоснуйте значениями и множествами $A$, $B$ "
            "элементарных высказываний посылки и заключения.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {excl_ans(a, b)}" for i, (a, b) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {excl_sol(a, b)}." for i, (a, b) in enumerate(items))
    return card(level, "S", "transfer", "short", src, "расширения, неклассический случай", cond, ans, sol,
                system="S^i_n", form="sym")


def c_excl_diag(level=6, src=SRC7):
    for _ in range(300):
        a1, b1 = sample_nrel("eq")                     # ошибка: «⌝x, ?x — новые элементарные»
        if not any(f in repr((a1, b1)) for f in ("nn", "qq")):
            continue
        if K.letters(b1) <= K.letters(a1):
            continue
        break
    a2, b2 = sample_n("cl", ("x",), lo=8, hi=22)        # ошибка: не исключена (а исключает MT1)
    a3, b3 = sample_nrel("sub")
    a4, b4 = sample_nrel("non")
    rows = [(a1, b1, "m", "исключена по MT2 § 5: в заключение входит высказывание с $\\urcorner$ или $?$, которого нет в "
             "посылке", True),
            (a2, b2, "s", "не исключена: в классическом случае это тавтология", True),
            (a3, b3, "c", None, False), (a4, b4, "w", None, False)]
    rnd.shuffle(rows)
    lines, ans, sol = [], [], []
    for i, (a, b, k, claim, wrong) in enumerate(rows):
        e = excl(a, b, k)
        if not wrong:
            claim = ((f"исключена по MT1 § 5: при {K.st_text(K.counter3(a, b))} посылка истинна, заключение ложно")
                     if e == "MT1" else {"MT2": "исключена по MT2 § 5: условие системы на элементарные высказывания нарушено",
                                         "open": "не исключена: тавтология, условие системы выполнено",
                                         "prov": "доказуема"}[e])
        else:
            if e == "open":
                ans.append(f"{i + 1}: в {STN[k]} не исключена (с. 76)")
                sol.append(f"{i + 1}. Неверно: $\\urcorner x$ и $?x$ образованы из $x$ (дополнение к определению высказывания, "
                           f"с. 76), элементарные высказывания в них те же — иначе MT2 не была бы «очевидна из вида "
                           f"$A^n1$–$A^n6$» (с. 76). {excl_sol(a, b)}.")
            else:
                st = K.counter3(a, b)
                ans.append(f"{i + 1}: в {STN[k]} исключена по MT1 § 5 (с. 76)")
                sol.append(f"{i + 1}. Неверно: $S^s_n$ — система для неклассического случая, $A^n7$ в ней нет (классический "
                           f"случай получается её присоединением, с. 77); по главной интерпретации (с. 76) при {K.st_text(st)} "
                           "посылка истинна, а заключение ложно — формула не тавтология, по MT1 § 5 недоказуема.")
        lines.append(f"{i + 1}. ${ftex(a, b)}$ в {STN[k]} — {claim}.")
    cond = (f"{NCONV} {EXTTXT} {SEM3} Студент проверил, исключают ли MT1 и MT2 § 5 доказуемость четырёх формул:\n\n" +
            "\n".join(lines) + "\n\nРовно два вывода неверны. Найдите их, назовите нарушенное положение книги со страницей и "
            "дайте верный ответ.")
    return card(level, "E", "vary", "text", src, "расширения, неклассический случай, диагностика", cond, "; ".join(ans),
                "\n".join(sol) + "\n\nОстальные выводы верны.", system="S^i_n")


def c_ext_E(level=5, src="с. 75–77, 79, гл. 5, § 5, 7"):
    n = rnd.choice("xy")
    base = rnd.choice(["m", "c", "w"])
    cond = (f"{NCONV} {EXTTXT} Студент утверждает: «1) {STN[base]} и $S^s_n$ — одна и та же система: дополнения у них "
            f"одинаковые, $A^n1$–$A^n6$. 2) В {STN[base]} формула $\\sim {n} \\vdash \\urcorner {n} \\vee ?{n}$ недоказуема, "
            f"потому что в её заключение входят элементарные высказывания $\\urcorner {n}$ и $?{n}$, которых нет в посылке». "
            "Найдите ошибки и назовите положения книги, которые нарушены.")
    ans = ("1) От выбора системы общей теории дедукции зависят получающиеся системы (с. 75, 79): к $S^" + base +
           "$ и $S^s$ присоединяются одни дополнения, но сами системы различны. 2) Это пример $A^n1$ — аксиома любой "
           f"$S^i_n$ (с. 76); $\\urcorner {n}$ и $?{n}$ образованы из ${n}$, элементарные высказывания в них те же.")
    sol = (f"1. Системы $S^s_n$, $S^w_n$ и т. д. обозначаются «в зависимости от выбора $S^s$, $S^w$ и т. д., к которым делается "
           f"это дополнение» (с. 75); по § 7 «в зависимости от того, какая система общей теории дедукции будет выбрана, "
           f"получатся различные системы» (с. 79). Например, в $S^s_n$ доказуема $xy \\vdash x$ (теорема $S^s$, MT1 § 2), а в "
           f"$S^m_n$ её исключает MT2 § 5 ($\\{{x, y\\}} \\neq \\{{x\\}}$).\n"
           f"2. $\\sim {n} \\vdash \\urcorner {n} \\vee ?{n}$ — схема $A^n1$, она — аксиома всякой системы, получаемой "
           f"дополнением § 5. По дополнению к определению высказывания (с. 76) $\\urcorner {n}$ и $?{n}$ получаются из ${n}$ "
           "помещением оператора перед главным оператором — нового элементарного высказывания не возникает; MT2 «очевидна "
           "из вида $A^n1$–$A^n6$» (с. 76).")
    return card(level, "E", "vary", "text", src, "расширения, диагностика", cond, ans, sol, form="meta")


def c_ext_construct(level=8, src=SRC7):
    pool = [(i, o) for i, o in requests_pool() if "q" not in i + o]
    for _ in range(5000):
        reqs = rnd.sample(pool, 3)
        feas = [bool([r for r in feasible(*q) if r != "non"]) for q in reqs]
        if sum(feas) in (1, 2):
            break
    ans, sol = [], []
    for i, (ins, outs) in enumerate(reqs):
        fr = [r for r in feasible(ins, outs) if r != "non"]
        if fr:
            r = rnd.choice(fr)
            a, b = sample_nrel(r if r != "disj" else "disj")
            got = {k for k in KSN if excl(a, b, k) != "MT2"}
            assert K.taut3(a, b) and set(ins) <= got and not (set(outs) & got), (ins, outs, ftex(a, b))
            ans.append(f"{L[i]}) например, ${ftex(a, b)}$")
            sol.append(f"{L[i]}) Нужно {REL_TEXT[r]}. Пример ${ftex(a, b)}$: {excl_sol(a, b)}.")
        else:
            ans.append(f"{L[i]}) нельзя")
            sol.append(f"{L[i]}) Нельзя: {why_impossible(ins, outs)}; условия теорем непарадоксальности для $S^i_n$ — те же "
                       "условия на множества $A$, $B$, что в MT1–MT4 § 2.")
    cond = (f"{NCONV} {EXTTXT} {SEM3} Для каждого требования постройте формулу с $\\urcorner$ или $?$, тавтологичную в "
            "неклассическом случае, или докажите, что такой нет. $A$, $B$ — множества элементарных высказываний посылки и "
            "заключения.\n\n" +
            "\n".join(f"{L[i]}) доказуемость не исключена MT2 § 5 в {', '.join(STN[k] for k in ins)} и исключена в "
                      f"{', '.join(STN[k] for k in outs)};" for i, (ins, outs) in enumerate(reqs)))
    return card(level, "S", "transfer", "build", src, "расширения, построение", cond, "; ".join(ans), "\n".join(sol),
                form="meta", system="S^i_n")


# ---------- § 8: семантическая интерпретация ----------
SRC8 = "с. 79–80, гл. 5, § 8"
SEM8 = ("По § 8 (с. 80) для целей книги достаточно такой интерпретации знака следования: $x \\vdash y$ имеет значение 1, "
        "если и только если, приписав $x$ значение 1 ($y$ значение 0), мы вследствие этого вынуждены приписать $y$ значение 1 "
        "($x$ значение 0).")


def sample_nd(want, lo=14, hi=34, names=("x", "y", "z")):
    for _ in range(40000):
        a, b = rnd_f(list(rnd.sample(names, 2)), 3, 0.2), rnd_f(list(rnd.sample(names, 2)), 3, 0.2)
        if a == b or not (lo <= size(a) + size(b) <= hi) or (a, b) in SEEN:
            continue
        if K.taut2(None, N(a)) or K.taut2(None, b):
            continue
        if K.taut2(a, b) == want:
            SEEN.add((a, b))
            return a, b
    raise RuntimeError


def rows_where(f, names, v=1):
    out = []
    for bits in product((0, 1), repeat=len(names)):
        e = dict(zip(names, bits))
        if K.val(f, e) == v:
            out.append("(" + ", ".join(map(str, bits)) + ")")
    return out


def sem_why(a, b):
    names = sorted(atoms(a) | atoms(b))
    if K.taut2(a, b):
        rs = rows_where(a, names)
        return (f"посылка истинна при $({', '.join(names)})$ $\\in \\{{{', '.join(rs)}\\}}$, и при каждом из этих наборов "
                "заключение истинно: приписав посылке 1, мы вынуждены приписать заключению 1 — значение 1")
    e = K.counter2(a, b)
    return f"при {env_t(e)} посылка 1, а заключение 0 — приписать заключению 1 мы не вынуждены: значение 0"


def c_sem_series(level=5, src=SRC8):
    wants = rnd.sample([True, False, True, False], 4)
    items = [sample_nd(w) for w in wants]
    cond = (f"{CONV} {SEM8} Посылки данных формул не противоречия, заключения не тавтологии. Найдите значение каждой формулы "
            "по этой интерпретации и обоснуйте наборами значений.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {1 if K.taut2(a, b) else 0}" for i, (a, b) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {sem_why(a, b)}." for i, (a, b) in enumerate(items))
    sol += "\n\nДля таких формул значение 1 совпадает с тавтологичностью, но и эта интерпретация — лишь «техническое» средство, а не определение условий истинности (с. 80)."
    return card(level, "V", "iso", "short", src, "семантическая интерпретация", cond, ans, sol)


def c_sem_diag(level=6, src=SRC8):
    items = [sample_nd(w) for w in rnd.sample([True, False, True, False], 4)]
    wrong = rnd.sample(range(4), 2)
    lines, ans, sol = [], [], []
    for i, (a, b) in enumerate(items):
        names = sorted(atoms(a) | atoms(b))
        t = K.taut2(a, b)
        if i in wrong:
            if t:
                e = next(dict(zip(names, bits)) for bits in product((0, 1), repeat=len(names))
                         if not K.val(a, dict(zip(names, bits))) and not K.val(b, dict(zip(names, bits)))) \
                    if any(not K.val(a, dict(zip(names, bits))) and not K.val(b, dict(zip(names, bits)))
                           for bits in product((0, 1), repeat=len(names))) else None
                if e is None:
                    e = next(dict(zip(names, bits)) for bits in product((0, 1), repeat=len(names))
                             if not K.val(a, dict(zip(names, bits))))
                claim = f"значение 0: при {env_t(e)} посылка {K.val(a, e)}, заключение {K.val(b, e)}"
                ans.append(f"{i + 1}: 1")
                sol.append(f"{i + 1}. Неверно: набор, где посылка 0, ничего не говорит — интерпретация спрашивает, что мы "
                           f"вынуждены приписать заключению, приписав посылке 1 (с. 80). {cap(sem_why(a, b))}.")
            else:
                good = [dict(zip(names, bits)) for bits in product((0, 1), repeat=len(names))
                        if K.val(a, dict(zip(names, bits))) and K.val(b, dict(zip(names, bits)))]
                if not good:
                    good = [K.counter2(a, b)]
                    claim = f"значение 1: при {env_t(good[0])} посылка истинна"
                else:
                    claim = f"значение 1: при {env_t(good[0])} посылка и заключение истинны"
                ans.append(f"{i + 1}: 0")
                sol.append(f"{i + 1}. Неверно: одного набора, где обе части истинны, мало — «вынуждены приписать» значит при "
                           f"всяком наборе с истинной посылкой (с. 80). {cap(sem_why(a, b))}.")
        else:
            claim = f"значение {1 if t else 0}: " + sem_why(a, b).split(" — ")[0]
        lines.append(f"{i + 1}. ${ftex(a, b)}$ — {claim}.")
    cond = (f"{CONV} {SEM8} Студент нашёл значения четырёх формул (посылки не противоречия, заключения не тавтологии):\n\n" +
            "\n".join(lines) + "\n\nРовно два ответа неверны. Найдите их, объясните ошибку и дайте верный ответ.")
    return card(level, "E", "vary", "text", src, "семантическая интерпретация, диагностика", cond, "; ".join(ans),
                "\n".join(sol) + "\n\nОстальные ответы верны.")


def c_sem_E(level=5, src=SRC8):
    a, b = sample_nd(False, lo=10, hi=24)
    e = K.counter2(a, b)
    names = sorted(atoms(a) | atoms(b))
    both = next((dict(zip(names, bits)) for bits in product((0, 1), repeat=len(names))
                 if K.val(a, dict(zip(names, bits))) and K.val(b, dict(zip(names, bits)))), None)
    if both is None:
        return c_sem_E(level, src)
    cond = (f"{CONV} Студент пишет: «1) Формула $x \\vdash y$ истинна тогда и только тогда, когда $x \\supset y$ — тавтология: "
            f"это и есть определение условий истинности высказываний о следовании. 2) Высказывание «из ${tex(a)}$ следует "
            f"${tex(b)}$» истинно, потому что при {env_t(both)} и посылка, и заключение истинны». Найдите ошибки, опираясь на "
            "§ 8 (с. 79–80).")
    ans = ("1) Интерпретация через тавтологичность принята из «технических» соображений, а не как определение условий "
           "истинности (с. 79–80); 2) «Из $x$ следует $y$» истинно, если и только если действительно имеется логическое "
           f"правило, согласно которому из $x$ следует $y$ (с. 80); здесь его нет: при {env_t(e)} посылка 1, заключение 0.")
    sol = ("1. С. 79–80: знак следования интерпретировался так, что $x \\vdash y$ — тавтология тогда и только тогда, когда "
           "$x \\supset y$ — тавтология; это сделано «исключительно из „технических“ соображений и для удобства сравнения… "
           "а не как определение условий истинности высказываний о следовании».\n"
           "2. Условия истинности (с. 80): высказывание «Из $x$ следует $y$» истинно, если и только если действительно имеется "
           "логическое правило (утверждение), согласно которому из $x$ следует $y$. Совпадение значений в одном наборе такого "
           f"правила не даёт. Более того, при {env_t(e)} посылка 1, а заключение 0: даже по интерпретации § 8 формула имеет "
           "значение 0, и ни одна система $S^s$, $S^w$, $S^m$, $S^c$, $S^6$ её не доказывает (MT1–MT4, MT6 § 2).")
    return card(level, "E", "vary", "text", src, "семантическая интерпретация, диагностика", cond, ans, sol, form="meta")


def s1_lines_letters(want, least):
    for _ in range(200):
        lines = H.build_ok(want, least)
        a, b = lines[-1][0], lines[-1][1]
        if atoms(a) | atoms(b) <= set("xyzu") and size(a) <= 22 and size(b) <= 26:
            return lines
    raise RuntimeError


def c_sem_rule(level=7, src="с. 17, 36, 45, 80, гл. 1, § 1; гл. 2, § 1, 5; гл. 5, § 8"):
    lines = s1_lines_letters(rnd.choice([9, 10]), 8)
    a, b = lines[-1][0], lines[-1][1]
    ph = phrases()
    names = atoms(a) | atoms(b)
    cond = (f"Рассуждение: «{cap(nl(a, ph))}; следовательно, {nl(b, ph)}». Обозначения: {dict_text(ph, names)}; «или … (по "
            "крайней мере одно)» — $\\vee$, «неверно, что» и «не» — $\\sim$. По § 8 (с. 80) высказывание «Из $x$ следует $y$» "
            "истинно, если и только если действительно имеется логическое правило, согласно которому из $x$ следует $y$. "
            f"Запишите рассуждение формулой и предъявите такое правило: выведите формулу в $S_1$. {S1CONV}")
    ans = f"${ftex(a, b)}$; вывод в {len(lines)} строк (см. решение) — формула есть теорема $S^s$."
    sol = (f"Формула: ${ftex(a, b)}$.\n\n" + show(lines) + "\n\nВыведенная формула — правило системы $S_1$ (то есть $S^s$), "
           "согласно которому из посылки следует заключение; по § 8 это и делает высказывание о следовании истинным (с. 80).")
    return card(level, "D", "vary", "proof", src, "семантическая интерпретация, вывод, обычный язык", cond, ans, sol,
                form="nat", system="S^s")


def c_sem_nat_E(level=6, src="с. 72, 80, гл. 5, § 2, 8"):
    ph = phrases()
    a1, b1 = sample_nd(False, lo=8, hi=20, names=("x", "y"))
    a2, b2 = sample("sub", lo=8, hi=22, depth=2)
    names2 = sorted(atoms(a2))
    e1 = K.counter2(a1, b1)
    cond = (f"Обозначения: {dict_text(ph, atoms(a1) | atoms(b1) | atoms(a2) | atoms(b2))}. Студент оценивает два рассуждения "
            f"по тому, что известно о сегодняшнем дне. 1) «{cap(nl(a1, ph))}; следовательно, {nl(b1, ph)}» — «правильно: "
            f"сегодня и посылка, и заключение истинны». 2) «{cap(nl(a2, ph))}; следовательно, {nl(b2, ph)}» — «неправильно: "
            "сегодня посылка ложна». Запишите рассуждения формулами, найдите ошибки студента и решите вопрос о следовании по "
            "§ 8 (с. 80) и MT1 § 2 (с. 72).")
    ans = (f"1) ${ftex(a1, b1)}$ — не следование: логического правила нет, при {env_t(e1)} посылка 1, заключение 0; "
           f"2) ${ftex(a2, b2)}$ — следование: сильная тавтология, теорема $S^s$ (MT1 § 2). Истинность частей в данном "
           "случае ничего не решает (с. 80).")
    sol = (f"1. ${ftex(a1, b1)}$: при {env_t(e1)} посылка истинна, а заключение ложно; по интерпретации § 8 значение 0, и "
           "правила, согласно которому из посылки следует заключение, нет — высказывание о следовании ложно (с. 80).\n"
           f"2. ${ftex(a2, b2)}$: при всех наборах, где посылка 1, заключение 1 — тавтология; в заключение не входят новые "
           "элементарные высказывания, так что это теорема $S^s$ (MT1 § 2, с. 72) — логическое правило есть, следование имеет "
           "место, какова бы ни была посылка сегодня.\n"
           "Ошибка студента — подмена условий истинности высказывания «Из $x$ следует $y$» (наличие логического правила, с. 80) "
           "истинностью самих $x$ и $y$.")
    return card(level, "E", "vary", "text", src, "семантическая интерпретация, обычный язык, диагностика", cond, ans, sol,
                form="nat")


def c_sem_transfer(level=7, src="с. 72–73, 79–80, гл. 5, § 2, 8"):
    pats = rnd.sample(["sup", "over", "sub", "eq"], 2) + ["non"]
    items = []
    for p in pats:
        for _ in range(300):
            a, b = sample(p, lo=14, hi=34)
            if not K.taut2(None, N(a)) and not K.taut2(None, b):
                items.append((a, b))
                break
    rnd.shuffle(items)
    cond = (f"{CONV} {SEM8} Для каждой формулы найдите её значение по этой интерпретации и все системы из $S^s$, $S^w$, "
            f"$S^m$, $S^c$, $S^6$, где она доказуема. Объясните, почему значение 1 не решает вопроса о доказуемости. {CRIT}\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    ans = "; ".join(f"{L[i]}) {1 if K.taut2(a, b) else 0}; {sys_list(provset(a, b))}" for i, (a, b) in enumerate(items))
    sol = "\n".join(f"{L[i]}) {sem_why(a, b)}. {explain(a, b)}" for i, (a, b) in enumerate(items))
    sol += ("\n\nЗначение 1 по § 8 совпадает с тавтологичностью; доказуемость в $S^s$, $S^w$, $S^m$, $S^c$ требует ещё "
            "условия на элементарные высказывания (MT1–MT4), и только в $S^6$ одного значения 1 достаточно (MT6).")
    return card(level, "S", "transfer", "short", src, "семантическая интерпретация, критерии", cond, ans, sol)


def c_sem_table(level=5, src=SRC8):
    a, b = sample_nd(rnd.random() < 0.5, lo=12, hi=26, names=("x", "y", "z"))
    names = sorted(atoms(a) | atoms(b))
    envs = [dict(zip(names, bits)) for bits in product((0, 1), repeat=len(names))]
    rows = [(e, K.val(a, e), K.val(b, e)) for e in envs]
    hide = set(rnd.sample(range(len(rows)), min(4, len(rows) - 1)))
    head = "| " + " | ".join(f"${n}$" for n in names) + " | посылка | заключение |\n|" + "---|" * (len(names) + 2) + "\n"
    body = "".join("| " + " | ".join(str(e[n]) for n in names) + f" | {'?' if i in hide else va} | {'?' if i in hide else vb} |\n"
                   for i, (e, va, vb) in enumerate(rows))
    t = K.taut2(a, b)
    cond = (f"{CONV} {SEM8} Заполните пропуски «?» в таблице значений посылки и заключения формулы ${ftex(a, b)}$ и по "
            f"таблице найдите значение формулы по этой интерпретации.\n\n{head}{body}")
    ans = "; ".join(f"строка {i + 1}: {rows[i][1]}, {rows[i][2]}" for i in sorted(hide)) + f"; значение {1 if t else 0}"
    sol = head + "".join("| " + " | ".join(str(e[n]) for n in names) + f" | {va} | {vb} |\n" for e, va, vb in rows) + \
        "\n" + cap(sem_why(a, b)) + "."
    return card(level, "V", "complete", "build", src, "семантическая интерпретация, значения", cond, ans, sol)


def c_sem_text(level=6, src="с. 72–73, 79–80, гл. 5, § 2, 8"):
    f1 = sample("sub", lo=10, hi=22, depth=2)
    f2 = sample("over", lo=10, hi=24, depth=2)
    f3 = sample_nd(False, lo=10, hi=22)
    cond = (f"{CONV} В § 8 сопоставлены три вещи: (а) интерпретация, при которой $x \\vdash y$ — тавтология тогда и только "
            f"тогда, когда $x \\supset y$ — тавтология (с. 79); (б) интерпретация «приписав $x$ значение 1, вынуждены приписать "
            "$y$ значение 1» (с. 80); (в) условия истинности: «Из $x$ следует $y$» истинно, если и только если имеется "
            "логическое правило, согласно которому из $x$ следует $y$ (с. 80). Для формул 1) "
            f"${ftex(*f1)}$, 2) ${ftex(*f2)}$, 3) ${ftex(*f3)}$ найдите значения по (а) и (б) и установите, в каких из "
            f"$S^s$, $S^w$, $S^6$ имеется соответствующее правило (теорема). Объясните, почему (в) не сводится к (а) и (б). {CRIT}")
    rowsx = []
    for i, (a, b) in enumerate((f1, f2, f3), 1):
        t = 1 if K.taut2(a, b) else 0
        ks = [k for k in ["s", "w", "q"] if SY.provable(k, a, b)]
        rowsx.append((i, t, ks, a, b))
    ans = "; ".join(f"{i}) (а) {'тавтология' if t else 'не тавтология'}, (б) {t}, правило — {sys_list(ks)}" for i, t, ks, a, b in rowsx)
    sol = "\n".join(f"{i}) {explain(a, b)}" for i, t, ks, a, b in rowsx)
    sol += ("\n\n(а) и (б) для таких формул дают одно и то же — значение 1 при тавтологичности. Но наличие правила зависит от "
            "системы: формула 2 — тавтология, а правило для неё есть в $S^w$ и $S^6$ и нет в $S^s$ (MT1). Поэтому, по книге, "
            "семантическая интерпретация — лишь «техническое» подсобное средство установления правил, а условия истинности "
            "определяются наличием правила (с. 80).")
    return card(level, "S", "vary", "text", src, "семантическая интерпретация, сравнение", cond, ans, sol, form="meta")


# ---------- § 9: операция замены отрицаний ----------
SRC9 = "с. 80–81, гл. 5, § 9"
OPTXT = ("Операция замены отрицаний (с. 81) применяется к $x \\vdash y$, если $x$ — противоречие или $y$ — тавтология (или то и "
         "другое): 1) все вхождения $a^1 : \\ldots : a^n$ заменяются на $b^1 : \\ldots : b^n$, где каждое $b^i$ есть конъюнкция "
         "$a^i$ и отрицаний всех остальных из $a^1, \\ldots, a^n$; 2) все вхождения $\\sim\\sim c$ заменяются на $c$, пока не "
         "останется высказывание без отрицания или только с одним отрицанием; 3) если в полученной формуле $x^* \\vdash y^*$ в "
         "$x^*$ или в $y^*$ входит $z$ без отрицания и с отрицанием, то $\\sim z$ везде заменяется на высказывание $v$, которое "
         "не входит в $x^* \\vdash y^*$; 4) сказанное в п. 3 делается для всех таких пар; получается $x^{**} \\vdash y^{**}$. "
         "Системы считаются достаточно полными, если в них доказуемы все непарадоксальные тавтологии $x \\vdash y$, для "
         "которых $x^{**} \\vdash y^{**}$ доказуемы в соответствующих системах (с. 81).")


def rnd_lit_f(names, depth):
    if depth == 0 or rnd.random() < 0.22:
        v = V(rnd.choice(names))
        r = rnd.random()
        return N(N(v)) if r < 0.12 else N(v) if r < 0.5 else v
    k = rnd.random()
    if k < 0.18:
        lits = [V(n) if rnd.random() < 0.6 else N(V(n)) for n in rnd.sample(names, 2)]
        return D(*lits)
    a, b = rnd_lit_f(names, depth - 1), rnd_lit_f(names, depth - 1)
    if a == b:
        return a
    return C(a, b) if k < 0.6 else W(a, b)


def step1(f):
    if f[0] in ("v",):
        return f
    if f[0] == "neg":
        return N(step1(f[1]))
    if f[0] == "dis":
        xs = [step1(t) for t in f[1]]
        return D(*(C(*([xs[i]] + [N(xs[j]) for j in range(len(xs)) if j != i])) for i in range(len(xs))))
    return (f[0], tuple(step1(t) for t in f[1]))


def step2(f):
    if f[0] == "neg" and f[1][0] == "neg":
        return step2(f[1][1])
    if f[0] == "v":
        return f
    if f[0] == "neg":
        return N(step2(f[1]))
    return (f[0], tuple(step2(t) for t in f[1]))


def lit_sets(f, pos, neg):
    if f[0] == "v":
        pos.add(f[1])
    elif f[0] == "neg" and f[1][0] == "v":
        neg.add(f[1][1])
    elif f[0] == "neg":
        raise ValueError("отрицание не перед буквой")
    else:
        for t in f[1]:
            lit_sets(t, pos, neg)


def op(a, b):
    a1, b1 = step1(a), step1(b)
    a2, b2 = step2(a1), step2(b1)
    pa, na, pb, nb = set(), set(), set(), set()
    lit_sets(a2, pa, na)
    lit_sets(b2, pb, nb)
    dbl = sorted(n for n in (pa | pb) & (na | nb) if (n in pa and n in na) or (n in pb and n in nb))
    amb = [n for n in (pa | pb) & (na | nb) if n not in dbl]
    used = atoms(a) | atoms(b)
    fresh = [v for v in "uwvpq" if v not in used]
    mp = dict(zip(dbl, fresh))

    def rep(f):
        if f[0] == "neg" and f[1][0] == "v" and f[1][1] in mp:
            return V(mp[f[1][1]])
        if f[0] == "v":
            return f
        if f[0] == "neg":
            return N(rep(f[1]))
        return (f[0], tuple(rep(t) for t in f[1]))
    return dict(s1=(a1, b1), s2=(a2, b2), s3=(rep(a2), rep(b2)), mp=mp, amb=amb)


def applicable(a, b):
    return K.taut2(None, N(a)) or K.taut2(None, b)


def sample_op(lo=12, hi=34, need_dis=False, need_dn=False, min_dbl=1):
    for _ in range(60000):
        names = rnd.sample("xyz", rnd.choice([2, 2, 3]))
        a, b = rnd_lit_f(names, 3), rnd_lit_f(names, 2)
        if a == b or not (lo <= size(a) + size(b) <= hi) or (a, b) in SEEN:
            continue
        if not K.taut2(a, b) or not applicable(a, b):
            continue
        if need_dis and "dis" not in repr((a, b)):
            continue
        if need_dn and "('neg', ('neg'" not in repr((a, b)):
            continue
        try:
            r = op(a, b)
        except ValueError:
            continue
        if r["amb"] or len(r["mp"]) < min_dbl:
            continue
        a3, b3 = r["s3"]
        if K.taut2(None, N(a3)) or K.taut2(None, b3):
            continue                       # после замены x** может быть 1, y** — 0 (с. 81)
        SEEN.add((a, b))
        return a, b, r
    raise RuntimeError


def op_steps(a, b, r):
    a1, b1 = r["s1"]
    a2, b2 = r["s2"]
    a3, b3 = r["s3"]
    out = []
    out.append(f"П. 1: ${ftex(a1, b1)}$" + ("" if (a1, b1) != (a, b) else " (сильных дизъюнкций нет — без изменений)"))
    out.append(f"П. 2: ${ftex(a2, b2)}$" + ("" if (a2, b2) != (a1, b1) else " (двойных отрицаний нет)"))
    if r["mp"]:
        out.append("Пп. 3–4: " + ", ".join(f"${k}$ входит без отрицания и с отрицанием — $\\sim {k}$ везде заменяется на ${v}$"
                                           for k, v in r["mp"].items()) + f"; получаем ${ftex(a3, b3)}$")
    return out


def why_appl(a, b):
    parts = []
    if K.taut2(None, N(a)):
        parts.append("посылка ложна при всех значениях — противоречие")
    if K.taut2(None, b):
        parts.append("заключение истинно при всех значениях — тавтология")
    return "; ".join(parts)


def c_op(level=6, src=SRC9):
    a, b, r = sample_op(need_dis=rnd.random() < 0.5, need_dn=rnd.random() < 0.4)
    a3, b3 = r["s3"]
    st = SY.provable("s", a3, b3)
    names = sorted(atoms(a3) | atoms(b3))
    e1 = next(dict(zip(names, bits)) for bits in product((0, 1), repeat=len(names)) if K.val(a3, dict(zip(names, bits))))
    e0 = next(dict(zip(names, bits)) for bits in product((0, 1), repeat=len(names)) if not K.val(b3, dict(zip(names, bits))))
    cond = (f"{CONV} {OPTXT} Проверьте, что к формуле ${ftex(a, b)}$ операция применима, выполните её по пунктам, покажите "
            "наборами значений, что $x^{**}$ может принять значение 1, а $y^{**}$ — значение 0, и исследуйте доказуемость "
            "$x^{**} \\vdash y^{**}$ в $S^s$ (MT1 § 2, с. 72: тавтология без элементарных высказываний заключения, "
            "отсутствующих в посылке).")
    ans = (f"$x^{{**}} \\vdash y^{{**}}$: ${ftex(a3, b3)}$; в $S^s$ {'доказуема' if st else 'недоказуема'}.")
    sol = (f"Применимость: {why_appl(a, b)}.\n\n" + "\n".join(op_steps(a, b, r)) +
           f"\n\n$x^{{**}} = 1$ при {env_t(e1)}; $y^{{**}} = 0$ при {env_t(e0)} — как и сказано на с. 81, после замены "
           f"рассматриваются формулы, где посылка может быть 1, а заключение 0.\n\n$S^s$: {SY.reason('s', a3, b3, tex)} "
           f"(MT1 § 2) — {'доказуема' if st else 'недоказуема'}.")
    return card(level, "D", "iso", "build", src, "полнота, замена отрицаний", cond, ans, sol)


def c_op_req(level=7, src=SRC9):
    for _ in range(200):
        items = [sample_op(lo=10, hi=28) for _ in range(3)]
        reqs = [SY.provable("s", a, b) and SY.provable("s", *r["s3"]) for a, b, r in items]
        if 0 < sum(reqs) < 3:
            break
    ans, sol = [], []
    for i, (a, b, r) in enumerate(items):
        a3, b3 = r["s3"]
        nonpar = SY.provable("s", a, b)
        req = nonpar and SY.provable("s", a3, b3)
        ans.append(f"{L[i]}) ${ftex(a3, b3)}$; {'требует' if req else 'не требует'}")
        sol.append(f"{L[i]}) {why_appl(a, b)}. " + " ".join(op_steps(a, b, r)) +
                   f". Исходная формула: {SY.reason('s', a, b, tex)} — {'непарадоксальна' if nonpar else 'парадоксальна'} для "
                   f"$S^s$; $x^{{**}} \\vdash y^{{**}}$: {SY.reason('s', a3, b3, tex)}. " +
                   ("Оба условия выполнены — достаточная полнота требует доказуемости (в $S^s$ формула и доказуема, MT1 § 2)."
                    if req else "Условие определения не выполнено — достаточная полнота доказуемости не требует."))
    cond = (f"{CONV} {OPTXT} Для систем сильного следования $S^s$ «непарадоксальная» тавтология — та, в заключение которой не "
            "входят элементарные высказывания, отсутствующие в посылке (MT1 § 2, с. 72). Для каждой формулы выполните "
            "операцию и установите, требует ли определение достаточной полноты, чтобы формула была доказуема в $S^s$.\n\n" +
            "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b, r) in enumerate(items)))
    return card(level, "C", "transfer", "short", src, "полнота, замена отрицаний", cond, "; ".join(ans), "\n".join(sol),
                system="S^s")


def c_op_complete(level=5, src=SRC9):
    a, b, r = sample_op(need_dis=True)
    steps = op_steps(a, b, r)
    a1, b1 = r["s1"]
    a2, b2 = r["s2"]
    a3, b3 = r["s3"]
    shown = [f"П. 1: …", f"П. 2: ${ftex(a2, b2)}$" if (a2, b2) != (a1, b1) else "П. 2: …",
             "Пп. 3–4: замены " + ", ".join(f"$\\sim {k}$ на …" for k in r["mp"]) + "; получаем …"]
    cond = (f"{CONV} {OPTXT} В записи операции для ${ftex(a, b)}$ пропущены результаты («…»). Восстановите их.\n\n" +
            "\n".join(shown))
    ans = (f"п. 1: ${ftex(a1, b1)}$; " + ("" if (a2, b2) != (a1, b1) else f"п. 2: ${ftex(a2, b2)}$; ") +
           ", ".join(f"$\\sim {k}$ на ${v}$" for k, v in r["mp"].items()) + f"; $x^{{**}} \\vdash y^{{**}}$: ${ftex(a3, b3)}$")
    sol = f"Применимость: {why_appl(a, b)}.\n\n" + "\n".join(steps)
    return card(level, "D", "complete", "build", src, "полнота, замена отрицаний, дополнение", cond, ans, sol)


def stud_op(a, b, r, errset, only_neg):
    s1 = (a, b) if "p1" in errset else (step1(a), step1(b))
    s2 = s1 if "dn" in errset else (step2(s1[0]), step2(s1[1]))
    mp = dict(r["mp"])
    if "same" in errset:
        ks = sorted(mp)
        mp[ks[1]] = mp[ks[0]]
    if "onlyneg" in errset:
        used = set(mp.values()) | atoms(a) | atoms(b)
        mp[only_neg[0]] = next(v for v in "pqvwu" if v not in used)

    def rep(f):
        if f[0] == "neg" and f[1][0] == "v" and f[1][1] in mp:
            return V(mp[f[1][1]])
        if f[0] == "v":
            return f
        if f[0] == "neg":
            return N(rep(f[1]))
        return (f[0], tuple(rep(t) for t in f[1]))
    return rep(s2[0]), rep(s2[1])


OPERR = {"onlyneg": ("п. 3", "заменено отрицание буквы, которая не входит без отрицания",
                     "п. 3 заменяет $\\sim z$ только для $z$, входящего и без отрицания, и с отрицанием"),
         "same": ("пп. 3–4", "для разных пар взято одно и то же новое высказывание",
                  "новое $v$ по п. 3 не должно входить в формулу, а после первой замены оно уже входит"),
         "dn": ("п. 2", "не сняты двойные отрицания", "п. 2 требует заменять $\\sim\\sim c$ на $c$"),
         "p1": ("п. 1", "сильная дизъюнкция не заменена", "п. 1 требует заменить $a^1 : \\ldots : a^n$ на "
                "$b^1 : \\ldots : b^n$, где $b^i$ — конъюнкция $a^i$ и отрицаний остальных")}


def c_op_diag(level=6, src=SRC9):
    for _ in range(2000):
        a, b, r = sample_op(min_dbl=1)
        a2, b2 = r["s2"]
        pa, na, pb, nb = set(), set(), set(), set()
        lit_sets(a2, pa, na)
        lit_sets(b2, pb, nb)
        only_neg = sorted((na | nb) - (pa | pb))
        errs = []
        if only_neg:
            errs.append("onlyneg")
        if len(r["mp"]) >= 2:
            errs.append("same")
        if "('neg', ('neg'" in repr((a, b)):
            errs.append("dn")
        if "'dis'" in repr((a, b)):
            errs.append("p1")
        pairs = [pr for pr in combinations(errs, 2) if set(pr) in ({"p1", "dn"}, {"same", "dn"}, {"onlyneg", "dn"},
                                                                     {"same", "onlyneg"})]
        if not pairs:
            continue
        chosen = list(rnd.choice(pairs))
        good = r["s3"]
        r1 = stud_op(a, b, r, {chosen[0]}, only_neg)
        r2 = stud_op(a, b, r, {chosen[1]}, only_neg)
        st = stud_op(a, b, r, set(chosen), only_neg)
        if len({good, r1, r2, st}) == 4:
            break
    else:
        raise RuntimeError
    a3, b3 = good
    cond = (f"{CONV} {OPTXT} Студент выполнил операцию для ${ftex(a, b)}$ и получил ${ftex(*st)}$. В его работе ровно две "
            "ошибки. Найдите их, назовите нарушенные пункты операции и дайте верный результат.")
    ans = "; ".join(f"{OPERR[c][0]}: {OPERR[c][1]}" for c in chosen) + f" (с. 81); верно: ${ftex(a3, b3)}$"
    sol = ("\n".join(f"{k + 1}. {cap(OPERR[c][0])}: {OPERR[c][1]}; {OPERR[c][2]} (с. 81)." for k, c in enumerate(chosen)) +
           f"\n\nВерное выполнение. Применимость: {why_appl(a, b)}.\n" + "\n".join(op_steps(a, b, r)))
    return card(level, "E", "vary", "text", src, "полнота, замена отрицаний, диагностика", cond, ans, sol)


S21TXT = ("Критерий доказуемости в $S_2^1$ (гл. 3, § 6, с. 55–57): формула доказуема тогда и только тогда, когда для каждого "
          "члена дизъюнктивной нормальной формы посылки найдётся член дизъюнктивной нормальной формы заключения, все "
          "конъюнктивные составляющие которого входят в него.")


def neg_lit(l):
    return l[1] if l[0] == "neg" else N(l)


def s21_template():
    P, Q, R = (rnd.choice([V(n), N(V(n))]) for n in rnd.sample("xyz", 3))
    if rnd.random() < 0.3:
        Q = C(Q, R) if rnd.random() < 0.5 else Q
    return rnd.choice([(C(W(P, Q), neg_lit(P)), Q), (C(W(P, Q), W(neg_lit(P), R)), W(Q, R)), (C(neg_lit(P), W(P, Q)), Q),
                       (C(W(P, Q, R), neg_lit(P), neg_lit(Q)) if Q[0] != "conj" else C(W(P, Q), neg_lit(P)), R if Q[0] != "conj" else Q),
                       (C(W(Q, P), neg_lit(P)), W(Q, R))])


def sample_s21(want_s21, lo=10, hi=30):
    for _ in range(40000):
        names = rnd.sample("xyz", rnd.choice([2, 3]))
        a, b = (rnd_lit_f(names, 2), rnd_lit_f(names, 2)) if want_s21 or rnd.random() < 0.2 else s21_template()
        if a == b or not (lo <= size(a) + size(b) <= hi) or (a, b) in SEEN or "'dis'" in repr((a, b)):
            continue
        if not SY.provable("w", a, b) or applicable(a, b):
            continue
        if SY.s21(a, b) == want_s21:
            SEEN.add((a, b))
            return a, b
    raise RuntimeError


def c_s21(level=7, src="с. 55–57, 73, 81, гл. 3, § 6; гл. 5, § 2, 9"):
    items = [sample_s21(w) for w in rnd.sample([True, False, False], 3)]
    ans, sol = [], []
    for i, (a, b) in enumerate(items):
        s = SY.s21(a, b)
        ans.append(f"{L[i]}) в $S_2^1$ {'доказуема' if s else 'недоказуема — свидетельство неполноты'}")
        sol.append(f"{L[i]}) Тавтология с общими элементарными высказываниями — по MT3 § 2 доказуема в $S^w$. Операция "
                   f"неприменима: посылка не противоречие, заключение не тавтология. ДНФ посылки: ${SY.dnf_tex(SY.dnf(a), tex)}$; "
                   f"заключения: ${SY.dnf_tex(SY.dnf(b), tex)}$. " +
                   ("Для каждого члена посылки есть подходящий член заключения — доказуема." if s else
                    "Есть член посылки, для которого подходящего члена заключения нет — недоказуема; как и формула "
                    "$(x \\vee y)\\sim x \\vdash y$ книги, это свидетельство того, что $S_2^1$ не полна в смысле § 9 (с. 81)."))
    cond = (f"{CONV.replace('«$:$» — сильная («одно и только одно из»); ', '')} {OPTXT} {S21TXT} Книга: $S_2^1$ не является "
            "полной в этом смысле, поскольку в ней недоказуема $(x \\vee y)\\sim x \\vdash y$, к которой операция замены "
            "неприменима (с. 81). Для каждой формулы проверьте доказуемость в $S^w$ (MT3 § 2) и в $S_2^1$ и установите, служит "
            "ли она таким же свидетельством.\n\n" + "\n".join(f"{L[i]}) ${ftex(a, b)}$" for i, (a, b) in enumerate(items)))
    return card(level, "S", "transfer", "short", src, "полнота, S21", cond, "; ".join(ans), "\n".join(sol), system="S_2^1")


def c_op_appl_E(level=5, src="с. 81, гл. 5, § 9"):
    a, b = sample_s21(False, lo=8, hi=24)
    cond = (f"{CONV} {OPTXT} {S21TXT} Студент пишет: «К тавтологии ${ftex(a, b)}$ применим операцию замены отрицаний: "
            "раз в ней есть отрицания, их можно заменить новыми буквами. А если операция к формуле неприменима, то "
            "определение достаточной полноты её вообще не касается, так что недоказуемость этой формулы в $S_2^1$ ни о чём не "
            "говорит». Найдите обе ошибки, сославшись на с. 81.")
    ans = (f"1) Операция применяется, только если посылка — противоречие или заключение — тавтология (с. 81); здесь ни то, ни "
           f"другое. 2) Книга как раз по формуле $(x \\vee y)\\sim x \\vdash y$, к которой операция неприменима, заключает, что "
           f"$S_2^1$ не полна (с. 81); данная формула доказуема в $S^w$ и недоказуема в $S_2^1$ — такое же свидетельство.")
    sol = ("1. С. 81: «Если в $x \\vdash y$ высказывание $x$ есть противоречие или $y$ есть тавтология (или и то и другое), "
           f"то…» — только тогда строится $x^* \\vdash y^*$. Посылка ${tex(a)}$ принимает значение 1 "
           f"(при {env_t(next(dict(zip(sorted(atoms(a)), bits)) for bits in product((0, 1), repeat=len(atoms(a))) if K.val(a, dict(zip(sorted(atoms(a)), bits)))))}), "
           f"заключение ${tex(b)}$ — значение 0 (при {env_t(next(dict(zip(sorted(atoms(b)), bits)) for bits in product((0, 1), repeat=len(atoms(b))) if not K.val(b, dict(zip(sorted(atoms(b)), bits)))))}).\n"
           "2. Операция лишь отсеивает формулы, где посылка не может быть 1 или заключение — 0; остальные непарадоксальные "
           "тавтологии система должна доказывать сами. Пример книги — $(x \\vee y)\\sim x \\vdash y$ (с. 81). Здесь: формула — "
           f"тавтология с общими элементарными высказываниями, по MT3 § 2 доказуема в $S^w$; ДНФ посылки "
           f"${SY.dnf_tex(SY.dnf(a), tex)}$, заключения ${SY.dnf_tex(SY.dnf(b), tex)}$ — по критерию $S_2^1$ недоказуема.")
    return card(level, "E", "vary", "text", src, "полнота, замена отрицаний, диагностика", cond, ans, sol)


def c_s21_E(level=6, src="с. 55–57, 81, гл. 3, § 6; гл. 5, § 9"):
    for _ in range(400):
        a, b, r = sample_op(lo=8, hi=24)
        a3, b3 = r["s3"]
        if not K.taut2(a3, b3) and SY.provable("w", a, b):
            break
    else:
        raise RuntimeError
    c, d = sample_s21(False, lo=8, hi=22)
    e = K.counter2(a3, b3)
    cond = (f"{CONV} {OPTXT} {S21TXT} Студент: «1) Тавтология ${ftex(a, b)}$ — свидетельство неполноты $S_2^1$ в смысле § 9: "
            f"это непарадоксальная тавтология, а $S_2^1$ её не доказывает. 2) Тавтология ${ftex(c, d)}$ такой неполноты не "
            "показывает: она парадоксальна, ведь из её посылки можно вывести не всё, что в заключении». Найдите ошибки.")
    ans = (f"1) К формуле применима операция ({why_appl(a, b)}); $x^{{**}} \\vdash y^{{**}}$ — ${ftex(a3, b3)}$ — не "
           f"тавтология (при {env_t(e)} посылка 1, заключение 0), так что определение с. 81 доказуемости не требует. 2) "
           "Формула непарадоксальна в смысле $S^w$ (тавтология с общими элементарными высказываниями, MT3 § 2), операция "
           "неприменима, а в $S_2^1$ она недоказуема — это свидетельство неполноты, как $(x \\vee y)\\sim x \\vdash y$ (с. 81).")
    sol = ("1. " + " ".join(op_steps(a, b, r)) + f". При {env_t(e)} $x^{{**}}$ = 1, $y^{{**}}$ = 0: $x^{{**}} \\vdash y^{{**}}$ "
           "не тавтология и ни в одной системе не доказуема; по определению (с. 81) достаточная полнота доказуемости исходной "
           "формулы не требует.\n"
           f"2. ${ftex(c, d)}$: посылка не противоречие, заключение не тавтология — операция неприменима; тавтология, общие "
           f"элементарные высказывания есть — по MT3 доказуема в $S^w$. ДНФ посылки ${SY.dnf_tex(SY.dnf(c), tex)}$, заключения "
           f"${SY.dnf_tex(SY.dnf(d), tex)}$ — по критерию $S_2^1$ недоказуема. Это такое же свидетельство, как пример книги "
           "(с. 81).")
    return card(level, "E", "vary", "text", src, "полнота, S21, диагностика", cond, ans, sol)


# ---------- карточки, перенесённые в другие id того же параграфа (тексты прежних ручных задач) ----------
MOVED = {
    '05.02-013': '---\nid: "05.02-013"\nchapter: 5\nsection: 2\nlevel: 8\ntype: M\nstep: transfer\ncondition: def\nform: meta\nanswer: proof\nsource: "с. 72–73, гл. 5, § 2"\ntags: [классическая логика]\n---\n\n## Условие\n\nДокажите MT1 § 2 гл. 5: $x \\vdash y$ доказуема в $S^s$ тогда и только тогда, когда $x \\supset y$ доказуема в классическом пропозициональном исчислении и в $y$ нет элементарных высказываний, отсутствующих в $x$.\n\n## Ответ\n\n$x \\supset y$ доказуема классически ⇔ тавтология ⇔ $x \\vdash y$ — тавтология. Дальше — полнота и непарадоксальность $S^s$.\n\n## Решение\n\n1. С. 72: интерпретация, применённая для полноты систем общей теории дедукции, — функционально полная двузначная алгебра, где знак следования истолкован как материальная импликация. Значит, $x \\vdash y$ — тавтология тогда и только тогда, когда тавтология $x \\supset y$: обе ложны ровно при $x = 1$, $y = 0$ (п. 5, с. 22; D1 § 3 гл. 1, с. 20).\n2. Классическое пропозициональное исчисление дедуктивно эквивалентно двузначной алгебре (с. 72): $x \\supset y$ доказуема в нём тогда и только тогда, когда она тавтология. Элементарному высказыванию соответствует пропозициональная переменная.\n3. ⇒. Если $x \\vdash y$ доказуема в $S^s$, то она тавтология (MT1 § 5 гл. 1, с. 22) — значит, $x \\supset y$ доказуема классически; и по непарадоксальности (MT1 § 4 гл. 1, с. 21) в $y$ нет элементарных высказываний, отсутствующих в $x$.\n4. ⇐. Если $x \\supset y$ доказуема классически, то $x \\vdash y$ — тавтология. Вместе с условием на элементарные высказывания это сильная тавтология, и по полноте (MT6 § 7 гл. 1, с. 32) она доказуема в $S^s$.',
    '05.02-014': '---\nid: "05.02-014"\nchapter: 5\nsection: 2\nlevel: 9\ntype: M\nstep: transfer\ncondition: def\nform: meta\nanswer: proof\nsource: "с. 72–73, гл. 5, § 2"\ntags: [классическая логика]\n---\n\n## Условие\n\nДокажите: каждая теорема $S^m$ — теорема $S^s$, $S^w$, $S^c$ и $S^6$; каждая теорема $S^s$ и $S^c$ — теорема $S^w$; каждая теорема $S^w$ — теорема $S^6$.\n\n## Ответ\n\nУсловия ослабевают: «совпадают» ⇒ «включение» ⇒ «есть общий» ⇒ «нет условий» (у каждого высказывания есть хотя бы одно элементарное).\n\n## Решение\n\n1. По MT1–MT4, MT6 § 2 (с. 72–73) во всех системах первое условие одно — доказуемость $x \\supset y$ в классическом исчислении. Сравниваем только условия на множества $A$ (элементарные высказывания посылки) и $B$ (заключения).\n2. $S^m$: $A = B$. Отсюда $B \\subseteq A$ (условие $S^s$) и $A \\subseteq B$ (условие $S^c$). Значит, теорема $S^m$ — теорема $S^s$ и $S^c$.\n3. $S^s$: $B \\subseteq A$. Множество $B$ не пусто: всякое высказывание строится из элементарных. Любой элемент $B$ лежит в $A$ — у $A$ и $B$ есть общий элемент (условие $S^w$). То же для $S^c$: $A \\subseteq B$ и $A$ не пусто.\n4. $S^w$: условие есть; в $S^6$ условия нет вовсе. Значит, теорема $S^w$ — теорема $S^6$.\n5. Цепочки дают и остальное: теорема $S^m$ — теорема $S^w$ (через $S^s$) и $S^6$ (через $S^w$).',
    '05.02-015': '---\nid: "05.02-015"\nchapter: 5\nsection: 2\nlevel: 10\ntype: I\nstep: transfer\ncondition: def\nform: meta\nanswer: proof\nsource: "с. 72–73, гл. 5, § 2"\ntags: [классическая логика]\n---\n\n## Условие\n\nКлассифицируйте возможные условия на множества $A$ (элементарные высказывания посылки) и $B$ (заключения): $B \\subseteq A$, $A \\subseteq B$, $A = B$, $A \\cap B \\neq \\varnothing$, без условия. Сопоставьте каждое условие с системами книги и объясните, почему условие $A \\cap B = \\varnothing$ бессмысленно.\n\n## Ответ\n\nКритерии: соотнесены $S^s$, $S^c$, $S^m$, $S^w$, $S^6$; показано, что при $A \\cap B = \\varnothing$ доказуемы лишь «парадоксы» (посылка — противоречие или заключение — тавтология).\n\n## Решение\n\nЭскиз.\n1. $B \\subseteq A$ — $S^s$ (MT1); $A \\subseteq B$ — $S^c$ (MT4); $A = B$ — $S^m$ (MT2); $A \\cap B \\neq \\varnothing$ — $S^w$ (MT3); без условия — $S^6$ (MT6), с. 72–73.\n2. Условие $A \\cap B = \\varnothing$. Если у $x$ и $y$ нет общих элементарных высказываний, их значения задаются независимо: найдись набор с $x = 1$ и набор с $y = 0$ — их объединение дало бы $x = 1$, $y = 0$. Значит, тавтология $x \\vdash y$ без общих элементарных высказываний возможна, только если $x$ — противоречие или $y$ — тавтология. Система с таким условием доказывала бы одни «парадоксы» вроде $\\sim xx \\vdash y$, $x \\vdash y : \\sim y$ — как раз то, что книга исключает (с. 73). И даже $x \\vdash x$ в ней была бы недоказуема.\n3. Хорошее решение добавляет, что условия упорядочены по силе: $A = B$ влечёт оба включения, каждое включение влечёт $A \\cap B \\neq \\varnothing$ (05.02-014).',
    '05.09-006': '---\nid: "05.09-006"\nchapter: 5\nsection: 9\nlevel: 9\ntype: M\nstep: transfer\ncondition: def\nform: meta\nanswer: proof\nsource: "с. 80–81, гл. 5, § 9"\ntags: [полнота, замена отрицаний]\n---\n\n## Условие\n\nДокажите, что п. 1 операции сохраняет равнозначность: $a^1 : \\ldots : a^n$ равнозначно $b^1 : \\ldots : b^n$, где $b^i$ — конъюнкция $a^i$ и отрицаний остальных $a^j$.\n\n## Ответ\n\nЕсли истинно ровно одно $a^i$, истинно ровно одно $b^i$; если ни одно или два и более, все $b^i$ ложны.\n\n## Решение\n\nПусть $b^i$ — конъюнкция $a^i$ и отрицаний всех остальных $a^j$ (п. 1, с. 81).\n1. Истинно ровно одно $a^i$. Тогда $b^i = 1$: $a^i = 1$, остальные $a^j = 0$, их отрицания истинны. Любое другое $b^j$ содержит множитель $\\sim a^i = 0$ и ложно. Истинно ровно одно $b^i$, и $b^1 : \\ldots : b^n = 1$, как и $a^1 : \\ldots : a^n$ (п. 4, с. 22).\n2. Ни одно $a^i$ не истинно. Каждое $b^i$ содержит множитель $a^i = 0$ — все $b^i$ ложны, обе дизъюнкции ложны.\n3. Истинны два или больше, например $a^i$ и $a^k$. $b^i$ содержит $\\sim a^k = 0$, $b^k$ содержит $\\sim a^i = 0$, любое другое $b^j$ содержит $\\sim a^i = 0$. Все $b$ ложны; $a^1 : \\ldots : a^n$ тоже ложно (истинно больше одного).\n4. Во всех случаях значения совпадают — п. 1 операции сохраняет равнозначность.',
    '05.09-011': '---\nid: "05.09-011"\nchapter: 5\nsection: 9\nlevel: 8\ntype: M\nstep: transfer\ncondition: def\nform: meta\nanswer: proof\nsource: "с. 80–81, гл. 5, § 9"\ntags: [полнота, замена отрицаний]\n---\n\n## Условие\n\nБуквы $x, y, z$ — элементарные высказывания; «$\\vee$» — соединительная, «$:$» — сильная дизъюнкция. Выполните операцию замены отрицаний (с. 81) для «парадокса» $\\sim xx \\vdash y$ и объясните, почему узкое понятие полноты § 9 не требует его доказуемости.\n\n## Ответ\n\nПолучается $ux \\vdash y$ — не тавтология (при $u = x = 1$, $y = 0$).\n\n## Решение\n\n1. $\\sim xx \\vdash y$: посылка — противоречие, операция (с. 81) применима.\n2. П. 1 (сильных дизъюнкций нет) и п. 2 (двойных отрицаний нет) ничего не меняют. Пп. 3–4: $x$ входит и без отрицания, и с отрицанием — $\\sim x$ заменяется новым высказыванием $u$. Получаем $x^{**} \\vdash y^{**}$: $ux \\vdash y$.\n3. $ux \\vdash y$ не тавтология: при $u = x = 1$, $y = 0$ посылка 1, заключение 0. Значит, ни в одной из систем она недоказуема.\n4. Узкое понятие полноты (с. 81) требует доказуемости только тех непарадоксальных тавтологий $x \\vdash y$, у которых $x^{**} \\vdash y^{**}$ доказуемы. Здесь $x^{**} \\vdash y^{**}$ недоказуема (и сама формула парадоксальна), поэтому доказуемости $\\sim xx \\vdash y$ «достаточная полнота» не требует.',
}


# ---------- ручные задачи ступеней 8–10 ----------
def hand_closure():
    cond = (f"{CONV} Пусть $T^s$ и $T^w$ — множества формул следования, доказуемых в $S^s$ и в $S^w$, — описаны критериями "
            "MT1 и MT3 § 2 (с. 72–73): тавтологичность и условие на множества $A$, $B$ элементарных высказываний посылки и "
            "заключения ($B \\subseteq A$ для $S^s$, $A \\cap B \\neq \\varnothing$ для $S^w$). Правила (с. 17): R1 — из "
            "$x \\vdash y$ и $y \\vdash z$ получить $x \\vdash z$; R2 — из $x \\vdash y$ и $x \\vdash z$ получить $x \\vdash yz$; "
            "R3 — из $x \\vdash y$ и $y \\vdash x$ получить $z \\vdash v$, где $v$ получено из $z$ заменой вхождений $x$ на $y$. "
            "Докажите или опровергните для каждого правила: множество $T^s$ (соответственно $T^w$) замкнуто относительно него. "
            "Сделайте вывод о правиле R1 в любой системе, теоремы которой — в точности $T^w$.")
    a1, b1 = x, C(x, W(y, N(y)))
    a2, b2 = C(x, W(y, N(y))), W(y, N(y))
    assert SY.provable("w", a1, b1) and SY.provable("w", a2, b2) and not SY.provable("w", a1, b2)
    ans = ("$T^s$ замкнуто относительно R1, R2, R3. $T^w$ замкнуто относительно R2 и R3, но не R1: $x \\vdash x(y \\vee \\sim y)$ "
           "и $x(y \\vee \\sim y) \\vdash y \\vee \\sim y$ лежат в $T^w$, а $x \\vdash y \\vee \\sim y$ — нет. Значит, в такой "
           "системе R1 не может действовать без ограничений.")
    sol = ("Тавтологичность: R1, R2 сохраняют её очевидно (если $x = 1$, то $y = 1$ и $z = 1$); в R3 $z$ и $v$ равнозначны, "
           "так как $x$ и $y$ равнозначны (обе формулы $x \\vdash y$, $y \\vdash x$ — тавтологии), — $z \\vdash v$ тавтология.\n"
           "$T^s$. R1: $C \\subseteq B \\subseteq A$. R2: $B \\subseteq A$, $C \\subseteq A$ дают $B \\cup C \\subseteq A$. R3: из "
           "$x \\vdash y$ и $y \\vdash x$ в $T^s$ множества элементарных высказываний $x$ и $y$ совпадают; $v$ отличается от $z$ "
           "лишь заменой вхождений $x$ на $y$, поэтому в $v$ нет элементарных высказываний, отсутствующих в $z$.\n"
           "$T^w$. R2: $A \\cap B \\neq \\varnothing$ и $B \\subseteq B \\cup C$ дают $A \\cap (B \\cup C) \\neq \\varnothing$. R3: если "
           "в $z$ есть элементарное высказывание вне заменяемых вхождений, оно есть и в $v$; иначе все элементарные "
           "высказывания $z$ — из вхождений $x$, а в $v$ на их месте стоят $y$ или $x$; у $x$ и $y$ есть общее элементарное "
           "высказывание ($x \\vdash y \\in T^w$) — оно общее у $z$ и $v$.\n"
           "R1 для $T^w$: $x \\vdash x(y \\vee \\sim y)$ — тавтология (при $x = 1$ обе части истинны), общее $x$; "
           "$x(y \\vee \\sim y) \\vdash y \\vee \\sim y$ — тавтология, общее $y$; обе в $T^w$ по MT3. Но $x \\vdash y \\vee \\sim y$: "
           "$A = \\{x\\}$, $B = \\{y\\}$ — по MT3 не в $T^w$. Если бы R1 было в такой системе правилом без ограничений, из двух "
           "теорем получилась бы нетеорема.")
    return card(9, "M", "transfer", "proof", "с. 17, 72–73, гл. 1, § 1; гл. 5, § 1–2", "общая теория дедукции, правила",
                cond, ans, sol, form="meta")


def hand_an7():
    lines = sn7_lines("x")
    cond = (f"{SNCONV} {SCH1} Классический случай получается присоединением $A^n7$ $\\sim x \\vdash \\urcorner x$ (с. 77); "
            "книга утверждает, что благодаря $A^n7$ доказуемы $\\sim x \\dashv\\vdash \\urcorner x$ и $\\sim\\urcorner x \\vdash x$. "
            "Докажите это, построив выводы в $S^s_n$ с $A^n7$, и докажите, что без $A^n7$ формулы $\\sim x \\vdash \\urcorner x$ "
            "и $\\sim\\urcorner x \\vdash x$ в $S^s_n$ недоказуемы.")
    ans = ("Строки 1–9 дают $\\urcorner x \\vdash \\sim x$ (T5) без $A^n7$; строка 10 — $A^n7$; вместе — $\\sim x \\dashv\\vdash "
           "\\urcorner x$; строки 11–13 — $\\sim\\urcorner x \\vdash x$. Без $A^n7$ обе формулы ложны при истинном $?x$ — по "
           "MT1 § 5 недоказуемы.")
    sol = (show(lines) + "\n\nНедоказуемость без $A^n7$: по главной интерпретации (с. 76) в состоянии «истинно $?x$» ложны "
           "$x$ и $\\urcorner x$; тогда $\\sim x$ истинно, а $\\urcorner x$ ложно, $\\sim\\urcorner x$ истинно, а $x$ ложно. Обе "
           "формулы не тавтологии, а по MT1 § 5 все теоремы $S^i_n$ — тавтологии (это и есть MT3 § 5 для "
           "$\\sim\\urcorner x \\vdash x$). В классическом случае состояния «истинно $?x$» нет, и вывод выше законен.")
    assert not check(lines, "Sn7") and check(lines, "Sn")
    return card(9, "M", "transfer", "proof", SRC5, "классический случай, метатеорема", cond, ans, sol, form="meta",
                system="S^s_n", case="classical")


def hand_mt3_6():
    comb = [C(x, y), N(x), C(x, N(y))]
    v = poss([x, y], comb)
    assert v[0] != "ext"
    cond = (f"{CONV} {D1TXT} MT1 § 6 (с. 77): если $y^1, \\ldots, y^m$ ($m \\geqslant 1$) не расширяют числа возможностей по "
            "$x^1, \\ldots, x^n$, то и $y^1, \\ldots, y^m, y^{m+1}$ не расширяют. MT2: каждое из $xy$, $\\sim xy$, $x\\sim y$, $x$, "
            "$y$, $\\sim x$, $\\sim y$ не расширяет числа возможностей по $x$ и $y$. Докажите MT3 § 6: любая комбинация из этих "
            "высказываний не расширяет числа возможностей по $x$ и $y$ (книга: «следует из MT1 и MT2»). Проверьте утверждение "
            f"на комбинации ${tex(comb[0])}$, ${tex(comb[1])}$, ${tex(comb[2])}$, указав доказуемую формулу D1.")
    ans = ("Индукция по числу членов: один член — MT2, добавление члена — MT1; порядок членов сильной дизъюнкции на значение не "
           f"влияет. Для примера: {v_short(v)}.")
    sol = ("1. Пусть дана комбинация $y^1, \\ldots, y^m$ из списка MT2. При $m = 1$ утверждение — MT2 (с. 78).\n"
           "2. Пусть для $m$ членов утверждение доказано. Комбинация из $m + 1$ членов получается добавлением $y^{m+1}$ к "
           "комбинации из $m$ членов, которая по предположению не расширяет числа возможностей; по MT1 не расширяет и новая.\n"
           "3. Порядок: $x : y : y^1 : \\ldots : y^m$ истинна, если и только если истинен ровно один член (с. 22), — значение не "
           "зависит от порядка членов; формулы D1 с переставленными членами — тавтологии одновременно и с теми же "
           "элементарными высказываниями, так что по MT1, MT5 § 2 доказуемы одновременно.\n"
           "4. Почему верна MT1 (с. 78): если $x^1 : \\ldots : y^m \\vdash x_1 : \\ldots : x_k$ доказуема, то либо доказуема формула "
           "с $y^{m+1}$ и частью $x_1, \\ldots, x_l$, либо $\\vdash \\sim(x^1 : \\ldots : y^m : y^{m+1})$; а доказуемость "
           "$\\vdash \\sim(\\ldots : y^m)$ сохраняется при добавлении члена.\n"
           f"5. Пример: {poss_text([x, y], comb, v)}.")
    return card(8, "M", "transfer", "proof", "с. 22, 72–73, 77–78, гл. 1, § 5; гл. 5, § 2, 6", "расширение возможностей",
                cond, ans, sol, form="meta", system="S^5")


def hand_mt5_3():
    rows, ext = [], []
    for signs in product((None, 0, 1), repeat=3):
        lits = [V(n) if s == 0 else N(V(n)) for n, s in zip("xyz", signs) if s is not None]
        if not lits:
            continue
        w = lits[0] if len(lits) == 1 else C(*lits)
        v = poss([x, y, z], [w])
        rows.append((w, v))
        if v[0] == "ext":
            ext.append(w)
    assert ext == [C(N(x), N(y), N(z))], [tex(w) for w in ext]
    pos = [(w, v) for w, v in rows if "('v'" in repr([t for t in (w[1] if w[0] == "conj" else (w,)) if t[0] == "v"])]
    cond = (f"{CONV} {D1TXT} По образцу MT5 § 6 (с. 78: любая конъюнкция из $x$, $y$ и их отрицаний не расширяет числа "
            "возможностей по $x$, $y$ и $\\sim x\\sim y$; а $\\sim x\\sim y$ расширяет число возможностей по $x$ и $y$, MT4) "
            "докажите: всякая конъюнкция $w$ из $x$, $y$, $z$ и их отрицаний (каждая буква — не более одного раза), отличная "
            "от $\\sim x\\sim y\\sim z$, не расширяет числа возможностей по $x$, $y$, $z$, а $\\sim x\\sim y\\sim z$ расширяет.")
    ans = ("Если в $w$ есть буква без отрицания — доказуема $x : y : z : w \\vdash x : y : z$; если $w$ — отрицания не всех букв "
           "и $t$ не входит в $w$ — доказуема $x : y : z : w \\vdash \\sim t$; для $\\sim x\\sim y\\sim z$ формула "
           "$x : y : z : w$ истинна при наборах $(0,0,0), (1,0,0), (0,1,0), (0,0,1)$, и ни одна формула D1 не проходит.")
    sol = ("1. Пусть в $w$ входит буква без отрицания, например $x$. Если $w = 1$, то и $x = 1$ — истинны два члена, "
           "$x : y : z : w = 0$. Значит, $x : y : z : w$ истинна лишь при $w = 0$ и ровно одном истинном из $x$, $y$, $z$; "
           "отсюда $x : y : z : w \\vdash x : y : z$ — тавтология без новых элементарных высказываний, доказуема (MT1 § 2), "
           "$k = 3$.\n"
           "2. Пусть $w$ — конъюнкция отрицаний не всех букв, и $t$ в $w$ не входит. Если $t = 1$ при истинной "
           "$x : y : z : w$, то остальные буквы ложны, их отрицания истинны и $w = 1$ — два истинных члена, противоречие. "
           "Значит, $x : y : z : w \\vdash \\sim t$ — тавтология, доказуема ($k = 1$).\n"
           "3. $w = \\sim x\\sim y\\sim z$: $x : y : z : w$ истинна, когда истинна ровно одна буква или ни одной; это не "
           "противоречие. Каждое $x_1 : \\ldots : x_k$ ложно хотя бы в одном из этих четырёх наборов (перебор всех 26 "
           "вариантов: при $k = 1$ буква или её отрицание, при $k = 2, 3$ — сильные дизъюнкции с разными буквами) — по D1 "
           "$w$ расширяет число возможностей.\n4. Проверка программой по всем 26 конъюнкциям: " +
           "; ".join(f"${tex(w)}$ — {v_short(v)}" for w, v in rows[:8]) + "; … (остальные — аналогично).")
    return card(9, "M", "transfer", "proof", "с. 72–73, 77–78, гл. 5, § 2, 6", "расширение возможностей, метатеорема",
                cond, ans, sol, form="meta", system="S^5")


def hand_contra():
    cond = (f"{CONV} {SEM8} Пусть посылка $x$ — не противоречие, а заключение $y$ — не тавтология. Докажите, что две "
            "формулировки — «приписав $x$ значение 1, мы вынуждены приписать $y$ значение 1» и «приписав $y$ значение 0, мы "
            "вынуждены приписать $x$ значение 0» — дают одно и то же значение $x \\vdash y$, и что это значение 1 тогда и "
            "только тогда, когда $x \\supset y$ — тавтология. Объясните, почему для таких формул интерпретация § 8 согласуется "
            "с прежней (с. 79), но всё же не служит определением условий истинности.")
    ans = ("Обе формулировки равносильны отсутствию набора значений с $x = 1$, $y = 0$, то есть тавтологичности $x \\supset y$; "
           "условия истинности «Из $x$ следует $y$» — наличие логического правила (с. 80).")
    sol = ("1. «Приписав $x$ значение 1, вынуждены приписать $y$ значение 1» — значит, среди наборов значений элементарных "
           "высказываний, где $x = 1$ (такие есть: $x$ не противоречие), нет ни одного с $y = 0$.\n"
           "2. «Приписав $y$ значение 0, вынуждены приписать $x$ значение 0» — среди наборов с $y = 0$ (они есть: $y$ не "
           "тавтология) нет ни одного с $x = 1$.\n"
           "3. Оба утверждения говорят одно: нет набора с $x = 1$ и $y = 0$. А $x \\supset y$ ложна ровно при $x = 1$, $y = 0$ "
           "(материальная импликация, с. 72), так что это и есть тавтологичность $x \\supset y$ — прежняя интерпретация "
           "(с. 79).\n"
           "4. Однако и она — «техническое» средство: высказывание «Из $x$ следует $y$» истинно, если и только если имеется "
           "логическое правило, согласно которому из $x$ следует $y$ (с. 80); например, $xy \\vdash x \\vee z$ имеет значение 1, "
           "но в $S^s$ правила для неё нет (MT1, с. 72: в заключение входит $z$).")
    assert K.taut2(C(x, y), W(x, z)) and not SY.provable("s", C(x, y), W(x, z))
    return card(8, "M", "transfer", "proof", "с. 72, 79–80, гл. 5, § 2, 8", "семантическая интерпретация, метатеорема",
                cond, ans, sol, form="meta")


def hand_311():
    cond = ("Формулы вида A (с. 74): $x \\vdash x : \\sim x$, $x \\vdash x \\vee \\sim x$, $\\sim xx \\vdash x$. Книга разбирает "
            "попытку построить более узкое исчисление, потребовав, например, недоказуемости формул вида $a \\vdash a : x$, "
            "$a \\vdash a : x^1 : \\ldots : x^n$ (с. 74). Исследуйте эту попытку: опишите, что пришлось бы исключить из $S^s$, "
            "приведите пример исключаемой сильной тавтологии и объясните по с. 74, почему, по автору, такие требования "
            "нельзя сформулировать априорно и почему формулы вида A — «законная плата за дедуктивный метод». Задача "
            "исследовательская: оценка выходит за пределы книги и должна быть отделена от её положений.")
    a, b = C(x, y), D(C(x, y), C(x, N(x)))
    assert SY.provable("s", a, b)
    ans = ("Критерии: показано, что требование задаётся только структурой формул; приведена сильная тавтология, которую оно "
           "исключило бы (например, $xy \\vdash xy : x\\sim x$ при $a := xy$, $x := x\\sim x$); изложены доводы с. 74 (длина ничего "
           "не даёт, вход в структуру — отказ от априорного понятия следования); собственная оценка отделена от книги.")
    sol = ("Эскиз.\n1. Требование (с. 74): сделать недоказуемыми $a \\vdash a : x$ и т. п. Это пришлось бы делать перечислением "
           "исключаемых формул или указанием их структурных признаков.\n"
           f"2. Пример: ${ftex(a, b)}$ — тавтология (при $xy = 1$ истинно ровно $xy$, так как $x\\sim x$ ложно), элементарные "
           "высказывания заключения есть в посылке — по MT1 § 2 (с. 72) теорема $S^s$; узкое исчисление должно её отвергнуть, "
           "хотя её доказуемость следует из тех же схем, что и прочих теорем.\n"
           "3. По автору, априорные требования, не зависящие от конкретной структуры формул, здесь сформулировать нельзя; "
           "отношения по длине ничего не дают, а входить в структуру формул — значит отказаться от априорного (интуитивного) "
           "понятия логического следования, не зависящего от вида формул и исчислений, т. е. снять проблему вообще (с. 74).\n"
           "4. Отсюда: формулы типа A — законная плата за дедуктивный метод и за полноту охвата формул определённого вида "
           "(с. 74). Собственная оценка студента (например, что исключения пришлось бы оговаривать для каждой новой схемы) "
           "должна быть отмечена как его рассуждение.")
    return card(10, "I", "transfer", "proof", "с. 72, 74, гл. 5, § 2–3", "парадоксы следования, исследование", cond, ans, sol,
                form="meta", system="S^s")


def HAND():
    return {"05.01-016": hand_closure(), "05.05-015": hand_an7(), "05.06-010": hand_mt3_6(), "05.06-015": hand_mt5_3(),
            "05.08-008": hand_contra(), "05.03-011": hand_311()}


# ---------- план ----------
S1SRC1 = "с. 72–73, гл. 5, § 1–2"


def plan():
    P = {}

    def put(sec, fns):
        for i, fn in enumerate(fns, 1):
            if fn is not None:
                P[f"05.{sec:02d}-{i:03d}"] = fn
    put(1, [lambda: c_crit_series(S1SRC1), c_s1_complete, lambda: c_crit_diag(S1SRC1), c_s1_deriv, lambda: c_nat(S1SRC1),
            c_s1_diag, lambda: c_crit_one(S1SRC1), c_s1_complete, lambda: c_crit_diag(S1SRC1), c_s1_deriv,
            lambda: c_nat(S1SRC1), c_s1_diag, lambda: c_crit_series(S1SRC1), c_s5_deriv, lambda: c_construct(S1SRC1), None])
    put(2, [c_crit_one, c_imp_diag, c_crit_series, c_separate, c_crit_diag, c_nat, c_s5_complete, c_s5_diag, c_crit_series,
            c_s5_deriv, c_separate, c_construct, None, None, None, c_crit_diag, c_nat, c_crit_one, c_s1_diag, c_crit_series,
            c_s1_complete])
    put(3, [c_s6_deriv, c_s6_complete, c_s6_diag, c_subst_B, c_ab, c_par_student, c_par_nat, c_s6_deriv])
    put(4, [c_intu_inst, c_s5_excl, lambda: c_s5_complete(src="с. 36, 67, 70, 73, 75, гл. 2, § 1; гл. 4, § 3; гл. 5, § 2, 4",
                                                          tags="интуиционистская логика, S5, дополнение"),
            lambda: c_s5_diag(src="с. 36, 67, 70, 73, 75, гл. 2, § 1; гл. 4, § 3; гл. 5, § 2, 4",
                              tags="интуиционистская логика, S5, диагностика"),
            c_intu_student, c_intu_nat, c_intu_six, None, None, c_intu_inst])
    put(5, [c_an_rec, c_sn_series, c_sn_complete, c_sn_student, c_sn_deriv, c_sn_diag, c_sn_nat, c_sn_table,
            lambda: c_sn_deriv(prefix=True), lambda: c_sn_series(names=("x", "y")), c_sn7_misuse, c_sn_complete,
            c_sn7_deriv, c_sn_diag, None, lambda: c_sn_deriv(kind="from"), c_sn_nat, lambda: c_sn_series(names=("x", "y")),
            lambda: c_sn_deriv(kind="second", prefix=True), c_sn_diag, None])
    put(6, [c_poss_series, c_poss_table, c_poss_diag, c_rel_series, c_rel_diag, c_s5_series, c_rel_nat, c_poss3,
            c_poss_diag, None, c_poss_series, c_rel_series, c_poss_construct, c_rel_diag, None, c_rel_nat, c_poss_table,
            c_poss_diag, c_poss3, None, None])
    put(7, [c_excl_series, lambda: dict(c_excl_series(classical=True), level=7), c_excl_diag, c_ext_E, c_ext_construct,
            lambda: c_sn_deriv(src=SRC7), lambda: c_sn_complete(src=SRC7), c_excl_series,
            lambda: c_sn_series(src="с. 76–77, 79, гл. 5, § 5, 7"), lambda: c_sn_table(src="с. 76–77, 79, гл. 5, § 5, 7")])
    put(8, [c_sem_series, c_sem_table, c_sem_diag, c_sem_E, c_sem_rule, lambda: c_sem_series(level=6), c_sem_nat_E, None,
            c_sem_transfer, c_sem_text, c_sem_rule])
    put(9, [c_op, c_op_complete, c_op_diag, c_op_appl_E, c_op, None, c_s21, c_op_req, c_op_diag, c_op, None, c_s21_E,
            c_op_req, c_op_complete, c_s21, None, None, c_op_diag, None, None, None])
    return P


def yaml_list(tags):
    return "[" + tags + "]"


def render(cid, c):
    sec = int(cid.split(".")[1].split("-")[0])
    extra = ""
    if c.get("system"):
        extra += f'system: "{c["system"]}"\n'
    if c.get("case"):
        extra += f'case: {c["case"]}\n'
    return (f'---\nid: "{cid}"\nchapter: 5\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\n'
            f'step: {c["step"]}\ncondition: {c.get("condition", "def")}\nform: {c["form"]}\nanswer: {c["answer"]}\n'
            f'source: "{c["source"]}"\n{extra}generated: true\ntags: {yaml_list(c["tags"])}\n---\n\n## Условие\n\n{c["cond"]}\n\n'
            f'## Ответ\n\n{c["ans"]}\n\n## Решение\n\n{c["sol"]}\n')


def render_hand(cid, c):
    return render(cid, c).replace("generated: true\n", "")


def main():
    texts = {}
    for cid, fn in plan().items():
        c = fn()
        assert not test_like(c["cond"]), (cid, c["cond"][:200])
        texts[cid] = render(cid, c)
    for cid, c in HAND().items():
        assert not test_like(c["cond"]), (cid, c["cond"][:200])
        texts[cid] = render_hand(cid, c)
    for cid, t in MOVED.items():
        texts[cid] = t + "\n"
    path = ROOT / "data" / "zadachi" / "05.md"
    parts = re.split(r"(\n=====\n)", path.read_text(encoding="utf-8"))
    done = set()
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(05\.\d\d-\d{3})"', chunk, re.M)
        if m and m.group(1) in texts:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            parts[i] = lead + texts[m.group(1)].rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
            done.add(m.group(1))
    assert done == set(texts), sorted(set(texts) - done)
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {len(done)}")


if __name__ == "__main__":
    main()
