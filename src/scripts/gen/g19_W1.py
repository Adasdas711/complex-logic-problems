#!/usr/bin/env python3
"""Серии раздела 19 («Логическая физика», 1972, гл. 3, § 1–10, с. 111–130), писатель W1.

Всё, что поддаётся механической проверке, считает программа:
  § 2  — эмпирическое тело относительно α и в ослабленном смысле (с. 112–113) по таблицам длин;
  § 3  — частные случаи превращения 1)–8) (с. 113) и условие ⊢ ~(x ∧ y);
  § 5  — выводы с терминами временного порядка по аксиомам C2, C4–C7 и определениям (с. 79, 82, 117)
         (машина lf_engine и генератор задач g18_hard);
  § 7  — X¹, X², X³ (с. 123), АФ³, АФ⁴, ТФ³ (с. 123–124) и схемы 1, 3 для различия ~ и ¬ (с. 125) на «линиях жизни»;
  § 10 — один и тот же индивид по условиям 1), 2) (с. 128); слабо / сильно тот же самый (с. 129–130).
Пишет gen19/19.<ПП>.md (generated: true); сборку черновиков делает merge19_W1.py.

Запуск: python3 src/scripts/gen/g19_W1.py
"""
import itertools
import random
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import lf_engine as E  # noqa: E402
import g18_hard as H  # noqa: E402

rnd = random.Random(19721128)
H.rnd.seed(19721129)
USED = set()
OUT = {}
LET = "абвгдеж"


def card(sec, lvl, typ, step, cond, form, ans, src, tags, U, A, R, case=None):
    key = U.strip()
    if key in USED:
        raise ValueError("повтор условия")
    USED.add(key)
    head = ["---", "chapter: 19", f"section: {sec}", f"level: {lvl}", f"type: {typ}", f"step: {step}",
            f"condition: {cond}", f"form: {form}", f"answer: {ans}", f'source: "{src}"']
    if case:
        head.append(f"case: {case}")
    head += ["generated: true", "tags: [" + ", ".join(tags) + "]", "---"]
    OUT.setdefault(sec, []).append(
        "\n".join(head) + f"\n\n## Условие\n\n{U.strip()}\n\n## Ответ\n\n{A.strip()}\n\n## Решение\n\n{R.strip()}\n")


def items(lst):
    return "\n".join(f"{LET[i]}) {s}" for i, s in enumerate(lst))


# ====================================================================== § 3 превращения

CASES = {1: "возникновение индивида", 2: "возникновение $sx$", 3: "уничтожение индивида", 4: "уничтожение $sx$",
         5: "потеря признака индивидом", 6: "приобретение признака индивидом",
         7: "уменьшение индивида по признаку $P$", 8: "увеличение индивида по признаку $P$"}

DEF3 = ("По § 3 (с. 113): пусть $sx$ — состояние эмпирического предмета $a$ в одно время, $sy$ — состояние того же "
        "индивида в другое, более позднее время, и при этом $\\vdash {\\sim}(x \\wedge y)$ (состояния исключают друг друга); "
        "тогда произошло превращение $sx \\Rightarrow sy$. Частные случаи: 1) $s\\urcorner E(a) \\Rightarrow sE(a)$ — "
        "возникновение $a$; 2) $s{\\sim}x \\Rightarrow sx$ — возникновение $sx$; 3) $sE(a) \\Rightarrow s\\urcorner E(a)$ — "
        "уничтожение $a$; 4) $sx \\Rightarrow s{\\sim}x$ — уничтожение $sx$; 5) $sP(a) \\Rightarrow s\\urcorner P(a)$ — потеря "
        "признака индивидом $a$; 6) $s\\urcorner P(a) \\Rightarrow sP(a)$ — приобретение признака; 7) $sP\\alpha(a) \\Rightarrow "
        "sP\\beta(a)$, где $\\alpha > \\beta$, — уменьшение $a$ по признаку $P$; 8) то же при $\\alpha < \\beta$ — увеличение.")

# (запись, номер случая или None, пояснение)
def change_pool():
    pool = []
    for a in "abc":
        pool.append((f"s\\urcorner E({a}) \\Rightarrow sE({a})", 1, f"вид $s\\urcorner E(a) \\Rightarrow sE(a)$ при $a = {a}$"))
        pool.append((f"sE({a}) \\Rightarrow s\\urcorner E({a})", 3, f"вид $sE(a) \\Rightarrow s\\urcorner E(a)$ при $a = {a}$"))
        for P in "PQ":
            pool.append((f"s{P}({a}) \\Rightarrow s\\urcorner {P}({a})", 5, f"вид 5) с признаком ${P}$ и индивидом ${a}$"))
            pool.append((f"s\\urcorner {P}({a}) \\Rightarrow s{P}({a})", 6, f"вид 6) с признаком ${P}$ и индивидом ${a}$"))
            pool.append((f"s{{\\sim}}{P}({a}) \\Rightarrow s{P}({a})", 2,
                         f"вид $s{{\\sim}}x \\Rightarrow sx$ при $x = {P}({a})$: отрицание внешнее (${{\\sim}}$), а не $\\urcorner$, поэтому это не 6)"))
            pool.append((f"s{P}({a}) \\Rightarrow s{{\\sim}}{P}({a})", 4,
                         f"вид $sx \\Rightarrow s{{\\sim}}x$ при $x = {P}({a})$: отрицание внешнее, поэтому это не 5)"))
        pool.append((f"s{{\\sim}}E({a}) \\Rightarrow sE({a})", 2, f"вид $s{{\\sim}}x \\Rightarrow sx$ при $x = E({a})$; это не 1): там $\\urcorner E$"))
        for u, v in [(7, 3), (12, 5), (40, 25), (9, 2)]:
            pool.append((f"sP{u}({a}) \\Rightarrow sP{v}({a})", 7, f"вид 7): ${u} > {v}$"))
            pool.append((f"sP{v}({a}) \\Rightarrow sP{u}({a})", 8, f"вид 8): ${v} < {u}$"))
    for x in ["(P(a) \\wedge Q(a))", "(P(b) \\vee Q(b))", "(a \\rightharpoonup b)"]:
        pool.append((f"s{{\\sim}}{x} \\Rightarrow s{x}", 2, f"вид $s{{\\sim}}x \\Rightarrow sx$ при $x = {x}$"))
        pool.append((f"s{x} \\Rightarrow s{{\\sim}}{x}", 4, f"вид $sx \\Rightarrow s{{\\sim}}x$ при $x = {x}$"))
    # не превращения
    for a in "abc":
        pool.append((f"sP({a}) \\Rightarrow sQ({a})", None,
                     f"$\\vdash {{\\sim}}(P({a}) \\wedge Q({a}))$ не имеет места: признаки $P$ и $Q$ разные, состояния не исключают друг друга"))
        pool.append((f"sP5({a}) \\Rightarrow sP5({a})", None, "состояния совпадают и не исключают друг друга"))
    pool.append(("s\\urcorner E(a) \\Rightarrow sE(b)", None, "это состояния разных индивидов $a$ и $b$, а превращение — смена состояний одного и того же индивида"))
    pool.append(("sP(a) \\Rightarrow s\\urcorner P(b)", None, "состояния разных индивидов $a$ и $b$"))
    pool.append(("sP3(a) \\Rightarrow sP8(b)", None, "состояния разных индивидов $a$ и $b$"))
    # убрать дубли
    seen, res = set(), []
    for t in pool:
        if t[0] not in seen:
            seen.add(t[0])
            res.append(t)
    return res


def case_text(n):
    return f"{n}) — {CASES[n]}" if n else "не превращение"


def g03():
    pool = change_pool()
    good = [p for p in pool if p[1]]
    bad = [p for p in pool if not p[1]]
    # серия: 6 пунктов, хотя бы 4 разных случая, один «не превращение», одна ловушка ~ / ¬
    for _ in range(500):
        its = rnd.sample(good, 5) + rnd.sample(bad, 1)
        rnd.shuffle(its)
        cs = {p[1] for p in its if p[1]}
        if len(cs) >= 4 and any("внешнее" in p[2] or "это не 1)" in p[2] for p in its):
            break
    U = (DEF3 + " Буквы $a, b, c$ — индивиды, $P, Q$ — признаки, числа — величины признака $P$. Для каждой записи "
         "установите, какой частный случай превращения она выражает; если запись не выражает превращения в смысле § 3, "
         "назовите нарушенное условие.\n\n" + items([f"${p[0]}$" for p in its]))
    A = "; ".join(f"{LET[i]}) {case_text(p[1])}" for i, p in enumerate(its)) + "."
    R = "\n".join(f"{LET[i]}) {p[2]} — {case_text(p[1])}." for i, p in enumerate(its))
    R += "\n\nОпределение превращения и список случаев 1)–8) — с. 113."
    card(3, 4, "R", "iso", "def", "sym", "short", "с. 113, гл. 3, § 3", ["изменение", "превращение"], U, A, R)

    # диагностика: таблица студента с двумя ошибками (перепутаны ~ и ¬ или 7/8)
    for _ in range(500):
        its = rnd.sample(good, 5)
        traps = [i for i, p in enumerate(its) if p[1] in (2, 4, 7, 8)]
        if len({p[1] for p in its}) >= 4 and len(traps) >= 2:
            break
    wrong = rnd.sample(traps, 2)
    claimed = []
    swap = {2: 6, 4: 5, 7: 8, 8: 7}
    for i, p in enumerate(its):
        claimed.append(swap[p[1]] if i in wrong else p[1])
    U = (DEF3 + " Буквы $a, b, c$ — индивиды, $P, Q$ — признаки, числа — величины признака $P$. Студент определил "
         "частные случаи превращений:\n\n" + items([f"${p[0]}$ — {case_text(c)}" for p, c in zip(its, claimed)])
         + "\n\nРовно две квалификации ошибочны. Найдите их, назовите пункт с. 113, который нарушен, и исправьте.")
    def why(p, c):
        if p[1] in (2, 4):
            return (f"в записи стоит внешнее отрицание ${{\\sim}}$, а случай {c}) требует $\\urcorner$; по форме это случай "
                    f"{p[1]}) — {CASES[p[1]]}")
        return f"случай {c}) требует обратного соотношения величин; {p[2]}, т. е. {CASES[p[1]]}"
    A = "; ".join(f"{LET[i]}) не {claimed[i]}), а {its[i][1]}) — {CASES[its[i][1]]}" for i in sorted(wrong)) + \
        " (с. 113). Остальные квалификации верны."
    R = "\n".join((f"{LET[i]}) Ошибка: {why(p, claimed[i])} (с. 113)." if i in wrong else f"{LET[i]}) Верно: {p[2]}.")
                  for i, p in enumerate(its))
    card(3, 6, "E", "vary", "def", "sym", "text", "с. 113, гл. 3, § 3", ["изменение", "превращение", "диагностика"], U, A, R)


# ====================================================================== § 5 выводы в терминах временного порядка

class TimeCmp(H.Cmp):
    """Термины порядка $>\\alpha$ с чтением «позже», «раньше», «одновременно» (с. 117, 123)."""
    WORDS = {">": "позже", "<": "раньше", "=": "одновременно с", "n>": "не позже"}

    def __init__(self):
        super().__init__("a")

    def nat(self, x):
        k, a, b = x
        if k == "=":
            return f"событие ${a}$ одновременно с событием ${b}$"
        return f"событие ${a}$ {self.WORDS[k]} события ${b}$"


HEAD5 = ("Буквы {T} обозначают события (воспринимаемые изменения, с. 118); $\\alpha$ — способ установления временного "
         "порядка. По § 5 (с. 117) простейшие временные термины «позже — раньше — одновременно» берутся из области значения "
         "знаков $> \\alpha$, $< \\alpha$, $= \\alpha$, и их отношения друг к другу таковы, как отношения этих знаков в общем "
         "случае. Читаем, как в § 7 (с. 123): $u > \\alpha v$ — «$u$ позже $v$», $u < \\alpha v$ — «$u$ раньше $v$», "
         "$u = \\alpha v$ — «$u$ одновременно с $v$», $u \\urcorner > \\alpha v$ — «$u$ не позже $v$». ")


def g05():
    C = TimeCmp()
    src = "с. 79, 82, 117, гл. 3, § 5"
    tags = ["пространственно-временные отношения", "порядок", "вывод"]
    # длинный вывод
    def make_long():
        r = H.cmp_problem("a", lo=8, hi=11)
        if not r:
            return None
        terms, prem, f, L, rules, how = r
        T = ", ".join(f"${t}$" for t in terms)
        P = "; ".join(C.nat(p) for p in prem)
        U = (HEAD5.format(T=T) + H.ref_text("a") + f" Известно: {P}. Запишите эти данные в символах и выведите, что "
             f"{C.nat(f)}. Укажите основание каждой строки (номера строк и аксиому или определение); перестановка членов "
             "конъюнкции и удаление члена конъюнкции подразумеваются.")
        A = f"${C.f(f)}$; вывод в {len(L)} строк (см. решение)."
        R = ("Запись данных: " + "; ".join(f"${C.f(p)}$" for p in prem) + ". Цель: $" + C.f(f) + "$.\n\n" + C.show(L))
        return U, A, R
    r = H.fresh(make_long)
    card(5, 5, "D", "iso", "def", "nat", "proof", src, tags, *r)
    # дополнение
    def make_complete():
        r = H.cmp_problem("a", lo=9, hi=12)
        if not r:
            return None
        terms, prem, f, L, rules, how = r
        inner = [i for i, x in enumerate(L, 1) if x[1] != "посылка" and i != len(L)]
        if len(inner) < 4:
            return None
        hide_f = set(rnd.sample(inner, 2))
        rest = [i for i, x in enumerate(L, 1) if x[1] != "посылка" and i not in hide_f]
        hide_w = set(rnd.sample(rest, min(3, len(rest))))
        T = ", ".join(f"${t}$" for t in terms)
        U = (HEAD5.format(T=T) + H.ref_text("a") + f" Из данных о порядке событий выведено, что {C.nat(f)}. В выводе "
             "пропущены формулы некоторых строк и основания некоторых шагов («…»). Восстановите их.\n\n"
             + C.show(L, hide_f, hide_w))
        parts = []
        for i in sorted(hide_f | hide_w):
            x = L[i - 1]
            s = f"{i} — " + (f"${C.f(x[0])}$" if i in hide_f else "")
            if i in hide_w:
                s += (" " if i in hide_f else "") + f"[{C.why(x[1], x[2])}]"
            parts.append(s)
        A = "; ".join(parts)
        R = ("Формулу пропущенной строки восстанавливаем по строкам, которые на неё ссылаются, и по её основанию. "
             "Полный вывод:\n\n" + C.show(L))
        return U, A, R
    r = H.fresh(make_complete)
    card(5, 4, "D", "complete", "def", "sym", "build", src, tags + ["дополнение"], *r)
    # две ошибки
    rules = H.cmp_rules(False)
    def make_err():
        r = H.cmp_problem("a", lo=9, hi=12)
        if not r:
            return None
        terms, prem, f, L, rules_, how = r
        inner = [i for i, x in enumerate(L, 1) if x[1] != "посылка"]
        bad = sorted(rnd.sample(inner, 2))
        L2 = list(L)
        for i in bad:
            fx, name, refs = L2[i - 1]
            alts = [(fx, n2, refs) for n2, ar, _ in rules if n2 != name and ar == len(refs)
                    and C.why(n2, refs) != C.why(name, refs)]
            rnd.shuffle(alts)
            for a in alts:
                L3 = list(L2)
                L3[i - 1] = a
                if i in E.check(L3, rules, prem):
                    L2 = L3
                    break
            else:
                return None
        if sorted(E.check(L2, rules, prem)) != bad:
            return None
        T = ", ".join(f"${t}$" for t in terms)
        U = (HEAD5.format(T=T) + H.ref_text("a") + f" Студент вывел, что {C.nat(f)}. В его выводе ровно два основания "
             "указаны неверно. Найдите обе ошибки, назовите, какая аксиома или какое определение на самом деле применены, "
             "и исправьте.\n\n" + C.show(L2))
        A = "; ".join(f"строка {i}: указано [{C.why(L2[i-1][1], L2[i-1][2])}], верно [{C.why(L[i-1][1], L[i-1][2])}]"
                      for i in bad) + " (с. 79, 82)."
        fn = {n: g for n, _, g in rules}
        expl = []
        for i in bad:
            fx, n2, refs2 = L2[i - 1]
            res = fn[n2](tuple(L2[q - 1][0] for q in refs2))
            why = (f"строки {', '.join(map(str, refs2))} не подходят под {C.why(n2, ())}" if res is None
                   else f"по [{C.why(n2, refs2)}] получилось бы ${C.f(res)}$, а не ${C.f(fx)}$")
            expl.append(f"Строка {i}: {why}. Верное основание — [{C.why(L[i-1][1], L[i-1][2])}].")
        R = "\n".join(expl) + "\n\nИсправленный вывод:\n\n" + C.show(L)
        return U, A, R
    r = H.fresh(make_err)
    card(5, 6, "E", "vary", "def", "sym", "text", src, tags + ["диагностика"], *r)
    # выведите или докажите, что нельзя (оба исхода)
    for want in (True, False):
        def make_open():
            r = H.cmp_problem("a", lo=6, hi=10)
            if not r:
                return None
            terms, prem, f, L, rules_, how = r
            if want:
                goal, model = f, None
            else:
                cands = []
                for a, b in itertools.permutations(terms, 2):
                    for k in (">", "n>", "="):
                        g = (k, a, b)
                        if g not in how:
                            m = H.num_model(prem, g, terms)
                            if m:
                                cands.append((g, m))
                if not cands:
                    return None
                goal, model = rnd.choice(cands)
            T = ", ".join(f"${t}$" for t in terms)
            P = "; ".join(C.nat(p) for p in prem) if want else "; ".join(f"${C.f(p)}$" for p in prem)
            U = (HEAD5.format(T=T) + H.ref_text("a") + f" Свидетели сообщили: {P}. Исследуйте, следует ли отсюда по "
                 f"аксиомам C2, C4–C7 и определениям, что {C.nat(goal)}: если следует — постройте вывод, если нет — "
                 "докажите, что вывода нет (можно сопоставить событиям номера моментов: $>$ — «больше», $=$ — «равно», "
                 "$\\urcorner >$ — «не больше»).")
            if want:
                A = f"Следует: ${C.f(goal)}$ (вывод в {len(L)} строк — см. решение)."
                R = "Запись данных: " + "; ".join(f"${C.f(p)}$" for p in prem) + ".\n\n" + C.show(L)
            else:
                vs = ", ".join(f"${t} = {model[t]}$" for t in terms)
                A = f"Не следует: при номерах моментов {vs} все данные верны, а ${C.f(goal)}$ неверно."
                R = (f"1. Сопоставим событиям номера моментов: {vs}; $>$ — «больше», $=$ — «равно», $\\urcorner >$ — "
                     "«не больше», $<$ — «меньше».\n2. При таком чтении верны аксиомы C2, C4–C7 и определения (с. 79, 82): "
                     "например, если $u > v$ и $v > w$, то $u > w$ (C4); $u = v$ тогда и только тогда, когда ни одно не "
                     "больше другого. Значит, всё выводимое из верных данных тоже верно.\n3. Данные верны: "
                     + "; ".join(f"${C.f(p)}$" for p in prem) + f".\n4. Цель ${C.f(goal)}$ неверна; будь она выводима, "
                     "она была бы верна (п. 2). Вывода нет.")
            return U, A, R
        r = H.fresh(make_open)
        card(5, 6, "C", "open", "def", "nat" if want else "sym", "proof", src,
             tags + ["открытый исход"], *r)


# ====================================================================== § 7 линии жизни

def sym(v):
    return {"E": "E", "~": "{\\sim}E", "n": "\\urcorner E", "?": "?E"}[v]


def word(v):
    return {"E": "существует", "~": "не существует", "n": "$\\urcorner E$", "?": "$?E$"}[v]


def neg(v):  # истинно ли ~E в момент с данным значением
    return v != "E"


def af3(line, nonc=None):
    """Нарушения АФ³: (α, β, γ) с γ < β < α, E в α, «не-E» в β и E (или не «не-E») в γ.
    nonc=None — классический случай (~E); nonc='n' — схема 1 (¬E вместо ~E в обоих местах)."""
    bad = []
    n = len(line)
    for al in range(n):
        if line[al] != "E":
            continue
        for be in range(al):
            okb = (line[be] == "n") if nonc else neg(line[be])
            if not okb:
                continue
            for ga in range(be):
                okg = (line[ga] == "n") if nonc else neg(line[ga])
                if not okg:
                    bad.append((al + 1, be + 1, ga + 1))
    return bad


def af4(line, nonc=None):
    bad = []
    n = len(line)
    for al in range(n):
        if line[al] != "E":
            continue
        for be in range(al + 1, n):
            okb = (line[be] == "n") if nonc else neg(line[be])
            if not okb:
                continue
            for ga in range(be + 1, n):
                okg = (line[ga] == "n") if nonc else neg(line[ga])
                if not okg:
                    bad.append((al + 1, be + 1, ga + 1))
    return bad


def tf3(line):
    bad = []
    n = len(line)
    for al in range(n):
        for ga in range(n):
            if line[al] == "E" and line[ga] == "E" and al != ga:
                for be in range(min(al, ga) + 1, max(al, ga)):
                    if line[be] != "E":
                        bad.append((al + 1, be + 1, ga + 1))
    return bad


def xcheck(line, t1, t2):
    """X¹, X², X³ (с. 123) при заявленных моментах возникновения t1 и исчезновения t2."""
    x1 = [i + 1 for i in range(t1 - 1) if line[i] == "E"]
    x2 = [i + 1 for i in range(t2, len(line)) if line[i] == "E"]
    x3 = [i + 1 for i in range(t1, t2 - 1) if line[i] != "E"]
    return x1, x2, x3


def tline(line):
    return "; ".join(f"{i + 1} — {word(v)}" for i, v in enumerate(line))


DEF7 = ("Моменты времени $1, 2, …, {n}$ упорядочены способом $\\alpha$: больший номер — позже (с. 123: $t^1 > t^2$ — "
        "«$t^1$ после $t^2$»); $Et(a)$ — «$a$ существует во время $t$» (с. 122). ")
AX7 = ("АФ³ (с. 123): если $a$ существует в $t^1$ и не существует в $t^2$ до $t^1$, то он не существует в любое время до "
       "$t^2$. АФ⁴: если $a$ существует в $t^1$ и не существует в $t^2$ после $t^1$, то он не существует в любое время после "
       "$t^2$. ТФ³ (с. 124): $\\vdash E\\alpha(a) \\wedge E\\gamma(a) \\to (\\forall\\beta)((((\\beta < \\alpha) \\wedge (\\gamma < "
       "\\beta)) \\vee ((\\beta > \\alpha) \\wedge (\\gamma > \\beta))) \\to E\\beta(a))$. ")


def g07():
    src = "с. 122–124, гл. 3, § 7"
    tags = ["время существования", "непрерывность"]
    # X¹–X³ при заявленных t¹, t²: серия из 4 летописей
    lines = []
    while len(lines) < 4:
        n = 8
        t1 = rnd.randint(2, 3)
        t2 = rnd.randint(t1 + 2, n - 1)
        line = ["E" if t1 <= i + 1 <= t2 else "~" for i in range(n)]
        kind = len(lines)
        if kind == 1:  # нарушение X¹
            line[rnd.randrange(0, t1 - 1)] = "E"
        elif kind == 2:  # нарушение X²
            line[rnd.randrange(t2, n)] = "E"
        elif kind == 3:  # нарушение X³
            line[rnd.randrange(t1, t2 - 1)] = "~"
        lines.append((line, t1, t2))
    rnd.shuffle(lines)
    its, ans, sol = [], [], []
    for k, (line, t1, t2) in enumerate(lines):
        x1, x2, x3 = xcheck(line, t1, t2)
        its.append(f"заявлено $t^1 = {t1}$, $t^2 = {t2}$; данные: {tline(line)}")
        viol = []
        if x1:
            viol.append(f"X¹ (существует в {', '.join(map(str, x1))} — до $t^1$)")
        if x2:
            viol.append(f"X² (существует в {', '.join(map(str, x2))} — после $t^2$)")
        if x3:
            viol.append(f"X³ (не существует в {', '.join(map(str, x3))} — между $t^1$ и $t^2$)")
        ans.append(f"{LET[k]}) " + ("X выполнено" if not viol else "нарушено " + "; ".join(viol)))
        sol.append(f"{LET[k]}) Моменты до {t1}: " + ("есть существование" if x1 else "$a$ не существует — X¹ выполнено")
                   + f"; моменты после {t2}: " + ("есть существование" if x2 else "не существует — X² выполнено")
                   + f"; моменты строго между {t1} и {t2}: " + ("есть несуществование" if x3 else "существует — X³ выполнено")
                   + ". " + ("Итог: X выполнено." if not viol else "Итог: нарушено " + "; ".join(viol) + "."))
    U = (DEF7.format(n=8) + "По с. 123 время существования эмпирического индивида локализовано и непрерывно (X): если "
         "$t^1$ — время возникновения $a$, $t^2$ — время его исчезновения, то X¹: в любое время $t^i < t^1$ $a$ не "
         "существует; X²: в любое время $t^i > t^2$ $a$ не существует; X³: в любое время $t^i$, такое что $t^2 > t^i$ и "
         "$t^i > t^1$, $a$ существует; $X \\equiv Df. X^1 \\wedge X^2 \\wedge X^3$. Для каждой летописи об индивиде $a$ "
         "проверьте X¹, X², X³ и назовите нарушенные утверждения с моментами.\n\n" + items(its))
    card(7, 4, "C", "iso", "def", "sym", "short", "с. 123, гл. 3, § 7", tags + ["X"], U, "; ".join(ans) + ".",
         "\n".join(sol) + "\n\nX¹, X², X³ и $X \\equiv Df. X^1 \\wedge X^2 \\wedge X^3$ — с. 123.")

    # АФ³, АФ⁴, ТФ³ на линиях: найти тройки
    its, ans, sol = [], [], []
    pats = []
    while len(pats) < 4:
        n = 7
        line = [rnd.choice("E~") for _ in range(n)]
        key = "".join(line)
        if key in [("".join(p)) for p in pats] or line.count("E") < 2:
            continue
        good = not tf3(line)
        if good and any(not tf3(p) for p in pats) and sum(not tf3(p) for p in pats) < 2 and len(pats) == 3:
            continue
        if not good and sum(not tf3(p) for p in pats) >= 3:
            continue
        pats.append(line)
    for k, line in enumerate(pats):
        b3, b4, bt = af3(line), af4(line), tf3(line)
        its.append(tline(line))
        if not bt:
            ans.append(f"{LET[k]}) все три выполнены")
            sol.append(f"{LET[k]}) Моменты существования идут подряд, между любыми двумя моментами существования нет "
                       "момента несуществования; тройки, нарушающей АФ³, АФ⁴ или ТФ³, нет.")
        else:
            a3, a4, t = rnd.choice(b3), rnd.choice(b4), rnd.choice(bt)
            ans.append(f"{LET[k]}) нарушены все три; АФ³: $\\alpha={a3[0]}, \\beta={a3[1]}, \\gamma={a3[2]}$; "
                       f"АФ⁴: $\\alpha={a4[0]}, \\beta={a4[1]}, \\gamma={a4[2]}$; ТФ³: $\\alpha={t[0]}, \\beta={t[1]}, \\gamma={t[2]}$")
            sol.append(f"{LET[k]}) АФ³: $a$ существует в {a3[0]}, не существует в {a3[1]} (раньше), но существует в "
                       f"{a3[2]} (ещё раньше). АФ⁴: существует в {a4[0]}, не существует в {a4[1]} (позже), но существует в "
                       f"{a4[2]} (ещё позже). ТФ³: существует в {t[0]} и {t[2]}, но не существует в {t[1]} между ними.")
    U = (DEF7.format(n=7) + AX7 + "Для каждой летописи об индивиде $a$ проверьте АФ³, АФ⁴ и ТФ³; для каждого нарушенного "
         "утверждения укажите моменты $\\alpha, \\beta, \\gamma$, на которых оно нарушается.\n\n" + items(its))
    card(7, 5, "C", "iso", "def", "sym", "short", src, tags + ["АФ³", "АФ⁴", "ТФ³"], U, "; ".join(ans) + ".",
         "\n".join(sol) + "\n\nФормулировки: АФ³, АФ⁴ — с. 123, ТФ³ — с. 124.")

    # неклассический случай: схемы 1 и 3 (с. 125) против АФ³, АФ⁴ с ~
    want = [  # (АФ³~ нарушено?, схема1 нарушена?) — подобрать разделяющие линии
        lambda l: bool(af3(l)) and not af3(l, "n"),
        lambda l: not af3(l) and bool(af3(l, "n")),
        lambda l: bool(af4(l, "n")) and not af4(l),
        lambda l: not af3(l) and not af4(l) and not af3(l, "n") and not af4(l, "n") and "?" in l and "n" in l,
    ]
    pats = []
    for w in want:
        for _ in range(5000):
            n = 6
            line = [rnd.choice("Enn??") for _ in range(n)]
            if line.count("E") >= 1 and w(line) and line not in pats:
                pats.append(line)
                break
    rnd.shuffle(pats)
    its, ans, sol = [], [], []
    for k, line in enumerate(pats):
        its.append(tline(line))
        res = []
        for name, b in [("АФ³", af3(line)), ("АФ⁴", af4(line)), ("схема 1", af3(line, "n")), ("схема 3", af4(line, "n"))]:
            b = sorted(b)
            res.append(f"{name} " + (f"нарушена ($\\alpha={b[0][0]}, \\beta={b[0][1]}, \\gamma={b[0][2]}$)" if b else "выполнена"))
        ans.append(f"{LET[k]}) " + ", ".join(res))
        sol.append(f"{LET[k]}) ${{\\sim}}E$ истинно в моменты " + (", ".join(str(i + 1) for i, v in enumerate(line) if v != "E") or "—")
                   + "; $\\urcorner E$ — в моменты " + (", ".join(str(i + 1) for i, v in enumerate(line) if v == "n") or "—")
                   + ". " + "; ".join(res) + ".")
    U = (DEF7.format(n=6) + "Неклассический случай: для каждого момента известно одно из $E$, $\\urcorner E$, $?E$; по "
         "определению гл. 2 (с. 66) $?E(a) \\equiv Df. {\\sim}E(a) \\wedge {\\sim}\\urcorner E(a)$, поэтому ${\\sim}E$ истинно "
         "и при $\\urcorner E$, и при $?E$. В символах (с. 123) АФ³: $\\vdash (E\\alpha(a) \\wedge (\\exists\\beta)((\\beta < "
         "\\alpha) \\wedge {\\sim}E\\beta(a)) \\to (\\forall\\gamma)((\\gamma < \\beta) \\to {\\sim}E\\gamma(a))$; АФ⁴ — то же с "
         "$>$ вместо $<$. С учётом различия ${\\sim}$ и $\\urcorner$ (с. 125) схема 1 есть АФ³, где ${\\sim}E\\beta(a)$ и "
         "${\\sim}E\\gamma(a)$ заменены на $\\urcorner E\\beta(a)$ и $\\urcorner E\\gamma(a)$; схема 3 — такая же замена в АФ⁴. "
         "Для каждой летописи проверьте АФ³, АФ⁴, схему 1 и схему 3; для нарушенных укажите $\\alpha, \\beta, \\gamma$.\n\n"
         + items(its))
    card(7, 7, "C", "transfer", "def", "sym", "short", "с. 66, 123, 125, гл. 3, § 7", tags + ["неклассический случай"],
         U, "; ".join(ans) + ".", "\n".join(sol) + "\n\nАФ³, АФ⁴ — с. 123; схемы 1, 3 — с. 125; $?E$ — с. 66.",
         case="nonclassical")

    # диагностика: таблица вердиктов с двумя ошибками (классический случай, X при t¹, t²)
    lines = []
    for kind in range(5):
        n = 8
        t1 = rnd.randint(2, 3)
        t2 = rnd.randint(t1 + 2, 7)
        line = ["E" if t1 <= i + 1 <= t2 else "~" for i in range(n)]
        if kind == 1:
            line[rnd.randrange(0, t1 - 1)] = "E"
        elif kind == 2:
            line[rnd.randrange(t2, n)] = "E"
        elif kind in (3, 4):
            line[rnd.randrange(t1, t2 - 1)] = "~"
        lines.append((line, t1, t2))
    rnd.shuffle(lines)
    truth = []
    for line, t1, t2 in lines:
        x1, x2, x3 = xcheck(line, t1, t2)
        truth.append("X¹" if x1 else "X²" if x2 else "X³" if x3 else "—")
    wrong = rnd.sample([i for i, t in enumerate(truth) if t != "—"], 2)
    claim = list(truth)
    alt = {"X¹": "X³", "X²": "X¹", "X³": "X²"}
    for i in wrong:
        claim[i] = alt[truth[i]]
    def show(c):
        return "нарушений нет" if c == "—" else f"нарушено {c}"
    its = [f"$t^1 = {t1}$, $t^2 = {t2}$; {tline(line)} — студент: {show(c)}" for (line, t1, t2), c in zip(lines, claim)]
    U = (DEF7.format(n=8) + "По с. 123: X¹ — в любое время до $t^1$ (возникновения $a$) $a$ не существует; X² — в любое "
         "время после $t^2$ (исчезновения) $a$ не существует; X³ — в любое время строго между $t^1$ и $t^2$ $a$ существует. "
         "Студент проверил летописи и указал нарушенные утверждения:\n\n" + items(its)
         + "\n\nРовно два вердикта ошибочны. Найдите их и исправьте, назвав нарушенное утверждение и момент.")
    A = "; ".join(f"{LET[i]}) не {claim[i]}, а {truth[i]}" for i in sorted(wrong)) + " (с. 123). Остальные вердикты верны."
    sol = []
    for k, (line, t1, t2) in enumerate(lines):
        x1, x2, x3 = xcheck(line, t1, t2)
        d = (f"существует в {x1[0]} до $t^1$ — X¹" if x1 else f"существует в {x2[0]} после $t^2$ — X²" if x2
             else f"не существует в {x3[0]} между $t^1$ и $t^2$ — X³" if x3 else "нарушений нет")
        sol.append(f"{LET[k]}) {d}; вердикт студента {'неверен' if k in wrong else 'верен'}.")
    card(7, 6, "E", "vary", "def", "sym", "text", "с. 123, гл. 3, § 7", tags + ["X", "диагностика"], U, A,
         "\n".join(sol) + "\n\nX¹, X², X³ — с. 123.")


# ====================================================================== § 10 тот же самый индивид

DEF10 = ("По § 10 (с. 128) индивиды $a$ и $b$ суть один и тот же индивид, если и только если 1) $(\\forall\\alpha)"
         "(\\forall\\beta)(a = \\beta b)$ — в любое время $a$ тождествен $b$ по пространственному положению относительно "
         "любого способа установления пространственного порядка, и 2) $(\\forall\\alpha)(E\\alpha(a) \\leftrightarrow "
         "E\\alpha(b))$ — времена их существования совпадают; $\\alpha$ — переменная для времени, $\\beta$ — для способов "
         "установления положения индивида в пространстве. ")


def same_case(kind):
    """Пара индивидов: моменты t¹..t³ (во все моменты хотя бы один существует), способы β¹, β²."""
    T = 3
    ex_a = ["E"] * T
    ex_b = ["E"] * T
    pos = {(t, b): True for t in range(T) for b in range(2)}
    if kind in ("2", "12"):
        t = rnd.randrange(T)
        if rnd.random() < 0.5:
            ex_a[t] = "~"
        else:
            ex_b[t] = "~"
    if kind in ("1", "12"):
        both = [t for t in range(T) if ex_a[t] == "E" and ex_b[t] == "E"]
        t = rnd.choice(both)
        pos[(t, rnd.randrange(2))] = False
    for t in range(T):
        if ex_a[t] != "E" or ex_b[t] != "E":
            for b in range(2):
                pos.pop((t, b), None)
    return ex_a, ex_b, pos


def same_eval(ex_a, ex_b, pos):
    v1 = [(t, b) for (t, b), ok in sorted(pos.items()) if not ok]
    v2 = [t for t in range(len(ex_a)) if (ex_a[t] == "E") != (ex_b[t] == "E")]
    return v1, v2


def same_text(ex_a, ex_b, pos):
    parts = []
    for t in range(len(ex_a)):
        s = f"в $t^{t+1}$: $a$ {'существует' if ex_a[t]=='E' else 'не существует'}, $b$ {'существует' if ex_b[t]=='E' else 'не существует'}"
        if (t, 0) in pos:
            s += ", " + ", ".join(f"$a {'=' if pos[(t, b)] else '\\urcorner ='} \\beta^{b+1} b$" for b in range(2))
        parts.append(s)
    return "; ".join(parts)


def same_verdict(v1, v2):
    if not v1 and not v2:
        return "один и тот же индивид"
    r = []
    if v1:
        r.append("нарушено 1) (" + ", ".join(f"$t^{t+1}$, $\\beta^{b+1}$" for t, b in v1) + ")")
    if v2:
        r.append("нарушено 2) (" + ", ".join(f"$t^{t+1}$" for t in v2) + ")")
    return "не один и тот же индивид: " + "; ".join(r)


def g10():
    src = "с. 128, гл. 3, § 10"
    tags = ["тот же самый индивид"]
    kinds = ["0", "1", "2", "12"]
    rnd.shuffle(kinds)
    its, ans, sol = [], [], []
    for k, kind in enumerate(kinds):
        ex_a, ex_b, pos = same_case(kind)
        v1, v2 = same_eval(ex_a, ex_b, pos)
        its.append(same_text(ex_a, ex_b, pos))
        ans.append(f"{LET[k]}) {same_verdict(v1, v2)}")
        sol.append(f"{LET[k]}) Условие 1): " + ("во все моменты, когда оба существуют, $a = \\beta b$ для $\\beta^1$ и $\\beta^2$"
                   if not v1 else "в " + ", ".join(f"$t^{t+1}$ относительно $\\beta^{b+1}$" for t, b in v1) + " $a \\urcorner = \\beta b$")
                   + ". Условие 2): " + ("в каждый момент оба существуют или оба не существуют" if not v2
                   else "в " + ", ".join(f"$t^{t+1}$" for t in v2) + " существует лишь один из них, $E\\alpha(a) \\leftrightarrow E\\alpha(b)$ ложно")
                   + f". Итог: {same_verdict(v1, v2)}.")
    U = (DEF10 + "Моменты $t^1, t^2, t^3$ — все рассматриваемые времена; $\\beta^1, \\beta^2$ — все рассматриваемые способы; "
         "$a \\urcorner = \\beta b$ — «$a$ не тождествен $b$ по положению относительно $\\beta$». Для каждой пары протоколов "
         "проверьте условия 1) и 2) и сделайте вывод; при нарушении назовите условие и момент.\n\n" + items(its))
    card(10, 5, "C", "iso", "def", "sym", "short", src, tags, U, "; ".join(ans) + ".",
         "\n".join(sol) + "\n\nОпределение — с. 128.")

    # диагностика: ровно две ошибки
    kinds = ["0", "1", "2", "12", "1"]
    rnd.shuffle(kinds)
    data = []
    for kind in kinds:
        ex_a, ex_b, pos = same_case(kind)
        data.append((ex_a, ex_b, pos, same_eval(ex_a, ex_b, pos)))
    verd = ["тот же" if not v[0] and not v[1] else "разные" for *_, v in data]
    wrong = rnd.sample(range(5), 2)
    claim = [("разные" if verd[i] == "тот же" else "тот же") if i in wrong else verd[i] for i in range(5)]
    def say(c):
        return "один и тот же индивид" if c == "тот же" else "не один и тот же индивид"
    its = [same_text(a, b, p) + f" — студент: {say(c)}" for (a, b, p, _), c in zip(data, claim)]
    U = (DEF10 + "Моменты $t^1, t^2, t^3$ — все рассматриваемые времена; $\\beta^1, \\beta^2$ — все рассматриваемые способы. "
         "Студент сделал выводы по протоколам:\n\n" + items(its) + "\n\nРовно два вывода ошибочны. Найдите их и исправьте, "
         "назвав условие определения (1 или 2), которое студент не учёл или применил неверно.")
    A = "; ".join(f"{LET[i]}) " + same_verdict(*data[i][3]) if verd[i] == "разные" else f"{LET[i]}) один и тот же индивид: 1) и 2) выполнены"
                  for i in sorted(wrong)) + " (с. 128). Остальные выводы верны."
    sol = []
    for k, (a, b, p, (v1, v2)) in enumerate(data):
        sol.append(f"{LET[k]}) {same_verdict(v1, v2)}; вывод студента {'неверен' if k in wrong else 'верен'}.")
    card(10, 6, "E", "vary", "def", "sym", "text", src, tags + ["диагностика"], U, A, "\n".join(sol) + "\n\nОпределение — с. 128.")

    # структуры: слабо / сильно (порядок) / сильно с интервалами
    src2 = "с. 128–130, гл. 3, § 10"
    base = sorted(rnd.sample(range(1, 10), 3))
    rows = {}
    def rel(p, i, j):
        return ">" if p[i] > p[j] else "<" if p[i] < p[j] else "="
    def classify(pa, pb, match):
        if match is None:
            return "не тот же"
        if any(rel(pa, i, j) != rel(pb, match[i], match[j]) for i in range(3) for j in range(3)):
            return "слабо"
        if any(abs(pa[i] - pa[j]) != abs(pb[match[i]] - pb[match[j]]) for i in range(3) for j in range(3)):
            return "сильно-порядок"
        return "сильно-интервалы"
    variants = []
    shift = rnd.randint(1, 3)
    variants.append(("тот же порядок и те же интервалы", [x + shift for x in base], [0, 1, 2]))
    variants.append(("тот же порядок, другой интервал", [base[0], base[1], base[2] + rnd.randint(2, 4)], [0, 1, 2]))
    variants.append(("порядок нарушен", [base[1], base[0], base[2]], [0, 1, 2]))
    variants.append(("нет соответствия", base[:2] + [base[2] + 1], None))
    rnd.shuffle(variants)
    names = ["B", "C", "D", "F"]
    its, ans, sol = [], [], []
    for k, ((_, pb, match), nm) in enumerate(zip(variants, names)):
        if match is None:
            L = nm.lower()
            its.append(f"структура ${nm}$ из ${L}^1, {L}^2, {L}^3$ с координатами {pb[0]}, {pb[1]}, {pb[2]}; ни один из ${L}^i$ не есть "
                       "один и тот же индивид ни с одним $a^k$")
            ans.append(f"{LET[k]}) ни в каком смысле не та же")
            sol.append(f"{LET[k]}) Нарушен п. 2 (с. 129): для $a^1$ нет индивида структуры ${nm}$, который был бы тем же "
                       "самым индивидом; значит, ни слабо, ни сильно.")
            continue
        r = classify(base, pb, match)
        L = nm.lower()
        its.append(f"структура ${nm}$ из ${L}^1, {L}^2, {L}^3$ с координатами {pb[0]}, {pb[1]}, {pb[2]}; ${L}^i$ и $a^i$ — "
                   "один и тот же индивид ($i = 1, 2, 3$)")
        if r == "слабо":
            i, j = next((i, j) for i in range(3) for j in range(3) if rel(base, i, j) != rel(pb, i, j))
            ans.append(f"{LET[k]}) слабо та же; сильно — нет")
            sol.append(f"{LET[k]}) Пп. 1–2 выполнены (по три индивида, попарно одни и те же) — слабо та же. Но $a^{i+1} "
                       f"{rel(base, i, j)} \\alpha a^{j+1}$, а ${L}^{i+1} {rel(pb, i, j)} \\alpha {L}^{j+1}$ — отношения порядка не "
                       "тождественны, поэтому сильно (и с интервалами) не та же.")
        elif r == "сильно-порядок":
            i, j = next((i, j) for i in range(3) for j in range(3) if abs(base[i] - base[j]) != abs(pb[i] - pb[j]))
            ans.append(f"{LET[k]}) слабо и сильно (по порядку) та же; с учётом интервалов — нет")
            sol.append(f"{LET[k]}) Пп. 1–2 выполнены; порядок соответствующих пар тот же. Интервал между $a^{i+1}$ и "
                       f"$a^{j+1}$ равен {abs(base[i]-base[j])}, между ${L}^{i+1}$ и ${L}^{j+1}$ — {abs(pb[i]-pb[j])}: с учётом "
                       "размера интервалов не та же.")
        else:
            ans.append(f"{LET[k]}) та же во всех трёх смыслах")
            sol.append(f"{LET[k]}) Пп. 1–2 выполнены; порядок пар тот же; все координаты больше на {shift}, поэтому "
                       "разности координат, т. е. интервалы между соответствующими индивидами, те же — та же и с учётом интервалов.")
    U = ("По § 10 (с. 129–130): для того чтобы структуры $A$ (из $a^1, …, a^n$) и $B$ (из $b^1, …, b^m$) считать одной и той "
         "же, необходимо: 1) $n = m$; 2) для каждого $a^i$ есть $b^k$, такой что $a^i$ и $b^k$ — один и тот же индивид, и "
         "обратно. «Слабо тот же самый» — достаточно пп. 1–2; «сильно тот же самый» — ещё п. 3: тождество отношений между "
         "соответствующими парами индивидов; сильный вариант можно ограничить предикатами порядка, а можно потребовать ещё "
         "совпадения соответствующих интервалов. Структура $A$ образована $a^1, a^2, a^3$; их координаты относительно "
         f"способа $\\alpha$ (число — протяжённость интервала от общей точки отсчёта; длина интервала между индивидами — "
         f"разность координат; учитываются только интервалы между индивидами структуры) равны {base[0]}, {base[1]}, {base[2]}; больше координата — дальше по $\\alpha$. Для каждой "
         "структуры установите, является ли она той же самой, что $A$, в слабом смысле, в сильном смысле на уровне "
         "предикатов порядка и в сильном смысле с учётом интервалов.\n\n" + items(its))
    card(10, 6, "C", "iso", "def", "sym", "short", src2, tags + ["структуры"], U, "; ".join(ans) + ".",
         "\n".join(sol) + "\n\nКритерии и пример рис. 8 — с. 129–130.")


# ====================================================================== § 2 тела

def g02():
    src = "с. 112–113, гл. 3, § 2"
    j = rnd.randrange(3)
    def mk(kind):
        v = [rnd.choice([1, 2, 3, 5, 7]) for _ in range(3)]
        if kind == "j0":
            v[j] = 0
        elif kind == "other0":
            v[rnd.choice([i for i in range(3) if i != j])] = 0
        elif kind == "all0":
            v = [0, 0, 0]
        elif kind == "only_j":
            v = [0, 0, 0]
            v[j] = rnd.choice([2, 3, 5])
        return v
    kinds = ["all", "j0", "other0", "only_j", rnd.choice(["all", "all0"])]
    rnd.shuffle(kinds)
    objs = [mk(k) for k in kinds]
    names = ["a", "b", "c", "d", "e"]
    its, ans, sol = [], [], []
    for k, (nm, v) in enumerate(zip(names, objs)):
        its.append(f"${nm}$: $l\\{{{nm}, \\alpha^1\\}} = {v[0]}$, $l\\{{{nm}, \\alpha^2\\}} = {v[1]}$, $l\\{{{nm}, \\alpha^3\\}} = {v[2]}$")
        rel = v[j] > 0
        weak = all(x > 0 for x in v)
        ans.append(f"{LET[k]}) {'тело' if rel else 'не тело'} отн. $\\alpha^{j+1}$, {'тело' if weak else 'не тело'} в ослабленном смысле")
        sol.append(f"{LET[k]}) $l\\{{{nm}, \\alpha^{j+1}\\}} = {v[j]}$ — " + ("$> 0$, тело относительно $\\alpha^{" + str(j+1) + "}$"
                   if rel else "$= 0$, по следствию с. 112 не тело относительно $\\alpha^{" + str(j+1) + "}$")
                   + "; " + ("все три длины больше нуля — тело в ослабленном смысле" if weak else
                   "есть способ с нулевой длиной — не тело в ослабленном смысле (требуется $l\\{a, \\alpha\\} > 0$ для любого $\\alpha$)") + ".")
    U = ("По § 2 (с. 112–113): $a$ есть эмпирическое тело относительно $\\alpha$, если и только если $a$ есть эмпирический "
         "предмет, такой что $l\\{a, \\alpha\\} > 0$ ($l\\{a, \\alpha\\}$ — «длина $a$ относительно $\\alpha$»); следствие: если "
         "$l\\{a, \\alpha\\} = 0$, то $a$ не есть эмпирическое тело относительно $\\alpha$. Ослабленное определение: $a$ есть "
         "эмпирическое тело, если и только если $a$ — эмпирический предмет и для любого $\\alpha$ верно $l\\{a, \\alpha\\} > 0$. "
         "Эмпирические предметы $a, …, e$ измерены тремя способами установления пространственного порядка $\\alpha^1, "
         f"\\alpha^2, \\alpha^3$ (других способов не рассматриваем). Для каждого предмета установите, есть ли он тело "
         f"относительно $\\alpha^{j+1}$ и тело в ослабленном смысле.\n\n" + items(its))
    card(2, 4, "R", "iso", "def", "sym", "short", src, ["эмпирические тела", "длина"], U, "; ".join(ans) + ".",
         "\n".join(sol) + "\n\nОпределения и следствие — с. 112–113.")


def main():
    g02()
    g03()
    g05()
    g07()
    g10()
    out = ROOT / "gen19"
    out.mkdir(exist_ok=True)
    for sec, cards in OUT.items():
        (out / f"19.{sec:02d}.md").write_text("\n=====\n\n".join(cards), encoding="utf-8")
        print(f"§ {sec}: {len(cards)}")


if __name__ == "__main__":
    main()
