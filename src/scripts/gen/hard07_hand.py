"""Ручные задачи гл. 7 ступеней 8–9 для hard07.py. Выводы в решениях проверяются q7.check, примеры — моделью q7
(проверки — в конце модуля, выполняются при импорте)."""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts" / "gen"))
import q7  # noqa: E402
import hard07_der as H  # noqa: E402
import hard07_b as B  # noqa: E402
from hard07_a import CONV, card  # noqa: E402
from q7 import ALL, C, EL, EX, N, NALL, QALL, V, W, ftex  # noqa: E402

x, y = V("x"), V("y")
ab, ac, ad = EL("a", "b"), EL("a", "c"), EL("a", "d")


def H_(level, typ, step, src, tags, cond, ans, sol, system="S^s_cq", form="meta", answer="proof"):
    c = card(level, typ, step, answer, src, tags, cond, ans, sol, form=form, system=system)
    c["generated"] = False
    return c


# ---- § 2, № 12: T17, T18 и T14 из аксиом
T17 = [(x, EX("a", x), "A2"), (EX("a", x), ALL("a", x), "A5"), (x, ALL("a", x), ("tr", 1, 2))]
T18 = [(EX("a", x), ALL("a", x), "A5"), (ALL("a", x), x, "A1"), (EX("a", x), x, ("tr", 1, 2))]
u = ALL("a", ALL("b", x))
T14 = [(ALL("b", x), x, "A1"), (u, ALL("a", x), ("R1", 1)), (u, ALL("b", u), "T17"),
       (ALL("b", u), ALL("b", ALL("a", x)), ("R1", 2)), (u, ALL("b", ALL("a", x)), ("tr", 3, 4))]
# x — метабуква: условия «a, b не входят свободно» проверяем на примере x = (a ← b)
for L_, allowed in ((T17, ["A2", "A5"]), (T18, ["A1", "A5"])):
    sb = {"x": EL("c", "d"), "@a": "a", "@b": "b"}
    inst = [(q7.build_inst((p, q, []), sb)[0] if isinstance(p, tuple) else p, q7.build_inst((p, q, []), sb)[1], w)
            for p, q, w in L_]
    assert not q7.check(inst, allowed), q7.check(inst, allowed)
inst14 = [tuple(q7.build_inst((p, q, []), {"x": ab, "@a": "a", "@b": "b"})) + (w,) for p, q, w in T14]
assert not q7.check(inst14, ["A1", "T17"]), q7.check(inst14, ["A1", "T17"])

HAND = {}
HAND["07.02-012"] = H_(8, "M", "vary", "с. 99–100, 104, гл. 7, § 2, 6", "кванторы, вывод, метатеорема",
    f"{CONV} В § 6 (с. 104) теоремные схемы T17 $x \\vdash (\\forall a)x$ и T18 $(\\exists a)x \\vdash x$ (где $a$ не входит "
    "свободно в $x$) снабжены ссылками [A2] и [A1], а T14 $(\\forall a)(\\forall b)x \\vdash (\\forall b)(\\forall a)x$ — "
    "ссылкой [A1, R1, T17]. По этим указаниям выведите T17 и T18 из аксиомных схем $S^s_{cq}$ (с. 99–100), затем T14, и "
    "укажите, в каком шаге каждого вывода используется условие на свободные вхождения и почему без него вывод "
    "невозможен.",
    "T17: A2, A5 (условие — в A5), R1 $S^s$; T18: A5, A1, R1 $S^s$; T14: A1, R1, T17 (для $b$, не входящего свободно в "
    "$(\\forall a)(\\forall b)x$), R1, R1 $S^s$.",
    "T17:\n\n" + H.show(T17) + "\n\nT18:\n\n" + H.show(T18) + "\n\nT14 (обозначим $u = (\\forall a)(\\forall b)x$):\n\n"
    + H.show(T14) + "\n\n"
    "Условие нужно в шаге A5: $(\\exists a)x \\vdash (\\forall a)x$ — аксиома лишь при $a$, не входящем свободно в $x$ "
    "(с. 99). В T14 оно выполнено автоматически: в $u = (\\forall a)(\\forall b)x$ все вхождения $b$ связаны (D4–D5), "
    "поэтому T17 применима к $u$ с термином $b$. Без условия получилась бы, например, $(a \\leftarrow b) \\vdash (\\forall a)"
    "(a \\leftarrow b)$, а она не тавтология (при двух отмеченных терминах для $a$ по п. 1 D2 § 7 форма $(1a \\leftarrow b)"
    "(2a \\leftarrow b) \\vdash (1a \\leftarrow b)(2a \\leftarrow b)$ — тавтология, но при замыкании $(\\exists a)$ форма "
    "$(1a \\leftarrow b) \\vee (2a \\leftarrow b) \\vdash (1a \\leftarrow b)(2a \\leftarrow b)$ ложна при $(1a \\leftarrow b) = 1$, "
    "$(2a \\leftarrow b) = 0$).")
assert q7.countermodel(ab, ALL("a", ab)) is not None

HAND["07.02-020"] = H_(9, "M", "open", "с. 99–100, гл. 7, § 2", "кванторы, метатеорема, индукция",
    f"{CONV} Докажите индукцией по $n \\geq 1$ для любых терминов $a^1, \\ldots, a^n$ и любого высказывания $x$: (1) в "
    "$S^s_{cq}$ доказуемы $(\\forall a^1)\\ldots(\\forall a^n)x \\vdash x$ и $x \\vdash (\\exists a^1)\\ldots(\\exists a^n)x$; "
    "(2) если $x \\vdash y$ доказуема, то доказуема $(K^1a^1)\\ldots(K^na^n)x \\vdash (K^1a^1)\\ldots(K^na^n)y$ при любых "
    "$K^i \\in \\{\\forall, \\exists\\}$; (3) выведите отсюда, что $(\\forall a^1)\\ldots(\\forall a^n)x \\vdash (\\exists "
    "a^1)\\ldots(\\exists a^n)x$ доказуема.",
    "(1) база — A1, A2; шаг — A1 (A2) и R1 $S^s$; (2) база — R1 или R2; шаг — R1 или R2 к доказанной формуле; (3) из (1): "
    "$\\ldots \\vdash x \\vdash \\ldots$ и R1 $S^s$.",
    "(1) $n = 1$: A1, A2 (с. 99). Шаг: пусть $(\\forall a^2)\\ldots(\\forall a^{n+1})x \\vdash x$ доказуема. По A1 "
    "$(\\forall a^1)z \\vdash z$ при $z = (\\forall a^2)\\ldots(\\forall a^{n+1})x$; по R1 $S^s$ (транзитивность, с. 17) — "
    "$(\\forall a^1)\\ldots(\\forall a^{n+1})x \\vdash x$. Для $\\exists$: по предположению $x \\vdash (\\exists a^2)\\ldots"
    "(\\exists a^{n+1})x = z'$, по A2 $z' \\vdash (\\exists a^1)z'$, транзитивность.\n"
    "(2) $n = 1$: R1 или R2 (с. 100). Шаг: из $x \\vdash y$ по предположению $(K^2a^2)\\ldots x \\vdash (K^2a^2)\\ldots y$; "
    "R1 (если $K^1 = \\forall$) или R2 (если $\\exists$) навешивает $(K^1a^1)$ на обе части.\n"
    "(3) $(\\forall a^1)\\ldots(\\forall a^n)x \\vdash x$ и $x \\vdash (\\exists a^1)\\ldots(\\exists a^n)x$ по (1); "
    "R1 $S^s$ даёт искомое (при $n = 1$ это T27, с. 104).")

# ---- § 6, № 28: T22 по указанию книги [T19, T20, A6, A7]
HAND["07.06-028"] = H_(8, "M", "vary", "с. 99–104, гл. 7, § 2, 6", "кванторы, теоремные схемы, метатеорема",
    f"{CONV} По указанию книги (с. 104: T22 [T19, T20, A6, A7]) докажите T22 $(\\exists a)(x \\vee y) \\vdash (\\exists a)x "
    "\\vee (\\exists a)y$. Разрешены A1–A7, R1, R2, T19, ссылки на $S^s$ и MT2 § 6 (с. 102: если $x \\vdash y$ доказуема и "
    "множества элементарных высказываний $x$ и $y$ совпадают, то $\\sim y \\vdash \\sim x$ доказуема). Проверьте условие "
    "MT2 при каждом применении.",
    "Доказывается $\\sim((\\exists a)x \\vee (\\exists a)y) \\vdash \\sim(\\exists a)(x \\vee y)$ через $(\\forall a)\\sim x"
    "(\\forall a)\\sim y$, T19, R1, A6, A7, затем MT2 и снятие двойных отрицаний.",
    "1. $\\sim\\sim x \\vdash x$ [$S^s$]; R2: $(\\exists a)\\sim\\sim x \\vdash (\\exists a)x$; MT2 (в обеих частях "
    "элементарные высказывания $x$): $\\sim(\\exists a)x \\vdash \\sim(\\exists a)\\sim\\sim x$.\n"
    "2. A7 при $x$ := $\\sim x$: $\\sim(\\exists a)\\sim\\sim x \\vdash (\\forall a)\\sim x$; транзитивность: "
    "$\\sim(\\exists a)x \\vdash (\\forall a)\\sim x$. Так же $\\sim(\\exists a)y \\vdash (\\forall a)\\sim y$.\n"
    "3. $\\sim((\\exists a)x \\vee (\\exists a)y) \\vdash \\sim(\\exists a)x\\sim(\\exists a)y$ [$S^s$]; по шагу 2, $S^s$ и "
    "R2 $S^s$: $\\sim((\\exists a)x \\vee (\\exists a)y) \\vdash (\\forall a)\\sim x(\\forall a)\\sim y$.\n"
    "4. T19: $(\\forall a)\\sim x(\\forall a)\\sim y \\vdash (\\forall a)(\\sim x\\sim y)$; $\\sim x\\sim y \\vdash \\sim(x \\vee y)$ "
    "[$S^s$] и R1: $(\\forall a)(\\sim x\\sim y) \\vdash (\\forall a)\\sim(x \\vee y)$.\n"
    "5. A6: $(\\forall a)\\sim(x \\vee y) \\vdash \\sim(\\exists a)\\sim\\sim(x \\vee y)$. Из $x \\vee y \\vdash \\sim\\sim(x "
    "\\vee y)$ [$S^s$] по R2 и MT2 (элементарные высказывания совпадают): $\\sim(\\exists a)\\sim\\sim(x \\vee y) \\vdash "
    "\\sim(\\exists a)(x \\vee y)$.\n"
    "6. Транзитивность 3–5: $\\sim((\\exists a)x \\vee (\\exists a)y) \\vdash \\sim(\\exists a)(x \\vee y)$. Элементарные "
    "высказывания в обеих частях — элементарные высказывания $x$ и $y$; по MT2 $\\sim\\sim(\\exists a)(x \\vee y) \\vdash "
    "\\sim\\sim((\\exists a)x \\vee (\\exists a)y)$; снимая и вводя двойные отрицания ($S^s$), получаем T22.\n"
    "T20 нужна для обратной схемы T23 (ей книга даёт те же ссылки).")

# ---- § 7, № 21: тавтология при n ≤ 2, но не при n = 3
P7 = C(EX("a", ab), EX("a", ac), EX("a", ad))
Q7 = W(EX("a", C(ab, ac)), EX("a", C(ab, ad)), EX("a", C(ac, ad)))
for n in (1, 2):
    ip, iq = q7.interp(P7, {"a": n}), q7.interp(Q7, {"a": n})
    assert all(not q7.pval(ip, e) or q7.pval(iq, e) for e in q7.penvs(ip, iq))
_cm = q7.countermodel(P7, Q7, nmax=3)
assert _cm and _cm[1] == {"a": 3}
HAND["07.07-021"] = H_(8, "K", "open", "с. 105–106, гл. 7, § 7", "кванторы, интерпретация, контрпример",
    f"{CONV} Постройте формулу $x \\vdash y$, интерпретационная форма которой (D2 § 7, с. 105) — тавтология при одном и при "
    "двух отмеченных терминах для $a$, но не при трёх. Докажите оба утверждения и объясните, почему D3 требует "
    "тавтологичности «при любом числе отмеченных терминов».",
    f"Например, ${ftex(P7, Q7)}$.",
    f"Формула: ${ftex(P7, Q7)}$.\n"
    "1. $n = 1$: посылка $(1a \\leftarrow b)(1a \\leftarrow c)(1a \\leftarrow d)$, а первый член заключения — "
    "$(1a \\leftarrow b)(1a \\leftarrow c)$: тавтология.\n"
    "2. $n = 2$: посылка утверждает, что каждое из $(ia \\leftarrow b)$, $(ja \\leftarrow c)$, $(ka \\leftarrow d)$ истинно при "
    "некоторых $i, j, k \\in \\{1, 2\\}$. Из трёх номеров два совпадают; если, скажем, $i = j$, истинен член "
    "$(ia \\leftarrow b)(ia \\leftarrow c)$ дизъюнкции $(\\exists a)((a \\leftarrow b)(a \\leftarrow c))$ — заключение истинно. "
    "Тавтология.\n"
    "3. $n = 3$: пусть истинны только $(1a \\leftarrow b)$, $(2a \\leftarrow c)$, $(3a \\leftarrow d)$. Посылка истинна, а "
    "каждый член каждой дизъюнкции заключения содержит два высказывания с одним и тем же $ia$ — ложен. Значит, форма не "
    "тавтология, и по D3 формула не тавтология.\n"
    "4. Проверка при малых $n$ не заменяет D3: свойства, зависящие от числа различных предметов, проявляются лишь при "
    "достаточно большом $n$; книга поэтому оговаривает доказательство «для любого числа отмеченных терминов» "
    "(математической индукцией, с. 106).", answer="build")

# ---- § 12, № 12: три высказывания с ∀, ⌝∀, ?∀ попарно несовместимы
NQ12 = [(ALL("a", x), C(N(NALL("a", x)), N(QALL("a", x))), "A^18"),
        (C(N(NALL("a", x)), N(QALL("a", x))), N(NALL("a", x)), ("Ss",)),
        (ALL("a", x), N(NALL("a", x)), ("tr", 1, 2)),
        (NALL("a", x), C(N(ALL("a", x)), N(QALL("a", x))), "A^28"),
        (C(N(ALL("a", x)), N(QALL("a", x))), N(QALL("a", x)), ("Ss",)),
        (NALL("a", x), N(QALL("a", x)), ("tr", 4, 5)),
        (QALL("a", x), C(N(ALL("a", x)), N(NALL("a", x))), "A^38"),
        (C(N(ALL("a", x)), N(NALL("a", x))), N(ALL("a", x)), ("Ss",)),
        (QALL("a", x), N(ALL("a", x)), ("tr", 7, 8))]


def _chk_sep(lines):
    """Проверка трёх отдельных выводов (строки 1–3, 4–6, 7–9)."""
    for k in range(0, 9, 3):
        part = [(a, b, (w if not (isinstance(w, tuple) and w[0] == "tr") else ("tr", 1, 2))) for a, b, w in lines[k:k + 3]]
        assert not q7.check(part, H.AXNQ), q7.check(part, H.AXNQ)


_chk_sep(NQ12)
HAND["07.12-012"] = H_(8, "M", "vary", "с. 122–123, гл. 7, § 12", "кванторы, Snq, вывод",
    f"{B.CONVN} Пользуясь схемами $A^18$, $A^28$, $A^38$ (§ 12, с. 123) и ссылками на $S^s$, докажите в $S^s_{{nq}}$ три формулы "
    "$(\\forall a)x \\vdash \\sim(\\urcorner\\forall a)x$, $(\\urcorner\\forall a)x \\vdash \\sim(?\\forall a)x$, $(?\\forall a)x "
    "\\vdash \\sim(\\forall a)x$ и объясните, почему вместе со схемой $A^39$ они выражают: из высказываний $(\\forall a)x$, "
    "$(\\urcorner\\forall a)x$, $(?\\forall a)x$ истинно не более одного, а если ложны два, истинно третье.",
    "Каждая — схема $A^i8$, затем удаление члена конъюнкции [$S^s$] и R1 $S^s$; попарная несовместимость следует из "
    "$A^18$–$A^38$, а $A^39$ (и $A^19$, $A^29$) даёт третье при ложности двух.",
    "Три вывода:\n\n" + H.show(NQ12[:3]) + "\n\n" + "\n".join(f"{n}. ${ftex(a, b)}$ [{q7.why_text(w)}]" for n, (a, b, w) in
                                                          enumerate(NQ12[3:6], 1)).replace("R1 $S^s$: 4, 5", "R1 $S^s$: 1, 2")
    + "\n\n" + "\n".join(f"{n}. ${ftex(a, b)}$ [{q7.why_text(w)}]" for n, (a, b, w) in enumerate(NQ12[6:], 1)).replace(
        "R1 $S^s$: 7, 8", "R1 $S^s$: 1, 2") +
    "\n\n$A^18$–$A^38$ говорят: из каждого высказывания тройки следует ложность двух других — истинных одновременно двух "
    "быть не может. $A^19$–$A^39$ (с. 123): $\\sim(\\urcorner\\forall a)x\\sim(?\\forall a)x \\vdash (\\forall a)x$ и т. д. — "
    "если ложны два, истинно третье. Это то, что в $S^5_{nq}$ выражает T5 § 16 (с. 126).", system="S^s_nq")

# ---- § 15, № 6: A^18, A^28, A^38 — тавтологии по § 15
for nm in ("A^18", "A^28", "A^38"):
    p, q, _ = q7.NQ[nm]
    P_, Q_ = q7.build_inst((p, q, []), {"x": ab, "@a": "a"})
    assert B.cm15(P_, Q_) is None, nm
HAND["07.15-006"] = H_(8, "M", "vary", "с. 123, 125, гл. 7, § 12, 15", "кванторы, Snq, интерпретация",
    f"{B.CONVN} По образцу проверки схем $S^s_{{cq}}$ в § 7 докажите, что при косвенной интерпретации § 15 (с. 125) примеры "
    "схем $A^18$ $(\\forall a)x \\vdash \\sim(\\urcorner\\forall a)x\\sim(?\\forall a)x$, $A^28$ $(\\urcorner\\forall a)x \\vdash "
    "\\sim(\\forall a)x\\sim(?\\forall a)x$ и $A^38$ $(?\\forall a)x \\vdash \\sim(\\forall a)x\\sim(\\urcorner\\forall a)x$ при "
    "$x$ := $(a \\leftarrow b)$ — тавтологии при любом числе отмеченных терминов. Укажите, где используется правило "
    f"«$\\{{x\\}}$ и $\\{{\\sim x\\}}$ не оба 1». {B.RULES15}",
    "$A^18$ и $A^28$ — по правилу п. 2 (из $\\{z\\} = 1$ следует $\\{\\sim z\\} = 0$ и наоборот); $A^38$ — посылка и "
    "заключение после замены (п. 3а) совпадают.",
    "Пусть $p_i = \\{(ia \\leftarrow b)\\}$, $q_i = \\{\\sim(ia \\leftarrow b)\\}$, по п. 2 $p_iq_i = 0$.\n"
    "Замены п. 3: $(\\forall a)x$ → $p_1 \\cdots p_n$; $(\\urcorner\\forall a)x$ → $(\\exists a)\\sim x$ → $q_1 \\vee \\ldots "
    "\\vee q_n$; $(?\\forall a)x$ → $\\sim(\\forall a)x\\sim(\\urcorner\\forall a)x$ → $\\sim(p_1\\cdots p_n)\\sim(q_1 \\vee "
    "\\ldots \\vee q_n)$.\n"
    "$A^18$: если $p_1 \\cdots p_n = 1$, то все $q_i = 0$ (п. 2), так что $\\sim(q_1 \\vee \\ldots) = 1$, а $\\sim(?\\forall a)x"
    " = \\sim(\\sim 1 \\cdot \\ldots) = 1$ — заключение истинно.\n"
    "$A^28$: если некоторое $q_j = 1$, то $p_j = 0$, $p_1 \\cdots p_n = 0$, $\\sim(\\forall a)x = 1$; $(?\\forall a)x$ содержит "
    "множитель $\\sim(q_1 \\vee \\ldots) = 0$, его отрицание — 1. Заключение истинно.\n"
    "$A^38$: заключение — та же конъюнкция, что и посылка после замены п. 3а: тавтология без всяких условий.\n"
    "Правило п. 2 использовано в $A^18$ и $A^28$; рассуждение не зависит от $n$ (перебор при $n \\leq 3$ подтверждает).",
    system="S^s_nq")

# ---- § 21, № 5 и 9
HAND["07.21-005"] = H_(8, "M", "open", "с. 99–100, 131, гл. 7, § 2, 21", "кванторы, условные высказывания, вывод",
    f"{CONV} {B.S21} Схемы $(\\exists a)(x \\rightarrow y) \\vdash (x \\rightarrow y)$ среди 1–5 нет. Докажите её, соединив "
    "схему 1 с A1, A5 и R2 системы $S^s_{cq}$ (с. 99–100); укажите, где используется условие A5.",
    "Схема 1, R2, A5 (для $(\\forall a)(x \\rightarrow y)$, где $a$ связан), A1 дважды, R1 $S^s$.",
    "1. $(x \\rightarrow y) \\vdash (\\forall a)(x \\rightarrow y)$ [схема 1]\n"
    "2. $(\\exists a)(x \\rightarrow y) \\vdash (\\exists a)(\\forall a)(x \\rightarrow y)$ [R2: 1]\n"
    "3. $(\\exists a)(\\forall a)(x \\rightarrow y) \\vdash (\\forall a)(\\forall a)(x \\rightarrow y)$ [A5: $a$ не входит свободно в "
    "$(\\forall a)(x \\rightarrow y)$ — все его вхождения связаны (D4–D5)]\n"
    "4. $(\\forall a)(\\forall a)(x \\rightarrow y) \\vdash (\\forall a)(x \\rightarrow y)$ [A1]\n"
    "5. $(\\forall a)(x \\rightarrow y) \\vdash (x \\rightarrow y)$ [A1]\n"
    "6. $(\\exists a)(x \\rightarrow y) \\vdash (\\forall a)(\\forall a)(x \\rightarrow y)$ [R1 $S^s$: 2, 3]\n"
    "7. $(\\exists a)(x \\rightarrow y) \\vdash (\\forall a)(x \\rightarrow y)$ [R1 $S^s$: 6, 4]\n"
    "8. $(\\exists a)(x \\rightarrow y) \\vdash (x \\rightarrow y)$ [R1 $S^s$: 7, 5]\n"
    "Условие A5 выполнено благодаря схеме 1: она «связывает» $a$, после чего квантор существования можно заменить "
    "квантором общности.")

HAND["07.21-009"] = H_(9, "M", "open", "с. 17, 131, гл. 1, § 1; гл. 7, § 21", "кванторы, условные высказывания, метатеорема",
    f"{CONV} {B.S21} Докажите индукцией по $m + n$: для любых терминов $a^1, \\ldots, a^m$, $b^1, \\ldots, b^n$ доказуемо "
    "$(x \\rightarrow y) \\dashv\\vdash ((\\exists a^1)\\ldots(\\exists a^m)x \\rightarrow (\\forall b^1)\\ldots(\\forall b^n)y)$. "
    "Затем выясните, следует ли из схем 4, 5 формула $(x \\rightarrow y) \\vdash ((\\forall a)x \\rightarrow y)$.",
    "Шаг индукции — схема 4 (для нового $b$) или 5 (для нового $a$) с подстановкой уже полученных антецедента и "
    "консеквента и транзитивность в обе стороны. Вторая формула схемами 4, 5 не даётся: они вводят в антецедент только "
    "$\\exists$.",
    "База $m + n = 0$: $(x \\rightarrow y) \\vdash (x \\rightarrow y)$ — теорема $S^s$.\n"
    "Шаг: пусть $(x \\rightarrow y) \\dashv\\vdash (X \\rightarrow Y)$, где $X = (\\exists a^2)\\ldots x$, $Y = (\\forall b^1)"
    "\\ldots y$. Схема 5 при $x$ := $X$, $y$ := $Y$ даёт $(X \\rightarrow Y) \\dashv\\vdash ((\\exists a^1)X \\rightarrow Y)$; "
    "по R1 $S^s$ (транзитивность, с. 17) в обе стороны — $(x \\rightarrow y) \\dashv\\vdash ((\\exists a^1)X \\rightarrow Y)$. "
    "Для нового $b$ — так же со схемой 4.\n"
    "Вторая часть: схемы 4 и 5 — единственные, меняющие антецедент или консеквент внутри $\\rightarrow$, и обе вводят "
    "строго определённый квантор ($\\forall$ в консеквент, $\\exists$ в антецедент). Получить $(\\forall a)x$ в антецеденте "
    "ими нельзя; вопрос о доказуемости этой формулы схемы § 21 не решают.")
