#!/usr/bin/env python3
"""Усложнение гл. 6 «Условные высказывания» (занятия 40–48) по образцу занятия 10.

Заменяет в src/data/zadachi/06.md карточки в тех же id (кроме оставленных ручных задач ступеней 8–10):
  § 1 — разбор длинных выражений по D1–D2 (в том числе D2 второе), диагностика, перевод, метатеоремы об элементарных
        высказываниях, построения;
  § 2 — состав высказываний, принцип «если из x следует y, то “Если x, то y”» с проверкой сильного следования, R1 § 8;
  § 3 — формулы с ⊃ и их аналоги с → при интерпретации § 4, априорная предпосылка (замена ⊃ на → по одному месту);
  § 4 — серии длинных формул с обоснованием значениями по пп. 1–12, построение приписываний, дополнение рассуждений;
  § 5 — три состояния (пп. 10–12), классический и неклассический случаи, выводы с Aⁿ1–Aⁿ6 и R3;
  § 6–7 — выводы в Sˢ_if и Sʷ_if в 8–12 строк, дополнение, две ошибки, почти-примеры, серии доказуемости (MT1–MT3);
  § 8–9 — выводы ⊢-формул в S⁵_if и S⁵*_if (R1, Rᵈ1, MT6, A5/A3 § 9), MT2/MT5/MT6/MT7, перенос выводов;
  § 10 — A*5 (условие на недоказуемость), выводы «парадоксов»; § 11 — базисные формулы, D2, подстановка.
Все выводы проверяет if6.check, значения — модели if6 (интерпретация § 4, три состояния, критерии S⁵_if).

Запуск: python3 src/scripts/gen/hard06.py
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hard06_lib as H  # noqa: E402
import hard06_sem as S  # noqa: E402
import hard06_sys as SY  # noqa: E402
import hard06_lang as G  # noqa: E402
import hard06_more as M  # noqa: E402
from hard06_lib import F, C, IF, N, V, W, ftex, tex, x, y, z, v, card, CV  # noqa: E402
from open_form import test_like  # noqa: E402

ROOT = H.ROOT
KEEP = {"06.02-009", "06.02-010", "06.03-026", "06.03-027", "06.03-028", "06.03-029", "06.03-030", "06.03-031",
        "06.03-032", "06.04-031", "06.04-032", "06.05-009", "06.05-010", "06.05-011", "06.06-031", "06.06-032",
        "06.08-061", "06.08-062", "06.08-063", "06.09-031", "06.09-032", "06.10-009", "06.10-010", "06.10-011",
        "06.11-016", "06.11-018", "06.11-019"}


# ---------------------------------------------------------------- ручные задачи (выводы проверяются программой)
def verified(lines, sysk):
    errs = F.check(lines, sysk)
    assert not errs, errs
    return F.show(lines, sysk)


def hand():
    out = {}
    out["06.01-009"] = card(
        8, "M", "transfer", "proof", "с. 82, гл. 6, § 1", "условные высказывания, элементарные высказывания, метатеорема",
        f"{G.D2E} Докажите: если в высказывание $z$ операторы условности ($\\rightarrow$, $\\urcorner\\!\\rightarrow$, "
        "$? \\rightarrow$ вместе) входят ровно один раз, то элементарными высказываниями $z$ по D2 (второму) являются в точности "
        "антецедент и консеквент этого условного высказывания. Покажите на примере, что при двух вхождениях элементарных "
        "высказываний может быть больше двух.",
        "Единственное условное высказывание $g = (x \\rightarrow y)$: в $x$, $y$ оператора нет, по п. 1 они элементарны в $g$, "
        "по п. 2 — в $z$; других условных высказываний нет, по п. 3 других элементарных нет. Пример: $(x \\rightarrow y)(z "
        "\\rightarrow v)$ — четыре.",
        "1. Пусть в $z$ ровно одно вхождение оператора; ему соответствует подвысказывание $g$ вида $(x \\rightarrow y)$, "
        "$(x \\urcorner\\!\\rightarrow y)$ или $(x? \\rightarrow y)$ (D1 § 1).\n"
        "2. В $x$ и $y$ оператор условности не входит (иначе вхождений было бы два). По п. 1 D2 $x$ и $y$ — элементарные "
        "высказывания, входящие в $g$; по п. 2, так как $g$ входит в $z$, они элементарны и в $z$.\n"
        "3. Других элементарных высказываний нет: п. 1 применим только к высказываниям с оператором условности, а оно в $z$ "
        "одно — $g$; п. 2 лишь переносит элементарные высказывания $g$ в объемлющие высказывания; по п. 3 высказывание элементарно "
        "лишь в силу пп. 1 и 2.\n"
        "4. При двух вхождениях: в $(x \\rightarrow y)(z \\rightarrow v)$ по пп. 1–2 элементарны $x, y, z, v$ — четыре.")
    out["06.01-010"] = card(
        9, "M", "transfer", "proof", "с. 82, гл. 6, § 1", "условные высказывания, элементарные высказывания, метатеорема",
        f"{G.D2E} Докажите две новые метатеоремы: а) всякое высказывание, в которое входит хотя бы один оператор условности, "
        "имеет по D2 (второму) хотя бы одно элементарное высказывание; б) ни одно элементарное высказывание (по D2) не содержит "
        "оператора условности.",
        "а) Возьмём условное подвысказывание наименьшей длины: в его частях оператора нет, по п. 1 они элементарны, по п. 2 — "
        "и в $z$. б) Элементарность даётся только п. 1 (части без оператора) и переносится п. 2 — значит, без оператора.",
        "а) 1. Пусть в $z$ входит оператор условности. Среди подвысказываний $z$ вида $(x \\rightarrow y)$, $(x \\urcorner\\!"
        "\\rightarrow y)$, $(x? \\rightarrow y)$ выберем $g$ наименьшей длины.\n"
        "2. В антецедент и консеквент $g$ оператор условности не входит: иначе в них было бы условное подвысказывание короче $g$.\n"
        "3. По п. 1 D2 антецедент и консеквент $g$ — элементарные высказывания $g$; по п. 2 — и $z$, так как $g$ входит в $z$.\n"
        "б) 4. По п. 3 высказывание элементарно лишь в силу пп. 1 и 2. По п. 1 элементарными объявляются только высказывания, в "
        "которые оператор условности не входит; п. 2 не создаёт новых элементарных высказываний, а переносит уже имеющиеся "
        "(индукция по числу применений п. 2). Значит, ни одно элементарное высказывание оператора условности не содержит.")
    out["06.01-011"] = card(
        7, "A", "open", "build", "с. 82, гл. 6, § 1", "условные высказывания, элементарные высказывания, построение",
        f"Буквы $x, y$ — высказывания без оператора условности. {G.D2E} Постройте высказывание или докажите, что его нет: "
        "а) оператор условности входит ровно три раза, а элементарных высказываний по D2 (второму) ровно два — $x$ и $y$; "
        "б) оператор условности входит ровно один раз, а элементарных высказываний три.",
        "а) Например, $((x \\rightarrow y) \\rightarrow (x \\rightarrow y))$; б) такого нет.",
        "а) В $((x \\rightarrow y) \\rightarrow (x \\rightarrow y))$ три вхождения $\\rightarrow$. Внутренние $(x \\rightarrow y)$ "
        "не содержат оператора в частях — по п. 1 элементарны $x$, $y$; по п. 2 они элементарны во всём высказывании. Части "
        "внешнего содержат оператор — п. 1 к нему неприменим; по п. 3 других элементарных нет.\n"
        "б) При одном вхождении оператора элементарны в точности антецедент и консеквент единственного условного высказывания "
        "(пп. 1–3; ср. задачу о единственном вхождении): их не больше двух. Высказывания с тремя элементарными нет.")
    # § 2: «Если x, то y» без «Из x следует y»
    lines = H.discharge(y, W(N(x), x), ["x"])
    out["06.02-002"] = card(
        8, "M", "transfer", "proof", "с. 83, 92, гл. 6, § 2, 8", "условность и следование, S5if, вывод",
        f"{CV} По § 2 (с. 83) не во всех случаях, когда истинно «Если $x$, то $y$», будет истинно «Из $x$ следует $y$». Докажите "
        f"это формально: выведите в $S^5_{{if}}$ теорему T5 § 8 $\\vdash (y \\rightarrow \\sim x \\vee x)$ (с. 92) по правилам "
        f"(без ссылки на MT5), а затем докажите, что $y \\vdash \\sim x \\vee x$ недоказуема в $S^s$. {H.S5_RULES} {G.SS_CRIT}",
        "Вывод из 8 строк со вспомогательной тавтологией $x \\vee \\sim x$ (A5, $R^d1$, A1, MT6); $y \\vdash \\sim x \\vee x$ "
        "недоказуема: в заключение входит $x$, которого нет в посылке.",
        verified(lines, "5") + "\n\nЗначит, «Если $y$, то $\\sim x \\vee x$» доказуемо в $S^5_{if}$. Но $y \\vdash \\sim x \\vee x$ — "
        "тавтология с элементарным высказыванием $x$, отсутствующим в посылке: не сильная тавтология, и в $S^s$ недоказуема "
        "(непарадоксальность, гл. 1, § 4). Условное высказывание истинно, а следования нет — что и утверждается на с. 83.")
    # § 6: построения
    out["06.06-027"] = card(
        6, "A", "open", "build", "с. 90, гл. 6, § 6", "условность, схемы, построение",
        f"{CV} Постройте формулу, которая одновременно является примером схем A5 $(xy \\rightarrow z) \\vdash (x \\rightarrow (y "
        "\\rightarrow z))$ и A6 $(x \\rightarrow (y \\rightarrow z)) \\vdash (xy \\rightarrow z)$ системы $S^s_{if}$, или докажите, "
        "что такой формулы нет.",
        "Такой формулы нет.",
        "1. Пример A5: $(XY \\rightarrow Z) \\vdash (X \\rightarrow (Y \\rightarrow Z))$; пример A6: $(X' \\rightarrow (Y' "
        "\\rightarrow Z')) \\vdash (X'Y' \\rightarrow Z')$ (с. 90).\n"
        "2. Посылки совпадают: антецедент $XY$ равен $X'$, консеквент $Z$ равен $(Y' \\rightarrow Z')$.\n"
        "3. Заключения совпадают: $X = X'Y'$ (антецеденты) и $(Y \\rightarrow Z) = Z'$.\n"
        "4. Тогда $X = X'Y' = (XY)Y'$ — высказывание совпадает с конъюнкцией, в которую оно входит как собственная часть, — "
        "невозможно (длина конъюнкции больше). Формулы нет.")
    out["06.06-028"] = card(
        6, "A", "open", "build", "с. 90, гл. 6, § 6", "условность, схемы, построение",
        f"{CV} Постройте формулу, которая одновременно является примером схем A3 $(x \\rightarrow y)(y \\rightarrow z) \\vdash (x "
        "\\rightarrow z)$ и A7 $(x \\rightarrow y)(z \\rightarrow v) \\vdash (xz \\rightarrow yv)$, или докажите, что такой формулы "
        "нет. Затем ответьте на тот же вопрос для A1 и A4.",
        "Для A3 и A7 — нет; для A1 и A4 — тоже нет.",
        "1. A3 и A7: посылки $(X \\rightarrow Y)(Y \\rightarrow Z)$ и $(X' \\rightarrow Y')(Z' \\rightarrow V')$ совпадают при "
        "$X' = X$, $Y' = Y$, $Z' = Y$, $V' = Z$. Заключения: $(X \\rightarrow Z)$ и $(XY \\rightarrow YZ)$ — должно быть $X = XY$, "
        "но высказывание не совпадает с конъюнкцией, куда оно входит как часть. Формулы нет.\n"
        "2. A1 и A4: посылка A1 — конъюнкция $(X \\rightarrow Y)X$, посылка A4 — условное высказывание $(X' \\rightarrow Y'Z')$; "
        "главные операторы разные — формулы нет (с. 90).")
    out["06.07-015"] = card(
        6, "A", "open", "build", "с. 90–91, гл. 6, § 7", "условность, схемы, построение",
        f"{CV} Постройте формулу, которая одновременно является примером A2 $(x \\rightarrow y) \\vdash (\\sim y \\rightarrow \\sim "
        "x)$ и A9 $(x \\rightarrow y) \\vdash (xz \\rightarrow y)$ системы $S^w_{if}$, или докажите, что её нет. Затем — то же "
        "для A9 и A4 $(x \\rightarrow yz) \\vdash (x \\rightarrow y)(x \\rightarrow z)$.",
        "Для A2 и A9 — нет; для A9 и A4 — нет.",
        "1. A2 и A9: посылки совпадают ($X' = X$, $Y' = Y$); антецеденты заключений $\\sim Y$ и $XZ$ должны совпасть, но одно — "
        "отрицание, другое — конъюнкция. Формулы нет.\n"
        "2. A9 и A4: заключение A9 — условное высказывание $(XZ \\rightarrow Y)$, заключение A4 — конъюнкция двух условных "
        "высказываний. Формулы нет (с. 90–91).")
    out["06.06-030"] = card(
        8, "M", "transfer", "proof", "с. 90, гл. 6, § 6", "условность, метатеоремы",
        f"{CV} Докажите MT3 § 6 (с. 90) по образцу доказательства непарадоксальности (индукция по выводу): если $x \\vdash y$ "
        f"доказуема в $S^s_{{if}}$ и в $y$ входит оператор условности, то он входит и в $x$. {H.SCH_S} {H.RULES}",
        "Индукция по выводу: в A1–A8 посылки содержат $\\rightarrow$; шаги $S^s$ не вводят новых условных высказываний; R1, R2, "
        "R3 сохраняют свойство.",
        "Свойство П: «если в заключение входит оператор условности, то он входит в посылку».\n"
        "1. Аксиомы A1–A8: в посылке каждой схемы есть $\\rightarrow$ (с. 90) — П выполнено для любого примера.\n"
        "2. Шаги общей теории дедукции: формула — сильная тавтология, если условные высказывания считать элементарными; в её "
        "заключение не входят «элементарные» высказывания, отсутствующие в посылке. Условное высказывание заключения — такое "
        "«элементарное» высказывание (или содержит его), значит, оно есть и в посылке.\n"
        "3. R1: из $x \\vdash y$ и $y \\vdash z$ — $x \\vdash z$. Если $\\rightarrow$ в $z$, то по П для $y \\vdash z$ он в $y$, по П "
        "для $x \\vdash y$ — в $x$.\n"
        "4. R2: из $x \\vdash y$ и $x \\vdash z$ — $x \\vdash yz$. Если $\\rightarrow$ в $yz$, то в $y$ или в $z$, и по П — в $x$.\n"
        "5. R3: из $x \\vdash y$, $y \\vdash x$ — $z \\vdash v$, $v$ — замена вхождений $x$ на $y$ в $z$. Если $\\rightarrow$ в $v$, "
        "то либо в неизменённой части (она есть и в $z$), либо в $y$; во втором случае по П для $x \\vdash y$ он в $x$, а $x$ "
        "входит в $z$.\n"
        "6. По индукции П верно для всех теорем $S^s_{if}$. Следствие (с. 90): $x \\vdash (y \\rightarrow z)$ при $x$ без "
        "оператора условности недоказуема.")
    out["06.07-016"] = card(
        8, "M", "transfer", "proof", "с. 86–87, 90–91, гл. 6, § 4, 6, 7", "условность, метатеоремы, интерпретация",
        f"{CV} По образцу MT1 § 6 (с. 90: «теорема легко доказывается путём перебора всех аксиомных схем») докажите MT2 § 7: "
        f"доказуемые в $S^w_{{if}}$ формулы суть тавтологии. Достаточно проверить новую схему A9 $(x \\rightarrow y) \\vdash (xz "
        f"\\rightarrow y)$ по правилам интерпретации § 4. {S.INTERP}",
        "Приписав $x \\rightarrow y$ значение 1 и $xz$ значение 1, получаем $x$ = 1, по п. 1 $y$ = 1: антецедент $xz$ вынуждает "
        "консеквент $y$, по п. 5 $xz \\rightarrow y$ = 1. A9 — тавтология; остальное — как в MT1 § 6.",
        "1. $S^w_{if}$ = $S^s_{if}$ + A9 (с. 91). Схемы A1–A8 — тавтологии (MT1 § 6), правила общей теории дедукции сохраняют "
        "тавтологичность, как там же.\n"
        "2. A9: пусть посылка $x \\rightarrow y$ имеет значение 1. Припишем антецеденту заключения $xz$ значение 1; тогда $x$ = 1, "
        "и по п. 1 (с. 86) мы вынуждены приписать $y$ значение 1.\n"
        "3. Значит, приписав $xz$ значение 1, мы вследствие этого вынуждены приписать $y$ значение 1; по п. 5 $xz \\rightarrow y$ "
        "имеет значение 1. Заключение получает 1 всякий раз, когда посылка имеет 1: A9 — тавтология (книга: «A9 есть, очевидно, "
        "тавтология», с. 91).\n"
        "4. Перебор схем A1–A9 завершён: все теоремы $S^w_{if}$ — тавтологии.")
    # § 8: метатеоремы и производные правила
    a, b_ = x, y
    lines = [(None, IF(x, y), "given"), (None, N(y), "given"), (IF(x, y), IF(N(y), N(x)), "A2"),
             (None, IF(N(y), N(x)), ("Rd1", 3, 1))]
    H.mp(lines, 4, 2)
    out["06.08-010"] = card(
        8, "M", "transfer", "proof", "с. 92, гл. 6, § 8", "условность, S5if, метатеоремы",
        f"{CV} Докажите MT4 § 8 (с. 92): если $\\vdash (x \\rightarrow y)$ и $\\vdash \\sim y$ доказуемы в $S^5_{{if}}$, то "
        f"$\\vdash \\sim x$ доказуема. Книга: «Доказательство аналогично [MT3]. Дополняется лишь то, что согласно A2 системы "
        f"$S^s_{{if}}$ доказуема $\\vdash (\\sim y \\rightarrow \\sim x)$». Проведите доказательство полностью, по строкам. "
        f"{H.S5_RULES}",
        f"Вывод из {len(lines)} строк: A2 и $R^d1$ дают $\\vdash (\\sim y \\rightarrow \\sim x)$; далее, как в MT3: A1, MT6, $R^d1$.",
        verified(lines, "5") + "\n\nСтроки 1–2 — условие. Строки 5–7 повторяют доказательство MT3 (с. 92) для "
        "$\\vdash (\\sim y \\rightarrow \\sim x)$ и $\\vdash \\sim y$.")
    lines = [(None, IF(x, y), "given"), (C(x, z), x, "Ss"), (None, IF(C(x, z), x), ("Rif", 2)),
             (None, C(IF(C(x, z), x), IF(x, y)), ("MT6", 3, 1)), (C(IF(C(x, z), x), IF(x, y)), IF(C(x, z), y), "A3"),
             (None, IF(C(x, z), y), ("Rd1", 5, 4))]
    out["06.08-020"] = card(
        8, "M", "transfer", "proof", "с. 90–92, гл. 6, § 7–8", "условность, S5if, производное правило",
        f"{CV} В $S^5_{{if}}$ схема A9 $(x \\rightarrow y) \\vdash (xz \\rightarrow y)$ системы $S^w_{{if}}$ не принята, а "
        f"$(x \\rightarrow y) \\vdash (xz \\rightarrow y)$ в $S^s_{{if}}$ по MT2 § 6 недоказуема. Докажите производное правило "
        f"$S^5_{{if}}$: если $\\vdash (x \\rightarrow y)$ доказуема, то $\\vdash (xz \\rightarrow y)$ доказуема. {H.S5_RULES} "
        f"A3 $(x \\rightarrow y)(y \\rightarrow z) \\vdash (x \\rightarrow z)$.",
        f"Вывод из {len(lines)} строк: $\\vdash (xz \\rightarrow x)$ по R1 § 8, MT6, A3, $R^d1$.",
        verified(lines, "5") + "\n\nКлюч — теорема $\\vdash (xz \\rightarrow x)$: она получена по R1 § 8 из $xz \\vdash x$ и "
        "присоединена к данной формуле по MT6. Правило — аналог A9 на уровне формул $\\vdash (x \\rightarrow y)$.")
    lines = H.discharge(C(x, N(y)), W(x, z), ["z"])
    out["06.08-030"] = card(
        9, "M", "transfer", "proof", "с. 91–93, гл. 6, § 8", "условность, S5if, метатеоремы",
        f"{CV} Докажите, не опираясь на MT5 § 8: если $x$ и $y$ — высказывания без оператора условности и $x \\supset y$ — "
        f"тавтология, то $\\vdash (x \\rightarrow y)$ доказуема в $S^5_{{if}}$. Указание: пусть $p^1, \\ldots, p^k$ — элементарные "
        f"высказывания $y$, отсутствующие в $x$, и $A = (p^1 \\vee \\sim p^1)\\ldots(p^k \\vee \\sim p^k)$ (при $k = 0$ "
        f"достаточно R1 § 8). Проведите доказательство и покажите его на формуле $\\vdash (x\\sim y \\rightarrow x \\vee z)$. "
        f"{H.S5_RULES} {G.SS_CRIT}",
        "$Ax \\vdash y$ — сильная тавтология (теорема $S^s$); далее R1 § 8, A5, $R^d1$, $\\vdash A$ (тавтология, MT4 гл. 4), A1, "
        "MT6, $R^d1$ дают $\\vdash (x \\rightarrow y)$.",
        "1. $Ax \\vdash y$: если $Ax$ = 1, то $x$ = 1, и так как $x \\supset y$ — тавтология, $y$ = 1; все элементарные "
        "высказывания $y$ входят в $x$ или в $A$. Сильная тавтология — теорема $S^s$ (гл. 2, § 2, MT5).\n"
        "2. По R1 § 8: $\\vdash (Ax \\rightarrow y)$; A5: $(Ax \\rightarrow y) \\vdash (A \\rightarrow (x \\rightarrow y))$; $R^d1$: "
        "$\\vdash (A \\rightarrow (x \\rightarrow y))$.\n"
        "3. $A$ — тавтология, по MT4 § 3 гл. 4 $\\vdash A$ доказуема в $S^5$. По доказательству MT3 § 8 (A1, MT6, $R^d1$) — "
        "$\\vdash (x \\rightarrow y)$.\n"
        "4. При $k = 0$ сама $x \\vdash y$ — сильная тавтология, и достаточно R1 § 8.\n\nПример ($k = 1$, $p^1 = z$):\n\n" +
        verified(lines, "5"))
    lines = [(C(x, z), x, "Ss"), (None, IF(C(x, z), x), ("Rif", 1)),
             (C(IF(C(x, z), x), IF(x, y)), IF(C(x, z), y), "A3"),
             (None, IF(C(IF(C(x, z), x), IF(x, y)), IF(C(x, z), y)), ("Rif", 3)),
             (IF(C(IF(C(x, z), x), IF(x, y)), IF(C(x, z), y)), IF(IF(C(x, z), x), IF(IF(x, y), IF(C(x, z), y))), "A5"),
             (None, IF(IF(C(x, z), x), IF(IF(x, y), IF(C(x, z), y))), ("Rd1", 5, 4))]
    H.mp(lines, 6, 2)
    out["06.08-038"] = card(
        9, "M", "transfer", "proof", "с. 90–92, гл. 6, § 6, 8", "условность, S5if, вывод",
        f"{CV} В $S^5_{{if}}$ доказуема T1 § 8 $\\vdash ((x \\rightarrow y) \\rightarrow (xz \\rightarrow y))$ (с. 92), хотя формула "
        f"$(x \\rightarrow y) \\vdash (xz \\rightarrow y)$ в $S^s_{{if}}$ недоказуема. Докажите оба утверждения: выведите T1 по "
        f"правилам $S^5_{{if}}$ и обоснуйте недоказуемость. {H.S5_RULES} A3 $(x \\rightarrow y)(y \\rightarrow z) \\vdash (x "
        f"\\rightarrow z)$, A5 $(xy \\rightarrow z) \\vdash (x \\rightarrow (y \\rightarrow z))$.",
        f"Вывод из {len(lines)} строк (вспомогательная теорема $\\vdash (xz \\rightarrow x)$, A3, R1 § 8, A5, $R^d1$, A1, MT6); "
        "недоказуемость в $S^s_{if}$ — MT2 § 6 ($z$ нет в посылке).",
        verified(lines, "5") + "\n\nВ $S^s_{if}$ формула $(x \\rightarrow y) \\vdash (xz \\rightarrow y)$ недоказуема: в заключение "
        "входит $z$, отсутствующее в посылке (MT2 § 6, с. 90). В $S^5_{if}$ недостающее $z$ «приходит» из теоремы "
        "$\\vdash (xz \\rightarrow x)$, у которой нет посылки.")
    lines = H.discharge(C(x, N(x)), y, ["y"])
    k = len(lines)
    P, Q = C(x, N(x)), y
    lines.append((IF(P, Q), IF(x, IF(N(x), y)), "A5"))
    lines.append((None, IF(x, IF(N(x), y)), ("Rd1", k + 1, k)))
    out["06.08-060"] = card(
        8, "D", "transfer", "proof", "с. 92, 94, гл. 6, § 8, 10", "условность, S5if, парадоксы, вывод",
        f"{CV} Выведите в $S^5_{{if}}$ теорему T8 § 8 $\\vdash (x \\rightarrow (\\sim x \\rightarrow y))$ (с. 92; один из «парадоксов» "
        f"§ 10) по правилам, без ссылки на MT5. Объясните, почему недостаточно R1 § 8 и A5. {H.S5_RULES}",
        f"Вывод из {len(lines)} строк: сначала $\\vdash (x\\sim x \\rightarrow y)$ с вспомогательной тавтологией $y \\vee \\sim y$, "
        "затем A5 и $R^d1$.",
        verified(lines, "5") + "\n\nR1 § 8 и A5 дали бы T8 из $x\\sim x \\vdash y$, но эта формула в $S^s$ недоказуема: $y$ нет в "
        "посылке (непарадоксальность $S^s$). Поэтому $y$ вводится через вспомогательную тавтологию $y \\vee \\sim y$.")
    return out


# ---------------------------------------------------------------- план замены
def plan():
    P = {}

    def put(sec, ids, fns):
        keys = [f"06.{sec:02d}-{i:03d}" for i in ids]
        assert len(keys) == len(fns), (sec, len(keys), len(fns))
        P.update(zip(keys, fns))

    s1 = "с. 82, гл. 6, § 1"
    put(1, range(1, 9), [G.c_wf, G.c_parts, G.c_elem, G.c_parse_diag, G.c_wf_diag, G.c_nat_formal, G.c_nat_e,
                         lambda: G.c_parts(level=5) | {"step": "iso"}])
    put(2, [1, 3, 4, 5, 6, 7, 8], [G.c_comp, lambda: M.claims_card(G.CLAIMS2, 2), G.c_principle, G.c_principle_e,
                                   G.c_s5_r1, lambda: G.c_comp(level=5), G.c_principle])
    bad3 = ["conj", "negneg", "negpos", "dis", "negif", "split", "split2", "orcons"]
    good3 = ["A1", "A2", "T4", "A3"]
    k3 = ([G.c_imp_series] * 5 + [G.c_imp_diag] * 3 + [G.c_apriori] * 4 + [G.c_nat_counter] * 2 +
          [lambda: G.c_nat_counter(diag=True)] * 2 + [lambda: S.c_vs_imp(src="с. 85–88, гл. 6, § 3")] * 2 +
          [lambda: M.claims_card(G.CLAIMS3, 3)] * 2 +
          [lambda: S.c_sem_build(src="с. 84–88, гл. 6, § 3", typ="V")] * 2 +
          [lambda: S.c_sem_series(src="с. 84–88, гл. 6, § 3", good_keys=good3, bad_keys=bad3,
                                  tags="условность, материальная импликация")] * 3)
    put(3, range(1, 26), k3)
    k4 = ([S.c_sem_series] * 7 + [S.c_sem_diag] * 4 + [S.c_sem_fill] * 4 + [S.c_sem_build] * 5 + [S.c_vs_imp] * 3 +
          [M.c_sit_diag] * 3 + [M.c_nat_sem] * 2 + [lambda: M.claims_card(M.CLAIMS4, 4)] * 2)
    put(4, range(1, 31), k4)
    put(5, range(1, 9), [SY.c_three_series, SY.c_three_series, SY.c_three_diag, SY.c_three_diag, SY.c_an_deriv,
                         SY.c_an_diag, lambda: H.c_complete("n", src="с. 89, гл. 6, § 5", lines=SY.an_deriv()) |
                         {"system": "S^s + A^n"}, lambda: M.claims_card(M.CLAIMS5, 5)])
    k6 = ([H.c_deriv] * 6 + [H.c_complete] * 5 + [H.c_diag] * 5 +
          [lambda: SY.c_near("A5", False), lambda: SY.c_near("A7", True), lambda: SY.c_near("A3", False),
           lambda: SY.c_near("A4", True)] + [SY.c_recog] * 2 + [SY.c_prov_series] * 4 + [lambda: M.claims_card(M.CLAIMS6, 6)])
    put(6, [i for i in range(1, 30) if i not in (27, 28)], k6)
    s7 = "с. 90–91, гл. 6, § 7"
    k7 = ([lambda: H.c_deriv("w", src=s7)] * 3 + [lambda: H.c_complete("w", src=s7)] * 2 + [lambda: H.c_diag("w", src=s7)] * 2 +
          [lambda: SY.c_prov_series("w", src=s7)] * 3 + [SY.c_cmp_sw] * 3 + [lambda: SY.c_near("A9", False, src=s7, sysk="w")])
    put(7, range(1, 15), k7)
    s8 = "с. 91–93, гл. 6, § 8"
    k8 = ([lambda: H.c_deriv("5", src=s8, lines=H.s5_deriv("5"))] * 9 + [M.c_discharge] * 4 +
          [lambda: H.c_complete("5", src=s8, lines=H.s5_deriv("5"))] * 6 +
          [lambda: H.c_diag("5", src=s8, lines_fn=lambda: H.s5_deriv("5"),
                            kinds_pool=[("ax", "rd"), ("ax", "r12"), ("rd", "r12"), ("ss", "rd")])] * 6 +
          [SY.c_s5_series] * 7 + [SY.c_s5_diag] * 3 + [SY.c_mt7] * 4 + [SY.c_mt6] * 3 + [M.c_mt34] * 4 +
          [lambda: SY.c_near("A6", False, src=s8), lambda: SY.c_near("A8", False, src=s8),
           lambda: SY.c_near("A2", False, src=s8)] + [lambda: SY.c_recog(src=s8)] * 2 + [M.c_s5_build] * 2 +
          [lambda: M.claims_card(M.CLAIMS8, 8)] * 2)
    put(8, [i for i in range(1, 60) if i not in (10, 20, 30, 38)], k8)
    s9 = "с. 93–94, гл. 6, § 9"
    k9 = ([lambda: H.c_deriv("5s", src=s9, lines=H.s5_deriv("5s"))] * 6 +
          [lambda: H.c_complete("5s", src=s9, lines=H.s5_deriv("5s"))] * 5 +
          [lambda: H.c_diag("5s", src=s9, lines_fn=lambda: H.s5_deriv("5s"),
                            kinds_pool=[("ax", "rd"), ("ax", "r12"), ("rd", "r12")])] * 5 +
          [lambda: SY.c_s5_series(src=s9, sysn="S^{5*}_{if}", extra=" По MT1 § 9 (с. 94) формулы $\\vdash (x \\rightarrow y)$, "
                                  "доказуемые в $S^5_{if}$, доказуемы в $S^{5*}_{if}$, и наоборот.")] * 4 +
          [lambda: SY.c_near("B2", False, src=s9, sysk="5s"), lambda: SY.c_near("B1", False, src=s9, sysk="5s"),
           lambda: SY.c_near("B3", False, src=s9, sysk="5s")] + [lambda: SY.c_recog(sysk="5s", src=s9)] * 2 +
          [lambda: M.claims_card(M.CLAIMS9, 9)] + [M.c_mt1_9] * 3 + [lambda: SY.c_near("B2", True, src=s9, sysk="5s")])
    put(9, range(1, 31), k9)
    put(10, range(1, 9), [SY.c_a5s, SY.c_a5s, SY.c_a5s_diag, SY.c_a5s_diag, M.c_par_deriv, M.c_par_deriv, M.c_par_e,
                          lambda: M.claims_card(M.CLAIMS10, 10)])
    k11 = ([SY.c_basis] * 4 + [SY.c_basis_taut] * 4 + [SY.c_basis_diag] * 2 + [lambda: M.claims_card(M.CLAIMS11, 11)] * 2 +
           [M.c_sub] * 2 + [M.c_extend] * 2)
    put(11, [i for i in range(1, 16)] + [17], k11)
    return P


def render(cid, c):
    sec = int(cid.split(".")[1].split("-")[0])
    sysl = f'system: "{c["system"]}"\n' if c.get("system") else ""
    return (f'---\nid: "{cid}"\nchapter: 6\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\n'
            f'step: {c["step"]}\ncondition: {c.get("condition", "def")}\nform: {c["form"]}\nanswer: {c["answer"]}\n'
            f'source: "{c["source"]}"\n{sysl}generated: true\ntags: [{c["tags"]}]\n---\n\n## Условие\n\n{c["cond"]}\n\n'
            f'## Ответ\n\n{c["ans"]}\n\n## Решение\n\n{c["sol"]}\n')


def main():
    pl = plan()
    hd = hand()
    assert not set(pl) & set(hd), set(pl) & set(hd)
    assert not (set(pl) | set(hd)) & KEEP
    cards = {}
    for cid in sorted(pl):
        cards[cid] = pl[cid]()
    cards.update(hd)
    for cid, c in cards.items():
        assert not test_like(c["cond"]), (cid, c["cond"][:160])
    path = ROOT / "data" / "zadachi" / "06.md"
    text = path.read_text(encoding="utf-8")
    parts = re.split(r"(\n=====\n)", text)
    done, ids = set(), []
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(06\.\d\d-\d{3})"', chunk, re.M)
        if not m:
            continue
        ids.append(m.group(1))
        if m.group(1) in cards:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            parts[i] = lead + render(m.group(1), cards[m.group(1)]).rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
            done.add(m.group(1))
    assert done == set(cards), sorted(set(cards) - done)
    missing = set(ids) - done - KEEP
    assert not missing, sorted(missing)
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {len(done)}; оставлено: {len(set(ids) & KEEP)}")


if __name__ == "__main__":
    main()
