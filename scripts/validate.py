#!/usr/bin/env python3
"""Проверка задач: формат карточки, коды классификации, уникальность номеров, квоты.

Запуск: python3 scripts/validate.py
Код возврата 1, если есть ошибки. Предупреждения ошибкой не считаются.
"""
from __future__ import annotations

import sys
from collections import Counter

from common import ID_RE, load_book, load_problems, load_yaml, compute_quotas

REQUIRED = ["id", "chapter", "section", "level", "type", "form", "answer"]
REQUIRED_BLOCKS = ["## Условие", "## Ответ", "## Решение"]


def main() -> int:
    tax = load_yaml("taxonomy.yaml")
    chapters = load_book()
    compute_quotas(chapters)
    by_num = {c.num: c for c in chapters}
    sections = {(s.chapter, s.num): s for c in chapters for s in c.sections}

    errors, warnings = [], []
    ids = Counter()
    per_section = Counter()
    problems = load_problems()

    for pr in problems:
        m = pr.meta
        rel = f"{pr.path.name}: {m.get('id', '?')}"
        err = lambda msg: errors.append(f"{rel}: {msg}")
        missing = [k for k in REQUIRED if k not in m]
        if missing:
            err(f"нет полей {missing}")
            continue
        pid = str(m["id"])
        ids[pid] += 1
        mm = ID_RE.match(pid)
        if not mm:
            err(f"номер {pid!r} не в формате ГГ.ПП-NNN или ГГ.ПП-NNNN")
            continue
        if pr.path.stem != pid[:2]:
            err(f"задача главы {pid[:2]} лежит в файле {pr.path.name}")
        if (int(mm.group(1)), int(mm.group(2))) != (m["chapter"], m["section"]):
            err("глава/параграф в номере не совпадают с полями chapter/section")
        ch = by_num.get(m["chapter"])
        if not ch:
            err(f"нет главы {m['chapter']}")
            continue
        sec = sections.get((m["chapter"], m["section"]))
        if not sec:
            err(f"в главе {m['chapter']} нет параграфа {m['section']}")
            continue
        per_section[(m["chapter"], m["section"])] += 1
        if m["level"] not in tax["levels"]:
            err(f"ступень {m['level']} вне 1–10")
        if m["type"] not in tax["types"]:
            err(f"неизвестный тип {m['type']}")
        if m["form"] not in tax["forms"]:
            err(f"неизвестная форма {m['form']}")
        if m["answer"] not in tax["answers"]:
            err(f"неизвестный формат ответа {m['answer']}")
        if m.get("condition") not in (None, *tax["conditions"]):
            err(f"поле condition: {m['condition']!r} (допустимо {', '.join(tax['conditions'])})")
        if m.get("step") not in (None, *tax["steps"]):
            err(f"поле step: {m['step']!r} (допустимо {', '.join(tax['steps'])})")
        if m.get("case") not in (None, "classical", "nonclassical"):
            err(f"поле case: {m['case']!r} (допустимо classical, nonclassical или пусто)")
        for block in REQUIRED_BLOCKS:
            if block not in pr.body:
                err(f"нет раздела «{block[3:]}»")
        allowed = tax["profiles"][sec.profile]["types"]
        if m["type"] not in allowed:
            warnings.append(f"{rel}: тип {m['type']} нетипичен для профиля {sec.profile} ({'/'.join(allowed)})")
        if not m.get("source") and sec.profile != "X":
            warnings.append(f"{rel}: не указан источник (source: с. N)")

    for pid, n in ids.items():
        if n > 1:
            errors.append(f"номер {pid} встречается {n} раз")
    for key, n in per_section.items():
        s = sections[key]
        if n > s.quota:
            warnings.append(f"{s.key}: задач {n}, квота {s.quota}")

    # Контрольные работы: новые задачи, не повторяющие задачи занятий.
    import re
    from build import load_kontrol
    cond = lambda body: (re.search(r"## Условие(.*?)## Ответ", body, re.S) or [None, body])[1].strip()
    taught = {cond(p.body) for p in problems}
    kseen, kcount = Counter(), 0
    for k, cards in load_kontrol().items():
        for pr in cards:
            kcount += 1
            m = pr.meta
            rel = f"kontrolnye/{pr.path.name}: {m.get('id', '?')}"
            missing = [f for f in REQUIRED if f not in m]
            if missing:
                errors.append(f"{rel}: нет полей {missing}")
                continue
            if not re.fullmatch(rf"K{k:02d}-\d{{2}}", str(m["id"])):
                errors.append(f"{rel}: номер не в формате K{k:02d}-NN")
            if (m["chapter"], m["section"]) not in sections:
                errors.append(f"{rel}: нет параграфа {m['chapter']}.{m['section']}")
            if m["level"] not in tax["levels"] or m["type"] not in tax["types"]:
                errors.append(f"{rel}: неизвестная ступень или тип")
            for block in REQUIRED_BLOCKS:
                if block not in pr.body:
                    errors.append(f"{rel}: нет раздела «{block[3:]}»")
            c = cond(pr.body)
            if c in taught:
                errors.append(f"{rel}: условие совпадает с задачей занятия")
            kseen[c] += 1
    # Разобранные примеры: по одному на параграф, условия не совпадают с задачами занятий и контрольных.
    from build import load_primery
    examples = load_primery()
    for key, pr in examples.items():
        rel = f"primery: {pr.meta.get('id', '?')}"
        if key not in sections:
            errors.append(f"{rel}: нет параграфа {key}")
        for block in REQUIRED_BLOCKS:
            if block not in pr.body:
                errors.append(f"{rel}: нет раздела «{block[3:]}»")
        c = cond(pr.body)
        if c in taught or c in kseen:
            errors.append(f"{rel}: условие совпадает с задачей занятия или контрольной")
    for c, n in kseen.items():
        if n > 1:
            errors.append(f"контрольные: одно условие встречается {n} раз: {c[:60]}…")

    for w in warnings:
        print("ПРЕДУПРЕЖДЕНИЕ:", w)
    for e in errors:
        print("ОШИБКА:", e)
    print(f"Задач: {len(problems)} из {tax['total']}; в контрольных: {kcount}; разобранных примеров: {len(examples)}. Ошибок: {len(errors)}, предупреждений: {len(warnings)}.")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
