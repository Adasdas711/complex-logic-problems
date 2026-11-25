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
        rel = pr.path.relative_to(pr.path.parent.parent.parent)
        m = pr.meta
        err = lambda msg: errors.append(f"{rel}: {msg}")
        missing = [k for k in REQUIRED if k not in m]
        if missing:
            err(f"нет полей {missing}")
            continue
        pid = str(m["id"])
        ids[pid] += 1
        mm = ID_RE.match(pid)
        if not mm:
            err(f"номер {pid!r} не в формате ГГ.ПП-NNN")
            continue
        if pr.path.stem != pid:
            err(f"имя файла не совпадает с номером {pid}")
        if (int(mm.group(1)), int(mm.group(2))) != (m["chapter"], m["section"]):
            err("глава/параграф в номере не совпадают с полями chapter/section")
        ch = by_num.get(m["chapter"])
        if not ch:
            err(f"нет главы {m['chapter']}")
            continue
        if pr.path.parent.name != ch.slug:
            err(f"файл должен лежать в problems/{ch.slug}/")
        sec = sections.get((m["chapter"], m["section"]))
        if not sec:
            err(f"в главе {m['chapter']} нет параграфа {m['section']}")
            continue
        per_section[(m["chapter"], m["section"])] += 1
        if m["level"] not in tax["levels"]:
            err(f"уровень {m['level']} вне 1–5")
        if m["type"] not in tax["types"]:
            err(f"неизвестный тип {m['type']}")
        if m["form"] not in tax["forms"]:
            err(f"неизвестная форма {m['form']}")
        if m["answer"] not in tax["answers"]:
            err(f"неизвестный формат ответа {m['answer']}")
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

    for w in warnings:
        print("ПРЕДУПРЕЖДЕНИЕ:", w)
    for e in errors:
        print("ОШИБКА:", e)
    print(f"Задач: {len(problems)} из {tax['total']}. Ошибок: {len(errors)}, предупреждений: {len(warnings)}.")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
