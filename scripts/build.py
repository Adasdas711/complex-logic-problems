#!/usr/bin/env python3
"""Генерация оглавлений и планов из data/*.yaml и карточек задач.

  python3 scripts/build.py          — пересобрать файлы
  python3 scripts/build.py --check  — проверить, что сгенерированные файлы актуальны

Генерируются: docs/01-soderzhanie-knigi.md, docs/03-plan.md, docs/progress.md,
docs/indeks-po-urovnyam.md, docs/indeks-po-tipam.md, problems/*/README.md
и таблица разделов в README.md (между пометками sections:start/end).
Эти файлы руками не правятся.
"""
from __future__ import annotations

import sys
from collections import Counter, defaultdict

from common import DOCS, PROBLEMS, ROOT, compute_quotas, load_book, load_problems, load_yaml, problem_title

GEN = "<!-- Файл сгенерирован scripts/build.py. Не редактировать вручную. -->\n\n"


def stars(n: int) -> str:
    return "★" * n


def soderzhanie(chapters, tax) -> str:
    prof = tax["profiles"]
    out = [GEN, "# Содержание книги\n\n",
           "А. А. Зиновьев. *Комплексная логика*. М.: Наука, 1970. 206 с.\n\n",
           "Страницы указаны по нумерации книги; в PDF-скане номер страницы на 1 больше. ",
           "Профиль — характер материала параграфа, от него зависит набор заданий ",
           "(см. [классификацию](02-klassifikaciya.md)).\n\n"]
    for c in chapters:
        if c.extra:
            continue
        head = f"## {c.label}. {c.title}" if c.num not in (0, 15) else f"## {c.title}"
        out.append(f"{head}\n\n")
        if c.systems:
            out.append("Системы: " + ", ".join(f"${s}$" for s in c.systems) + "\n\n")
        out.append("| § | Название | Страницы | PDF | Профиль | Задач |\n|---|---|---|---|---|---|\n")
        for s in c.sections:
            pages = f"{s.page}" if s.end_page <= s.page + 1 else f"{s.page}–{s.end_page - 1}"
            pdf = f"{s.page + 1}"
            out.append(f"| {s.label} | {s.title} | {pages} | {pdf} | {s.profile} — {prof[s.profile]['name'].lower()} | {s.quota} |\n")
        out.append(f"\nВсего задач по главе: **{sum(s.quota for s in c.sections)}**\n\n")
    out.append("## Без параграфов\n\n- Заключение — с. 198 (используется в сквозных задачах).\n- Литература — с. 199.\n")
    return "".join(out)


def plan(chapters, tax) -> str:
    levels = sorted(tax["levels"])
    out = [GEN, "# План распределения 1000 задач\n\n",
           "Квота параграфа пропорциональна его объёму в страницах "
           f"(не меньше {tax['quota']['min_per_section']} и не больше {tax['quota']['max_per_section']} задач). "
           "Внутри параграфа задачи делятся по уровням согласно профилю параграфа. "
           "Числа меняются правкой `data/toc.yaml` и `data/taxonomy.yaml` и пересборкой.\n\n"]
    tot = Counter()
    rows = []
    for c in chapters:
        lc = Counter()
        for s in c.sections:
            lc.update(s.level_quota)
        tot.update(lc)
        rows.append((c, lc))
    out.append("## По главам и уровням\n\n| Глава | " + " | ".join(stars(l) for l in levels) + " | Всего |\n")
    out.append("|---|" + "---|" * (len(levels) + 1) + "\n")
    for c, lc in rows:
        name = f"{c.label}. {c.title}" if c.num not in (0, 15) else c.title
        out.append(f"| {name} | " + " | ".join(str(lc[l]) for l in levels) + f" | **{sum(lc.values())}** |\n")
    out.append("| **Итого** | " + " | ".join(f"**{tot[l]}**" for l in levels) + f" | **{sum(tot.values())}** |\n\n")
    out.append("## По профилям\n\n| Профиль | Параграфов | Задач | Типы заданий |\n|---|---|---|---|\n")
    pc, pq = Counter(), Counter()
    for c in chapters:
        for s in c.sections:
            pc[s.profile] += 1
            pq[s.profile] += s.quota
    for p, d in tax["profiles"].items():
        out.append(f"| {p} — {d['name']} | {pc[p]} | {pq[p]} | {', '.join(f'{t} ({tax['types'][t].lower()})' for t in d['types'])} |\n")
    out.append("\n## По параграфам\n\n")
    for c in chapters:
        name = f"{c.label}. {c.title}" if c.num not in (0, 15) else c.title
        out.append(f"### {name}\n\n| § | Название | Профиль | " + " | ".join(stars(l) for l in levels) + " | Всего |\n")
        out.append("|---|---|---|" + "---|" * (len(levels) + 1) + "\n")
        for s in c.sections:
            out.append(f"| {s.label} | {s.title} | {s.profile} | " + " | ".join(str(s.level_quota[l]) for l in levels) + f" | {s.quota} |\n")
        out.append("\n")
    return "".join(out)


def progress(chapters, problems, tax) -> str:
    levels = sorted(tax["levels"])
    done = defaultdict(Counter)
    for pr in problems:
        done[pr.meta.get("chapter")][pr.meta.get("level")] += 1
    out = [GEN, "# Прогресс\n\n| Глава | " + " | ".join(stars(l) for l in levels) + " | Готово | План |\n"]
    out.append("|---|" + "---|" * (len(levels) + 2) + "\n")
    all_done = all_plan = 0
    for c in chapters:
        lq = Counter()
        for s in c.sections:
            lq.update(s.level_quota)
        d = done[c.num]
        name = f"{c.label}. {c.title}" if c.num not in (0, 15) else c.title
        out.append(f"| [{name}](../problems/{c.slug}/) | " + " | ".join(f"{d[l]}/{lq[l]}" for l in levels)
                   + f" | {sum(d.values())} | {sum(lq.values())} |\n")
        all_done += sum(d.values())
        all_plan += sum(lq.values())
    out.append(f"| **Итого** | " + " | ".join("" for _ in levels) + f" | **{all_done}** | **{all_plan}** |\n")
    return "".join(out)


def chapter_readme(c, problems, tax) -> str:
    mine = [p for p in problems if p.meta.get("chapter") == c.num]
    head = f"# {c.label}. {c.title}" if c.num not in (0, 15) else f"# {c.title}"
    out = [GEN, head, "\n\n"]
    if c.systems:
        out.append("Системы: " + ", ".join(f"${s}$" for s in c.systems) + "\n\n")
    out.append(f"Задач: {len(mine)} из {sum(s.quota for s in c.sections)}.\n\n")
    for s in c.sections:
        secp = [p for p in mine if p.meta.get("section") == s.num]
        pages = "" if c.extra else (f", с. {s.page}" if s.end_page <= s.page + 1 else f", с. {s.page}–{s.end_page - 1}")
        title = s.title if c.extra else f"{s.label}. {s.title}"
        out.append(f"## {title}{pages}\n\nЗадач: {len(secp)} из {s.quota}.\n\n")
        if secp:
            out.append("| № | Уровень | Тип | Задача |\n|---|---|---|---|\n")
            for p in sorted(secp, key=lambda p: p.meta["id"]):
                out.append(f"| [{p.meta['id']}]({p.path.name}) | {stars(p.meta['level'])} | "
                           f"{tax['types'].get(p.meta['type'], '?')} | {problem_title(p)} |\n")
            out.append("\n")
    return "".join(out)


def index_by(problems, tax, field, title, labels) -> str:
    groups = defaultdict(list)
    for p in problems:
        groups[p.meta.get(field)].append(p)
    out = [GEN, f"# {title}\n\n"]
    if not problems:
        out.append("Задач пока нет.\n")
    for key in labels:
        items = sorted(groups.get(key, []), key=lambda p: p.meta["id"])
        if not items:
            continue
        out.append(f"## {labels[key]} ({len(items)})\n\n")
        for p in items:
            rel = p.path.relative_to(ROOT).as_posix()
            out.append(f"- [{p.meta['id']}](../{rel}) {stars(p.meta['level'])} — {problem_title(p)}\n")
        out.append("\n")
    return "".join(out)


TITLES = {0: "Введение: операторы, термины, высказывания, следование",
          2: "Сильное следование, другой вариант"}


def readme(chapters) -> str:
    text = (ROOT / "README.md").read_text(encoding="utf-8")
    rows = ["<!-- sections:start -->\n| № | Раздел | Задач |\n|---|---|---|\n"]
    for c in chapters:
        title = TITLES.get(c.num, c.title)
        if c.systems:
            title += " (" + ", ".join(f"${s}$" for s in c.systems) + ")"
        rows.append(f"| {c.num} | [{title}](problems/{c.slug}/) | {sum(s.quota for s in c.sections)} |\n")
    rows.append(f"| | **Всего** | **{sum(s.quota for c in chapters for s in c.sections)}** |\n<!-- sections:end -->")
    start, end = text.index("<!-- sections:start -->"), text.index("<!-- sections:end -->") + len("<!-- sections:end -->")
    return text[:start] + "".join(rows) + text[end:]


def generate() -> dict:
    tax = load_yaml("taxonomy.yaml")
    chapters = load_book()
    compute_quotas(chapters)
    problems = [p for p in load_problems() if "id" in p.meta]
    files = {
        DOCS / "01-soderzhanie-knigi.md": soderzhanie(chapters, tax),
        DOCS / "03-plan.md": plan(chapters, tax),
        DOCS / "progress.md": progress(chapters, problems, tax),
        DOCS / "indeks-po-urovnyam.md": index_by(problems, tax, "level", "Задачи по уровням сложности",
                                                 {l: f"{stars(l)} {d['name']}" for l, d in tax["levels"].items()}),
        DOCS / "indeks-po-tipam.md": index_by(problems, tax, "type", "Задачи по типам",
                                              {t: f"{t} — {n}" for t, n in tax["types"].items()}),
    }
    files[ROOT / "README.md"] = readme(chapters)
    for c in chapters:
        files[PROBLEMS / c.slug / "README.md"] = chapter_readme(c, problems, tax)
    return files


def main() -> int:
    check = "--check" in sys.argv
    stale = []
    for path, text in generate().items():
        old = path.read_text(encoding="utf-8") if path.exists() else None
        if old != text:
            if check:
                stale.append(path.relative_to(ROOT).as_posix())
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
    if check and stale:
        print("Устарели сгенерированные файлы (запустите scripts/build.py):\n  " + "\n  ".join(stale))
        return 1
    print("Проверено: файлы актуальны." if check else "Готово.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
