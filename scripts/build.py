#!/usr/bin/env python3
"""Генерация оглавлений, плана и расписания занятий из data/*.yaml и карточек задач.

  python3 scripts/build.py          — пересобрать файлы
  python3 scripts/build.py --check  — проверить, что сгенерированные файлы актуальны

Генерируются: docs/01-soderzhanie.md, docs/03-plan.md, docs/06-zanyatiya.md, docs/07-uchebnyj-plan.md,
docs/progress.md,
docs/indeks-po-urovnyam.md, docs/indeks-po-tipam.md, problems/*/README.md
документы занятий zanyatiya/NN.md
и таблица разделов в README.md (между пометками sections:start/end).
Эти файлы руками не правятся.
"""
from __future__ import annotations

import sys
from collections import Counter, defaultdict

from common import (DOCS, PROBLEMS, ROOT, compute_quotas, compute_sessions, load_book, load_problems,
                    load_yaml, problem_title, study_order)

GEN = "<!-- Файл сгенерирован scripts/build.py. Не редактировать вручную. -->\n\n"
LEVELS = range(1, 11)


def lev_head() -> str:
    return " | ".join(str(l) for l in LEVELS)


def soderzhanie(chapters, tax) -> str:
    prof = tax["profiles"]
    out = [GEN, "# Содержание\n\n",
           "Основа — А. А. Зиновьев. *Комплексная логика*. М.: Наука, 1970. 206 с. ",
           "Страницы указаны по нумерации книги; в PDF-скане номер страницы на 1 больше.\n\n",
           "Профиль — характер материала параграфа; от него зависят ступени и типы задач "
           "(см. [классификацию](02-klassifikaciya.md)).\n\n"]
    for c in chapters:
        if c.mixed:
            continue
        out.append(f"## {c.full_title}\n\n")
        if c.systems:
            out.append("Системы: " + ", ".join(f"${s}$" for s in c.systems) + "\n\n")
        if c.sources:
            out.append("Источники:\n\n" + "".join(f"- {s}\n" for s in c.sources) + "\n")
        out.append("| § | Название | Страницы | Профиль | Задач | Диагностика |\n|---|---|---|---|---|---|\n")
        for s in c.sections:
            out.append(f"| {s.label} | {s.title} | {s.pages} | {s.profile} — {prof[s.profile]['name'].lower()} "
                       f"| {s.quota} | {s.diag_quota} |\n")
        out.append(f"\nВсего задач: **{sum(s.quota for s in c.sections)}**\n\n")
    mixed = next(c for c in chapters if c.mixed)
    out.append(f"## {mixed.full_title}\n\nПосле каждой главы — набор задач на всё пройденное к этому моменту, "
               f"всего **{sum(s.quota for s in mixed.sections)}**. Распределение — в [плане](03-plan.md).\n")
    return "".join(out)


def plan(chapters, tax) -> str:
    total = tax["total"]
    out = [GEN, f"# План: {total} задач\n\n",
           "Столбцы 1–10 — ступени сложности (см. [классификацию](02-klassifikaciya.md)). "
           "«Диагн.» — сколько из задач параграфа — диагностика ошибок (тип E).\n\n",
           "Квота параграфа книги пропорциональна его объёму в страницах с весами для плотных мест "
           f"(от {tax['quota']['min_per_section']} до {tax['quota']['max_per_section']} задач). "
           "Перед работой над главой квоты уточняются по числу определений, аксиом и правил в ней. "
           "Числа меняются правкой `data/toc.yaml` и `data/taxonomy.yaml` и пересборкой.\n\n"]
    tot, diag = Counter(), 0
    rows = []
    for c in chapters:
        lc = Counter()
        for s in c.sections:
            lc.update(s.level_quota)
        tot.update(lc)
        d = sum(s.diag_quota for s in c.sections)
        diag += d
        rows.append((c, lc, d))
    out.append(f"## По главам\n\n| Раздел | {lev_head()} | Всего | Диагн. |\n|---|" + "---|" * 12 + "\n")
    for c, lc, d in rows:
        out.append(f"| {c.full_title} | " + " | ".join(str(lc[l]) for l in LEVELS)
                   + f" | **{sum(lc.values())}** | {d} |\n")
    all_ = sum(tot.values())
    out.append("| **Итого** | " + " | ".join(f"**{tot[l]}**" for l in LEVELS) + f" | **{all_}** | **{diag}** |\n")
    out.append("| Доля, % | " + " | ".join(str(round(100 * tot[l] / all_)) for l in LEVELS)
               + f" | 100 | {round(100 * diag / all_)} |\n\n")
    out.append("## Ступени\n\n| № | Ступень | Что требуется | Задач |\n|---|---|---|---|\n")
    for l in LEVELS:
        d = tax["levels"][l]
        out.append(f"| {l} | {d['name']} | {d['short']} | {tot[l]} |\n")
    out.append("\n## По профилям\n\n| Профиль | Параграфов | Задач | Типичные типы |\n|---|---|---|---|\n")
    pc, pq = Counter(), Counter()
    for c in chapters:
        for s in c.sections:
            pc[s.profile] += 1
            pq[s.profile] += s.quota
    for p, d in tax["profiles"].items():
        types = ", ".join(f"{t} ({tax['types'][t].lower()})" for t in d["types"])
        out.append(f"| {p} — {d['name']} | {pc[p]} | {pq[p]} | {types} |\n")
    out.append("\n## По параграфам\n\n")
    for c in chapters:
        out.append(f"### {c.full_title}\n\n| § | Название | Проф. | {lev_head()} | Всего | Диагн. |\n|---|---|---|"
                   + "---|" * 12 + "\n")
        for s in c.sections:
            out.append(f"| {s.label} | {s.title} | {s.profile} | " + " | ".join(str(s.level_quota[l]) for l in LEVELS)
                       + f" | {s.quota} | {s.diag_quota} |\n")
        out.append("\n")
    return "".join(out)


def zanyatiya(chapters, tax) -> str:
    sessions = compute_sessions(chapters)
    size, per_week = tax["sessions"]["size"], tax["sessions"]["per_week"]
    weeks = -(-len(sessions) // per_week)
    out = [GEN, "# Занятия\n\n",
           f"Задачник разбит на **{len(sessions)} занятий** примерно по {size} задач — по образцу семинара "
           f"Зиновьева: занятие 4–6 часов, {per_week} раза в неделю. Это **{weeks} недель**.\n\n",
           "В каждом занятии:\n\n"
           "- **новый материал** — задачи очередных параграфов, по лестнице от простого к сложному;\n"
           "- **повторение** — задачи из смешанного набора по уже пройденным главам: "
           "правила нужно узнавать вперемешку, а не по одному;\n"
           "- около четверти задач в обеих частях — **диагностика**: найти, что не так, и назвать нарушенное правило.\n\n"
           "Последние занятия целиком состоят из смешанных наборов — это итоговое повторение.\n\n"
           "| № | Неделя | Новый материал | Повторение | Задач |\n|---|---|---|---|---|\n"]
    for s in sessions:
        new = "; ".join(f"{sec.key} {sec.title[:40]} ({n})" for c, sec, n in s["new"]) or "—"
        rev = "; ".join(f"{m.title.replace('После: ', 'пройденное до: ')[:60]} ({n})" for m, n in s["mixed"]) or "—"
        n = sum(t for *_, t in s["new"]) + sum(t for _, t in s["mixed"])
        out.append(f"| {s['num']} | {(s['num'] - 1) // per_week + 1} | {new} | {rev} | {n} |\n")
    return "".join(out)


def uchebnyj_plan(chapters, tax) -> str:
    modules = load_yaml("toc.yaml")["modules"]
    sessions = compute_sessions(chapters)
    per_week = tax["sessions"]["per_week"]
    week = lambda n: (n - 1) // per_week + 1
    rows = []
    for i, m in enumerate(modules):
        nums = [s["num"] for s in sessions if any(c.num in m["chapters"] for c, _, _ in s["new"])]
        if i == len(modules) - 1:   # итоговые занятия без нового материала — в последний модуль
            nums += [s["num"] for s in sessions if not s["new"]]
        a, b = min(nums), max(nums)
        new = sum(n for s in sessions for c, _, n in s["new"] if c.num in m["chapters"])
        rev = sum(n for s in sessions if a <= s["num"] <= b for _, n in s["mixed"])
        titles = ", ".join(c.full_title for c in chapters if c.num in m["chapters"])
        rows.append((m, titles, a, b, new, rev))
    total_weeks = week(len(sessions))
    out = [GEN, "# Учебный план\n\n",
           f"**{total_weeks} недель**, {per_week} занятия в неделю по 4–6 часов, {tax['sessions']['size']} задач в занятии — "
           f"всего {len(sessions)} занятий и {sum(s.quota for c in chapters for s in c.sections)} задач. "
           "Задачи идут от простого к сложному; в каждом занятии есть повторение пройденного. "
           "Подробное расписание по занятиям — в [06-zanyatiya.md](06-zanyatiya.md).\n\n",
           "## Модули\n\n| Модуль | Главы | Недели | Занятия | Новых задач | Повторение | Что вы должны уметь к концу модуля |\n"
           "|---|---|---|---|---|---|---|\n"]
    for m, titles, a, b, new, rev in rows:
        out.append(f"| **{m['name']}** | {titles} | {week(a)}–{week(b)} | {a}–{b} | {new} | {rev} | {m['goal']} |\n")
    out.append("""
Соседние модули делят пограничное занятие: в нём заканчивается одна глава и начинается следующая.

## Как проходит занятие (4–6 часов)

| Часть | Время | Что делать |
|---|---|---|
| Чтение | 30 мин | Параграфы книги, которые изучаются сегодня |
| Разобранные примеры | 30 мин | По одному на каждый новый навык; разобрать и пересказать себе каждый шаг |
| Новые задачи | 2,5–3,5 ч | Около 35 задач по лестнице: дополнение решения, однотипные задачи, вариации, задачи без известного ответа, перенос |
| Повторение | 40 мин | Около 5 задач из смешанного набора по прошлым главам |
| Разбор ошибок | 20 мин | Для каждой ошибки записать, какое правило нарушено; задачи с ошибками решить повторно на следующем занятии |

Около четверти задач в каждом занятии — диагностические: «что здесь не так и какое правило нарушено».

## Контрольные точки

В конце каждого модуля — смешанный набор по всему модулю. Он сдан, если решено не меньше 90 % задач, а среди задач ступеней 1–4 — не меньше 95 %. Если результат ниже, повторить задачи по навыкам с ошибками, а потом решить набор снова. Переходить к следующему модулю стоит только после сдачи: каждый модуль опирается на предыдущие.

## Регулярность

Пропуски можно навёрстывать, но лучше не реже двух занятий в неделю: при длинных перерывах навык успевает забыться, и повторение не спасает. Задачи с ошибками стоит вести в отдельном списке и возвращаться к ним через неделю и через месяц.
""")
    return "".join(out)


def progress(chapters, problems, tax) -> str:
    done = defaultdict(Counter)
    for pr in problems:
        done[pr.meta.get("chapter")][pr.meta.get("level")] += 1
    out = [GEN, f"# Прогресс\n\nГотово / план по ступеням.\n\n| Раздел | {lev_head()} | Готово | План |\n|---|"
           + "---|" * 12 + "\n"]
    all_done = all_plan = 0
    for c in chapters:
        lq = Counter()
        for s in c.sections:
            lq.update(s.level_quota)
        d = done[c.num]
        out.append(f"| [{c.full_title}](../problems/{c.slug}/) | " + " | ".join(f"{d[l]}/{lq[l]}" for l in LEVELS)
                   + f" | {sum(d.values())} | {sum(lq.values())} |\n")
        all_done += sum(d.values())
        all_plan += sum(lq.values())
    out.append("| **Итого** | " + " | ".join("" for _ in LEVELS) + f" | **{all_done}** | **{all_plan}** |\n")
    return "".join(out)


def chapter_readme(c, problems, tax) -> str:
    mine = [p for p in problems if p.meta.get("chapter") == c.num]
    out = [GEN, f"# {c.full_title}\n\n"]
    if c.systems:
        out.append("Системы: " + ", ".join(f"${s}$" for s in c.systems) + "\n\n")
    if c.sources:
        out.append("Источники:\n\n" + "".join(f"- {s}\n" for s in c.sources) + "\n")
    out.append(f"Задач: {len(mine)} из {sum(s.quota for s in c.sections)}.\n\n")
    for s in c.sections:
        secp = [p for p in mine if p.meta.get("section") == s.num]
        where = f", {s.pages}" if s.pages else ""
        out.append(f"## {s.label}. {s.title}{where}\n\nЗадач: {len(secp)} из {s.quota} (диагностика: {s.diag_quota}).\n\n")
        if secp:
            out.append("| № | Ступень | Тип | Задача |\n|---|---|---|---|\n")
            for p in sorted(secp, key=lambda p: p.meta["id"]):
                out.append(f"| [{p.meta['id']}]({p.path.name}) | {p.meta['level']} | "
                           f"{tax['types'].get(p.meta['type'], '?')} | {problem_title(p)} |\n")
            out.append("\n")
    return "".join(out)


def index_by(problems, field, title, labels) -> str:
    groups = defaultdict(list)
    for p in problems:
        groups[p.meta.get(field)].append(p)
    out = [GEN, f"# {title}\n\n"]
    if not problems:
        out.append("Задач пока нет.\n")
    for key in labels:
        items = sorted(groups.get(key, []), key=lambda p: p.meta["id"])
        if items:
            out.append(f"## {labels[key]} ({len(items)})\n\n")
            for p in items:
                rel = p.path.relative_to(ROOT).as_posix()
                out.append(f"- [{p.meta['id']}](../{rel}) ступень {p.meta['level']} — {problem_title(p)}\n")
            out.append("\n")
    return "".join(out)


def card_parts(pr) -> dict:
    """Условие, подсказка, ответ и решение карточки без разметки раскрывающихся блоков."""
    import re
    out, parts = {}, re.split(r"^## (.+)$", pr.body, flags=re.M)
    for title, text in zip(parts[1::2], parts[2::2]):
        text = re.sub(r"</?details>|<summary>.*?</summary>", "", text).strip()
        out[title] = text
    return out


def session_sheets(chapters, problems, tax) -> dict:
    """Один документ на занятие: что прочитать, задачи, затем ответы и решения."""
    sessions = compute_sessions(chapters)
    by_sec = defaultdict(list)
    for p in sorted(problems, key=lambda p: p.meta["id"]):
        by_sec[(p.meta["chapter"], p.meta["section"])].append(p)
    started = set()
    files = {}
    for s in sessions:
        items, reading = [], []
        for c, sec, n in s["new"]:
            q = by_sec[(sec.chapter, sec.num)]
            items += q[:n]
            del q[:n]
            cont = " (продолжение)" if sec.key in started else ""
            started.add(sec.key)
            where = c.full_title if sec.num == 0 else f"{c.full_title}, {sec.label}. {sec.title}"
            if sec.page is not None:
                pdf = (f"PDF {sec.page + 1}" if sec.end_page <= sec.page
                       else f"PDF {sec.page + 1}–{sec.end_page + 1}")
                reading.append(f"- {where}{cont} — {sec.pages} ({pdf})")
            else:
                reading.append(f"- {where}{cont} — {sec.source}")
        review = []
        for m, n in s["mixed"]:
            q = by_sec[(m.chapter, m.num)]
            items += q[:n]
            del q[:n]
            review.append(m.title.replace("После: ", ""))
        if not items:
            continue
        items.sort(key=lambda p: (p.meta["level"], p.meta["id"]))
        out = [GEN, f"# Занятие {s['num']}\n\n",
               f"{len(items)} задач, неделя {(s['num'] - 1) // tax['sessions']['per_week'] + 1}. "
               "Ответы и решения — в конце документа; смотрите их только после того, как решите.\n\n",
               "## Что прочитать\n\n",
               "А. А. Зиновьев. *Комплексная логика*. М.: Наука, 1970. "
               "Страницы книги; в скобках — страницы PDF-скана.\n\n", "\n".join(reading) + "\n\n"]
        if review:
            out.append("Повторение без нового чтения: пройденное до — " + "; ".join(review) + ".\n\n")
        out.append("## Задачи\n\n")
        ans = ["\n---\n\n&nbsp;\n\n&nbsp;\n\n&nbsp;\n\n# Ответы и решения\n\n## Ответы\n\n| № | Задача | Ответ |\n|---|---|---|\n"]
        sol = ["\n## Решения\n\n"]
        for i, p in enumerate(items, 1):
            parts = card_parts(p)
            out.append(f"**{i}.** Ступень {p.meta['level']} · {tax['types'][p.meta['type']].lower()}"
                       f" · `{p.meta['id']}`\n\n{parts.get('Условие', '')}\n\n")
            full = parts.get("Ответ", "")
            simple = "|" not in full and len(full) <= 220
            short = full.replace("\n", " ") if simple else "см. ниже, в решениях"
            ans.append(f"| {i} | `{p.meta['id']}` | {short} |\n")
            extra = "" if simple else f"Ответ:\n\n{full}\n\nРешение:\n\n"
            sol.append(f"**{i}.** `{p.meta['id']}`\n\n{extra}{parts.get('Решение', '')}\n\n")
        files[ROOT / "zanyatiya" / f"{s['num']:02d}.md"] = "".join(out + ans + sol)
    return files

TITLES = {0: "Введение: операторы, термины, высказывания, следование",
          2: "Сильное следование, другой вариант"}


def readme(chapters) -> str:
    text = (ROOT / "README.md").read_text(encoding="utf-8")
    rows = ["<!-- sections:start -->\n| № | Раздел | Задач |\n|---|---|---|\n"]
    order = study_order(chapters) + [c for c in chapters if c.mixed]
    for c in order:
        title = TITLES.get(c.num, c.title)
        if c.systems:
            title += " (" + ", ".join(f"${s}$" for s in c.systems) + ")"
        rows.append(f"| {c.num} | [{title}](problems/{c.slug}/) | {sum(s.quota for s in c.sections)} |\n")
    rows.append(f"| | **Всего** | **{sum(s.quota for c in chapters for s in c.sections)}** |\n<!-- sections:end -->")
    a, b = text.index("<!-- sections:start -->"), text.index("<!-- sections:end -->") + len("<!-- sections:end -->")
    return text[:a] + "".join(rows) + text[b:]


def generate() -> dict:
    tax = load_yaml("taxonomy.yaml")
    chapters = load_book()
    compute_quotas(chapters)
    problems = [p for p in load_problems() if "id" in p.meta]
    files = {
        DOCS / "01-soderzhanie.md": soderzhanie(chapters, tax),
        DOCS / "03-plan.md": plan(chapters, tax),
        DOCS / "06-zanyatiya.md": zanyatiya(chapters, tax),
        DOCS / "07-uchebnyj-plan.md": uchebnyj_plan(chapters, tax),
        DOCS / "progress.md": progress(chapters, problems, tax),
        DOCS / "indeks-po-urovnyam.md": index_by(problems, "level", "Задачи по ступеням",
                                                 {l: f"{l}. {d['name']}" for l, d in tax["levels"].items()}),
        DOCS / "indeks-po-tipam.md": index_by(problems, "type", "Задачи по типам",
                                              {t: f"{t} — {n}" for t, n in tax["types"].items()}),
        ROOT / "README.md": readme(chapters),
    }
    for c in chapters:
        files[PROBLEMS / c.slug / "README.md"] = chapter_readme(c, problems, tax)
    files.update(session_sheets(chapters, problems, tax))
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
