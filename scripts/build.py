#!/usr/bin/env python3
"""Генерация оглавлений, плана и расписания занятий из data/*.yaml и карточек задач.

  python3 scripts/build.py          — пересобрать файлы
  python3 scripts/build.py --check  — проверить, что сгенерированные файлы актуальны

Генерируются: docs/01-soderzhanie.md, docs/03-plan.md, docs/06-zanyatiya.md, docs/07-uchebnyj-plan.md,
docs/progress.md,
docs/indeks-po-urovnyam.md, docs/indeks-po-tipam.md,
документы занятий и ежемесячных контрольных в zanyatiya/ — «NN. Неделя W Тема.md» и «NNк. Неделя W Контрольная работа K.md»
(контрольные — из data/kontrolnye/KNN.md)
и таблица разделов в README.md (между пометками sections:start/end).
Эти файлы руками не правятся.
"""
from __future__ import annotations

import re
import sys
from collections import Counter, defaultdict
from urllib.parse import quote

import yaml

from common import (CARD_SEP, DATA, DOCS, FRONT_RE, ROOT, Problem, compute_quotas, compute_sessions, load_book, load_problems,
                    load_yaml, problem_title, study_order)

GEN = "<!-- Файл сгенерирован scripts/build.py. Не редактировать вручную. -->\n\n"
LEVELS = range(1, 11)
SHEETS = ROOT / "zanyatiya"


def _clean(name: str) -> str:
    """Имя файла без символов, недопустимых в Windows и macOS."""
    name = re.sub(r":\s*(\w)", lambda m: ". " + m.group(1).upper(), name).replace("*", "∗").replace("/", "–")
    return re.sub(r'[<>"\\|?]', "", name).strip()


def session_topic(s) -> str:
    """Тема занятия. Одна глава: название параграфа или «глава, § a–b»; несколько глав: «глава, § …» для каждой."""
    by_ch = {}
    for c, sec, _ in s["new"]:
        ch, secs = by_ch.setdefault(c.num, (c, []))
        if sec.num not in [x.num for x in secs]:
            secs.append(sec)
    short = lambda c: c.title.split(":")[0]
    parts = []
    for c, secs in by_ch.values():
        nums = [x.num for x in secs if x.num]
        if len(by_ch) == 1 and len(secs) == 1:
            parts.append(short(c) if secs[0].num == 0 else secs[0].title)
        elif not nums:
            parts.append(short(c))
        else:
            parts.append(f"{short(c)}, § {min(nums)}" + (f"–{max(nums)}" if max(nums) > min(nums) else ""))
    return "; ".join(parts) or "Итоговое повторение"


def chapters_label(s) -> str:
    """«Глава 7», «Главы 6, 7», «Введение, глава 1», «Глава 5, раздел 16», «Итоговое повторение»."""
    nums = list(dict.fromkeys(c.num for c, _, _ in s["new"]))
    if not nums:
        return "Итоговое повторение"
    special = {0: "Введение", 15: "приложение", 16: "раздел 16"}
    regular = [n for n in nums if n not in special]
    parts = []
    if 0 in nums:
        parts.append("Введение")
    if regular:
        word = "глава" if len(regular) == 1 else "главы"
        parts.append(f"{word} " + ", ".join(map(str, regular)))
    parts += [special[n] for n in nums if n in (15, 16)]
    text = ", ".join(parts)
    return text[0].upper() + text[1:]


def week_of(num: int, tax) -> int:
    return (num - 1) // tax["sessions"]["per_week"] + 1


def session_name(s, tax) -> str:
    return _clean(f"{s['num']:02d}. Неделя {week_of(s['num'], tax)} {session_topic(s)}") + ".md"


def kontrol_name(k: int, after: int, tax) -> str:
    return _clean(f"{after:02d}к. Неделя {week_of(after, tax)} Контрольная работа {k}") + ".md"


def link(name: str, prefix: str = "../zanyatiya/") -> str:
    return prefix + quote(name)



def expand_source(src: str) -> str:
    """«Очерки, с. 352–353; LSR, с. 496» → полные названия и страницы PDF (Очерки: +5; LSR: +4)."""
    import re as _re

    def pdf(m):
        a, b = int(m.group(1)), int(m.group(2) or m.group(1))
        return f"{m.group(0)} (PDF {a + 5}" + (f"–{b + 5})" if b != a else ")")
    out = []
    for part in src.split("; "):
        if part.startswith("Очерки"):
            pages = _re.sub(r"(\d+)(?:–(\d+))?", pdf, part[len("Очерки, "):])
            out.append(f"А. А. Зиновьев. *Очерки комплексной логики* (2000), {pages}")
        elif part.startswith("LSR"):
            pages = _re.sub(r"(\d+)(?:–(\d+))?", lambda m: f"{m.group(0)} (PDF {int(m.group(1)) + 4}" +
                            (f"–{int(m.group(2)) + 4})" if m.group(2) else ")"), part[len("LSR, "):])
            out.append(f"A. Sinowjew, H. Wessel. *Logische Sprachregeln*, Kap. 14, § 3, {pages}")
        else:
            out.append(part)
    return "; ".join(out)

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
        out.append(f"| [{s['num']}]({link(session_name(s, tax))}) | {(s['num'] - 1) // per_week + 1} | {new} | {rev} | {n} |\n")
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
| Примеры решений | 30 мин | По одному на каждый новый параграф; разобрать и пересказать себе каждый шаг. С главы 6 решение примера скрыто: сначала попробовать решить самому, потом открыть |
| Задачи | 3–4 ч | 40 задач занятия и от 0 до 7 задач планового повторения |
| Разбор ошибок | 20 мин | Для каждой ошибки записать, какое правило нарушено; задачи с ошибками решить повторно на следующем занятии |

Задачи идут не блоками, а вперемешку. Первые четыре задачи каждого нового параграфа стоят подряд сразу после его примера. Дальше задачи разных параграфов и типов чередуются, чтобы для каждой задачи приходилось самому выбирать нужное правило. Внутри параграфа сохраняется порядок от простых к сложным.

Каждый параграф возвращается дважды: через неделю (два занятия спустя) и через месяц (восемь занятий спустя) — по одной новой задаче. Эти задачи не повторяют задач занятий и контрольных.

Около четверти задач в каждом занятии — диагностические: «что здесь не так и какое правило нарушено».

## Контрольные точки

""" + kontrol_section(chapters, tax) + """В конце каждого модуля — смешанный набор по всему модулю. Он сдан, если решено не меньше 90 % задач, а среди задач ступеней 1–4 — не меньше 95 %. Если результат ниже, повторить задачи по навыкам с ошибками, а потом решить набор снова. Переходить к следующему модулю стоит только после сдачи: каждый модуль опирается на предыдущие.

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
        out.append(f"| {c.full_title} | " + " | ".join(f"{d[l]}/{lq[l]}" for l in LEVELS)
                   + f" | {sum(d.values())} | {sum(lq.values())} |\n")
        all_done += sum(d.values())
        all_plan += sum(lq.values())
    out.append("| **Итого** | " + " | ".join("" for _ in LEVELS) + f" | **{all_done}** | **{all_plan}** |\n")
    return "".join(out)


def index_by(problems, field, title, labels, where, names) -> str:
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
                n = where.get(p.meta["id"])
                ref = f"[занятие {n}]({link(names[n])})" if n else "вне занятий"
                out.append(f"- `{p.meta['id']}` ступень {p.meta['level']}, {ref} — {problem_title(p)}\n")
            out.append("\n")
    return "".join(out)


def card_parts(pr) -> dict:
    """Условие, подсказка, ответ и решение карточки без разметки раскрывающихся блоков."""
    import re
    out, parts = {}, re.split(r"^## (.+)$", pr.body, flags=re.M)
    for title, text in zip(parts[1::2], parts[2::2]):
        text = re.sub(r"</?details>|<summary>.*?</summary>", "", text).strip()
        # Подпункты «а) … б) …» на отдельных строках: в Markdown одиночный перевод строки — пробел, нужен жёсткий перенос.
        text = re.sub(r"(?<=\S)\n(?=[а-з]\) )", "  \n", text)
        out[title] = text
    return out


def assign(chapters, problems):
    """Раскладывает задачи по занятиям: {номер занятия: [задачи]}."""
    by_sec = defaultdict(list)
    for p in sorted(problems, key=lambda p: p.meta["id"]):
        by_sec[(p.meta["chapter"], p.meta["section"])].append(p)
    out = {}
    for s in compute_sessions(chapters):
        items = []
        for _, sec, n in s["new"]:
            q = by_sec[(sec.chapter, sec.num)]
            items += q[:n]
            del q[:n]
        for m, n in s["mixed"]:
            q = by_sec[(m.chapter, m.num)]
            items += q[:n]
            del q[:n]
        out[s["num"]] = items
    return out


def session_of(chapters, problems) -> dict:
    return {p.meta["id"]: n for n, items in assign(chapters, problems).items() for p in items}


def session_sheets(chapters, problems, tax) -> dict:
    """Один документ на занятие: что прочитать, примеры решений, задачи, затем решения и ответы."""
    sessions = compute_sessions(chapters)
    assigned = assign(chapters, problems)
    started = set()
    files = {}
    examples = load_primery()
    spaced = load_povtorenie()
    hide_from = next((x["num"] for x in sessions if any(c.num == HIDE_FROM_CHAPTER for c, _, _ in x["new"])), 10 ** 6)
    for s in sessions:
        items, reading, fresh = list(assigned[s["num"]]) + spaced.get(s["num"], []), [], []
        for c, sec, n in s["new"]:
            cont = " (продолжение)" if sec.key in started else ""
            if sec.key not in started:
                fresh.append((c, sec))
            started.add(sec.key)
            where = c.full_title if sec.num == 0 else f"{c.full_title}, {sec.label}. {sec.title}"
            if sec.page is not None:
                pdf = (f"PDF {sec.page + 1}" if sec.end_page <= sec.page
                       else f"PDF {sec.page + 1}–{sec.end_page + 1}")
                reading.append(f"- {where}{cont} — {sec.pages} ({pdf})")
            else:
                reading.append(f"- {where}{cont} — {expand_source(sec.source)}")
        review = [m.title.replace("После: ", "") for m, _ in s["mixed"]]
        if not items:
            continue
        items.sort(key=lambda p: (p.meta["level"], p.meta["id"]))
        out = [GEN, f"# Занятие {s['num']}. Неделя {week_of(s['num'], tax)}. {chapters_label(s)}\n\n",
               "## Что прочитать\n\n"]
        if not reading:
            out.append("Нового чтения нет: занятие целиком повторительное.\n\n")
        else:
            out += [("А. А. Зиновьев. *Комплексная логика*. М.: Наука, 1970. "
                     "Страницы книги; в скобках — страницы PDF-скана.\n\n" if any(sec.page is not None for _, sec, _ in s["new"])
                     else "Страницы книг; в скобках — страницы PDF-скана, где он есть.\n\n"), "\n".join(reading) + "\n\n"]
        if review:
            out.append("Повторение без нового чтения: пройденное до — " + "; ".join(review) + ".\n\n")
        shown = [(c, sec, examples[(c.num, sec.num)]) for c, sec in fresh if (c.num, sec.num) in examples]
        out.append("## Примеры решений\n\n")
        if not shown:
            out.append("Нет.\n\n")
        for j, (c, sec, ex) in enumerate(shown, 1):
            parts = card_parts(ex)
            body = f"**Решение.**\n\n{parts.get('Решение', '')}\n\n**Ответ.** {parts.get('Ответ', '')}\n\n"
            if s["num"] >= hide_from:
                body = f"<details>\n<summary>Решение</summary>\n\n{body}</details>\n\n"
            out.append(f"**Пример {j}.** {parts.get('Условие', '')}\n\n{body}")
        items = interleave(items, [(c.num, sec.num) for c, sec in fresh])
        out.append("## Задачи\n\n")
        sol = ["\n---\n\n&nbsp;\n\n&nbsp;\n\n&nbsp;\n\n## Ответы и решения\n\n### Решения\n\n"]
        ans = ["\n### Ответы\n\n| № | Ответ |\n|---|---|\n"]
        for i, p in enumerate(items, 1):
            parts = card_parts(p)
            out.append(f"{i}\\. {parts.get('Условие', '')}\n\n")
            full = parts.get("Ответ", "")
            simple = "|" not in full and len(full) <= 220
            short = full.replace("\n", " ") if simple else f"см. решение {i}"
            ans.append(f"| {i} | {short} |\n")
            extra = "" if simple else f"\n\nОтвет:\n\n{full}"
            sol.append(f"{i}\\. {parts.get('Решение', '')}{extra}\n\n")
        files[SHEETS / session_name(s, tax)] = "".join(out + sol + ans)
    return files

KONTROL = DATA / "kontrolnye"
KONTROL_TIME = "3 часа"
KONTROL_PASS = ("Работа сдана, если верно решено не меньше 24 задач из 30 (80 %) и среди задач ступеней 1–4 "
                "ошибок не больше одной. Задача засчитывается, только если ответ верен и обоснование ссылается "
                "на нужные определения и правила книги; для задач-диагностик — если названо нарушенное правило.")


PRIMERY = DATA / "primery" / "primery.md"
POVTORENIE = DATA / "povtorenie" / "povtorenie.md"
# С какой главы (в порядке изучения) решение примера скрыто: сначала попробовать решить самому.
HIDE_FROM_CHAPTER = 6


def load_povtorenie() -> dict:
    """{занятие: [задачи планового повторения]} из data/povtorenie/povtorenie.md."""
    out = defaultdict(list)
    if not POVTORENIE.exists():
        return out
    for chunk in CARD_SEP.split(POVTORENIE.read_text(encoding="utf-8")):
        chunk = chunk.strip()
        m = FRONT_RE.match(chunk + "\n") if chunk else None
        if m:
            meta = yaml.safe_load(m.group(1)) or {}
            out[meta["session"]].append(Problem(POVTORENIE, meta, chunk[m.end():]))
    return out


def interleave(items, fresh_keys, warmup=4):
    """Порядок задач занятия.

    Первые `warmup` задач каждого начинающегося параграфа идут подряд (после его примера), остальные задачи всех
    параграфов — продолжающихся, новых и повторения — перемешиваются так, чтобы соседние задачи по возможности
    относились к разным параграфам, а внутри параграфа — к разным типам. Внутри параграфа сохраняется порядок
    лестницы (по возрастанию ступени)."""
    key = lambda p: (p.meta["chapter"], p.meta["section"])
    groups = defaultdict(list)
    for p in items:
        groups[key(p)].append(p)
    for g in groups.values():
        g.sort(key=lambda p: (p.meta["level"], str(p.meta.get("id"))))
    head = []
    for k in fresh_keys:
        if k in groups:
            head += groups[k][:warmup]
            groups[k] = groups[k][warmup:]
    # Задачи повторения — одна общая группа, чтобы они расходились по всему занятию, а не стояли подряд.
    rev = [p for k in list(groups) for p in groups[k] if str(p.meta.get("id", "")).startswith("R-")]
    for k in list(groups):
        groups[k] = [p for p in groups[k] if not str(p.meta.get("id", "")).startswith("R-")]
    if rev:
        groups["повторение"] = rev
    # Равномерное распределение: i-я задача группы из n получает место (i + 0.5) / n.
    order = sorted(((i + 0.5) / len(g), gi, i, p) for gi, g in enumerate(groups.values()) for i, p in enumerate(g))
    rest = [p for *_, p in order]
    # Соседние задачи одного параграфа и типа разводим, меняя местами с ближайшей подходящей.
    sig = lambda p: (key(p), p.meta["type"])
    prev = head[-1] if head else None
    for i in range(len(rest)):
        if prev is not None and sig(rest[i]) == sig(prev):
            for j in range(i + 1, min(i + 6, len(rest))):
                if sig(rest[j]) != sig(prev) and (j + 1 >= len(rest) or sig(rest[i]) != sig(rest[j + 1]) or True):
                    if key(rest[j]) == key(rest[i]) and rest[j].meta["level"] < rest[i].meta["level"] - 1:
                        continue
                    rest[i], rest[j] = rest[j], rest[i]
                    break
        prev = rest[i]
    return head + rest


def load_primery() -> dict:
    """{(глава, параграф): карточка разобранного примера} из data/primery/primery.md."""
    out = {}
    if not PRIMERY.exists():
        return out
    for chunk in CARD_SEP.split(PRIMERY.read_text(encoding="utf-8")):
        chunk = chunk.strip()
        m = FRONT_RE.match(chunk + "\n") if chunk else None
        if m:
            meta = yaml.safe_load(m.group(1)) or {}
            out[(meta["chapter"], meta["section"])] = Problem(PRIMERY, meta, chunk[m.end():])
    return out


def load_kontrol() -> dict:
    """{номер работы: [карточки]} из data/kontrolnye/KNN.md."""
    import re
    out = {}
    for f in sorted(KONTROL.glob("K*.md")):
        cards = []
        for chunk in CARD_SEP.split(f.read_text(encoding="utf-8")):
            chunk = chunk.strip()
            m = FRONT_RE.match(chunk + "\n") if chunk else None
            if m:
                cards.append(Problem(f, yaml.safe_load(m.group(1)) or {}, chunk[m.end():]))
        out[int(re.sub(r"\D", "", f.stem))] = cards
    return out


def kontrol_ranges(sessions) -> list:
    """Месяц — 8 занятий; последняя работа охватывает и итоговые занятия."""
    last = len(sessions)
    out, a = [], 1
    while a <= last:
        b = a + 7 if last - (a + 7) >= 8 else last
        out.append((a, b))
        a = b + 1
    return out


def kontrol_section(chapters, tax) -> str:
    tests = load_kontrol()
    if not tests:
        return ""
    sessions = compute_sessions(chapters)
    per_week = tax["sessions"]["per_week"]
    rows = ["Раз в месяц (после каждых восьми занятий) — контрольная работа: 30 новых задач, которых нет в занятиях, "
            f"время — {KONTROL_TIME}. Около трёх четвертей задач — по материалу месяца, остальные — по прошлым месяцам; "
            "ступени 1–7, около четверти — диагностика.\n\n"
            "| Работа | После занятия | Неделя | Материал месяца |\n|---|---|---|---|\n"]
    for k, (a, b) in enumerate(kontrol_ranges(sessions), 1):
        if k not in tests:
            continue
        chs = sorted({c.num for s in sessions if a <= s["num"] <= b for c, _, _ in s["new"]})
        mat = ", ".join(f"гл. {n}" if n else "введение" for n in chs) or "повторение"
        rows.append(f"| [Контрольная {k}]({link(kontrol_name(k, b, tax))}) | {b} | {(b - 1) // per_week + 1} | {mat} |\n")
    return "".join(rows) + "\n"


def kontrol_sheets(chapters, tax) -> dict:
    tests = load_kontrol()
    sessions = compute_sessions(chapters)
    secs = {(c.num, sec.num): (c, sec) for c in chapters for sec in c.sections}
    per_week = tax["sessions"]["per_week"]
    files = {}
    for k, (a, b) in enumerate(kontrol_ranges(sessions), 1):
        items = tests.get(k)
        if not items:
            continue
        def where_key(key):
            c, sec = secs[key]
            return c.full_title if sec.num == 0 else f"{c.full_title}, {sec.label}"
        where = lambda p: where_key((p.meta["chapter"], p.meta["section"]))
        mat = sorted({(p.meta["chapter"], p.meta["section"]) for p in items})
        cur = {(sec.chapter, sec.num) for s in sessions if a <= s["num"] <= b for _, sec, _ in s["new"]}
        month = {"new": [t for x in sessions if a <= x["num"] <= b for t in x["new"]]}
        out = [GEN, f"# Контрольная работа {k}. Неделя {week_of(b, tax)}. {chapters_label(month)}\n\n",
               f"После занятия {b} (неделя {(b - 1) // per_week + 1}); материал месяца — занятия {a}–{b}. "
               f"30 задач, время — **{KONTROL_TIME}**. Книгой и своими записями пользоваться можно, "
               "ответами и решениями занятий — нельзя. Решения и ответы — в конце документа.\n\n",
               "## Как оценивать\n\n" + KONTROL_PASS + " Если работа не сдана, по таблице ответов найдите параграфы "
               "с ошибками, повторите их задачи в занятиях и через неделю решите неверные задачи этой работы снова.\n\n",
               "## Что проверяется\n\n",
               "По материалу месяца: " + "; ".join(where_key(x) for x in mat if x in cur) + ".\n\n"]
        prev = [where_key(x) for x in mat if x not in cur]
        if prev:
            out.append("Повторение прошлых месяцев: " + "; ".join(prev) + ".\n\n")
        out.append("## Задачи\n\n")
        sol = ["\n---\n\n&nbsp;\n\n&nbsp;\n\n&nbsp;\n\n## Ответы и решения\n\n### Решения\n\n"]
        ans = ["\n### Ответы\n\n| № | Ответ | Что повторить при ошибке |\n|---|---|---|\n"]
        for i, p in enumerate(items, 1):
            parts = card_parts(p)
            out.append(f"{i}\\. {parts.get('Условие', '')}\n\n")
            full = parts.get("Ответ", "")
            simple = "|" not in full and len(full) <= 220
            short = full.replace("\n", " ") if simple else f"см. решение {i}"
            ans.append(f"| {i} | {short} | {where(p)} |\n")
            extra = "" if simple else f"\n\nОтвет:\n\n{full}"
            sol.append(f"{i}\\. {parts.get('Решение', '')}{extra}\n\n")
        files[SHEETS / kontrol_name(k, b, tax)] = "".join(out + sol + ans)
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
        rows.append(f"| {c.num} | {title} | {sum(s.quota for s in c.sections)} |\n")
    rows.append(f"| | **Всего** | **{sum(s.quota for c in chapters for s in c.sections)}** |\n<!-- sections:end -->")
    a, b = text.index("<!-- sections:start -->"), text.index("<!-- sections:end -->") + len("<!-- sections:end -->")
    return text[:a] + "".join(rows) + text[b:]


def generate() -> dict:
    tax = load_yaml("taxonomy.yaml")
    chapters = load_book()
    compute_quotas(chapters)
    problems = [p for p in load_problems() if "id" in p.meta]
    where = session_of(chapters, problems)
    names = {s["num"]: session_name(s, tax) for s in compute_sessions(chapters)}
    files = {
        DOCS / "01-soderzhanie.md": soderzhanie(chapters, tax),
        DOCS / "03-plan.md": plan(chapters, tax),
        DOCS / "06-zanyatiya.md": zanyatiya(chapters, tax),
        DOCS / "07-uchebnyj-plan.md": uchebnyj_plan(chapters, tax),
        DOCS / "progress.md": progress(chapters, problems, tax),
        DOCS / "indeks-po-urovnyam.md": index_by(problems, "level", "Задачи по ступеням",
                                                 {l: f"{l}. {d['name']}" for l, d in tax["levels"].items()}, where, names),
        DOCS / "indeks-po-tipam.md": index_by(problems, "type", "Задачи по типам",
                                              {t: f"{t} — {n}" for t, n in tax["types"].items()}, where, names),
        ROOT / "README.md": readme(chapters),
    }
    files.update(session_sheets(chapters, problems, tax))
    files.update(kontrol_sheets(chapters, tax))
    return files


def main() -> int:
    check = "--check" in sys.argv
    stale = []
    files = generate()
    # Лишние файлы в папках документов (старые имена) удаляются; при --check считаются устаревшими.
    for folder in (SHEETS, ROOT / "kontrolnye"):
        for f in sorted(folder.glob("*.md")) if folder.exists() else []:
            if f not in files:
                if check:
                    stale.append(f.relative_to(ROOT).as_posix() + " (лишний)")
                else:
                    f.unlink()
    for path, text in files.items():
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
