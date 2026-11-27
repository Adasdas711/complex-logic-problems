#!/usr/bin/env python3
"""Сборка сайта: site_src/ + данные занятий → _site/ (в репозиторий не кладётся).

Данные берутся из тех же карточек и той же раскладки по занятиям, что и документы zanyatiya/
(build.session_models), поэтому сайт и документы не расходятся. Текст задач остаётся в Markdown
с формулами $...$ — сайт показывает их сам.

  _site/                 копия site_src/ (кроме README.md)
  _site/data/index.json  модули, занятия (номер, неделя, тема), контрольные, входные тесты — для меню и поиска
  _site/data/z/NN.json   занятие NN: что прочитать, примеры, задачи с ответами и решениями
  _site/data/k/NN.json   контрольная работа NN
  _site/data/t/NN.json   входной тест к главе NN
  _site/data/spravka.json обозначения и классификация задач

Запуск: python3 src/scripts/site.py [--out каталог]
"""
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from build import (KONTROL_PASS, KONTROL_TIME, VHOD_PASS, VHOD_TIME, card_parts, chapter_starts,  # noqa: E402
                   chapters_label, kontrol_ranges, load_kontrol, load_vhod, session_models, studied_in, week_of)
from common import DOCS, REPO, compute_quotas, compute_sessions, load_book, load_problems, load_yaml  # noqa: E402


def card(p, n=None):
    parts = card_parts(p)
    out = {"id": str(p.meta.get("id", "")), "level": p.meta.get("level"), "type": p.meta.get("type"),
           "chapter": p.meta.get("chapter"), "section": p.meta.get("section"),
           "cond": parts.get("Условие", ""), "ans": parts.get("Ответ", ""), "sol": parts.get("Решение", "")}
    if n is not None:
        out["n"] = n
    return out


def write(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")


def main() -> int:
    out = Path(sys.argv[sys.argv.index("--out") + 1]) if "--out" in sys.argv else REPO / "_site"
    tax = load_yaml("taxonomy.yaml")
    toc = load_yaml("toc.yaml")
    chapters = load_book()
    compute_quotas(chapters)
    problems = [p for p in load_problems() if "id" in p.meta]
    sessions = compute_sessions(chapters)
    secs = {(c.num, s.num): (c, s) for c in chapters for s in c.sections}
    where = studied_in(sessions)

    if out.exists():
        shutil.rmtree(out)
    src = REPO / "site_src"
    if src.exists():
        shutil.copytree(src, out, ignore=shutil.ignore_patterns("README.md"))
    out.mkdir(parents=True, exist_ok=True)

    def module_of(chs):
        for i, m in enumerate(toc["modules"]):
            if chs and chs[0] in m["chapters"]:
                return i
        return len(toc["modules"]) - 1

    def repeat(p):
        c, s = secs[(p.meta["chapter"], p.meta["section"])]
        return {"section": s.key, "title": c.full_title if s.num == 0 else f"{c.full_title}, {s.label}. {s.title}",
                "pages": s.pages if s.page is not None else s.source, "sessions": where.get((c.num, s.num), [])}

    # Занятия
    index_sessions = []
    for m in session_models(chapters, problems, tax):
        mod = module_of(m["chapters"])
        index_sessions.append({"num": m["num"], "week": m["week"], "label": m["label"], "topic": m["topic"],
                               "module": mod, "chapters": m["chapters"], "file": m["file"], "tasks": len(m["items"])})
        write(out / "data" / "z" / f"{m['num']:02d}.json", {
            "num": m["num"], "week": m["week"], "label": m["label"], "topic": m["topic"], "module": mod,
            "reading": m["reading"], "review": m["review"],
            "tests": [{"chapter": v["chapter"], "what": v["what"]} for v in m["tests"]],
            "examples": [card(e) for e in m["examples"]], "hideExamples": m["hide_examples"],
            "tasks": [card(p, i) for i, p in enumerate(m["items"], 1)],
        })

    # Контрольные
    index_k = []
    tests = load_kontrol()
    for k, (a, b) in enumerate(kontrol_ranges(sessions), 1):
        if k not in tests:
            continue
        month = {"new": [t for x in sessions if a <= x["num"] <= b for t in x["new"]]}
        index_k.append({"k": k, "after": b, "from": a, "week": week_of(b, tax), "label": chapters_label(month)})
        write(out / "data" / "k" / f"{k:02d}.json", {
            "k": k, "after": b, "from": a, "week": week_of(b, tax), "label": chapters_label(month),
            "time": KONTROL_TIME, "pass": KONTROL_PASS,
            "tasks": [dict(card(p, i), repeat=repeat(p)) for i, p in enumerate(tests[k], 1)],
        })

    # Входные тесты
    index_t = []
    starts = chapter_starts(sessions)
    titles = {c.num: c.full_title for c in chapters}
    for ch, items in load_vhod().items():
        index_t.append({"chapter": ch, "title": titles[ch], "before": starts[ch], "week": week_of(starts[ch], tax),
                        "sections": sorted({secs[(p.meta["chapter"], p.meta["section"])][1].key for p in items})})
        write(out / "data" / "t" / f"{ch:02d}.json", {
            "chapter": ch, "title": titles[ch], "before": starts[ch], "time": VHOD_TIME, "pass": VHOD_PASS,
            "tasks": [dict(card(p, i), repeat=repeat(p)) for i, p in enumerate(items, 1)],
        })
    index_t.sort(key=lambda t: t["before"])

    write(out / "data" / "index.json", {
        "modules": [{"name": m["name"], "goal": m["goal"], "chapters": m["chapters"]} for m in toc["modules"]],
        "sessions": index_sessions, "kontrol": index_k, "tests": index_t,
    })
    write(out / "data" / "spravka.json", {
        "oboznacheniya": (DOCS / "04-oboznacheniya.md").read_text(encoding="utf-8"),
        "levels": tax["levels"], "types": tax["types"], "steps": tax["steps"],
    })
    n = sum(1 for _ in out.rglob("*.json"))
    print(f"Сайт: {out} — занятий {len(index_sessions)}, контрольных {len(index_k)}, тестов {len(index_t)}, файлов данных {n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
