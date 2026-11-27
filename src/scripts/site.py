#!/usr/bin/env python3
"""Данные сайта: карточки → site_src/data/ (генерируются, руками не править); сборка _site/ для публикации.

Данные берутся из тех же карточек и той же раскладки по занятиям, что и документы zanyatiya/
(build.session_models), поэтому сайт и документы не расходятся. Условия, ответы и решения
переводятся в HTML (html_fmt): формулы — символами книги, индексы — верхние и нижние.

  site_src/data/index.json   модули, занятия (номер, неделя, тема), контрольные, входные тесты — для меню и поиска
  site_src/data/z/NN.json    занятие NN: что прочитать, примеры, задачи с ответами и решениями
  site_src/data/k/NN.json    контрольная работа NN
  site_src/data/t/NN.json    входной тест к главе NN
  site_src/data/spravka.json обозначения и классификация задач
  _site/                     index.html + site_src/ (без README) — то, что публикуется на GitHub Pages

Сайт открывается и прямо из корня репозитория: index.html → site_src/.

Запуск: python3 src/scripts/site.py [--check]   (--check: данные актуальны, ничего не пишет)
"""
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from build import (KONTROL_PASS, KONTROL_TIME, VHOD_PASS, VHOD_TIME, card_parts, chapter_starts,  # noqa: E402
                   chapters_label, kontrol_ranges, load_kontrol, load_vhod, session_models, studied_in, week_of)
from common import DOCS, REPO, compute_quotas, compute_sessions, load_book, load_problems, load_yaml  # noqa: E402
from html_fmt import UNKNOWN, md, title  # noqa: E402

DATA_DIR = REPO / "site_src" / "data"
FILES: dict = {}


def card(p, n=None):
    parts = card_parts(p)
    out = {"id": str(p.meta.get("id", "")), "level": p.meta.get("level"), "type": p.meta.get("type"),
           "chapter": p.meta.get("chapter"), "section": p.meta.get("section"),
           "cond": md(parts.get("Условие", "")), "ans": md(parts.get("Ответ", "")), "sol": md(parts.get("Решение", ""))}
    if n is not None:
        out["n"] = n
    return out


def write(path: Path, data) -> None:
    FILES[path] = json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n"


def oboznacheniya() -> list:
    """Обозначения: разделы «## …» документа 04 (без вводного абзаца и столбца LaTeX)."""
    text = (DOCS / "04-oboznacheniya.md").read_text(encoding="utf-8")
    out = []
    for part in re.split(r"^## ", text, flags=re.M)[1:]:
        head, _, body = part.partition("\n")
        out.append({"title": title(head.strip()), "html": md(body)})
    return out


def main() -> int:
    check = "--check" in sys.argv
    out = REPO / "_site"
    tax = load_yaml("taxonomy.yaml")
    toc = load_yaml("toc.yaml")
    chapters = load_book()
    compute_quotas(chapters)
    problems = [p for p in load_problems() if "id" in p.meta]
    sessions = compute_sessions(chapters)
    secs = {(c.num, s.num): (c, s) for c in chapters for s in c.sections}
    where = studied_in(sessions)


    late = {c.num for c in chapters if c.after_course}
    last_main = max(i for i, m in enumerate(toc["modules"]) if not set(m["chapters"]) & late)

    def module_of(chs):
        for i, m in enumerate(toc["modules"]):
            if chs and chs[0] in m["chapters"]:
                return i
        return last_main   # итоговые занятия без нового материала

    def repeat(p):
        c, s = secs[(p.meta["chapter"], p.meta["section"])]
        return {"section": s.key, "title": title(c.full_title if s.num == 0 else f"{c.full_title}, {s.label}. {s.title}"),
                "pages": s.pages if s.page is not None else s.source, "sessions": where.get((c.num, s.num), [])}

    # Занятия
    index_sessions = []
    for m in session_models(chapters, problems, tax):
        mod = module_of(m["chapters"])
        index_sessions.append({"num": m["num"], "week": m["week"], "label": m["label"], "topic": m["topic"],
                               "topicH": title(m["topic"]), "module": mod, "chapters": m["chapters"],
                               "file": m["file"], "tasks": len(m["items"])})
        write(DATA_DIR / "z" / f"{m['num']:02d}.json", {
            "num": m["num"], "week": m["week"], "label": m["label"], "topic": m["topic"], "topicH": title(m["topic"]),
            "module": mod, "book1970": m["book1970"],
            "reading": [dict(r, whereH=title(r["where"])) for r in m["reading"]],
            "review": [title(r) for r in m["review"]],
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
        write(DATA_DIR / "k" / f"{k:02d}.json", {
            "k": k, "after": b, "from": a, "week": week_of(b, tax), "label": chapters_label(month),
            "time": KONTROL_TIME, "pass": KONTROL_PASS,
            "tasks": [dict(card(p, i), repeat=repeat(p)) for i, p in enumerate(tests[k], 1)],
        })

    # Входные тесты
    index_t = []
    starts = chapter_starts(sessions)
    titles = {c.num: c.full_title for c in chapters}
    for ch, items in load_vhod().items():
        index_t.append({"chapter": ch, "title": titles[ch], "titleH": title(titles[ch]), "before": starts[ch], "week": week_of(starts[ch], tax),
                        "sections": sorted({secs[(p.meta["chapter"], p.meta["section"])][1].key for p in items})})
        write(DATA_DIR / "t" / f"{ch:02d}.json", {
            "chapter": ch, "title": titles[ch], "titleH": title(titles[ch]), "before": starts[ch], "time": VHOD_TIME, "pass": VHOD_PASS,
            "tasks": [dict(card(p, i), repeat=repeat(p)) for i, p in enumerate(items, 1)],
        })
    index_t.sort(key=lambda t: t["before"])

    write(DATA_DIR / "index.json", {
        "modules": [{"name": m["name"], "goal": m["goal"], "chapters": m["chapters"]} for m in toc["modules"]],
        "sessions": index_sessions, "kontrol": index_k, "tests": index_t,
    })
    write(DATA_DIR / "spravka.json", {
        "oboznacheniya": oboznacheniya(),
        "levels": tax["levels"], "types": tax["types"], "steps": tax["steps"],
    })
    if UNKNOWN:
        print("Неизвестные команды TeX:", ", ".join(sorted(UNKNOWN)), file=sys.stderr)
        return 1

    old = {p for p in DATA_DIR.rglob("*.json")} if DATA_DIR.exists() else set()
    stale = [p for p, s in FILES.items() if not p.exists() or p.read_text(encoding="utf-8") != s]
    extra = sorted(old - set(FILES))
    if check:
        for p in stale + extra:
            print("устарел:", p.relative_to(REPO))
        if stale or extra:
            print("Данные сайта устарели: python3 src/scripts/site.py")
            return 1
    for p in extra:
        p.unlink()
    for p in stale:
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(FILES[p], encoding="utf-8")

    # site_src/version.json: версии app.css и app.js (хэш содержимого) — index.html грузит их мимо кэша
    ver = json.dumps({n.split(".")[1]: hashlib.sha1((REPO / "site_src" / n).read_bytes()).hexdigest()[:8]
                      for n in ("app.css", "app.js")}) + "\n"
    vfile = REPO / "site_src" / "version.json"
    if not vfile.exists() or vfile.read_text(encoding="utf-8") != ver:
        if check:
            print("устарел: site_src/version.json (версии app.css/app.js)")
            return 1
        vfile.write_text(ver, encoding="utf-8")

    if check:
        print("Проверено: данные сайта актуальны.")
        return 0

    # _site/ — то, что публикуется: index.html из корня и site_src/ без README
    if out.exists():
        shutil.rmtree(out)
    out.mkdir()
    shutil.copy2(REPO / "index.html", out / "index.html")
    (out / ".nojekyll").write_text("", encoding="utf-8")
    shutil.copytree(REPO / "site_src", out / "site_src", ignore=shutil.ignore_patterns("README.md"))
    print(f"Сайт: занятий {len(index_sessions)}, контрольных {len(index_k)}, тестов {len(index_t)}; "
          f"файлов данных {len(FILES)}, обновлено {len(stale)}, удалено {len(extra)}; для публикации — {out.name}/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
