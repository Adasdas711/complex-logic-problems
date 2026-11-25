#!/usr/bin/env python3
"""Разрезает черновики drafts/*.md на карточки problems/<глава>/<id>.md.

Черновик — карточки подряд, разделённые строкой «=====». У каждой карточки YAML-заголовок
без id (номер назначается здесь) и разделы «## Условие», «## Подсказка» (необязательно),
«## Ответ», «## Решение» простым текстом: в раскрывающиеся блоки они оборачиваются здесь.

Номера в параграфе назначаются по возрастанию ступени, после уже существующих карточек.
Существующие карточки не перезаписываются.

  python3 scripts/split_cards.py drafts/00.04.md [...] [--remove]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml

from common import PROBLEMS, ROOT, load_book

ORDER = ["id", "chapter", "section", "level", "type", "step", "condition", "form", "answer",
         "source", "system", "case", "series", "generated", "tags"]
FOLD = {"Подсказка": "Подсказка", "Ответ": "Показать ответ", "Решение": "Показать решение"}


def parse(path: Path):
    for n, chunk in enumerate(re.split(r"^=====\s*$", path.read_text(encoding="utf-8"), flags=re.M)):
        chunk = chunk.strip()
        if not chunk:
            continue
        m = re.match(r"^---\n(.*?)\n---\n(.*)$", chunk, re.S)
        if not m:
            raise SystemExit(f"{path}, карточка {n + 1}: нет YAML-заголовка")
        yield yaml.safe_load(m.group(1)), m.group(2).strip()


def fold(body: str) -> str:
    parts = re.split(r"^## (.+)$", body, flags=re.M)
    out = []
    for title, text in zip(parts[1::2], parts[2::2]):
        text = text.strip()
        if title in FOLD and not text.startswith("<details>"):
            text = f"<details><summary>{FOLD[title]}</summary>\n\n{text}\n\n</details>"
        if title == "Подсказка":
            out.append(text)
        else:
            out.append(f"## {title}\n\n{text}")
    return "\n\n".join(out) + "\n"


def dump_meta(meta: dict) -> str:
    keys = [k for k in ORDER if k in meta] + [k for k in meta if k not in ORDER]
    lines = []
    for k in keys:
        v = meta[k]
        lines.append(f"{k}: " + (f'"{v}"' if k in ("id", "source") else yaml.safe_dump(v, allow_unicode=True,
                     default_flow_style=True).strip().removesuffix("...").strip()))
    return "---\n" + "\n".join(lines) + "\n---\n\n"


def main(args):
    remove = "--remove" in args
    files = [Path(a) for a in args if a != "--remove"]
    slugs = {c.num: c.slug for c in load_book()}
    cards = {}
    for f in files:
        for i, (meta, body) in enumerate(parse(f)):
            cards.setdefault((meta["chapter"], meta["section"]), []).append((meta["level"], f.name, i, meta, body))
    written = 0
    for (ch, sec), items in sorted(cards.items()):
        folder = PROBLEMS / slugs[ch]
        folder.mkdir(parents=True, exist_ok=True)
        prefix = f"{ch:02d}.{sec:02d}-"
        used = [int(p.stem.split("-")[1]) for p in folder.glob(prefix + "*.md")]
        nxt = max(used, default=0) + 1
        for level, _, _, meta, body in sorted(items, key=lambda t: t[:3]):
            pid = f"{prefix}{nxt:03d}"
            path = folder / f"{pid}.md"
            if path.exists():
                raise SystemExit(f"{path} уже существует")
            meta = {**meta, "id": pid}
            path.write_text(dump_meta(meta) + fold(body), encoding="utf-8")
            nxt += 1
            written += 1
    print(f"Записано карточек: {written}")
    if remove:
        for f in files:
            f.unlink()


if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).parent))
    main(sys.argv[1:])
