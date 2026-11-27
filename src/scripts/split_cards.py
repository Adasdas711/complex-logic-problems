#!/usr/bin/env python3
"""Переносит карточки из черновиков drafts/*.md в data/zadachi/<ГГ>.md, назначая номера.

Черновик — карточки подряд, разделённые строкой «=====». У каждой карточки YAML-заголовок
без id (номер назначается здесь) и разделы «## Условие», «## Подсказка» (необязательно),
«## Ответ», «## Решение».

Номера в параграфе назначаются по возрастанию ступени, после уже существующих карточек.
Существующие карточки не меняются: новые дописываются в конец файла главы.

  python3 src/scripts/split_cards.py drafts/00.04.md [...] [--remove]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml

from common import ZADACHI, load_problems

ORDER = ["id", "chapter", "section", "level", "type", "step", "condition", "form", "answer",
         "source", "system", "case", "series", "generated", "tags"]


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
    return body.strip() + "\n"


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
    existing = {}
    for p in load_problems():
        if "id" in p.meta:
            existing.setdefault(p.meta["id"][:5], []).append(int(p.meta["id"].split("-")[1]))
    cards = {}
    for f in files:
        for i, (meta, body) in enumerate(parse(f)):
            cards.setdefault((meta["chapter"], meta["section"]), []).append((meta["level"], f.name, i, meta, body))
    written = 0
    ZADACHI.mkdir(parents=True, exist_ok=True)
    new_text = {}
    for (ch, sec), items in sorted(cards.items()):
        prefix = f"{ch:02d}.{sec:02d}"
        nxt = max(existing.get(prefix, []), default=0) + 1
        for level, _, _, meta, body in sorted(items, key=lambda t: t[:3]):
            pid = f"{prefix}-{nxt:03d}"
            new_text.setdefault(f"{ch:02d}", []).append(dump_meta({**meta, "id": pid}) + fold(body))
            nxt += 1
            written += 1
    for ch, chunks in new_text.items():
        path = ZADACHI / f"{ch}.md"
        old = path.read_text(encoding="utf-8").rstrip() + "\n\n=====\n\n" if path.exists() else ""
        path.write_text(old + "\n=====\n\n".join(chunks), encoding="utf-8")
    print(f"Записано карточек: {written}")
    if remove:
        for f in files:
            f.unlink()


if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).parent))
    main(sys.argv[1:])
