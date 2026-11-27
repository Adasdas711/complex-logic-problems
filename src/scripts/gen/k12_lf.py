#!/usr/bin/env python3
"""Контрольная 12 (модуль IX, занятия 91–100) и входной тест к разделу 18: пул новых задач из генераторов.

Генераторы g18 («Логическая физика», гл. 2) и g10_12, g12_15 («Комплексная логика», гл. 10–13) запускаются
с новыми зёрнами, как в kontrolnye.py. Из пула убираются ручные карточки (условие повторяется в разных прогонах)
и все условия, которые уже есть в занятиях, контрольных, входных тестах, примерах и повторении.
Пишет drafts/k12-pool-<глава>.md — из них вручную отбираются карточки для data/kontrolnye/K12.md и
data/vhodnye/V18.md.
"""
import re
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import kontrolnye as K  # noqa: E402
from common import load_problems  # noqa: E402

ROOT = HERE.parents[1]
GENS = {"g18": 18, "g10_12": None, "g12_15": None}
CHAPTERS = {"0", "7", "10", "11", "12", "13", "18"}


def used_conditions():
    out = {K.cond_of(p.body) for p in load_problems()}
    for d in ("kontrolnye", "vhodnye", "primery", "povtorenie"):
        for f in (ROOT / "data" / d).rglob("*.md"):
            for c in f.read_text(encoding="utf-8").split("\n=====\n"):
                k = K.cond_of(c)
                if k:
                    out.add(k)
    return out


def main():
    used = used_conditions()
    pool = defaultdict(list)
    seen = set()
    with tempfile.TemporaryDirectory() as tmp:
        for name in GENS:
            runs = [K.run(name, 12000 + 41 * r, tmp) for r in range(3)]
            freq = Counter(k for cards in runs for k in {K.cond_of(c) for c in cards})
            for cards in runs:
                for c in cards:
                    k, m = K.cond_of(c), K.meta(c)
                    if not k or m["chapter"] not in CHAPTERS or int(m["level"]) > 7:
                        continue
                    if freq[k] > 1 or k in used or k in seen or K.has_repeat(c):
                        continue
                    seen.add(k)
                    pool[m["chapter"]].append(K.open_form_text(c))
    for ch, cards in pool.items():
        path = ROOT / "drafts" / f"k12-pool-{ch}.md"
        path.parent.mkdir(exist_ok=True)
        path.write_text("\n=====\n\n".join(cards), encoding="utf-8")
        print(f"гл. {ch}: {len(cards)} → {path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
