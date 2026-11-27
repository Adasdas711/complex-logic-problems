#!/usr/bin/env python3
"""Усложнение гл. 7 «Теория кванторов» (занятия 48–59) по образцу занятия 10.

Заменяет карточки src/data/zadachi/07.md в тех же номерах (глава и параграф сохраняются; задачи ступеней 8–10
расставлены по номерам так, чтобы в каждое занятие попало 3–6 таких задач). Виды задач:
  — выводы в S^s_cq и S^s_nq в 8–12 строк (схемы, R1, R2, ссылки на S^s), проверка q7.check; дополнение длинных
    выводов (пропущены и основания, и формулы строк); выводы с двумя неверными основаниями; вывод с ошибочным шагом
    (почти-пример схемы: условие на свободные вхождения, ∀ вместо ∃ и т. п.);
  — составные замены и почти-примеры схем (A5, T17, T18, T7, A*5 — условия на свободные вхождения);
  — свободные и связанные вхождения, вырожденные группы, бескванторные формы длинных высказываний и формул;
  — серии длинных формул с обоснованием: MT1–MT3 § 3, интерпретационная форма § 7 (опровергающие значения на
    конечных областях отмеченных терминов), контрольная форма и процедура § 9, неклассический случай § 15–17;
  — построения «постройте или докажите, что нельзя» и метатеоремы ступеней 8–10 (вручную, hard07_hand.py; часть —
    прежние ручные задачи главы, перенесённые в другие номера параграфа).
Модель — src/scripts/logic/q7.py, выводы — hard07_der.py, задачи параграфов — hard07_a.py (§ 1–9), hard07_b.py
(§ 10–21).

Запуск: python3 src/scripts/gen/hard07.py
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
sys.path.insert(0, str(ROOT / "scripts" / "gen"))
sys.path.insert(0, str(ROOT / "scripts"))
from open_form import test_like  # noqa: E402
import hard07_a as A  # noqa: E402
import hard07_a2 as A2  # noqa: E402
import hard07_a3 as A3  # noqa: E402
import hard07_b as B  # noqa: E402
import hard07_hand as HH  # noqa: E402

PATH = ROOT / "data" / "zadachi" / "07.md"
KEEPFILE = ROOT / "scripts" / "gen" / "hard07_keep.md"


def render(cid, c):
    sec = int(cid.split(".")[1].split("-")[0])
    sysl = f'system: {c["system"]}\n' if c.get("system") else ""
    gen = "generated: true\n" if c.get("generated", True) else ""
    return (f'---\nid: "{cid}"\nchapter: 7\nsection: {sec}\nlevel: {c["level"]}\ntype: {c["type"]}\n'
            f'step: {c["step"]}\ncondition: {c.get("condition", "def")}\nform: {c["form"]}\nanswer: {c["answer"]}\n'
            f'source: "{c["source"]}"\n{sysl}{gen}tags: [{c["tags"]}]\n---\n\n## Условие\n\n{c["cond"]}\n\n'
            f'## Ответ\n\n{c["ans"]}\n\n## Решение\n\n{c["sol"]}\n')


def main():
    text = PATH.read_text(encoding="utf-8")
    parts = re.split(r"(\n=====\n)", text)
    old = {}
    for chunk in parts:
        m = re.search(r'^id: "(07\.\d\d-\d{3})"', chunk, re.M)
        if m:
            old[m.group(1)] = chunk
    kept = {}
    for chunk in KEEPFILE.read_text(encoding="utf-8").split("\n=====\n"):
        m = re.search(r'^id: "(07\.\d\d-\d{3})"', chunk, re.M)
        if m:
            kept[m.group(1)] = chunk
    cards = {}
    for mod in (A, A2, A3, B):
        for cid, fn in mod.plan().items():
            cards[cid] = fn() if callable(fn) else fn
    cards.update(HH.HAND)
    keep = {}
    for mod in (A, A2, A3, B, HH):
        keep.update(getattr(mod, "KEEP", {}))
    assert not set(cards) & set(keep), sorted(set(cards) & set(keep))
    for cid, c in cards.items():
        assert not test_like(c["cond"]), (cid, c["cond"][:160])
        assert cid in old, cid
    done = set()
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(07\.\d\d-\d{3})"', chunk, re.M)
        if not m:
            continue
        cid = m.group(1)
        lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
        tail = "\n" if chunk.endswith("\n") else ""
        if cid in cards:
            parts[i] = lead + render(cid, cards[cid]).rstrip("\n") + tail
        elif cid in keep:
            src, lvl = keep[cid]
            body = kept[src].lstrip("\n")
            body = re.sub(r'^id: "[^"]+"', f'id: "{cid}"', body, count=1, flags=re.M)
            if lvl:
                body = re.sub(r"^level: \d+", f"level: {lvl}", body, count=1, flags=re.M)
            parts[i] = lead + body.rstrip("\n") + tail
        else:
            continue
        done.add(cid)
    missing = sorted(set(old) - done)
    PATH.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {len(cards)}, перенесено ручных: {len(keep)}, без изменений: {len(missing)}")
    if missing:
        print("без изменений:", ", ".join(missing))


if __name__ == "__main__":
    main()
