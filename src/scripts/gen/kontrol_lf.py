#!/usr/bin/env python3
"""Контрольные модуля IX после расширения раздела 18 до 800 задач (20 занятий, 91–110).

Контрольная 12 — занятия 91–98 (§ 1–16), контрольная 13 — занятия 99–106 (§ 16–31). Из прежней K12 карточки § 1–16 и
повторение гл. 11–13 остаются в K12, карточки § 18–31 переходят в K13. Недостающие задачи дают трудные генераторы
g18_hard* с другим зерном; их условия не совпадают ни с задачами занятий, ни с другими контрольными, тестами,
примерами и повторением. Переписывает data/kontrolnye/K12.md и K13.md.

Запуск (один раз): python3 src/scripts/gen/kontrol_lf.py
"""
import random
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import g18_hard as H  # noqa: E402
import g18_hard2 as H2  # noqa: E402
import g18_hard3 as H3  # noqa: E402
from g18_open import process_card  # noqa: E402
import kontrolnye as K  # noqa: E402
from common import load_problems  # noqa: E402

SEP = "\n=====\n"


def used():
    out = {K.cond_of(p.body) for p in load_problems()}
    for d in ("kontrolnye", "vhodnye", "primery", "povtorenie"):
        for f in (ROOT / "data" / d).rglob("*.md"):
            for c in f.read_text(encoding="utf-8").split(SEP):
                k = K.cond_of(c)
                if k:
                    out.add(k)
    return out


def gen(plan, seed):
    """plan: [(функция, аргументы)] — по одной карточке на пункт."""
    rnd = random.Random(seed)
    H.rnd = rnd
    H.OUT.clear()
    H.USED.clear()
    H.USED.update(x.replace("## Условие", "").strip() for x in used() if x)
    for mod in (H2, H3):
        mod.card, mod.fresh, mod.rnd = H.card, H.fresh, rnd
    taken = used()
    out = []
    for fn, args in plan:
        for _ in range(20):
            n = len(H.OUT)
            fn(*args)
            if len(H.OUT) > n:
                c = process_card(H.OUT[-1])
                if K.cond_of(c) not in taken:
                    out.append(c)
                    taken.add(K.cond_of(c))
                    break
    return out


def g(c, key):
    return int(re.search(rf"^{key}: (\d+)", c, re.M).group(1))


def assemble(cards, prefix):
    cards = sorted(cards, key=lambda c: (g(c, "level"), 0 if g(c, "chapter") == 18 else 1, g(c, "chapter"), g(c, "section")))
    out = []
    for n, c in enumerate(cards, 1):
        m = re.match(r"---\n(.*?)\n---\n(.*)", c.strip(), re.S)
        front = "\n".join(l for l in m.group(1).splitlines() if not l.startswith(("id:", "test_for:", "generated:")))
        out.append(f"---\nid: {prefix}-{n:02d}\n{front}\n---\n\n{m.group(2).strip()}\n")
    return "\n=====\n\n".join(out)


def main():
    k12 = [c for c in (ROOT / "data/kontrolnye/K12.md").read_text(encoding="utf-8").split(SEP) if c.strip()]
    keep = [c for c in k12 if g(c, "chapter") != 18 or g(c, "section") <= 16]
    move = [c for c in k12 if g(c, "chapter") == 18 and g(c, "section") > 16]
    add12 = gen([(H2.e_series, ()), (H2.k_relations, ()), (H2.v_series, ()), (H2.p_open, ()), (H2.m_long, ()),
                 (H2.k_errors, ()), (H2.md_long, ()), (H2.m_open, ()), (H2.p_series, ())], 20261128)
    add13 = gen([(H.cmp_long, ("p",)), (H.cmp_two_errors, ("p",)), (H.cmp_open, ("p",)), (H.cmp_complete, ("p",)),
                 (H.cmp_long, ("a",)), (H.cmp_complete, ("a",)), (H.cmp_two_errors, ("a",)), (H.cmp_open, ("a",)),
                 (H2.between_general, ()), (H2.between_general, ()), (H2.row_series, ()), (H2.row_series, ()),
                 (H2.row_series, ()), (H2.row_touch_errors, ()), (H3.str_series, ()), (H3.str_series, ()),
                 (H3.str_errors, ()), (H2.p_series, ()), (H2.e_errors, ()), (H2.m_complete, ()), (H2.k_series, ()),
                 (H2.v_open, ()), (H2.md_errors, ())], 20261129)
    k12_new = keep + add12[:30 - len(keep)]
    k13_new = move + add13
    print(f"K12: {len(k12_new)}, K13: {len(k13_new)}")
    assert len(k12_new) == 30 and len(k13_new) == 30
    (ROOT / "data/kontrolnye/K12.md").write_text(assemble(k12_new, "K12"), encoding="utf-8")
    (ROOT / "data/kontrolnye/K13.md").write_text(assemble(k13_new, "K13"), encoding="utf-8")


if __name__ == "__main__":
    main()
