#!/usr/bin/env python3
"""Разобранные примеры к параграфам раздела 18: 14 — из генераторов g18_hard* (новое зерно), остальные — вручную
(drafts/primery18-hand.md). Дописывает их в data/primery/primery.md с номерами «П-18.NN». Запуск один раз."""
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
from kontrol_lf import gen  # noqa: E402

PLAN = [(H2.v_series, ()), (H2.k_series, ()), (H2.e_series, ()), (H2.m_long, ()), (H2.md_long, ()), (H2.p_series, ()),
        (H.cmp_long, ("p",)), (H.cmp_long, ("a",)), (H2.between_general, ()), (H2.row_series, ()),
        (H2.row_touch_errors, ()), (H3.str_series, ()), (H.cmp_long, ("m", True)), (H3.ord_series, ())]


def norm(c, sec_hint=None):
    m = re.match(r"---\n(.*?)\n---\n(.*)", c.strip(), re.S)
    front = [l for l in m.group(1).splitlines() if not l.startswith(("id:", "step:", "condition:", "generated:", "case:"))]
    sec = int(re.search(r"^section: (\d+)", m.group(1), re.M).group(1))
    return sec, f'---\nid: "П-18.{sec:02d}"\n' + "\n".join(front) + f"\n---\n\n{m.group(2).strip()}\n"


def main():
    cards = gen(PLAN, 20261130)
    hand = [c for c in (ROOT / "drafts/primery18-hand.md").read_text(encoding="utf-8").split("\n=====\n") if c.strip()]
    allc = dict(norm(c) for c in cards + hand)
    assert len(allc) == 41, sorted(allc)
    path = ROOT / "data/primery/primery.md"
    text = path.read_text(encoding="utf-8").rstrip() + "\n\n=====\n\n" + "\n=====\n\n".join(allc[s] for s in sorted(allc))
    path.write_text(text, encoding="utf-8")
    print("примеров:", len(allc))


if __name__ == "__main__":
    main()
