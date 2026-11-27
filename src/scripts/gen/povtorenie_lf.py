#!/usr/bin/env python3
"""Плановое повторение для раздела 18 (модуль IX): параграф, начатый в занятии t, возвращается в занятиях t + 2
(неделя) и t + 8 (месяц), если они не позже последнего занятия раздела 18. Задачи — из генераторов g18 (ступени 2–3)
и g18_hard* (ступени 4–6) с новыми зёрнами; условия не совпадают ни с какими другими задачами; около четверти —
диагностика. Для параграфов без генератора повторения нет. Пишет data/povtorenie/lf18.md. Запуск один раз."""
import random
import re
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import g18_hard as H  # noqa: E402
import g18_hard2 as H2  # noqa: E402
import g18_hard3 as H3  # noqa: E402
import kontrolnye as K  # noqa: E402
from kontrol_lf import gen, used  # noqa: E402
from povtorenie import GAPS, ahead, started_by  # noqa: E402
from g18_open import process_card  # noqa: E402
from common import compute_quotas, compute_sessions, load_book  # noqa: E402

FAM = [(H2.v_series, ()), (H2.v_errors, ()), (H2.p_series, ()), (H2.p_errors, ()), (H2.e_series, ()), (H2.e_errors, ()),
       (H2.m_long, ()), (H2.m_errors, ()), (H2.k_series, ()), (H2.k_errors, ()), (H2.k_relations, ()),
       (H.cmp_long, ("p",)), (H.cmp_two_errors, ("p",)), (H.cmp_complete, ("a",)), (H.cmp_two_errors, ("a",)),
       (H2.between_general, ()), (H2.row_series, ()), (H2.row_touch_errors, ()), (H3.str_series, ()), (H3.str_errors, ()),
       (H.cmp_long, ("m", True)), (H.cmp_two_errors, ("m", True)), (H3.ord_series, ()), (H3.ord_errors, ()),
       (H2.md_errors, ())]


def pool():
    out = defaultdict(list)
    taken = used()
    for c in gen(FAM * 3, 20261201):
        out[int(K.meta(c)["section"])].append(c)
    with tempfile.TemporaryDirectory() as tmp:
        for r in range(6):
            try:
                run = K.run("g18", 7100 + 37 * r, tmp)
            except ValueError:
                continue
            for c in run:
                m, k = K.meta(c), K.cond_of(c)
                if k and k not in taken and 2 <= int(m["level"]) <= 3:
                    taken.add(k)
                    out[int(m["section"])].append(process_card(c))
    return out


def main():
    chapters = load_book()
    compute_quotas(chapters)
    sessions = compute_sessions(chapters)
    last = max(s["num"] for s in sessions if any(c.num == 18 for c, _, _ in s["new"]))
    start, taught = started_by(sessions)
    P = pool()
    rnd = random.Random(2028)
    plan = sorted((t + d, key) for key, t in start.items() if key[0] == 18 for d in GAPS if t + d <= last)
    out, e = [], 0
    for t, key in plan:
        cands = [c for c in P.get(key[1], []) if not ahead(c, 18, taught[t])]
        if not cands:
            continue
        want_e = e < 0.25 * (len(out) + 1)
        best = max(cands, key=lambda c: 3 * (K.meta(c)["type"] == "E") * (1 if want_e else -1) + rnd.random())
        P[key[1]].remove(best)
        e += K.meta(best)["type"] == "E"
        out.append((t, key, best))
    cards = []
    for t, key, c in sorted(out):
        c = re.sub(r"^generated: true\n", "", c.strip(), flags=re.M)
        c = re.sub(r"^(id|step|condition|system|series|case): .*\n", "", c, flags=re.M)
        c = re.sub(r"^---\n", f'---\nid: "R-{t:02d}-18.{key[1]:02d}"\nsession: {t}\n', c, count=1)
        cards.append(c)
    (ROOT / "data/povtorenie/lf18.md").write_text("\n\n=====\n\n".join(cards) + "\n", encoding="utf-8")
    print(f"задач повторения: {len(cards)} из {len(plan)}; диагностика: {e}")


if __name__ == "__main__":
    main()
