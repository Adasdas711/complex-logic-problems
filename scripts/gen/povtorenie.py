#!/usr/bin/env python3
"""Плановое повторение: каждый параграф возвращается через неделю и через месяц после занятия, где он начался.

Для параграфа, начатого в занятии t, в занятия t + 2 (неделя) и t + 8 (месяц) добавляется по одной новой задаче этого
параграфа. Задачи берутся из генераторов глав с новыми зёрнами (как для контрольных): их условия не совпадают с задачами
занятий, контрольных и примеров решений; ступени 2–6; задача не опирается на главы и параграфы, которые к целевому
занятию ещё не начаты. Около четверти — диагностика (тип E).

Пишет data/povtorenie/povtorenie.md (карточки с полем session — номер занятия); в документ занятия задачи попадают
через scripts/build.py и перемешиваются с остальными.
"""
import random
import re
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "gen"))
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import kontrolnye as K  # noqa: E402
import expand_solutions as X  # noqa: E402
from build import load_kontrol, load_primery  # noqa: E402
from common import compute_quotas, compute_sessions, load_book, load_problems  # noqa: E402

GAPS = {2: "неделя", 8: "месяц"}
RUNS = 4


def started_by(sessions):
    """{занятие: множество начатых к нему (глава, параграф)} и {параграф: занятие, где он начат}."""
    start, seen, by = {}, set(), {}
    for s in sessions:
        for c, sec, _ in s["new"]:
            start.setdefault((c.num, sec.num), s["num"])
            seen.add((c.num, sec.num))
        by[s["num"]] = set(seen)
    return start, by


def ahead(card, ch, taught):
    """Ссылается ли карточка на ещё не начатые главы или параграфы."""
    body = card.split("\n---\n", 1)[-1]
    chapters = {c for c, _ in taught}
    for m in re.finditer(r"гл\. (\d+)", body):
        if int(m.group(1)) not in chapters:
            return True
    for m in re.finditer(r"§ (\d+)(?!\d)(.{0,12})", body):
        if "гл." in m.group(2) or "Введени" in m.group(2) or ch == 0:
            continue
        if (ch, int(m.group(1))) not in taught:
            return True
    return False


def harvest():
    taken = {K.cond_of(p.body) for p in load_problems()}
    taken |= {K.cond_of(p.body) for v in load_kontrol().values() for p in v}
    taken |= {K.cond_of(p.body) for p in load_primery().values()}
    pool, seen = defaultdict(list), set()
    with tempfile.TemporaryDirectory() as tmp:
        for name in K.GENS:
            for r in range(RUNS):
                try:
                    cards = K.run(name, 3000 + 41 * r + K.GENS.index(name), tmp)
                except Exception as e:  # noqa: BLE001
                    print(f"{name}, прогон {r}: {type(e).__name__}: {e}", file=sys.stderr)
                    continue
                for c in cards:
                    m, k = K.meta(c), K.cond_of(c)
                    if not k or not m["level"] or m["chapter"] in (None, "17") or not 2 <= int(m["level"]) <= 6:
                        continue
                    if k in taken or k in seen or K.has_repeat(c):
                        continue
                    seen.add(k)
                    pool[(int(m["chapter"]), int(m["section"]))].append(c)
    reg = X.registry()
    home = X.homes(reg)
    for key, cards in pool.items():
        for i, c in enumerate(cards):
            new = X.expand(c, reg, home)
            if new:
                a = c.index("## Решение")
                cards[i] = c[:a] + "## Решение\n\n" + new + "\n"
    return pool


def main():
    chapters = load_book()
    compute_quotas(chapters)
    sessions = compute_sessions(chapters)
    last = sessions[-1]["num"]
    start, taught = started_by(sessions)
    pool = harvest()
    rnd = random.Random(2027)
    plan = sorted((t + d, key) for key, t in start.items() for d in GAPS if t + d <= last)
    out, e_count, used_skel = [], 0, defaultdict(set)
    for n, (t, key) in enumerate(plan):
        cands = [c for c in pool.get(key, []) if not ahead(c, key[0], taught[t]) and K.skeleton(c) not in used_skel[key]]
        if not cands:
            print(f"нет задачи для § {key} в занятие {t}", file=sys.stderr)
            continue
        want_e = e_count < 0.25 * (len(out) + 1)

        def score(c):
            m = K.meta(c)
            sol = X.parts(c).get("Решение", "")
            return (3 * (m["type"] == "E") * (1 if want_e else -1) - abs(int(m["level"]) - 4)
                    + min(len(sol), 600) / 300 + rnd.random())
        best = max(cands, key=score)
        pool[key].remove(best)
        used_skel[key].add(K.skeleton(best))
        e_count += K.meta(best)["type"] == "E"
        out.append((t, key, best))
    cards = []
    for i, (t, key, c) in enumerate(sorted(out), 1):
        c = re.sub(r"^generated: true\n", "", c.strip(), flags=re.M)
        c = re.sub(r"^(id|step|condition|system|series|case): .*\n", "", c, flags=re.M)
        c = re.sub(r"^---\n", f'---\nid: "R-{t:02d}-{key[0]:02d}.{key[1]:02d}"\nsession: {t}\n', c, count=1)
        cards.append(c)
    d = ROOT / "data" / "povtorenie"
    d.mkdir(parents=True, exist_ok=True)
    (d / "povtorenie.md").write_text("\n\n=====\n\n".join(cards) + "\n", encoding="utf-8")
    print(f"задач повторения: {len(cards)} из {len(plan)}; диагностика: {e_count}")


if __name__ == "__main__":
    main()
