#!/usr/bin/env python3
"""Ежемесячные контрольные работы: новые задачи из генераторов глав с другими зёрнами случайности.

Каждый генератор scripts/gen/g*.py запускается заново (несколько прогонов с новыми зёрнами), его карточки
собираются в общий пул. Из пула убираются задачи ступеней 8–10, перемаркированные смешанные наборы (гл. 17) и все задачи,
условие которых уже встречается в data/zadachi. Затем для каждого месяца (8 занятий; последняя работа — после
занятия 90) составляется контрольная: 30 задач, из них около 22 по материалу месяца и около 8 по прошлым месяцам,
ступени 1–7, около четверти — диагностика (тип E).

Пишет data/kontrolnye/KNN.md (карточки, разделённые «=====»); документы kontrolnye/NN.md собирает scripts/build.py.
"""
import importlib.util
import random
import re
import sys
import tempfile
import types
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from common import compute_quotas, compute_sessions, load_book, load_problems  # noqa: E402

GENS = ["g00_04", "g00_05_08", "g01_01", "g01_02", "g01_04_09", "g02", "g02_05", "g05_16", "g06_07", "g07_08", "g08_10", "g10_12", "g12_15"]
RUNS = 3
SIZE, CUR = 30, 22
LEVEL_TARGET = {1: 1, 2: 3, 3: 5, 4: 5, 5: 6, 6: 6, 7: 4}
E_TARGET = 8
TESTS = [(1, 8), (9, 16), (17, 24), (25, 32), (33, 40), (41, 48), (49, 56), (57, 64), (65, 72), (73, 80), (81, 90)]


def cond_of(c):
    return c[c.index("## Условие"):c.index("## Ответ")] if "## Условие" in c and "## Ответ" in c else None


def lock_randoms(mod, seed, seen=None):
    """Пересеять все генераторы случайности модуля и его подмодулей и запретить им повторный seed()."""
    seen = set() if seen is None else seen
    if id(mod) in seen:
        return
    seen.add(id(mod))
    for name, val in list(vars(mod).items()):
        if isinstance(val, random.Random):
            val.seed(seed * 1000 + (hash(mod.__name__ + name) % 997))
            val.seed = lambda *a, **k: None
        elif isinstance(val, types.ModuleType) and re.search(r"scripts/(gen|logic)/", getattr(val, "__file__", "") or ""):
            lock_randoms(val, seed, seen)


def run(name, seed, tmp):
    spec = importlib.util.spec_from_file_location(f"{name}_k{seed}", ROOT / "scripts" / "gen" / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    random.seed(seed)
    lock_randoms(mod, seed)
    root = Path(tmp) / f"{name}_{seed}"
    (root / "drafts").mkdir(parents=True)
    (root / "data").symlink_to(ROOT / "data")
    (root / "scripts").symlink_to(ROOT / "scripts")
    (root / "books").symlink_to(ROOT / "books")
    mod.ROOT = root
    import contextlib
    import io
    with contextlib.redirect_stdout(io.StringIO()):
        mod.main()
    cards = []
    for f in (root / "drafts").glob("*.md"):
        cards += [c.strip() for c in f.read_text(encoding="utf-8").split("\n=====\n") if c.strip()]
    return cards


def has_repeat(c):
    """Подпункты а), б), … с одинаковым содержимым."""
    k = cond_of(c) or ""
    its = re.findall(r"^[а-е]\) (.+)$", k, re.M)
    return len(its) != len(set(its))


def skeleton(c):
    """Условие без формул: одинаковый скелет — одна и та же задача с другими буквами."""
    return re.sub(r"\$[^$]*\$", "$", cond_of(c) or "")


def meta(c):
    m = {}
    for key in ("chapter", "section", "level", "type"):
        mm = re.search(rf"^{key}: (\S+)", c, re.M)
        m[key] = mm.group(1) if mm else None
    return m


def harvest():
    existing = {cond_of(p.body if p.body.startswith("##") else "\n" + p.body) for p in load_problems()}
    existing |= {cond_of(p.body) for p in load_problems()}
    pool, seen = defaultdict(list), set()
    with tempfile.TemporaryDirectory() as tmp:
        for name in GENS:
            runs = []
            for r in range(RUNS):
                try:
                    cards = run(name, 9000 + 37 * r + GENS.index(name), tmp)
                except Exception as e:  # noqa: BLE001
                    print(f"{name}, прогон {r}: {type(e).__name__}: {e}", file=sys.stderr)
                    continue
                runs.append(cards)
            # Условие, повторившееся в разных прогонах, — неслучайная (ручная) карточка: её не берём.
            freq = Counter(k for cards in runs for k in {cond_of(c) for c in cards})
            for cards in runs:
                for c in cards:
                    m = meta(c)
                    k = cond_of(c)
                    if not k or not m["level"] or int(m["level"]) > 7 or m["chapter"] in (None, "17"):
                        continue
                    if freq[k] > 1 or k in existing or k in seen or has_repeat(c):
                        continue
                    seen.add(k)
                    pool[(int(m["chapter"]), int(m["section"]))].append(c)
            print(f"{name}: всего в пуле {sum(len(v) for v in pool.values())}", file=sys.stderr)
    return pool


def month_sections(chapters):
    """{номер работы: Counter({(глава, параграф): задач в занятиях месяца})} — только новый материал."""
    sessions = compute_sessions(chapters)
    out = {}
    for k, (a, b) in enumerate(TESTS, 1):
        cnt = Counter()
        for s in sessions:
            if a <= s["num"] <= b:
                for _, sec, n in s["new"]:
                    cnt[(sec.chapter, sec.num)] += n
        out[k] = cnt
    return out


def alloc(weights, total):
    w = {k: v for k, v in weights.items() if v > 0}
    s = sum(w.values())
    raw = {k: total * v / s for k, v in w.items()}
    res = {k: int(v) for k, v in raw.items()}
    for k in sorted(raw, key=lambda k: raw[k] - res[k], reverse=True)[:total - sum(res.values())]:
        res[k] += 1
    return res


def pick(pool, sec, want_levels, want_e, rnd, used=frozenset()):
    cands = [c for c in pool.get(sec, []) if skeleton(c) not in used]
    if not cands:
        return None
    def score(c):
        m = meta(c)
        lv = int(m["level"])
        s = want_levels.get(lv, 0) * 2
        if m["type"] == "E" and want_e > 0:
            s += 3
        if m["type"] == "E" and want_e <= 0:
            s -= 3
        return s + rnd.random()
    best = max(cands, key=score)
    pool[sec].remove(best)
    return best


def compose(pool, chapters):
    rnd = random.Random(2026)
    months = month_sections(chapters)
    tests = {}
    taught = Counter()
    for k in sorted(months):
        cur = {s: n for s, n in months[k].items() if pool.get(s)}
        prev = {s: n for s, n in taught.items() if pool.get(s)}
        n_cur = CUR if prev else SIZE
        plan = Counter(alloc(cur, n_cur))
        if prev:
            plan.update(alloc(prev, SIZE - n_cur))
        want_l, want_e = dict(LEVEL_TARGET), E_TARGET
        chosen = []
        order = sorted(plan.items(), key=lambda kv: -kv[1])
        slots = [s for s, n in order for _ in range(n)]
        rnd.shuffle(slots)
        for s in slots:
            used = {skeleton(x) for x in chosen}
            c = pick(pool, s, want_l, want_e, rnd, used)
            alt = [x for x in list(cur) + list(prev) if pool.get(x)]
            rnd.shuffle(alt)
            while c is None and alt:
                c = pick(pool, alt.pop(), want_l, want_e, rnd, used)
            if c is None:
                continue
            m = meta(c)
            want_l[int(m["level"])] = want_l.get(int(m["level"]), 0) - 1
            if m["type"] == "E":
                want_e -= 1
            chosen.append(c)
        chosen.sort(key=lambda c: (int(meta(c)["level"]), int(meta(c)["chapter"]), int(meta(c)["section"])))
        tests[k] = chosen
        taught.update(months[k])
    return tests


def write(tests):
    out_dir = ROOT / "data" / "kontrolnye"
    out_dir.mkdir(parents=True, exist_ok=True)
    for k, cards in tests.items():
        fixed = []
        for i, c in enumerate(cards, 1):
            c = re.sub(r"^---\n", f"---\nid: K{k:02d}-{i:02d}\n", c, count=1)
            c = re.sub(r"^generated: true\n", "", c, flags=re.M)
            fixed.append(c)
        (out_dir / f"K{k:02d}.md").write_text("\n\n=====\n\n".join(fixed) + "\n", encoding="utf-8")
        m = [meta(c) for c in cards]
        print(f"K{k:02d}: {len(cards)} задач; ступени {dict(sorted(Counter(int(x['level']) for x in m).items()))}; "
              f"диагностика {sum(x['type'] == 'E' for x in m)}")


def main():
    chapters = load_book()
    compute_quotas(chapters)
    pool = harvest()
    write(compose(pool, chapters))


if __name__ == "__main__":
    main()
