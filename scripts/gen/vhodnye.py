#!/usr/bin/env python3
"""Входные тесты к главам: 8–10 новых задач на то, что глава берёт из предыдущих.

Для каждой главы (кроме Введения и смешанных наборов) задан перечень параграфов прежних глав,
на которые она опирается (PREREQ). Задачи берутся из тех же генераторов, что и контрольные
(scripts/gen/kontrolnye.py), но с другими зёрнами случайности; условия, уже встречающиеся
в занятиях, контрольных и плановом повторении, отбрасываются. Ступени 1–5, хотя бы одна задача
на каждый параграф перечня, около четверти — диагностика.

Пишет data/vhodnye/VNN.md (NN — номер главы); документы собирает scripts/build.py.
Запуск: python3 scripts/gen/vhodnye.py [--pool] (с --pool — только показать, сколько задач в пуле).
"""
import random
import re
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import kontrolnye as K  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import expand_solutions as X  # noqa: E402

REF = re.compile(r"[сС]\. \d|§|D\d|A\d|T\d|R\d|MT\d|Очерки")
_REG = None


def prepare(c):
    """Решение из одной ссылки на страницу расписывается по шагам (scripts/expand_solutions.py);
    если это невозможно — задача не берётся. Решению без ссылки на книгу добавляется источник."""
    global _REG
    if _REG is None:
        reg = X.registry()
        _REG = (reg, X.homes(reg))
    if "## Решение" not in c:
        return None
    new = X.expand(c, *_REG)
    sol = c[c.index("## Решение") + len("## Решение"):].strip()
    core = re.sub(r"\n\nИсточник:.*", "", sol).strip()
    if new:
        c = c[:c.index("## Решение")] + "## Решение\n\n" + new.strip()
    elif X.PAGE_ONLY.fullmatch(core):
        # У диагностики ответ уже называет нарушенное правило: решение — этот разбор со ссылкой на страницу.
        ans = c.split("## Ответ", 1)[1].split("## Решение", 1)[0].strip()
        typ = (re.search(r"^type: (\S+)", c, re.M) or [None, ""])[1]
        if typ != "E" or len(ans) < 40 or not REF.search(ans + core):
            return None
        c = c[:c.index("## Решение")] + "## Решение\n\n" + ans + f"\n\nИсточник: {core.rstrip('.')}."
    sol = c[c.index("## Решение") + len("## Решение"):]
    if not REF.search(sol):
        src = (re.search(r'^source: "?(.*?)"?$', c, re.M) or [None, ""])[1]
        if not src:
            return None
        c = c.rstrip() + f"\n\nИсточник: {src}."
    if len(re.sub(r"\s", "", sol)) < 12:
        return None
    return c

ROOT = K.ROOT
OUT = ROOT / "data" / "vhodnye"

# Глава → параграфы прежних глав, которыми она пользуется (по тексту книги: на что ссылаются
# определения, аксиомные схемы и доказательства главы).
PREREQ = {
    1: ["00.04", "00.05", "00.07", "00.08"],
    2: ["01.01", "01.02", "01.05", "01.07"],
    3: ["01.01", "01.04", "01.05", "02.01"],
    4: ["01.04", "01.05", "03.01", "03.02", "03.05"],
    5: ["01.05", "03.02", "04.01", "04.02", "04.03", "04.04"],
    16: ["00.05", "01.05", "05.02", "05.06"],
    6: ["01.05", "04.03", "05.02", "05.05", "05.06"],
    7: ["00.04", "00.05", "00.07", "01.05", "05.02"],
    8: ["05.05", "05.06", "07.01", "07.02"],
    9: ["00.04", "07.01", "07.02", "08.01", "08.02"],
    10: ["09.01", "09.02", "09.04", "07.02", "07.07"],
    11: ["09.01", "09.03", "07.02", "08.01", "08.03", "05.05"],
    12: ["06.01", "06.04", "07.02", "11.01", "11.02", "05.05"],
    13: ["05.05", "06.06", "07.02", "11.02", "12.02"],
    14: ["05.05", "08.01", "08.03", "12.02", "12.06"],
    15: ["01.05", "01.07", "07.01", "07.07", "07.15"],
}
SIZE_MIN, SIZE_MAX = 8, 10
MAX_LEVEL = 5


def key(c):
    m = K.meta(c)
    return f"{int(m['chapter']):02d}.{int(m['section']):02d}"


def taken():
    """Условия, которые уже есть в занятиях, контрольных и плановом повторении."""
    out = set()
    for d in ("zadachi", "kontrolnye", "povtorenie", "primery"):
        for f in (ROOT / "data" / d).glob("*.md"):
            for c in f.read_text(encoding="utf-8").split("\n=====\n"):
                k = K.cond_of(c.strip())
                if k:
                    out.add(k.replace("## Условие", "").strip())
    return out


def harvest():
    K.RUNS = 3
    # другие зёрна, чем у контрольных
    orig = K.run
    K.run = lambda name, seed, tmp: orig(name, seed + 4000, tmp)
    pool = K.harvest()
    K.run = orig
    busy = taken()
    out = {}
    for sec, cards in pool.items():
        k = f"{sec[0]:02d}.{sec[1]:02d}"
        good = [c for c in cards if K.cond_of(c).replace("## Условие", "").strip() not in busy and int(K.meta(c)["level"]) <= MAX_LEVEL]
        good = [x for x in (prepare(c) for c in good) if x]
        if good:
            out[k] = good
    return out


def compose(pool):
    rnd = random.Random(1970)
    tests = {}
    used, proofs = set(), set()
    for ch, secs in PREREQ.items():
        avail = [s for s in secs if pool.get(s)]
        missing = [s for s in secs if not pool.get(s)]
        if missing:
            print(f"гл. {ch}: в пуле нет задач для {', '.join(missing)}", file=sys.stderr)
        size = max(SIZE_MIN, min(SIZE_MAX, 2 * len(avail)))
        slots = list(avail)
        while len(slots) < size and avail:
            slots += avail
        slots = slots[:size]
        chosen, n_e, skels = [], 0, set()
        want_e = round(size / 4)
        for i, s in enumerate(slots):
            first = i < len(avail)          # первый проход — по одной задаче на параграф, попроще
            cands = [c for c in pool[s] if skel(c) not in skels and K.cond_of(c) not in used
                     and re.sub(r"\[[^\]]*\]", "", K.cond_of(c)) not in proofs]
            if not cands:
                continue

            def score(c):
                m = K.meta(c)
                lv, sc = int(m["level"]), 0.0
                sc -= abs(lv - (2 if first else 4))
                if m["type"] == "E":
                    sc += 2 if n_e < want_e and not first else -2
                return sc + rnd.random()
            best = max(cands, key=score)
            pool[s].remove(best)
            used.add(K.cond_of(best))
            skels.add(skel(best))
            if K.cond_of(best).count("\n1. ") or re.search(r"\n\d+\. .*\[", K.cond_of(best)):
                proofs.add(re.sub(r"\[[^\]]*\]", "", K.cond_of(best)))   # один и тот же вывод — в одном тесте
            n_e += K.meta(best)["type"] == "E"
            chosen.append(best)
        chosen.sort(key=lambda c: (int(K.meta(c)["level"]), key(c)))
        tests[ch] = chosen
    return tests


QPAREN = re.compile(r"(\(\\(?:exists|forall) [a-z]\))\(\\sim \(([a-z]) \\leftarrow ([a-z])\)\)")


def tidy(c):
    """Запись по соглашению задачника: после кванторной группы $\\sim(a \\leftarrow b)$ без лишних скобок;
    тильда над составным термином — $\\widetilde{(\\ldots)}$."""
    c = QPAREN.sub(r"\1\\sim (\2 \\leftarrow \3)", c)
    while "\\tilde (" in c:
        i = c.index("\\tilde (")
        j, d = i + len("\\tilde "), 0
        for k in range(j, len(c)):
            d += (c[k] == "(") - (c[k] == ")")
            if d == 0:
                break
        c = c[:i] + "\\widetilde{" + c[j:k + 1] + "}" + c[k + 1:]
    return c


def skel(c):
    """Скелет условия без формул, слов в кавычках и оснований в скобках: одинаковый — одна и та же задача."""
    k = K.cond_of(c) or ""
    return re.sub(r"\$[^$]*\$|«[^»]*»|\[[^\]]*\]", "", k)


def write(tests):
    OUT.mkdir(parents=True, exist_ok=True)
    for ch, cards in tests.items():
        fixed = []
        for i, c in enumerate(cards, 1):
            c = re.sub(r"^---\n", f"---\nid: V{ch:02d}-{i:02d}\ntest_for: {ch}\n", c, count=1)
            c = re.sub(r"^generated: true\n", "", c, flags=re.M)
            fixed.append(tidy(c))
        (OUT / f"V{ch:02d}.md").write_text("\n\n=====\n\n".join(fixed) + "\n", encoding="utf-8")
        m = [K.meta(c) for c in cards]
        print(f"V{ch:02d}: {len(cards)} задач; параграфы {dict(Counter(key(c) for c in cards))}; "
              f"ступени {dict(sorted(Counter(int(x['level']) for x in m).items()))}; "
              f"диагностика {sum(x['type'] == 'E' for x in m)}")


def main():
    pool = harvest()
    if "--pool" in sys.argv:
        for ch, secs in PREREQ.items():
            print(ch, {s: len(pool.get(s, [])) for s in secs})
        return
    write(compose(pool))


if __name__ == "__main__":
    main()
