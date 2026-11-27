#!/usr/bin/env python3
"""Усложнённые серии гл. 1, § 5 и § 7: длинные формулы (3–4 буквы, вложенность 3) и обязательное обоснование
значениями. Заменяет в src/data/zadachi/01.md карточки § 5, § 7 с сериями трёх видов (по формулировке условия):
  «тавтология (§ 5, D2), противоречие (§ 5, D3)…» — вид высказывания и свидетельствующие значения;
  «Проверьте тавтологичность каждой формулы следования…» — тавтологичность и опровергающие значения;
  «сильная тавтология (§ 7, D1)…» — сильная тавтология, тавтология с новой буквой, нетавтология.
Значения вычисляются по s1.value (главная интерпретация, § 5, с. 22).

Запуск: python3 src/scripts/gen/hard01_series.py
"""
import itertools
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
from s1 import C, D, N, V, atoms, counterexample, ftex, new_atoms, strong_tautology, tautology, tex, value  # noqa: E402

rnd = random.Random(1970_105)
L = "абвгдеж"
CONV = "Буквы $x, y, z, u, w$ — элементарные высказывания; запись по соглашению книги (с. 15)."


def rand_f(depth, letters):
    if depth == 0 or rnd.random() < 0.2:
        a = V(rnd.choice(letters))
        return N(a) if rnd.random() < 0.3 else a
    k = rnd.random()
    if k < 0.2:
        return N(rand_f(depth - 1, letters))
    op = C if k < 0.6 else D
    return op(rand_f(depth - 1, letters), rand_f(depth - 1, letters))


def dup(f):
    """Есть одинаковые члены конъюнкции или дизъюнкции ($yy$, $y : y$) или двойное отрицание буквы."""
    if f[0] == "v":
        return False
    if f[0] == "neg":
        return (f[1][0] == "neg") or dup(f[1])
    return len(set(f[1])) < len(f[1]) or any(dup(c) for c in f[1])


def rand_ok(depth, letters):
    while True:
        f = rand_f(depth, letters)
        if not dup(f):
            return f


def envs(names):
    for vals in itertools.product((0, 1), repeat=len(names)):
        yield dict(zip(names, vals))


def kind(f):
    names = sorted(atoms(f))
    vs = {value(f, e) for e in envs(names)}
    return "taut" if vs == {1} else "contr" if vs == {0} else "neither"


def env_t(e):
    return ", ".join(f"${k} = {v}$" for k, v in sorted(e.items()))


def witness(f, want):
    names = sorted(atoms(f))
    return next(e for e in envs(names) if value(f, e) == want)


def classify_card():
    need = ["taut", "contr", "neither", "neither", rnd.choice(["taut", "contr"])]
    items = []
    while len(items) < 5:
        f = rand_ok(3, rnd.sample("xyz", rnd.choice([2, 3])))
        k = kind(f)
        if k == need[len(items)] and 14 <= len(tex(f)) <= 32 and f not in items and len(atoms(f)) >= 2:
            items.append(f)
    rnd.shuffle(items)
    name = {"taut": "тавтология", "contr": "противоречие", "neither": "ни тавтология, ни противоречие"}
    ans, sol = [], []
    for k, f in enumerate(items):
        kd = kind(f)
        ans.append(f"{L[k]}) {name[kd]}")
        n = 2 ** len(atoms(f))
        if kd == "neither":
            sol.append(f"{L[k]}) При {env_t(witness(f, 1))} — 1, при {env_t(witness(f, 0))} — 0.")
        else:
            sol.append(f"{L[k]}) Во всех {n} наборах значений — {1 if kd == 'taut' else 0}.")
    body = "\n".join(f"{L[k]}) ${tex(f)}$" for k, f in enumerate(items))
    cond = (f"{CONV} Определите вид каждого высказывания по D2 и D3 § 5 (с. 22) и обоснуйте его значениями: "
            "для тавтологии и противоречия — перебором всех наборов, для остального — двумя наборами с разными "
            f"значениями.\n\n{body}")
    return dict(cond=cond, ans="; ".join(ans), sol="По главной интерпретации (§ 5, с. 22):\n\n" + "  \n".join(sol), level=4)


def entail_card():
    items = []
    need = [True, False, False, rnd.choice([True, False])]
    while len(items) < 4:
        lt = rnd.sample("xyz", 3)
        a, b = rand_ok(2, lt), rand_ok(2, lt)
        if tautology(a, b) == need[len(items)] and 16 <= len(tex(a)) + len(tex(b)) <= 36 and kind(a) == "neither":
            items.append((a, b))
    rnd.shuffle(items)
    ans, sol = [], []
    for k, (a, b) in enumerate(items):
        if tautology(a, b):
            ans.append(f"{L[k]}) тавтология")
            sol.append(f"{L[k]}) Во всех наборах, где посылка равна 1, заключение равно 1.")
        else:
            e = counterexample(a, b)
            ans.append(f"{L[k]}) не тавтология: {env_t(e)}")
            sol.append(f"{L[k]}) При {env_t(e)} посылка — 1, заключение — 0.")
    body = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b) in enumerate(items))
    cond = (f"{CONV} Проверьте тавтологичность каждой формулы следования при главной интерпретации (§ 5, D1). "
            f"Для нетавтологий укажите значения элементарных высказываний, при которых формула имеет значение 0.\n\n{body}")
    return dict(cond=cond, ans="; ".join(ans), sol="§ 5, D1 (с. 22): формула следования имеет значение 0, только если "
                "посылка — 1, а заключение — 0.\n\n" + "  \n".join(sol), level=4)


def strong_card():
    items = []
    need = ["strong", "new", "non", rnd.choice(["strong", "new", "non"])]
    while len(items) < 4:
        lt = rnd.sample("xyz", 2)
        a = rand_ok(2, lt)
        if need[len(items)] == "new":
            b = rand_ok(2, lt + ["u"])
        else:
            b = rand_ok(2, lt)
        st = "strong" if strong_tautology(a, b) else "new" if tautology(a, b) else "non"
        if st == need[len(items)] and 14 <= len(tex(a)) + len(tex(b)) <= 34 and kind(a) == "neither":
            items.append((a, b))
    rnd.shuffle(items)
    ans, sol = [], []
    for k, (a, b) in enumerate(items):
        if strong_tautology(a, b):
            ans.append(f"{L[k]}) сильная тавтология")
            sol.append(f"{L[k]}) Тавтология, и в заключении нет букв, отсутствующих в посылке.")
        elif tautology(a, b):
            na = ", ".join(f"${t}$" for t in sorted(new_atoms(a, b)))
            ans.append(f"{L[k]}) тавтология, но не сильная")
            sol.append(f"{L[k]}) Тавтология, но в заключение входит {na}, которого нет в посылке.")
        else:
            e = counterexample(a, b)
            ans.append(f"{L[k]}) не тавтология")
            sol.append(f"{L[k]}) При {env_t(e)} посылка — 1, заключение — 0.")
    body = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b) in enumerate(items))
    cond = (f"{CONV} Сильная тавтология (§ 7, D1, с. 25) — тавтология, в заключение которой не входят элементарные "
            "высказывания, отсутствующие в посылке. Установите для каждой формулы, сильная ли это тавтология, и "
            f"обоснуйте: для нетавтологии — опровергающими значениями, для несильной — новой буквой.\n\n{body}")
    return dict(cond=cond, ans="; ".join(ans), sol="  \n".join(sol), level=4)


STEMS = [("тавтология (§ 5, D2), противоречие (§ 5, D3)", classify_card),
         ("Определите вид каждого высказывания по D2 и D3 § 5", classify_card),
         ("Установите для каждой формулы, сильная ли это тавтология", strong_card),
         ("Проверьте тавтологичность каждой формулы следования при главной интерпретации (§ 5, D1)", entail_card),
         ("сильная тавтология (§ 7, D1), тавтология, но не сильная", strong_card)]


def main():
    path = ROOT / "data" / "zadachi" / "01.md"
    parts = re.split(r"(\n=====\n)", path.read_text(encoding="utf-8"))
    done = []
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "(01\.0[57]-\d{3})"', chunk, re.M)
        if not m:
            continue
        cm = re.search(r"(## Условие\n\n)(.*?)(\n\n## Ответ\n\n)(.*?)(\n\n## Решение\n\n)(.*)", chunk, re.S)
        for stem, fn in STEMS:
            if cm and stem in cm.group(2):
                c = fn()
                new = chunk[:cm.start(2)] + c["cond"] + cm.group(3) + c["ans"] + cm.group(5) + c["sol"] + "\n"
                lv = int(re.search(r"^level: (\d+)", chunk, re.M).group(1))
                new = re.sub(r"^level: \d+", f"level: {max(lv, c['level'])}", new, count=1, flags=re.M)
                parts[i] = new.rstrip("\n") + ("\n" if chunk.endswith("\n") else "")
                done.append(m.group(1))
                break
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено: {len(done)} — {', '.join(done)}")


if __name__ == "__main__":
    main()
