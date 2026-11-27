#!/usr/bin/env python3
"""Усложнённые задачи § 1 гл. 1 (система S¹: только аксиомные схемы A1–A11 и правила R1–R3).

Заменяет в src/data/zadachi/01.md карточки 01.01-005…028 и 01.01-031…048 (ступени 1–4) трудными:
  005…016 — получается ли формула из аксиомной схемы при составной замене; почти-примеры (ступени 4–5);
  017…021 — все аксиомные схемы для формул с составными частями и замена метапеременных (ступень 4);
  022…026 — все формулы, которые даёт R3 при замене некоторых вхождений (ступень 4);
  027, 028 — почти-примеры аксиомных схем (диагностика, ступень 4);
  031…042 — длинные выводы, где пропущены основания и формулы строк (ступень 5);
  043…048 — длинные выводы с двумя неверными основаниями (диагностика, ступень 6).
Выводы строятся генератором hard01_02 без теоремных схем и проверяются s1.check.

Запуск: python3 src/scripts/gen/hard01_01.py
"""
import importlib.util
import itertools
import random
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("h", ROOT / "scripts" / "gen" / "hard01_02.py")
h = importlib.util.module_from_spec(spec)
spec.loader.exec_module(h)
from s1 import C, D, N, axiom, check, ftex, replaceable, tex  # noqa: E402

h.ALLOW_T = False
h.check2 = check                                   # в § 1 основания — только аксиомы и правила
h.WRONG = {"A3": "A4", "A4": "A3", "A1": "A2", "A2": "A1", "A7": "A9", "A9": "A7"}
h.rnd = random.Random(1970_1001)
_build_ok = h.build_ok
h.build_ok = lambda want, least=7: _build_ok(want, min(least, 7))   # без теоремных схем выводы короче
rnd = h.rnd
CONV, L = h.CONV, h.L
SRC = "с. 15–17, гл. 1, § 1"
A_NAMES = ["A1", "A2", "A3", "A4", "A7", "A8", "A9", "A10"]


def a_schemes(a, b):
    out = []
    for n in A_NAMES:
        if n in ("A3", "A4"):
            if a[0] == "conj" and len(a[1]) == 2 and b == (a[1][0] if n == "A3" else C(a[1][1], a[1][0])):
                out.append(n)
        elif axiom(a, b) == n:
            out.append(n)
    return out


def recognize_a():
    X, Y, Z = h.compound(), h.compound(), h.compound()
    while len({X, Y, Z}) < 3:
        Y, Z = h.compound(), h.compound()
    pool = [(*h.inst("A7", X, Y), "A7", f"$x$ := ${tex(X)}$, $y$ := ${tex(Y)}$"),
            (C(X, X), X, "A3", f"$x$ := ${tex(X)}$, $y$ := ${tex(X)}$"),
            (D(C(Y, Z), C(N(Y), N(Z))), N(D(Y, Z)), "A10", f"$x$ := ${tex(Y)}$, $y$ := ${tex(Z)}$"),
            (N(N(C(Z, X))), C(Z, X), "A2", f"$x$ := ${tex(C(Z, X))}$"),
            (*h.near_miss("A4", Y, Z), None, "")]
    rnd.shuffle(pool)
    items = "\n".join(f"{L[k]}) ${ftex(a, b)}$" for k, (a, b, _, _) in enumerate(pool))
    ans = "; ".join(f"{L[k]}) " + (", ".join(a_schemes(a, b)) + f" ({n}: {s})" if n else "ни одной")
                    for k, (a, b, n, s) in enumerate(pool))
    for a, b, n, _ in pool:
        assert (n in a_schemes(a, b)) if n else not a_schemes(a, b)
    cond = (f"{CONV} Для каждой формулы найдите все аксиомные схемы $S^1$ (A1–A4, A7–A10), примером которых она "
            f"является, и для одной из них укажите замену метапеременных; если схемы нет — объясните, что мешает.\n\n{items}")
    sol = ("Формула — пример схемы, если получается из неё заменой метапеременных (одинаковые — одинаково); "
           "совпадение членов конъюнкции даёт сразу несколько схем ($XX \\vdash X$ — пример A3). Схемы — с. 15–16.\n\n" + ans)
    return dict(level=4, type="R", step="iso", form="sym", answer="short", source=SRC, tags="S1, аксиомные схемы",
                cond=cond, ans=ans, sol=sol)


def r3_card():
    """R3 при двух вхождениях заменяемого высказывания: три результата."""
    X = rnd.choice([h.compound(), C(h.x, h.y), D(h.u, h.w)])
    Y = N(N(X))
    W = rnd.choice([h.z, N(h.w), h.u])
    zz = rnd.choice([D(C(X, W), X), C(X, D(W, X)), N(C(X, N(X)))])
    occ = []

    def subs(f, path=()):
        if f == X:
            occ.append(path)
            return
        if f[0] == "neg":
            subs(f[1], path + (1,))
        elif f[0] in ("conj", "dis"):
            for i, c in enumerate(f[1]):
                subs(c, path + (i,))
    subs(zz)

    def put(f, path, val):
        if not path:
            return val
        if f[0] == "neg":
            return N(put(f[1], path[1:], val))
        kids = list(f[1])
        kids[path[0]] = put(kids[path[0]], path[1:], val)
        return (f[0], tuple(kids))
    res = []
    for k in range(1, len(occ) + 1):
        for comb in itertools.combinations(occ, k):
            v = zz
            for pth in comb:
                v = put(v, pth, Y)
            res.append(v)
    for v in res:
        assert replaceable(zz, v, X, Y)
    cond = (f"{CONV} Даны теоремы $S^1$ ${ftex(X, Y)}$ (A1) и ${ftex(Y, X)}$ (A2). Найдите все формулы вида "
            f"${tex(zz)} \\vdash v$, которые даёт по ним правило R3 (замена некоторых, не обязательно всех, вхождений "
            f"${tex(X)}$ на ${tex(Y)}$). Сколько их?")
    ans = f"{len(res)}: " + "; ".join(f"${ftex(zz, v)}$" for v in res)
    sol = (f"R3 (с. 17): если $x \\vdash y$ и $y \\vdash x$, то $z \\vdash v$, где $v$ получается из $z$ заменой "
           f"некоторых вхождений $x$ на $y$. В ${tex(zz)}$ высказывание ${tex(X)}$ входит {len(occ)} раза; "
           f"непустых наборов заменяемых вхождений — {len(res)}:\n\n" + "\n".join(f"- ${ftex(zz, v)}$" for v in res))
    return dict(level=4, type="D", step="vary", form="sym", answer="build", source=SRC, tags="S1, правило R3",
                cond=cond, ans=ans, sol=sol)


def subst_a(name, yes):
    num, c = h.subst_card(0, name, yes)
    c["source"] = SRC
    return c


def main():
    cards = {}
    plan = [("A7", True), ("A9", True), ("A3", False), ("A4", True), ("A9", False), ("A7", True),
            ("A3", True), ("A4", False), ("A7", False), ("A9", True), ("A4", True), ("A3", True)]
    for num, (n, yes) in zip(range(5, 17), plan):
        cards[num] = subst_a(n, yes)
    for num in range(17, 22):
        cards[num] = recognize_a()
    for num in range(22, 27):
        cards[num] = r3_card()
    for num, n in ((27, "A4"), (28, "A7")):
        cards[num] = subst_a(n, False)
    for num in range(31, 43):
        c = h.complete_card(num)
        c["source"] = SRC
        cards[num] = c
    for num in range(43, 49):
        c = h.diag_card(num)[1]
        c["source"] = SRC
        cards[num] = c
    for c in cards.values():
        c["sol"] = c["sol"].replace("Схемы — с. 15–18; правила — с. 17.", "Схемы — с. 15–16; правила — с. 17.")
        assert not h.test_like(c["cond"]), c["cond"][:80]
        assert not re.search(r"\[T\d", c["cond"] + c["sol"]), "теоремная схема в задаче § 1"
    path = ROOT / "data" / "zadachi" / "01.md"
    parts = re.split(r"(\n=====\n)", path.read_text(encoding="utf-8"))
    done = 0
    for i, chunk in enumerate(parts):
        m = re.search(r'^id: "01\.01-(\d{3})"', chunk, re.M)
        if m and int(m.group(1)) in cards:
            lead = chunk[: len(chunk) - len(chunk.lstrip("\n"))]
            parts[i] = lead + h.render(f"01.01-{m.group(1)}", cards[int(m.group(1))], 1).rstrip("\n") + (
                "\n" if chunk.endswith("\n") else "")
            done += 1
    path.write_text("".join(parts), encoding="utf-8")
    print(f"Заменено карточек: {done} из {len(cards)}")


if __name__ == "__main__":
    main()
