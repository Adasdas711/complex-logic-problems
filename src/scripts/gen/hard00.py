#!/usr/bin/env python3
"""Усложнение Введения (занятия 1–6) по образцу занятия 10.

Заменяет в src/data/zadachi/00.md карточки ступеней 1–3 (и короткие ступени 4) трудными:
  § 1–3, § 6, § 9, § 10 (часть) — задачи, написанные вручную (hard00_hand.py): диагностика с несколькими
      ошибками, построения и доказательства невозможности, расширения в духе § 6;
  § 4, § 5 — длинные разборы с пропусками формул и оснований, разборы с двумя ошибками, серии длинных выражений
      с обоснованием, составные замены в образце и почти-примеры, чтение длинных терминов и высказываний, главный
      оператор; построения и метатеоремы о языке (★, ступени 8–10) — вручную;
  § 7, § 8 — вхождение в длинные высказывания и формулы следования, диагностика с двумя ошибками, запись формул
      с несколькими знаками ⊢ по § 4–5 (с. 10–11) и обратно;
  § 10 — аксиомные схемы в смысле § 10 (почти-примеры, подстановка термина, совпадающие буквы).
Все ответы генерируемых задач и примеры в ручных задачах проверяются моделью src/scripts/logic/lang0.py.

Запуск: python3 src/scripts/gen/hard00.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import hard00_lib as H  # noqa: E402
from hard00_gen import (c_complete, c_diag, c_series, c_subst, c_read, c_mainop, c_sread, c_occ, c_occ_diag,  # noqa: E402
                        c_occ_build, c_transcribe, c_ent_series, c_ent_occ, c_scheme10)
from hard00_hand import HAND  # noqa: E402
import lang0 as G  # noqa: E402
from lang0 import tex, kind, is_stmt  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
s, t, u, p, q, r, x, y, z = H.s, H.t, H.u, H.p, H.q, H.r, H.x, H.y, H.z


def ids(sec, a, b):
    return [f"00.{sec:02d}-{n:03d}" for n in range(a, b + 1)]


def plan():
    """{id: функция} для генерируемых карточек."""
    out = {}
    m4 = {"00.04-001": lambda: c_series(4), "00.04-002": lambda: c_complete(4), "00.04-003": lambda: c_subst(4, True),
          "00.04-004": lambda: c_diag(4), "00.04-005": c_read, "00.04-006": lambda: c_subst(4, False),
          "00.04-007": lambda: c_complete(4), "00.04-008": lambda: c_series(4), "00.04-009": lambda: c_diag(4)}
    out.update(m4)
    s2 = [i for i in ids(4, 13, 51) if i not in HAND]
    kinds = ([lambda: c_series(4)] * 6 + [lambda: c_complete(4)] * 6 + [lambda: c_diag(4)] * 7 +
             [lambda: c_subst(4, True)] * 5 + [lambda: c_subst(4, False)] * 4 + [c_read] * 4)
    assert len(s2) == len(kinds), (len(s2), len(kinds))
    H.rnd.shuffle(kinds)
    out.update(zip(s2, kinds))
    s3 = [i for i in ids(5, 1, 29) if i not in HAND]
    k3 = ([lambda: c_series(5)] * 4 + [lambda: c_complete(5)] * 4 + [lambda: c_diag(5)] * 5 +
          [lambda: c_subst(5, True)] * 3 + [lambda: c_subst(5, False)] * 3 + [c_mainop] * 3 + [c_sread] * 2)
    assert len(s3) == len(k3), (len(s3), len(k3))
    H.rnd.shuffle(k3)
    out.update(zip(s3, k3))
    s4 = [i for i in ids(5, 30, 51) if i not in HAND]
    k4 = ([lambda: c_series(5)] * 3 + [lambda: c_complete(5)] * 3 + [lambda: c_diag(5)] * 4 +
          [lambda: c_subst(5, True)] * 2 + [lambda: c_subst(5, False)] * 2 + [c_mainop] * 2 + [c_sread] * 2)
    assert len(s4) == len(k4), (len(s4), len(k4))
    H.rnd.shuffle(k4)
    out.update(zip(s4, k4))
    s7 = ids(7, 1, 13)
    k7 = [c_occ] * 5 + [c_occ_diag] * 5 + [c_occ_build] * 3
    H.rnd.shuffle(k7)
    out.update(zip(s7, k7))
    s8 = ids(8, 1, 14)
    k8 = ([c_ent_series] * 4 + [c_transcribe] * 3 + [lambda: c_transcribe(back=True)] * 2 + [c_ent_occ] * 2 +
          [lambda: c_ent_occ(diag=True)] * 3)
    H.rnd.shuffle(k8)
    out.update(zip(s8, k8))
    out["00.08-016"] = lambda: c_ent_occ(diag=True)
    out["00.08-017"] = lambda: c_ent_occ(diag=True)
    out.update({i: c_scheme10 for i in ids(10, 7, 11)})
    return out


def checks():
    """Проверка примеров из ручных задач моделью lang0."""
    G.ARITY["r"] = 2
    T, St = G, G
    ok = [
        ("S" in kind(T.each(T.name(p), T.name(x))), "·([p], [x]) — субъект"),
        ("S" in kind(T.tup(s, t)) and "S" in kind(T.tup(T.tup(s, t), u)), "(s, t), ((s, t), u) — субъекты"),
        ("S" in kind(T.tneg(T.name(St.sneg(x)))), "∼[∼x] — субъект"),
        ("S" in kind(T.tconj(T.name(p), s)), "([p] · s) — субъект"),
        (is_stmt(St.forall(s, x)), "(∀s) x — высказывание"),
        ("S" in kind(T.fact(St.basic(s, p, "q"))), "↓(s? ← p) — субъект"),
        (is_stmt(St.basic(T.tup(s, s), r)), "((s, s) ← r) — высказывание"),
        (is_stmt(St.basic(T.tup(T.name(x), s), r)), "(([x], s) ← r) — высказывание"),
    ]
    pred = T.some(T.such(x), T.tneg(q), T.asuch(T.tconj(p, r), y), T.asuch(r, z))
    ok.append(("P" in kind(pred) and tex(pred).count("\\downarrow") == 3 and tex(pred).count("\\sim") == 1,
               "предикат с тремя ↓ и одним ∼"))
    e12 = St.cond(St.basic(T.tup(T.fact(x), T.name(s)), r), St.exists(T.tneg(p), St.basic(t, q)))
    ok.append((is_stmt(e12), "пример 00.05-012"))
    e40 = St.sdis(St.basic(s, p, "q"), St.basic(T.tup(T.name(St.forall(t, x)), u), r), St.cond(x, y, "q"))
    ok.append((is_stmt(e40) and tex(e40).count("?") == 2, "пример 00.05-040"))
    e16 = St.sconj(St.sdis(x, y, z), z)
    ok.append((len(G.occurring(e16, "X")) == 5 and St.sdis(x, y) not in G.occurring(e16, "X"), "((x : y : z) · z)"))
    for e in (T.name(St.sneg(x)), T.fact(St.sdis(x, x))):
        ok.append((len(G.occurring(e, "X")) == 2 and len(G.occurring(e, "T")) == 1, f"{tex(e)}: 2 выск., 1 термин"))
    e15 = St.sconj(x, St.basic(s, p))
    ok.append((len(G.occurring(e15, "X")) == 3, "(x · (s ← p)) — 3 высказывания"))
    ok.append((len(G.occurring(St.sconj(x, x), "X")) == 2, "(x · x) — 2 высказывания"))
    for ex in (St.sconj(St.basic(s, p), St.basic(t, q)), St.sconj(z, z),
               St.sconj(St.cond(y, z), St.basic(T.tup(T.fact(x), s), r))):
        ok.append((is_stmt(ex), f"{tex(ex)} — высказывание"))
    bad = [m for good, m in ok if not good]
    assert not bad, bad
    return len(ok)


def main():
    H.set_seed(1970_00)
    cards = {}
    for cid, fn in plan().items():
        c = fn()
        assert not H.test_like(c["cond"]), (cid, c["cond"][:100])
        cards[cid] = c
    for cid, c in HAND.items():
        assert not H.test_like(c["cond"]), (cid, c["cond"][:100])
    cards.update(HAND)
    n = checks()
    done = H.replace_cards(ROOT / "data" / "zadachi" / "00.md", cards, 0)
    print(f"Заменено карточек: {done}; проверок примеров: {n}")


if __name__ == "__main__":
    main()
