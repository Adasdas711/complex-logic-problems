#!/usr/bin/env python3
"""Серии к Введению: § 5 «Высказывания», § 7 «Вхождение», § 8 «Логическое следование»,
смешанный набор после Введения (раздел 17, § 1). Ступени 1–4. Пишет drafts/00.05-08-gen.md и drafts/17.01-gen.md.
"""
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "logic"))
import terms as T  # noqa: E402
import statements as St  # noqa: E402
from statements import (ARITY, basic, cond, exists, forall, is_stmt, latex, main_op, main_op_point,  # noqa: E402
                        reading, sub_statements, sub_terms, why_not)

ARITY["r"] = 2
rnd = random.Random(1970_5)
s, t, u = T.S("s"), T.S("t"), T.S("u")
p, q, r = T.P("p"), T.P("q"), T.P("r")
x, y, z = T.X("x"), T.X("y"), T.X("z")
CONV = ("Обозначения: $s, t, u$ — простые субъекты; $p, q$ — одноместные простые предикаты, "
        "$r$ — двухместный простой предикат; $x, y, z$ — высказывания.")
L = "абвгдежз"


def card(ch, sec, level, typ, step, form, ans, src, tags, body, series):
    meta = (f"chapter: {ch}\nsection: {sec}\nlevel: {level}\ntype: {typ}\nstep: {step}\ncondition: def\n"
            f"form: {form}\nanswer: {ans}\nsource: \"{src}\"\nseries: {series}\ngenerated: true\ntags: [{tags}]")
    return f"---\n{meta}\n---\n\n{body}\n"


def good_basic():
    return rnd.choice([basic(rnd.choice([s, t, u]), rnd.choice([p, q]), rnd.choice(["", "not", "q"])),
                       basic(T.tup(*rnd.sample([s, t, u], 2)), r, rnd.choice(["", "not", "q"]))])


def bad_basic():
    return rnd.choice([basic(rnd.choice([s, t]), r), basic(rnd.choice([p, q]), rnd.choice([s, t])),
                       basic(T.tup(s, t), p), basic(rnd.choice([s, t]), x)])


def atom_stmt():
    return rnd.choice([x, y, z, good_basic()])


def stmt(depth):
    if depth == 0:
        return atom_stmt()
    k = rnd.choice(["neg", "conj", "sdis", "wdis", "quant", "cond"])
    if k == "neg":
        return St.neg(stmt(depth - 1))
    if k in ("conj", "sdis", "wdis"):
        a = stmt(depth - 1)
        b = stmt(rnd.randint(0, depth - 1))
        while latex(b) == latex(a):
            b = atom_stmt()
        return {"conj": St.conj, "sdis": St.sdis, "wdis": St.wdis}[k](a, b)
    if k == "quant":
        return rnd.choice([forall, exists])(rnd.choice([s, t, p]), stmt(depth - 1), rnd.choice(["", "not", "q"]))
    return cond(stmt(depth - 1), stmt(rnd.randint(0, depth - 1)), rnd.choice(["", "not", "q"]))


def spoil(e):
    """Портит высказывание в одном месте."""
    if isinstance(e, T.Atom) or e.op == "basic":
        return rnd.choice([bad_basic(), rnd.choice([s, p])])
    args = list(e.args)
    idx = [i for i, a in enumerate(args) if isinstance(a, St.St) or (isinstance(a, T.Atom) and a.kind == "X")]
    i = rnd.choice(idx)
    args[i] = spoil(args[i])
    return St.St(e.op, tuple(args), e.mod)


def one_level():
    k = rnd.choice(["basic", "basic", "bad", "neg", "conj", "quant", "cond"])
    good = rnd.random() < 0.55
    if k == "basic":
        return good_basic()
    if k == "bad":
        return bad_basic()
    if k == "neg":
        return St.neg(atom_stmt() if good else rnd.choice([s, p]))
    if k == "conj":
        f = rnd.choice([St.conj, St.sdis, St.wdis])
        return f(atom_stmt(), atom_stmt() if good else rnd.choice([s, p, T.tup(s, t)]))
    if k == "quant":
        return rnd.choice([forall, exists])(rnd.choice([s, p]), atom_stmt() if good else rnd.choice([s, q]),
                                             rnd.choice(["", "not", "q"]))
    return cond(atom_stmt(), atom_stmt() if good else rnd.choice([t, q]), rnd.choice(["", "not", "q"]))


def uniq(n, gen, pred=lambda e: True):
    out, seen = [], set()
    while len(out) < n:
        e = gen()
        if pred(e) and latex(e) not in seen:
            seen.add(latex(e))
            out.append(e)
    return out


def verdict(e):
    return "высказывание" if is_stmt(e) else "не высказывание"


SRC5 = "с. 7–8, § 5, D1–D3"


def sec5():
    out = []
    for _ in range(13):  # ступень 1
        es = uniq(5, one_level)
        cond_ = "\n".join(f"{L[i]}) ${latex(e)}$" for i, e in enumerate(es))
        ans = "; ".join(f"{L[i]}) {verdict(e)}" for i, e in enumerate(es))
        sol = "\n".join(f"{L[i]}) ${latex(e)}$ — " + (f"высказывание: {St.POINT[e.op]} § 5." if is_stmt(e)
                        else f"не высказывание: {why_not(e)}.") for i, e in enumerate(es))
        body = (f"## Условие\n\n{CONV} Какие из выражений — высказывания по определениям § 5?\n\n{cond_}\n\n"
                f"## Ответ\n\n{ans}\n\n## Решение\n\n{sol}")
        out.append(card(0, 5, 1, "R", "iso", "sym", "short", SRC5, "высказывания", body, "опознание-высказываний"))
    for _ in range(5):  # ступень 2: главный оператор
        es = uniq(4, lambda: stmt(2), lambda e: is_stmt(e) and main_op(e) is not None)
        cond_ = "\n".join(f"{L[i]}) ${latex(e)}$" for i, e in enumerate(es))
        ans = "; ".join(f"{L[i]}) ${main_op(e)}$" for i, e in enumerate(es))
        sol = "\n".join(f"{L[i]}) ${main_op(e)}$ — D3, {main_op_point(e)} (с. 8)." for i, e in enumerate(es))
        body = (f"## Условие\n\n{CONV} Найдите главный оператор каждого высказывания.\n\n{cond_}\n\n"
                f"## Ответ\n\n{ans}\n\n## Решение\n\n{sol}\n\nОтрицания $\\sim$, $\\urcorner$ и оператор $?$ "
                "главными не бывают.")
        out.append(card(0, 5, 2, "A", "iso", "sym", "short", "с. 8, § 5, D3", "главный оператор", body, "главный-оператор"))
    readable = lambda: rnd.choice([good_basic(), forall(rnd.choice([s, t]), rnd.choice([x, y]), rnd.choice(["", "not"])),
                                   exists(rnd.choice([s, t]), rnd.choice([x, y]), rnd.choice(["", "not"])),
                                   cond(x, y, rnd.choice(["", "not"])), St.conj(x, y), St.sdis(x, y, z),
                                   St.wdis(y, z), St.neg(rnd.choice([x, y]))])
    for i in range(5):  # ступень 2: чтение и запись
        es = uniq(5, readable)
        if i < 3:
            cond_ = "\n".join(f"{L[k]}) ${latex(e)}$" for k, e in enumerate(es))
            ans = "; ".join(f"{L[k]}) «{reading(e)}»" for k, e in enumerate(es))
            task, typ, step, series = "Прочитайте высказывания по правилам § 5.", "T", "iso", "чтение-высказываний"
        else:
            cond_ = "\n".join(f"{L[k]}) «{reading(e)}»" for k, e in enumerate(es))
            ans = "; ".join(f"{L[k]}) ${latex(e)}$" for k, e in enumerate(es))
            task, typ, step, series = "Запишите символами книги.", "T", "vary", "запись-высказываний"
        body = (f"## Условие\n\n{CONV} {task}\n\n{cond_}\n\n## Ответ\n\n{ans}\n\n## Решение\n\n"
                "Правила чтения основных высказываний — § 5, с. 7; остальных — с. 8, пп. 1–6.")
        out.append(card(0, 5, 2, typ, step, "sym", "short", "с. 7–8, § 5", "чтение", body, series))
    for _ in range(8):  # ступень 3: разбор
        es = uniq(3, lambda: (lambda e: spoil(e) if rnd.random() < 0.4 else e)(stmt(3)))
        cond_ = "\n".join(f"{L[i]}) ${latex(e)}$" for i, e in enumerate(es))
        ans = "; ".join(f"{L[i]}) {verdict(e)}" for i, e in enumerate(es))
        sol = "\n".join(f"{L[i]}) Разбор снизу вверх:\n" + "\n".join(f"   - {l}" for l in St.chain(e))
                        for i, e in enumerate(es))
        body = (f"## Условие\n\n{CONV} Высказывание ли это? Обоснуйте разбором снизу вверх: для каждой части "
                f"укажите пункт D1 или D2 § 5 или назовите нарушение.\n\n{cond_}\n\n## Ответ\n\n{ans}\n\n"
                f"## Решение\n\n{sol}")
        out.append(card(0, 5, 3, "A", "iso", "sym", "proof", SRC5, "высказывания", body, "разбор-высказываний"))
    for _ in range(3):  # ступень 4: дополнение разбора
        e = uniq(1, lambda: stmt(3), is_stmt)[0]
        lines = St.chain(e)
        lines_blank = [l.rsplit(" (", 1)[0] + " (…)" if "(дано)" not in l else l for l in lines]
        body = (f"## Условие\n\n{CONV} Восстановите пункты определений § 5 в разборе высказывания "
                f"${latex(e)}$:\n\n" + "\n".join(f"{k + 1}. {l}" for k, l in enumerate(lines_blank)) +
                "\n\n## Ответ\n\n" + "; ".join(f"{k + 1} — {l.rsplit(' (', 1)[1].rstrip(')')}" for k, l in enumerate(lines)
                                              if "(дано)" not in l) +
                "\n\n## Решение\n\nD1 и D2 § 5, с. 7–8: основные высказывания — по D1, остальные — по пунктам D2.")
        out.append(card(0, 5, 4, "A", "complete", "sym", "short", SRC5, "высказывания", body, "дополнение-разбора"))
    return out


def sec7():
    out, SRC = [], "с. 9–10, § 7, D1"
    for _ in range(4):  # ступень 1
        e = uniq(1, lambda: St.conj(atom_stmt(), atom_stmt(), atom_stmt()), is_stmt)[0]
        a, b, c = e.args
        cands = [(a, True), (St.conj(a, b), False), (e, True), (St.conj(b, c), False), (rnd.choice([x, y, z]), None)]
        lines, ans, sol = [], [], []
        for k, (cand, v) in enumerate(cands):
            if v is None:
                v = any(latex(cand) == latex(w) for w in sub_statements(e))
            lines.append(f"{L[k]}) ${latex(cand)}$")
            ans.append(f"{L[k]}) {'да' if v else 'нет'}")
            why = ("высказывание входит само в себя" if cand == e else
                   "это графическая часть, являющаяся высказыванием" if v else
                   "такой части со скобками в записи нет, а без внешних скобок это не высказывание"
                   if cand.__class__ is St.St and cand.op == "conj" else "такой части в записи нет")
            sol.append(f"{L[k]}) {'входит' if v else 'не входит'}: {why}.")
        body = (f"## Условие\n\n{CONV} Входят ли в высказывание ${latex(e)}$ следующие высказывания?\n\n"
                + "\n".join(lines) + "\n\n## Ответ\n\n" + "; ".join(ans) +
                "\n\n## Решение\n\n§ 7, D1, с. 9–10: одно высказывание входит в другое, если оно — графическая часть "
                "другого; высказывание входит само в себя.\n\n" + "\n".join(sol))
        out.append(card(0, 7, 1, "A", "iso", "sym", "short", SRC, "вхождение", body, "вхождение"))
    for level, n, depth in ((2, 4, 2), (3, 3, 3)):
        for _ in range(n):
            e = uniq(1, lambda: stmt(depth), is_stmt)[0]
            subs = sub_statements(e)
            ts = sub_terms(e)
            task = ("Перечислите все высказывания, входящие в" if level == 2 else
                    "Перечислите все высказывания и все термины, входящие в")
            ans = "Высказывания: " + ", ".join(f"${latex(w)}$" for w in subs)
            if level == 3:
                ans += ". Термины: " + (", ".join(f"${T.latex(w)}$" for w in ts) or "нет")
            body = (f"## Условие\n\n{CONV} {task} ${latex(e)}$.\n\n## Ответ\n\n{ans}.\n\n## Решение\n\n"
                    "§ 7, D1, с. 9–10. Входят: само высказывание, каждая его часть, которая сама является "
                    "высказыванием, и далее части частей." +
                    (" Термины входят в высказывание, если они — его графические части: субъекты и предикаты "
                     "основных высказываний, их составные части, термины в кванторных группах." if level == 3 else ""))
            out.append(card(0, 7, level, "A", "iso", "sym", "short", SRC, "вхождение", body, "вхождение-перечень"))
    return out


def sec8():
    out, SRC = [], "с. 10–11, § 8, D1–D6"
    def item():
        A, B = uniq(2, lambda: stmt(1), is_stmt)
        k = rnd.choice(["ok", "ok", "term", "deg", "double", "pred"])
        if k == "ok":
            return f"{latex(A)} \\vdash {latex(B)}", "формула следования", "D1: посылка и заключение — высказывания"
        if k == "term":
            return f"{latex(A)} \\vdash s", "не формула следования", "D1: $s$ — термин, а не высказывание"
        if k == "pred":
            return f"p \\vdash {latex(B)}", "не формула следования", "D1: $p$ — предикат, а не высказывание"
        if k == "deg":
            return f"\\vdash {latex(A)}", "формула вырожденного следования", "D5"
        return (f"{latex(A)} \\vdash ({latex(B)} \\vdash x)", "не рассматривается",
                "формулы с двумя и более знаками $\\vdash$ в книге не рассматриваются (с. 11)")
    for _ in range(4):
        its, seen = [], set()
        while len(its) < 5:
            it = item()
            if it[0] not in seen:
                seen.add(it[0])
                its.append(it)
        body = (f"## Условие\n\n{CONV} Какие из выражений — формулы следования или вырожденного следования "
                "по § 8?\n\n" + "\n".join(f"{L[k]}) ${e}$" for k, (e, _, _) in enumerate(its)) +
                "\n\n## Ответ\n\n" + "; ".join(f"{L[k]}) {v}" for k, (_, v, _) in enumerate(its)) +
                "\n\n## Решение\n\n" + "\n".join(f"{L[k]}) {w}." for k, (_, _, w) in enumerate(its)))
        out.append(card(0, 8, 1, "R", "iso", "sym", "short", SRC, "формулы следования", body, "формулы-следования"))
    for level, n in ((2, 4), (3, 3)):
        for _ in range(n):
            A, B = uniq(2, lambda: stmt(level - 1), is_stmt)
            deg = level == 3 and rnd.random() < 0.34
            f = f"\\vdash {latex(B)}" if deg else f"{latex(A)} \\vdash {latex(B)}"
            subs = sub_statements(B) if deg else sub_statements(A) + [w for w in sub_statements(B)
                                                                         if latex(w) not in {latex(v) for v in sub_statements(A)}]
            ts = sub_terms(B) if deg else sub_terms(A) + [w for w in sub_terms(B)
                                                           if T.latex(w) not in {T.latex(v) for v in sub_terms(A)}]
            if level == 2:
                task = "Укажите посылку и заключение и перечислите все высказывания, входящие в формулу"
                ans = (f"Посылка ${latex(A)}$, заключение ${latex(B)}$. Входят: " +
                       ", ".join(f"${latex(w)}$" for w in subs))
                sol = "§ 8, D2 (посылка и заключение) и D3 (вхождение высказывания в формулу следования), с. 10."
            else:
                task = "Перечислите все высказывания и все термины, входящие в формулу"
                ans = ("Высказывания: " + ", ".join(f"${latex(w)}$" for w in subs) + ". Термины: " +
                       (", ".join(f"${T.latex(w)}$" for w in ts) or "нет"))
                sol = ("§ 8, с. 10–11: " + ("D6 — высказывание входит в $\\vdash x$, если оно входит в $x$; "
                       "так же для терминов." if deg else "D3 — вхождение высказывания; D4 — термин входит в "
                       "$x \\vdash y$, если входит в $x$ или в $y$."))
            body = f"## Условие\n\n{CONV} {task} ${f}$.\n\n## Ответ\n\n{ans}.\n\n## Решение\n\n{sol}"
            out.append(card(0, 8, level, "A", "iso", "sym", "short", SRC, "формулы следования", body, "вхождение-в-формулу"))
    return out


def mixed():
    """Смешанный набор после Введения: 4 карточки ступени 2, 6 ступени 3, 2 ступени 4 (диагностика)."""
    import importlib.util
    out = []
    spec = importlib.util.spec_from_file_location("g4", ROOT / "scripts" / "gen" / "g00_04.py")
    g4 = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g4)
    g4.rnd.seed(17_01)
    def relabel(c, level, typ="A"):
        c = c.replace("chapter: 0\nsection: 4", "chapter: 17\nsection: 1").replace("chapter: 0\nsection: 5", "chapter: 17\nsection: 1")
        c = c.replace("chapter: 0\nsection: 7", "chapter: 17\nsection: 1").replace("chapter: 0\nsection: 8", "chapter: 17\nsection: 1")
        import re
        c = re.sub(r"level: \d+", f"level: {level}", c, count=1)
        return c.replace("step: iso", "step: mixed").replace("step: vary", "step: mixed")
    # ступень 2: термины, главный оператор, вхождение в формулу, чтение
    out.append(relabel(g4.classify_card(2, g4.items(4, lambda: g4.term_of(rnd.choice("SP"), 2)), "смешанный"), 2))
    out += [relabel(c, 2) for c in sec5()[13:14]]
    out += [relabel(c, 2) for c in sec8()[4:5]]
    out += [relabel(c, 2) for c in sec5()[18:19]]
    # ступень 3: разбор терминов и высказываний, вхождение
    out.append(relabel(g4.classify_card(3, g4.items(3, lambda: g4.term_of(rnd.choice("SP"), 3)), "смешанный"), 3))
    out += [relabel(c, 3) for c in sec5()[23:25]]
    out += [relabel(c, 3) for c in sec7()[8:9]]
    out += [relabel(c, 3) for c in sec8()[8:10]]
    # ступень 4: найти неверную строку в разборе (диагностика)
    for _ in range(2):
        e = uniq(1, lambda: stmt(3), is_stmt)[0]
        lines = St.chain(e)
        cand = [k for k, l in enumerate(lines) if "(дано)" not in l]
        k = rnd.choice(cand)
        wrong = lines[k].replace("высказывание (", "не высказывание (")
        wrong = wrong.replace("D2, п. 2", "D2, п. 3") if wrong == lines[k] else wrong
        shown = lines[:k] + [wrong] + lines[k + 1:]
        body = (f"## Условие\n\n{CONV} В разборе высказывания ${latex(e)}$ ровно одна строка ошибочна. "
                "Найдите её и исправьте.\n\n" + "\n".join(f"{i + 1}. {l}" for i, l in enumerate(shown)) +
                f"\n\n## Ответ\n\nСтрока {k + 1}: верно — {lines[k].split(' — ')[1]}.\n\n## Решение\n\n"
                "Разбор по D1 и D2 § 5 (с. 7–8) снизу вверх:\n" + "\n".join(f"- {l}" for l in lines))
        out.append(card(17, 1, 4, "E", "mixed", "sym", "short", "с. 7–8, § 5", "смешанный, диагностика", body, None))
    return out


def main():
    rnd.seed(1970_5)
    a = sec5() + sec7() + sec8()
    (ROOT / "drafts").mkdir(exist_ok=True)
    (ROOT / "drafts" / "00.05-08-gen.md").write_text("\n=====\n".join(a), encoding="utf-8")
    rnd.seed(17_01)
    b = mixed()
    (ROOT / "drafts" / "17.01-gen.md").write_text("\n=====\n".join(b), encoding="utf-8")
    print(len(a), len(b))


if __name__ == "__main__":
    main()
