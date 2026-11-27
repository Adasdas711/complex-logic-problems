"""Генерируемые усложнённые задачи Введения (§ 4, 5, 7, 8, 10): длинные разборы с пропусками, разборы с двумя
ошибками, серии длинных выражений с обоснованием, составные замены и почти-примеры, вхождения, формулы следования.
Ответы вычисляет модель src/scripts/logic/lang0.py.
"""
from hard00_lib import *  # noqa: F401,F403
from hard00_lib import G, rnd, Atom, Op, St, tex, kind, parse, verdict, why_not, is_stmt, CONV4, CONV5, L, \
    s, t, u, p, q, r, x, y, z, SUBJ, PRED1, LET, r_term, r_statement, r_subject, r_predicate, fresh, pick, plen, \
    show, corrupt, t_member, t_bounded, t_tilde, s_bounded, s_arrow

SRC4 = "с. 5–6, § 4, D1–D3"
SRC5 = "с. 5–8, § 4, D1–D3; § 5, D1–D3"


def conv(mode):
    return CONV4 if mode == 4 else CONV5


def gen_expr(mode, lo, hi, want=None, maxlen=72):
    full = mode == 5

    def g():
        if want == "X" or (want is None and full and rnd.random() < 0.5):
            return r_statement(5, True)
        if want == "S":
            return r_subject(5, full)
        if want == "P":
            return r_predicate(5, full)
        return r_term(5, full)

    def ok(e):
        k = kind(e)
        if not k or (want and want not in k):
            return False
        if mode == 5 and not any(isinstance(f, St) and f.op != "basic" for f in G.parts(e)) and "X" not in k:
            return False
        return lo <= plen(e) <= hi and len(tex(e)) <= maxlen
    return fresh(g, ok)


# ---------- 1. Длинный разбор с пропусками (и формулы строк, и основания) ----------
def c_complete(mode, level=5):
    e = gen_expr(mode, 9, 12)
    rows = parse(e)
    inner = [n for n, (f, _, _) in enumerate(rows, 1) if not isinstance(f, Atom) and n < len(rows)]
    hide_e = set(rnd.sample(inner, 2))
    rest = [n for n, (f, _, _) in enumerate(rows, 1) if not isinstance(f, Atom) and n not in hide_e]
    hide_r = set(rnd.sample(rest, min(4, len(rest))))
    what = "терминов (§ 4)" if mode == 4 else "терминов и высказываний (§ 4–5)"
    cond = (f"{conv(mode)} В разборе выражения ${tex(e)}$ снизу вверх по определениям {what} пропущены формулы "
            f"некоторых строк и вид с основанием в других строках («…»). Восстановите пропуски.\n\n"
            f"{show(rows, hide_e, hide_r)}")
    ans = "; ".join(f"{n} — " + (f"${tex(rows[n - 1][0])}$" if n in hide_e else "") +
                    (f"{rows[n - 1][1]} ({rows[n - 1][2]})" if n in hide_r else "")
                    for n in sorted(hide_e | hide_r))
    sol = ("Формулу пропущенной строки находим как часть исходного выражения, из которой по указанному пункту "
           "строится следующая по разбору строка; вид и пункт — по последнему применённому построению. Полный разбор:\n\n"
           + show(rows) + ("\n\nОпределения — с. 5–6." if mode == 4 else "\n\nОпределения — с. 5–8."))
    return dict(level=level, type="A", step="complete", form="sym", answer="build",
                source=SRC4 if mode == 4 else SRC5, tags="разбор, дополнение", cond=cond, ans=ans, sol=sol)


# ---------- 2. Разбор с двумя ошибками ----------
def c_diag(mode, level=6):
    for _ in range(400):
        e = gen_expr(mode, 9, 12)
        rows = parse(e)
        cand = [(n, corrupt(f, v, rf, mode)) for n, (f, v, rf) in enumerate(rows, 1) if not isinstance(f, Atom)]
        cand = [(n, c) for n, c in cand if c]
        if len(cand) < 2:
            continue
        (i, ci), (j, cj) = sorted(rnd.sample(cand, 2))
        if rows[i - 1][0].op == rows[j - 1][0].op:
            continue
        break
    else:
        raise RuntimeError("нет разбора для диагностики")
    bad = list(rows)
    for n, c in ((i, ci), (j, cj)):
        f, _, _ = rows[n - 1]
        bad[n - 1] = (f, c[0], c[1])
    what = "§ 4" if mode == 4 else "§ 4–5"
    cond = (f"{conv(mode)} Студент разобрал выражение ${tex(e)}$ снизу вверх по определениям {what}. Ровно в двух строках "
            f"неверно указан вид или пункт определения. Найдите эти строки, объясните ошибки и исправьте.\n\n{show(bad)}")
    ans = "; ".join(f"строка {n}: ${tex(rows[n - 1][0])}$ — {rows[n - 1][1]} ({rows[n - 1][2]})" for n in (i, j))
    sol = "\n".join(f"Строка {n}: {c[2]}." for n, c in ((i, ci), (j, cj))) + "\n\nВерный разбор:\n\n" + show(rows)
    return dict(level=level, type="E", step="vary", form="sym", answer="text",
                source=SRC4 if mode == 4 else SRC5, tags="разбор, диагностика", cond=cond, ans=ans, sol=sol)


# ---------- 3. Серия длинных выражений: вид и обоснование ----------
def subs_paths(e, path=()):
    out = [path]
    for i, c in enumerate(G.children(e)):
        out += subs_paths(c, path + (i,))
    return out


def get(e, path):
    for i in path:
        e = G.children(e)[i]
    return e


def put(e, path, val):
    if not path:
        return val
    i = path[0]
    if isinstance(e, Op):
        a = list(e.args)
        a[i] = put(a[i], path[1:], val)
        return Op(e.op, tuple(a))
    if e.op == "quant":
        qq, a, b = e.args
        if i == 0:
            return St("quant", (qq, put(a, path[1:], val), b), e.mod)
        return St("quant", (qq, a, put(b, path[1:], val)), e.mod)
    a = list(e.args)
    a[i] = put(a[i], path[1:], val)
    return St(e.op, tuple(a), e.mod)


def wrong_for(old, mode):
    """Подмена части выражением другого вида (правдоподобная ошибка записи)."""
    k = kind(old)
    if "X" in k:
        return rnd.choice([s, p, G.tup(s, t), G.name(x)] if mode == 5 else [s, p, G.name(x), G.tup(t, u)])
    if "S" in k:
        return rnd.choice([p, q, G.such(x), x] if mode == 5 else [p, G.such(y), x])
    if "P" in k:
        return rnd.choice([s, G.fact(x), G.name(p), x])
    return None


def spoil(e, mode):
    """Портит выражение в глубине; возвращает (испорченное, самая нижняя неверная часть)."""
    for _ in range(200):
        paths = [pp for pp in subs_paths(e) if len(pp) >= 2]
        if not paths:
            return None
        pp = rnd.choice(paths)
        old = get(e, pp)
        new = wrong_for(old, mode)
        if new is None:
            continue
        f = put(e, pp, new)
        if kind(f):
            continue
        rows = parse(f)
        bad = next(g for g, v, _ in rows if not kind(g))
        if bad is f:
            continue
        if not (s_arrow(new) or not isinstance(get(e, pp[:-1]), Op) or get(e, pp[:-1]).op not in ("fact", "such", "asuch")):
            continue
        return f, bad
    return None


def c_series(mode, level=5):
    words = {"S": "субъект", "P": "предикат", "X": "высказывание"}
    need = ["S", "P", "bad", "bad", rnd.choice(["S", "P"])] if mode == 4 else ["X", rnd.choice("SP"), "bad", "bad", "X"]
    items = []
    while len(items) < 5:
        w = need[len(items)]
        if w == "bad":
            base = gen_expr(mode, 7, 11, want=rnd.choice(["S", "P", "X"] if mode == 5 else ["S", "P"]), maxlen=60)
            res = spoil(base, mode)
            if not res or len(tex(res[0])) > 64 or tex(res[0]) in [tex(a) for a, _ in items]:
                continue
            items.append(res)
        else:
            e = gen_expr(mode, 7, 11, want=w, maxlen=60)
            items.append((e, None))
    rnd.shuffle(items)
    ans, sol = [], []
    for k, (e, bad) in enumerate(items):
        if bad is None:
            v = verdict(e)
            ans.append(f"{L[k]}) {v}")
            kids = [c for c in G.children(e) if not isinstance(c, Atom)]
            extra = ("; части: " + ", ".join(f"${tex(c)}$ — {verdict(c)}" for c in kids)) if kids else ""
            sol.append(f"{L[k]}) {v.capitalize()}: последнее построение — {G.ref(e)}{extra}.")
        elif mode == 4:
            ans.append(f"{L[k]}) не термин")
            sol.append(f"{L[k]}) Часть ${tex(bad)}$ — не термин: {why_not(bad)}. Все пункты D1 и D2 § 4 строят термин "
                       "только из терминов и высказываний (D1, п. 7; D2, п. 9), поэтому и всё выражение — не термин.")
        else:
            ans.append(f"{L[k]}) ни термин, ни высказывание")
            sol.append(f"{L[k]}) Часть ${tex(bad)}$ — ни термин, ни высказывание: {why_not(bad)}. Все пункты § 4–5 "
                       "строят новое выражение только из терминов и высказываний (§ 4, D1, п. 7; D2, п. 9; § 5, D2, п. 6), "
                       "поэтому и всё выражение — ни термин, ни высказывание.")
    if mode == 5:
        what = ("(субъект, предикат, высказывание; иначе — ни термин, ни высказывание). Обоснуйте: для термина или "
                "высказывания — последним построением и видом его частей; иначе — назовите самую нижнюю часть, которая "
                "не термин и не высказывание, и нарушенный пункт.")
    else:
        what = ("по § 4 (субъект, предикат; иначе — не термин). Обоснуйте: для термина — последним построением и видом "
                "его частей; иначе — назовите самую нижнюю часть, которая не термин, и нарушенный пункт.")
    cond = (f"{conv(mode)} Для каждого выражения определите его вид {what}\n\n"
            + "\n".join(f"{L[k]}) ${tex(e)}$" for k, (e, _) in enumerate(items)))
    return dict(level=level, type="R", step="iso", form="sym", answer="short",
                source=SRC4 if mode == 4 else SRC5, tags="опознание, обоснование", cond=cond,
                ans="; ".join(ans), sol="\n".join(sol))


# ---------- 4. Составная замена в образце и почти-примеры ----------
def Ma(n): return Atom(n, "a")      # метабуква-термин
def Mx(n): return Atom(n, "v")      # метабуква-высказывание
def Ms(n): return Atom(n, "s")      # метабуква-субъект


def match(pat, e, env):
    if isinstance(pat, Atom) and pat.kind in "avs":
        need = {"a": {"S", "P"}, "v": {"X"}, "s": {"S"}}[pat.kind]
        if pat.name in env:
            return env[pat.name] == e
        if not (kind(e) & need):
            return False
        env[pat.name] = e
        return True
    if type(pat) is not type(e):
        return False
    if isinstance(pat, Atom):
        return pat == e
    if pat.op != e.op or len(pat.args) != len(e.args) or (isinstance(pat, St) and pat.mod != e.mod):
        return False
    for a, b in zip(pat.args, e.args):
        if isinstance(a, str) or isinstance(b, str):
            if a != b:
                return False
        elif not match(a, b, env):
            return False
    return True


def subst(pat, env):
    if isinstance(pat, Atom) and pat.kind in "avs":
        return env[pat.name]
    if isinstance(pat, Atom):
        return pat
    args = tuple(a if isinstance(a, str) else subst(a, env) for a in pat.args)
    return Op(pat.op, args) if isinstance(pat, Op) else St(pat.op, args, pat.mod)


a_, b_, c_ = Ma("a"), Ma("b"), Ma("c")
x_, y_ = Mx("x"), Mx("y")
sa = Ms("a")
PAT4 = [  # (образец, нужные границы для замены)
    (G.some(G.asuch(a_, x_), G.name(b_)), {"a": t_bounded, "x": s_arrow, "b": lambda e: True}),
    (G.tup(G.opp(a_), G.name(x_), G.fact(y_)), {"a": t_tilde, "x": lambda e: True, "y": s_arrow}),
    (G.asuch(G.tconj(a_, G.tneg(b_)), x_), {"a": t_member, "b": t_bounded, "x": s_arrow}),
    (G.asuch(G.each(a_, G.tneg(a_)), x_), {"a": t_bounded, "x": s_arrow}),
    (G.tdisj(G.name(G.tdisj(a_, b_)), G.tneg(a_)), {"a": t_member, "b": t_member}),
]
PAT5 = [
    (G.cond(x_, G.forall(a_, G.wdis(y_, G.sneg(x_)))), {"x": s_bounded, "y": s_bounded, "a": lambda e: True}),
    (G.basic(G.tup(G.fact(x_), sa), r), {"x": s_arrow, "a": lambda e: True}),
    (G.sneg(G.sdis(x_, G.sconj(y_, G.sneg(x_)))), {"x": s_bounded, "y": s_bounded}),
    (G.asuch(G.name(G.wdis(x_, y_)), G.sconj(x_, y_)), {"x": s_bounded, "y": s_bounded}),
    (G.exists(G.name(x_), G.cond(x_, y_, "not")), {"x": s_bounded, "y": lambda e: True}),
]
META_TXT4 = "$a, b$ — термины, $x, y$ — высказывания"
META_TXT5 = "$a, b$ — термины, $x, y$ — высказывания (в образце с $\\leftarrow$ буква $a$ — субъект)"


def value_for(mk, mode, ok):
    full = mode == 5
    for _ in range(500):
        if mk == "a":
            v = r_term(rnd.choice([2, 3]), full)
        elif mk == "s":
            v = r_subject(rnd.choice([2, 3]), full)
        else:
            v = r_statement(rnd.choice([2, 3]), True) if full else rnd.choice(LET)
        if not ok(v):
            continue
        if mk == "v" and not full:
            return v
        if 4 <= len(tex(v)) <= 26:
            return v
    raise RuntimeError(mk)


def metas(pat):
    out = {}
    for f in G.parts(pat):
        if isinstance(f, Atom) and f.kind in "avs":
            out.setdefault(f.name, [f.kind, 0])[1] += 1
    return out


def meta_paths(pat, m):
    return [pp for pp in subs_paths(pat) if isinstance(get(pat, pp), Atom) and get(pat, pp).kind in "avs"
            and get(pat, pp).name == m]


SWAP = {"some": "each", "each": "some", "disj": "conj", "conj": "disj"}
STSWAP = {"conj": "wdis", "wdis": "sdis", "sdis": "conj"}


def swapped(f):
    return Op(SWAP[f.op], f.args) if isinstance(f, Op) else St(STSWAP[f.op], f.args, f.mod)


def swappable(f):
    return (isinstance(f, Op) and f.op in SWAP) or (isinstance(f, St) and f.op in STSWAP)


def c_subst(mode, yes, level=5):
    pats = PAT4 if mode == 4 else PAT5
    for _ in range(800):
        pat, need = rnd.choice(pats)
        ms = metas(pat)
        env = {m: value_for(ms[m][0], mode, need[m]) for m in sorted(ms)}
        if len({tex(v) for v in env.values()}) < len(env):
            continue
        e = subst(pat, env)
        if not kind(e):
            continue
        why = ""
        if not yes:
            how = rnd.choice(["repeat", "type", "struct"])
            if how == "repeat":
                rep = [m for m in ms if ms[m][1] > 1]
                if not rep:
                    continue
                m = rep[0]
                other = value_for(ms[m][0], mode, need[m])
                if other == env[m]:
                    continue
                e2 = put(e, meta_paths(pat, m)[-1], other)
                why = (f"буква ${m}$ встречается в образце дважды, а на её местах стоят разные выражения "
                       f"${tex(env[m])}$ и ${tex(other)}$")
            elif how == "type":
                vm = [m for m in ms if ms[m][0] == "v"]
                if not vm:
                    continue
                m = rnd.choice(vm)
                bad = rnd.choice([G.name(s), G.tup(s, t), G.tconj(p, q)])
                e2 = e
                for pp in meta_paths(pat, m):
                    e2 = put(e2, pp, bad)
                why = f"на месте буквы ${m}$ (высказывание) стоит ${tex(bad)}$ — {verdict(bad)}, а не высказывание"
            else:
                cand = [pp for pp in subs_paths(pat) if len(pp) <= 2 and swappable(get(pat, pp))]
                if not cand:
                    continue
                pp = rnd.choice(cand)
                f = get(e, pp)
                g = swapped(f)
                e2 = put(e, pp, g)
                why = (f"в образце на месте части ${tex(f)}$ стоит {opname(f.op)}, а в выражении — {opname(g.op)}: "
                       f"${tex(g)}$")
            if match(pat, e2, {}) or e2 == e:
                continue
            e = e2
        break
    else:
        raise RuntimeError("подстановка не построена")
    kinds_txt = {"a": "термин", "v": "высказывание", "s": "субъект"}
    meta = ", ".join(f"${m}$ — {kinds_txt[ms[m][0]]}" for m in sorted(ms))
    cond = (f"{conv(mode)} Дан образец ${tex(pat)}$, где {meta}. Установите, получается ли из него выражение ${tex(e)}$ "
            "заменой букв (одинаковые буквы — одинаковыми выражениями нужного вида). Если получается — укажите "
            "замену и определите вид полученного выражения с пунктом определения; если нет — назовите место, "
            "которое мешает.")
    if yes:
        assert match(pat, e, {})
        sub = ", ".join(f"${m}$ := ${tex(v)}$" for m, v in sorted(env.items()))
        ans = f"Получается: {sub}; {verdict(e)} ({G.ref(e)})."
        sol = (f"1. Сопоставляем выражение с образцом сверху вниз: {sub}.\n"
               "2. Каждая буква получила выражение нужного вида: " +
               ", ".join(f"${tex(v)}$ — {verdict(v)}" for _, v in sorted(env.items())) + ".\n"
               f"3. Подстановка даёт ровно данное выражение; последнее построение — {G.ref(e)}, поэтому это {verdict(e)}.")
    else:
        ans = f"Не получается: {why}."
        sol = (f"1. Сопоставляем выражение с образцом сверху вниз.\n2. Расхождение: {why}.\n"
               "3. Каждое место образца задаёт замену однозначно, другой замены нет — выражение не получается "
               "из образца.")
    return dict(level=level if yes else level - 1, type="A" if yes else "E", step="vary", form="sym",
                answer="short", source=SRC4 if mode == 4 else SRC5, tags="образец, замена", cond=cond, ans=ans, sol=sol)


def opname(o):
    return {"some": "$\\vee\\,(\\ldots)$", "each": "$\\cdot\\,(\\ldots)$", "disj": "$\\vee$ между членами",
            "conj": "$\\cdot$ между членами", "tuple": "скобки без знака", "wdis": "$\\vee$ между членами",
            "sdis": "$:$ между членами"}.get(o, o)


# ---------- 5. Чтение длинных терминов (§ 4, с. 6) ----------
def reading(e):
    if isinstance(e, Atom):
        return f"${e.name}$"
    if isinstance(e, St):
        return f"${tex(e)}$"

    def q(c):
        return reading(c) if isinstance(c, Atom) else f"«{reading(c)}»"
    a = [q(c) for c in e.args]
    lst = ", ".join(a)
    return {
        "neg": lambda: f"предмет, не обозначаемый термином {a[0]}",
        "conj": lambda: f"предмет, обозначаемый каждым из терминов {lst}",
        "disj": lambda: f"предмет, обозначаемый по крайней мере одним из терминов {lst}",
        "each": lambda: f"каждый из предметов {lst}",
        "some": lambda: f"по крайней мере один из предметов {lst}",
        "opp": lambda: (f"предмет не-{a[0]} (противоположный {a[0]})" if isinstance(e.args[0], Atom)
                        else f"предмет не-{a[0]}"),
        "fact": lambda: f"тот факт, что {a[0]}",
        "such": lambda: f"такой, что {a[0]}",
        "asuch": lambda: f"{a[0]}, такой, что {a[1]}",
        "name": lambda: f"термин {a[0]}",
        "tuple": lambda: f"({lst})",
    }[e.op]()


def c_read(level=4):
    es = []
    while len(es) < 3:
        e = gen_expr(4, 6, 8, maxlen=44)
        if (not any(isinstance(f, Op) and (f.op == "tuple" or f.op == "opp" and not isinstance(f.args[0], Atom))
                    for f in G.parts(e)) and e not in es and len(reading(e)) <= 170):
            es.append(e)
    cond = (f"{CONV4} Восстановите запись символами книги для каждого термина, заданного чтением по правилам § 4 (с. 6); "
            "в кавычках «…» — чтение составной части. Определите вид каждого термина и пункт D1 или D2.\n\n" +
            "\n".join(f"{L[k]}) {reading(e)}" for k, e in enumerate(es)))
    ans = "; ".join(f"{L[k]}) ${tex(e)}$ — {verdict(e)}" for k, e in enumerate(es))
    sol = "\n".join(f"{L[k]}) ${tex(e)}$ — {verdict(e)} ({G.ref(e)}). Разбор: " +
                    "; ".join(f"${tex(f)}$ — {v}" for f, v, _ in parse(e, atoms=False)) + "." for k, e in enumerate(es))
    return dict(level=level, type="T", step="vary", form="nat", answer="build", source=SRC4,
                tags="чтение терминов", cond=cond, ans=ans, sol=sol)


# ---------- 6. Вхождение (§ 7) ----------
SRC7 = "с. 9–10, § 7, D1; § 4–5"


def three_member(e):
    return [f for f in G.parts(e) if isinstance(f, St) and f.op in ("conj", "sdis", "wdis") and len(f.args) >= 3]


def inner_stmt_in_term(e):
    return [f for f in G.parts(e) if isinstance(f, Op) and any(isinstance(c, St) for c in f.args)]


def gen_occ_stmt(lo=12, hi=60):
    def g():
        return r_statement(5, True)

    def ok(e):
        return (is_stmt(e) and three_member(e) and inner_stmt_in_term(e) and lo <= len(tex(e)) <= hi + 20
                and 5 <= len(G.occurring(e, "X")) <= 9)
    return fresh(g, ok, 200000)


def sep_of(f):
    return {"conj": " \\cdot ", "sdis": " : ", "wdis": " \\vee "}[f.op]


def nonocc(e):
    f = three_member(e)[0]
    return f"{tex(f.args[0])}{sep_of(f)}{tex(f.args[1])}", f


def occ_lists(e):
    xs = G.occurring(e, "X")
    ts = G.occurring(e, "T")
    xs_t = "; ".join(f"${tex(f)}$" + (f" ({G.count_occ(e, f)} раза)" if G.count_occ(e, f) > 1 else "") for f in xs)
    ts_t = "; ".join(f"${tex(f)}$" for f in ts)
    return xs, ts, xs_t, ts_t


def c_occ(level=5):
    e = gen_occ_stmt()
    xs, ts, xs_t, ts_t = occ_lists(e)
    part, f = nonocc(e)
    cond = (f"{CONV5} Перечислите все различные высказывания и все различные термины, входящие в высказывание "
            f"${tex(e)}$ (§ 7, D1), и укажите, сколько раз входит каждое высказывание, входящее больше одного раза. "
            f"Затем объясните, почему графическая часть ${part}$ этого высказывания не есть вхождение в него высказывания.")
    ans = (f"Высказываний {len(xs)}: {xs_t}. Терминов {len(ts)}: {ts_t}. ${part}$ — не высказывание (нет внешних скобок).")
    sol = (f"По § 7, D1 (с. 9) высказывание входит в другое, если оно его графическая часть; высказывание входит само в "
           f"себя. Перебираем графические части, которые суть высказывания по § 5 (включая высказывания внутри терминов: "
           f"после $\\downarrow$, в $[\\ ]$), и графические части, которые суть термины по § 4.\n\n"
           f"Высказывания: {xs_t}.\n\nТермины: {ts_t}.\n\n"
           f"${part}$ — графическая часть ${tex(f)}$, но не высказывание: по D2, п. 3 § 5 запись с ${sep_of(f).strip()}$ "
           f"имеет внешние скобки; так и в примере книги $x : y$ не входит в $(x : y : z)$ (с. 9).")
    return dict(level=level, type="A", step="iso", form="sym", answer="short", source=SRC7,
                tags="вхождение", cond=cond, ans=ans, sol=sol)


def occ_errors(e, kinds_, whole=None):
    """Ошибки в списке высказываний, входящих в e (или в формулу whole): [(тип, текст в списке, пояснение)]."""
    xs = G.occurring(e, "X")
    out = []
    f3 = three_member(e)[0]
    a1, a2 = f3.args[0], f3.args[1]
    inner = [g for g in xs if any(isinstance(h, Op) and g in h.args for h in G.parts(e))]
    terms_with = [h for h in G.parts(e) if isinstance(h, Op) and any(isinstance(c, St) for c in h.args)]
    for k in kinds_:
        if k == "graph":
            part = f"{tex(a1)}{sep_of(f3)}{tex(a2)}"
            out.append((k, f"${part}$", f"${part}$ лишнее: это графическая часть ${tex(f3)}$, но не высказывание — "
                        f"по § 5, D2, п. 3 у записи с ${sep_of(f3).strip()}$ есть внешние скобки; так и $x : y$ не "
                        "входит в $(x : y : z)$ (§ 7, D1, с. 9)"))
        elif k == "brackets":
            part = f"({tex(a1)}{sep_of(f3)}{tex(a2)})"
            out.append((k, f"${part}$", f"${part}$ лишнее: это высказывание, но не графическая часть данного — "
                        f"в записи ${tex(f3)}$ после ${tex(a2)}$ нет закрывающей скобки (§ 7, D1, с. 9)"))
        elif k == "omit" and inner:
            g = inner[0]
            where = next(h for h in G.parts(e) if isinstance(h, Op) and g in h.args)
            out.append((k, None, f"пропущено ${tex(g)}$: оно — графическая часть термина ${tex(where)}$, а значит, и "
                        "всего высказывания; § 7, D1 говорит о любой графической части (с. 9)"))
        elif k == "term" and terms_with:
            h = terms_with[0]
            out.append((k, f"${tex(h)}$", f"${tex(h)}$ лишнее: это {verdict(h)}, а не высказывание (§ 4, "
                        f"{G.ref(h).replace('§ 4, ', '')}); в него входит высказывание, но сам он высказыванием не "
                        "является"))
        elif k == "self" and whole is not None:
            out.append((k, f"${whole}$", f"сама формула ${whole}$ лишняя: по D3 § 8 (с. 10) в формулу входят только "
                        "посылка, заключение и то, что входит в них (п. 3: «только в силу 1 и 2»)"))
    return out


def c_occ_diag(level=6):
    for _ in range(50):
        e = gen_occ_stmt()
        kinds_ = rnd.sample(["graph", "brackets", "omit", "term"], 2)
        errs = occ_errors(e, kinds_)
        if len(errs) == 2:
            break
    xs = G.occurring(e, "X")
    omit = [tex(g) for g in xs if any(k == "omit" for k, _, _ in errs) and
            any(isinstance(h, Op) and g in h.args for h in G.parts(e))][:1]
    lst = [f"${tex(g)}$" for g in xs if tex(g) not in omit]
    for k, txt, _ in errs:
        if txt:
            lst.insert(rnd.randrange(1, len(lst) + 1), txt)
    xs_t = "; ".join(f"${tex(g)}$" for g in xs)
    cond = (f"{CONV5} Студент выписал все различные высказывания, входящие в ${tex(e)}$ (§ 7, D1):\n\n"
            + "; ".join(lst) + ".\n\nВ списке ровно две ошибки. Найдите их, назовите нарушенное определение и исправьте список.")
    ans = "; ".join(w[0].upper() + w[1:] for _, _, w in errs) + "."
    sol = "\n".join(f"{n}. {w[0].upper() + w[1:]}." for n, (_, _, w) in enumerate(errs, 1)) + \
        f"\n\nВерный список ({len(xs)}): {xs_t}."
    return dict(level=level, type="E", step="vary", form="sym", answer="text", source=SRC7,
                tags="вхождение, диагностика", cond=cond, ans=ans, sol=sol)


def plural(n, one, few, many):
    if n % 10 == 1 and n % 100 != 11:
        return f"{n} {one}"
    if 2 <= n % 10 <= 4 and not 12 <= n % 100 <= 14:
        return f"{n} {few}"
    return f"{n} {many}"


def c_occ_build(level=6):
    e = gen_occ_stmt(10, 50)
    xs = G.occurring(e, "X")
    ts = G.occurring(e, "T")
    mx = max(xs, key=lambda f: G.count_occ(e, f))
    k = G.count_occ(e, mx)
    if k < 2:
        return c_occ_build(level)
    cond = (f"{CONV5} Постройте высказывание, в которое (§ 7, D1) входят ровно "
            f"{plural(len(xs), 'высказывание', 'различных высказывания', 'различных высказываний')}, причём одно из них — "
            f"ровно {plural(k, 'раз', 'раза', 'раз')}, и ровно {plural(len(ts), 'термин', 'различных термина', 'различных терминов')}, "
            f"{'и этот термин содержит' if len(ts) == 1 else 'среди которых есть термин, содержащий'} высказывание. "
            "Проверьте построенное по определениям § 4, § 5 и § 7.")
    xs_t = "; ".join(f"${tex(f)}$" for f in xs)
    ans = f"Например, ${tex(e)}$ (высказывание ${tex(mx)}$ входит {k} раза)."
    sol = (f"Пример: ${tex(e)}$. Это высказывание (§ 5, {G.ref(e).replace('§ 5, ', '')}). Входящие высказывания "
           f"({len(xs)}): {xs_t}; ${tex(mx)}$ входит {k} раза. Термины ({len(ts)}): " +
           "; ".join(f"${tex(f)}$" for f in ts) + ". Годится любое высказывание с теми же числами — проверка "
           "та же: выписать графические части, которые суть высказывания и термины.")
    return dict(level=level, type="A", step="open", form="sym", answer="build", source=SRC7,
                tags="вхождение, построение", cond=cond, ans=ans, sol=sol)


# ---------- 7. Формулы следования (§ 8) ----------
SRC8 = "с. 10–11, § 8, D1–D6"
Ent, etex, transcribe = G.Ent, G.etex, G.transcribe


def short_stmt():
    return pick(lambda: r_statement(2, True), lambda e: is_stmt(e) and len(tex(e)) <= 18 and s_bounded(e))


def r_ent(n):
    """Формула с n знаками ⊢ (вложенные формулы — в скобках, как на с. 11)."""
    if n == 0:
        return short_stmt()
    if n == 1:
        return Ent(short_stmt(), short_stmt()) if rnd.random() < .75 else Ent(None, short_stmt())
    k = rnd.randint(0, n - 1)
    left = r_ent(k) if rnd.random() < .85 else None
    if left is None:
        return Ent(None, r_ent(n - 1))
    return Ent(left, r_ent(n - 1 - k))


def c_transcribe(level=5, back=False):
    f = pick(lambda: r_ent(rnd.choice([2, 3])), lambda f: G.turnstiles(f) >= 2 and len(etex(f)) <= 70)
    conv = ("Запись по § 4–5 — как на с. 10–11: $x \\vdash y$ есть $([x], [y] \\leftarrow (\\vdash))$, "
            "$\\vdash x$ есть $([x] \\leftarrow (\\vdash))$, где $[x]$ — субъект «высказывание $x$» (§ 4, D2, п. 8), "
            "$\\vdash$ — предикат «из первого следует второе» (в $\\vdash x$ — «принимается из логических соображений»).")
    subj = sorted({m for m in __import__("re").findall(r"\[[^\[\]]*\]", transcribe(f))})
    if not back:
        cond = (f"{CONV5} {conv} Выражение ${etex(f)}$ содержит знак $\\vdash$ {G.turnstiles(f)} раза; по § 8 (с. 11) "
                "это лишь сокращённая запись высказывания. Запишите это высказывание полностью и укажите, сколько в "
                "нём вхождений предиката $\\vdash$.")
        ans = f"${transcribe(f)}$; предикат $\\vdash$ входит {G.turnstiles(f)} раза."
        sol = (f"Раскрываем изнутри: каждая формула следования $a \\vdash b$ заменяется на $([a], [b] \\leftarrow "
               f"(\\vdash))$, каждая $\\vdash a$ — на $([a] \\leftarrow (\\vdash))$ (§ 8, с. 10–11).\n\n"
               + steps_tr(f) + f"\n\nИтог: ${transcribe(f)}$. Каждому знаку $\\vdash$ сокращённой записи отвечает одно "
               f"вхождение предиката $\\vdash$ — всего {G.turnstiles(f)}.")
        return dict(level=level, type="T", step="vary", form="sym", answer="build", source=SRC8,
                    tags="формулы следования, запись", cond=cond, ans=ans, sol=sol)
    cond = (f"{CONV5} {conv} Восстановите сокращённую запись со знаками $\\vdash$ для высказывания "
            f"${transcribe(f)}$ и найдите в ней посылку и заключение внешней формулы следования (или установите, что "
            "внешняя формула — вырожденное следование).")
    outer = (f"посылка ${etex(f.a, False)}$, заключение ${etex(f.b, False)}$" if f.a is not None
             else f"вырожденное следование с заключением ${etex(f.b, False)}$")
    ans = f"${etex(f)}$; {outer}."
    sol = (f"Внешнее основное высказывание с предикатом $(\\vdash)$ — внешняя формула: "
           + ("двухместный субъект $([a], [b])$ даёт $a \\vdash b$" if f.a is not None else
              "одноместный субъект $[a]$ даёт $\\vdash a$")
           + "; так же раскрываем высказывания в квадратных скобках.\n\n" + steps_tr(f) + f"\n\nИтог: ${etex(f)}$ ({outer}).")
    return dict(level=level, type="T", step="vary", form="sym", answer="build", source=SRC8,
                tags="формулы следования, запись", cond=cond, ans=ans, sol=sol)


def steps_tr(f):
    out, seen = [], set()

    def go(g):
        if not isinstance(g, Ent):
            return
        if g.a is not None:
            go(g.a)
        go(g.b)
        if etex(g) not in seen:
            seen.add(etex(g))
            out.append(f"- ${etex(g)}$ → ${transcribe(g)}$")
    go(f)
    return "\n".join(out)


def c_ent_series(level=5):
    kinds_ = ["ent", "deg", "two", "term", "bad"]
    rnd.shuffle(kinds_)
    items = []
    for k in kinds_:
        if k == "ent":
            a, b = gen_expr(5, 5, 9, want="X", maxlen=34), gen_expr(5, 4, 8, want="X", maxlen=30)
            items.append((f"{tex(a)} \\vdash {tex(b)}", "формула следования",
                          f"$x$ и $y$ — высказывания (§ 8, D1); посылка ${tex(a)}$, заключение ${tex(b)}$ (D2)"))
        elif k == "deg":
            a = gen_expr(5, 6, 10, want="X", maxlen=40)
            items.append((f"\\vdash {tex(a)}", "формула вырожденного следования", f"${tex(a)}$ — высказывание (§ 8, D5)"))
        elif k == "two":
            a, b, c = short_stmt(), short_stmt(), short_stmt()
            items.append((f"({tex(a)} \\vdash {tex(b)}) \\vdash {tex(c)}", "не рассматривается как формула следования книги",
                          "знак $\\vdash$ встречается дважды; по § 8 (с. 11) такие выражения — лишь сокращённая запись "
                          f"высказывания $([([{tex(a)}], [{tex(b)}] \\leftarrow (\\vdash))], [{tex(c)}] \\leftarrow (\\vdash))$"))
        elif k == "term":
            a = gen_expr(5, 5, 8, want=rnd.choice("SP"), maxlen=26)
            b = gen_expr(5, 4, 8, want="X", maxlen=30)
            items.append((f"{tex(a)} \\vdash {tex(b)}", "не формула следования",
                          f"слева {verdict(a)} ${tex(a)}$, а не высказывание (§ 8, D1)"))
        else:
            base = gen_expr(5, 6, 10, want="X", maxlen=36)
            res = spoil(base, 5)
            while not res:
                base = gen_expr(5, 6, 10, want="X", maxlen=36)
                res = spoil(base, 5)
            bad, part = res
            a = gen_expr(5, 4, 8, want="X", maxlen=28)
            items.append((f"{tex(a)} \\vdash {tex(bad)}", "не формула следования",
                          f"справа не высказывание: часть ${tex(part)}$ — ни термин, ни высказывание ({why_not(part)}); "
                          "§ 8, D1"))
    cond = (f"{CONV5} Для каждого выражения установите, формула ли это следования (§ 8, D1), формула вырожденного "
            "следования (D5) или ни то ни другое, и обоснуйте. Для формулы следования назовите посылку и заключение (D2).\n\n"
            + "\n".join(f"{L[k]}) ${e}$" for k, (e, _, _) in enumerate(items)))
    ans = "; ".join(f"{L[k]}) {v}" for k, (_, v, _) in enumerate(items))
    sol = "\n".join(f"{L[k]}) {v.capitalize()}: {w}." for k, (_, v, w) in enumerate(items))
    return dict(level=level, type="R", step="iso", form="sym", answer="short", source=SRC8,
                tags="формулы следования", cond=cond, ans=ans, sol=sol)


def c_ent_occ(level=5, diag=False):
    a = gen_occ_stmt(10, 40)
    b = gen_expr(5, 5, 9, want="X", maxlen=32)
    xs = G.occurring(a, "X") + [g for g in G.occurring(b, "X") if g not in G.occurring(a, "X")]
    ts = G.occurring(a, "T") + [g for g in G.occurring(b, "T") if g not in G.occurring(a, "T")]
    f = f"{tex(a)} \\vdash {tex(b)}"
    xs_t = "; ".join(f"${tex(g)}$" for g in xs)
    ts_t = "; ".join(f"${tex(g)}$" for g in ts)
    if not diag:
        cond = (f"{CONV5} Перечислите все различные высказывания, входящие в формулу следования ${f}$ (§ 8, D3), и все "
                "различные термины, входящие в неё (§ 8, D4).")
        ans = f"Высказываний {len(xs)}, терминов {len(ts)} (списки — в решении)."
        sol = (f"По D3 (с. 10) в формулу входят посылка, заключение и всё, что входит в них; по D4 (с. 11) термин входит "
               f"в формулу, если входит в посылку или в заключение. Вхождение в посылку и заключение — по § 7, D1.\n\n"
               f"Высказывания: {xs_t}.\n\nТермины: {ts_t}.")
        return dict(level=level, type="A", step="iso", form="sym", answer="short", source=SRC8,
                    tags="формулы следования, вхождение", cond=cond, ans=ans, sol=sol)
    kinds_ = ["self", rnd.choice(["graph", "brackets", "term", "omit"])] if rnd.random() < .6 else \
        rnd.sample(["graph", "brackets", "term", "omit"], 2)
    errs = occ_errors(a, kinds_, whole=f)
    if len(errs) < 2:
        errs = occ_errors(a, ["self", "graph"], whole=f)
    omit = [tex(g) for g in G.occurring(a, "X") if any(k == "omit" for k, _, _ in errs) and
            any(isinstance(h, Op) and g in h.args for h in G.parts(a))][:1]
    lst = [f"${tex(g)}$" for g in xs if tex(g) not in omit]
    for k, txt, _ in errs:
        if txt:
            lst.insert(rnd.randrange(0, len(lst) + 1), txt)
    cond = (f"{CONV5} Студент выписал все различные высказывания, входящие в формулу следования ${f}$ (§ 8, D3):\n\n"
            + "; ".join(lst) + ".\n\nВ списке ровно две ошибки. Найдите их и назовите нарушенное определение.")
    ans = "; ".join(w[0].upper() + w[1:] for _, _, w in errs) + "."
    sol = ("По D3 § 8 (с. 10) в формулу следования входят посылка, заключение и всё, что входит в них по § 7, D1.\n\n"
           + "\n".join(f"{n}. {w[0].upper() + w[1:]}." for n, (_, _, w) in enumerate(errs, 1))
           + f"\n\nВерный список ({len(xs)}): {xs_t}.")
    return dict(level=level, type="E", step="vary", form="sym", answer="text", source=SRC8,
                tags="формулы следования, диагностика", cond=cond, ans=ans, sol=sol)


# ---------- 8. Аксиомные схемы в смысле § 10 ----------
SRC10 = "с. 12–14, § 10"
SCHEMES10 = [
    (G.sconj(x_, y_), G.sconj(y_, x_)),
    (G.sneg(G.sconj(x_, y_)), G.wdis(G.sneg(x_), G.sneg(y_))),
    (G.cond(x_, y_), G.wdis(G.sneg(x_), y_)),
    (G.wdis(G.sconj(x_, y_), z_ := Mx("z")), G.sconj(G.wdis(x_, z_), G.wdis(y_, z_))),
]


V_, W_ = X("v"), X("w")
CONV10 = ("Обозначения: $s, t, u$ — простые субъекты; $p, q$ — одноместные простые предикаты, $r$ — двухместный простой "
          "предикат; $v, w$ — высказывания; $x, y, z$ — буквы схемы.")


def rename(e):
    if isinstance(e, Atom):
        return {"x": V_, "y": W_, "z": W_}.get(e.name, e) if e.kind == "X" else e
    args = tuple(a if isinstance(a, str) else rename(a) for a in e.args)
    return Op(e.op, args) if isinstance(e, Op) else St(e.op, args, e.mod)


def c_scheme10(level=5):
    a0, b0 = rnd.choice(SCHEMES10)
    ms = sorted(metas(G.sconj(a0, b0)))
    items = []
    plan = ["yes", "same", "term", "near", rnd.choice(["yes", "near"])]
    rnd.shuffle(plan)
    for kind_ in plan:
        for _ in range(300):
            env = {m: rename(pick(lambda: r_statement(rnd.choice([1, 2]), True),
                                  lambda e: is_stmt(e) and s_bounded(e) and len(tex(e)) <= 16)) for m in ms}
            if kind_ == "same":
                env[ms[1]] = env[ms[0]]
            elif len({tex(v) for v in env.values()}) < len(env):
                continue
            a, b = subst(a0, env), subst(b0, env)
            why = ""
            if kind_ == "term":
                m = rnd.choice(ms)
                bad = rnd.choice([G.name(s), G.tup(s, t), G.fact(V_)])
                env2 = dict(env)
                env2[m] = bad
                a, b = subst(a0, env2), subst(b0, env2)
                why = f"на месте ${m}$ стоит {verdict(bad)} ${tex(bad)}$, а буквы схемы обозначают высказывания"
            elif kind_ == "near":
                m = ms[0]
                other = rename(pick(lambda: r_statement(1, True), lambda e: is_stmt(e) and s_bounded(e)))
                if other == env[m]:
                    continue
                pp = meta_paths(b0, m)[0]
                b = put(b, pp, other)
                why = (f"буква ${m}$ в посылке заменена на ${tex(env[m])}$, а в заключении на её месте "
                       f"${tex(other)}$; одинаковые буквы должны заменяться одинаково")
            fe = f"{tex(a)} \\vdash {tex(b)}"
            if fe not in [i[0] for i in items]:
                items.append((fe, kind_, env, why))
                break
    sch = f"{tex(a0)} \\vdash {tex(b0)}"
    cond = (f"{CONV10} Пусть в некоторой системе принята аксиомная схема ${sch}$ в смысле § 10 (с. 12–13). Для каждой "
            "формулы установите, принимается ли она по этой схеме, и обоснуйте: укажите, какие высказывания "
            "подставлены вместо букв, или назовите, что мешает.\n\n" +
            "\n".join(f"{L[k]}) ${fe}$" for k, (fe, _, _, _) in enumerate(items)))
    ans, sol = [], []
    for k, (fe, kd, env, why) in enumerate(items):
        sub = ", ".join(f"${m}$ — ${tex(v)}$" for m, v in sorted(env.items()))
        if kd in ("yes", "same"):
            ans.append(f"{L[k]}) принимается")
            note = (" Разные буквы здесь обозначают одно и то же высказывание — по § 10 (с. 13) это допустимо: различие "
                    "букв означает лишь, что высказывания могут различаться." if kd == "same" else "")
            sol.append(f"{L[k]}) Принимается: {sub}.{note}")
        else:
            ans.append(f"{L[k]}) не принимается")
            sol.append(f"{L[k]}) Не принимается: {why}.")
    return dict(level=level, type="A", step="iso", form="sym", answer="short", source=SRC10,
                tags="аксиомные схемы", cond=cond, ans="; ".join(ans),
                sol="По § 10 (с. 13): принять $x \\vdash y$ как схему — значит принять формулу для любых высказываний "
                    "$x$, $y$ указанного строения; одинаковые буквы — одно и то же высказывание.\n\n" + "\n".join(sol))


# ---------- 9. Главный оператор (§ 5, D3) и чтение высказываний ----------
MAINW = {"\\leftarrow": "п. 1", "\\cdot": "п. 2", ":": "п. 2", "\\vee": "п. 2", "\\forall": "п. 3",
         "\\exists": "п. 3", "\\to": "п. 4"}


def main_op(e):
    """(оператор, цепочка пунктов D3) по § 5, D3, с. 8; None — у буквы и её отрицаний главного оператора нет."""
    n = 0
    while isinstance(e, St) and e.op == "neg":
        e, n = e.args[0], n + 1
    if isinstance(e, Atom):
        return None
    o = {"basic": "\\leftarrow", "conj": "\\cdot", "sdis": ":", "wdis": "\\vee", "cond": "\\to"}.get(e.op)
    if e.op == "quant":
        o = "\\forall" if e.args[0] == "A" else "\\exists"
    return o, MAINW[o], n, e


def c_mainop(level=5):
    items = []
    need = [True] * 5
    while len(items) < 5:
        e = gen_expr(5, 7, 12, want="X", maxlen=58)
        if rnd.random() < 0.55:
            e = G.sneg(e) if s_bounded(e) else e
            if rnd.random() < 0.4 and s_bounded(e):
                e = G.sneg(e)
        mo = main_op(e)
        if need[len(items)] and (mo is None or mo[2] == 0 and len(items) < 2):
            continue
        used = [main_op(a)[0] for a in items if main_op(a)]
        if mo and mo[0] in used:
            continue
        if tex(e) not in [tex(a) for a in items]:
            items.append(e)
    rnd.shuffle(items)
    ans, sol = [], []
    for k, e in enumerate(items):
        mo = main_op(e)
        if mo is None:
            ans.append(f"{L[k]}) главного оператора нет")
            sol.append(f"{L[k]}) ${tex(e)}$ — отрицание буквы; D3 (с. 8) называет главными только $\\leftarrow$, "
                       "$\\cdot$, $:$, $\\vee$, $\\forall$, $\\exists$, $\\to$, а у буквы $x$ главного оператора нет, "
                       "значит, по п. 5 его нет и у $\\sim x$.")
            continue
        o, pt, n, core = mo
        ans.append(f"{L[k]}) ${o}$")
        times = {1: "один раз", 2: "дважды", 3: "трижды"}.get(n, f"{n} раз")
        chain = (f"; затем {times} п. 5: оператор, главный в $x$, главный и в $\\sim x$" if n else "")
        sol.append(f"{L[k]}) Снимаем внешние отрицания: ${tex(core)}$ — по D3, {pt} главный ${o}${chain}.")
    cond = (f"{CONV5} Найдите главный оператор каждого высказывания по D3 § 5 (с. 8) и обоснуйте цепочкой пунктов "
            "D3.\n\n" + "\n".join(f"{L[k]}) ${tex(e)}$" for k, e in enumerate(items)))
    return dict(level=level, type="A", step="iso", form="sym", answer="short", source="с. 7–8, § 5, D2–D3",
                tags="главный оператор", cond=cond, ans="; ".join(ans), sol="\n".join(sol))


def sreading(e):
    """Чтение высказывания по § 5 (с. 7–8); составные части — в кавычках «…»."""
    def qq(c):
        if isinstance(c, Atom):
            return f"${c.name}$"
        if isinstance(c, Op):
            return f"${tex(c)}$"
        return f"«{sreading(c)}»"
    if isinstance(e, Atom):
        return f"${e.name}$"
    o, m = e.op, e.mod
    if o == "basic":
        a, b = (f"${tex(c)}$" for c in e.args)
        return {"": f"{a} имеет признак {b}", "not": f"{a} не имеет {b}",
                "q": f"{a} неопределённо имеет {b}"}[m]
    if o == "neg":
        return f"Не так, как говорится в {qq(e.args[0])}"
    if o == "conj":
        return "Каждое из " + ", ".join(qq(c) for c in e.args)
    if o == "sdis":
        return "Одно и только одно из " + ", ".join(qq(c) for c in e.args)
    if o == "wdis":
        return "По крайней мере одно из " + ", ".join(qq(c) for c in e.args)
    if o == "quant":
        qn, a, b = e.args
        a, b = f"${tex(a)}$", qq(b)
        if m == "q":
            return f"Неопределённо, все {a} таковы, что {b}, или не все" if qn == "A" else \
                f"Неопределённо, некоторые {a} таковы, что {b}, или нет таких"
        return {("A", ""): f"Все {a} таковы, что {b}", ("E", ""): f"Некоторые {a} таковы, что {b}",
                ("A", "not"): f"Не все {a} таковы, что {b}", ("E", "not"): f"Нет таких {a}, что {b}"}[(qn, m)]
    if o == "cond":
        a, b = (qq(c) for c in e.args)
        return {"": f"Если {a}, то {b}", "not": f"Признание {a} не обязывает признать {b}",
                "q": f"Неопределённо, обязывает ли признание {a} признать {b}"}[m]
    raise ValueError(o)


def c_sread(level=4):
    es = []
    while len(es) < 3:
        e = gen_expr(5, 6, 10, want="X", maxlen=46)
        if e.op != "basic" and not any(isinstance(f, St) and f.op == "quant" and f.mod == "q" for f in G.parts(e)) \
                and not any(isinstance(f, St) and f.op == "cond" and f.mod == "q" for f in G.parts(e)) and e not in es:
            es.append(e)
    cond = (f"{CONV5} Восстановите запись символами книги для каждого высказывания, заданного чтением по правилам § 5 "
            "(с. 7–8); в кавычках «…» — чтение составной части. Назовите главный оператор каждого высказывания (D3).\n\n" +
            "\n".join(f"{L[k]}) {sreading(e)}" for k, e in enumerate(es)))
    ans = "; ".join(f"{L[k]}) ${tex(e)}$, главный ${main_op(e)[0]}$" if main_op(e) else f"{L[k]}) ${tex(e)}$"
                    for k, e in enumerate(es))
    sol = "\n".join(f"{L[k]}) ${tex(e)}$. Разбор: " + "; ".join(f"${tex(f)}$ — {G.ref(f)}" for f, _, _ in
                                                               parse(e, atoms=False) if isinstance(f, St)) + "."
                    for k, e in enumerate(es))
    return dict(level=level, type="T", step="vary", form="nat", answer="build", source="с. 7–8, § 5, D1–D3",
                tags="чтение высказываний", cond=cond, ans=ans, sol=sol)
