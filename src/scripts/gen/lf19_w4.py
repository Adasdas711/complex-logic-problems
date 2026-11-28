"""Модель для задач § 32–39 раздела 19 («Логическая физика», гл. 3, с. 171–189).

Формулы — кортежи:
  "x"                         — простое высказывание (строка в LaTeX);
  ("not", f)                  — внешнее отрицание ~f;
  ("neg", a)                  — внутреннее отрицание ¬a (a — простое);
  ("q", a)                    — ?a (оператор неопределённости, П1);
  ("and", f1, ..., fn), ("or", f1, ..., fn);
  ("imp", f, g)               — f → g;
  ("rimp", R, f, g)           — f → (R f) g (с. 171);
  ("all", v, f), ("ex", v, f) — кванторы.

Правила — по книге: Д1–Д16, У1–У7, П1, К1–К24 (гл. 1, с. 34–36) и свойства видов причинных связей (с. 171).
check_line() проверяет, что строка вывода следует из указанных строк по названному правилу
(посылка — конъюнкция указанных строк, с. 33). Трёхзначные значения — по положениям § 36 (с. 177–178).
"""

# ------------------------------------------------------------------ запись

SIM = "{\\sim}"


def tex(f, ctx=None):
    if isinstance(f, str):
        return f
    op = f[0]
    if op == "not":
        g = f[1]
        inner = tex(g)
        if isinstance(g, str) or g[0] in ("not", "neg", "q", "all", "ex"):
            return SIM + inner
        return SIM + "(" + inner + ")"
    if op == "neg":
        return "\\urcorner " + tex(f[1])
    if op == "q":
        return "?" + tex(f[1])
    if op in ("and", "or"):
        sym = " \\wedge " if op == "and" else " \\vee "
        parts = []
        for g in f[1:]:
            s = tex(g)
            if not isinstance(g, str) and g[0] in ("imp", "rimp", "and", "or"):
                s = "(" + s + ")"
            parts.append(s)
        out = sym.join(parts)
        return out
    if op == "imp":
        a, b = f[1], f[2]
        sa, sb = tex(a), tex(b)
        if not isinstance(a, str) and a[0] in ("imp", "rimp"):
            sa = "(" + sa + ")"
        if not isinstance(b, str) and b[0] in ("imp", "rimp"):
            sb = "(" + sb + ")"
        return sa + " \\to " + sb
    if op == "rimp":
        R, a, b = f[1], f[2], f[3]
        sa, sb = tex(a), tex(b)
        pa = sa if isinstance(a, str) or a[0] in ("not", "neg", "q") else "(" + sa + ")"
        pb = sb if isinstance(b, str) or b[0] in ("not", "neg", "q") else "(" + sb + ")"
        return f"{pa} \\to ({R}{sa}){pb}"
    if op in ("all", "ex"):
        q = "\\forall " if op == "all" else "\\exists "
        g = f[2]
        s = tex(g)
        if not isinstance(g, str) and g[0] in ("and", "or", "imp", "rimp"):
            s = "(" + s + ")"
        return f"({q}{f[1]})" + s
    raise ValueError(f)


def T(f):
    """Формула в $…$; формула с → верхнего уровня — в скобках, если её цитируют внутри текста."""
    return "$" + tex(f) + "$"


def N(f):
    return ("not", f)


def A(*fs):
    return ("and",) + fs


def O(*fs):
    return ("or",) + fs


def I(a, b):
    return ("imp", a, b)


# ------------------------------------------------------------------ правила

def flat(f, op):
    if not isinstance(f, str) and f[0] == op:
        out = []
        for g in f[1:]:
            out += flat(g, op)
        return out
    return [f]


def prem(cited):
    """Посылка — конъюнкция указанных строк (с. 33); список её конъюнктивных членов."""
    out = []
    for c in cited:
        out += flat(c, "and")
    return out


def eq_pairs(rule):
    """Пары эквивалентных форм для правил ⊣⊢: функция f -> список g с f ⊣⊢ g по правилу."""
    def d1(f):
        res = []
        if not isinstance(f, str) and f[0] == "not" and not isinstance(f[1], str) and f[1][0] == "not":
            res.append(f[1][1])
        res.append(N(N(f)))
        return res

    def d6(f):
        res = []
        if not isinstance(f, str) and f[0] == "not" and not isinstance(f[1], str) and f[1][0] in ("and", "or"):
            op = "or" if f[1][0] == "and" else "and"
            res.append((op,) + tuple(N(g) for g in f[1][1:]))
        if not isinstance(f, str) and f[0] in ("and", "or") and all(not isinstance(g, str) and g[0] == "not" for g in f[1:]):
            op = "or" if f[0] == "and" else "and"
            res.append(N((op,) + tuple(g[1] for g in f[1:])))
        return res

    def p1(f):
        res = []
        if not isinstance(f, str) and f[0] == "q":
            res.append(A(N(f[1]), N(("neg", f[1]))))
        if (not isinstance(f, str) and f[0] == "and" and len(f) == 3 and not isinstance(f[1], str) and f[1][0] == "not"
                and isinstance(f[1][1], str) and f[2] == N(("neg", f[1][1]))):
            res.append(("q", f[1][1]))
        return res

    return {"Д1": d1, "Д6": d6, "П1": p1}[rule]


def subterms_replace(f, fn):
    """Все формулы, получаемые из f заменой одного вхождения подформулы g на fn(g) (Д11)."""
    out = [h for h in fn(f)]
    if isinstance(f, str):
        return out
    for i in range(1, len(f)):
        if isinstance(f[i], (str, tuple)) and not (f[0] in ("rimp",) and i == 1) and not (f[0] in ("all", "ex") and i == 1) \
                and not (f[0] in ("neg", "q")):
            for h in subterms_replace(f[i], fn):
                out.append(f[:i] + (h,) + f[i + 1:])
    return out


def follows(rule, cited, concl):
    """Следует ли concl из конъюнкции cited по правилу rule. rule — строка: 'У1', 'Д11/Д6', 'К22/К14' и т. п."""
    P = prem(cited)
    if rule == "посылка":
        return True
    if rule == "Д2":
        return concl in P or (not isinstance(concl, str) and concl[0] == "and" and all(c in P for c in concl[1:]))
    if rule == "Д10":
        return not isinstance(concl, str) and concl[0] == "and" and list(concl[1:]) == list(cited)
    if rule == "Д3":
        c = cited[0]
        return len(cited) == 1 and not isinstance(c, str) and not isinstance(concl, str) and c[0] == concl[0] \
            and c[0] in ("and", "or") and sorted(map(repr, c[1:])) == sorted(map(repr, concl[1:]))
    if rule in ("Д1", "Д6", "П1"):
        return len(cited) == 1 and concl in eq_pairs(rule)(cited[0])
    if rule.startswith("Д11/"):
        inner = rule.split("/")[1]
        return len(cited) == 1 and concl in subterms_replace(cited[0], eq_pairs(inner))
    if rule == "Д13":
        return not cited and not isinstance(concl, str) and concl[0] == "not" and concl[1][0] == "and" \
            and len(concl[1]) == 3 and concl[1][2] == N(concl[1][1])
    if rule == "Д16":  # из теорем ⊢x и ⊢y — ⊢x ∧ y
        return not isinstance(concl, str) and concl[0] == "and" and list(concl[1:]) == list(cited)
    if rule == "У1":
        return any(not isinstance(p, str) and p[0] == "imp" and p[1] in P and p[2] == concl for p in P) or \
            any(not isinstance(p, str) and p[0] == "imp" and p[2] == concl and not isinstance(p[1], str) and p[1][0] == "and"
                and all(m in P for m in p[1][1:]) for p in P)
    if rule == "У2":
        return any(not isinstance(p, str) and p[0] == "imp" and N(p[2]) in P and concl == N(p[1]) for p in P)
    if rule == "У3":
        return len(cited) == 1 and cited[0][0] == "imp" and concl == I(N(cited[0][2]), N(cited[0][1]))
    if rule == "У4":
        return any(p[0] == "imp" and q[0] == "imp" and p[2] == q[1] and concl == I(p[1], q[2])
                   for p in P for q in P if not isinstance(p, str) and not isinstance(q, str))
    if rule == "У5":
        if not isinstance(concl, str) and concl[0] == "imp" and not isinstance(concl[2], str) and concl[2][0] == "and":
            return all(I(concl[1], m) in P for m in concl[2][1:]) and len(P) == len(concl[2]) - 1
        if len(cited) == 1 and cited[0][0] == "imp" and cited[0][2][0] == "and":
            return concl == A(*[I(cited[0][1], m) for m in cited[0][2][1:]])
        return False
    if rule == "У6":
        if not isinstance(concl, str) and concl[0] == "imp" and not isinstance(concl[1], str) and concl[1][0] == "or":
            return all(I(m, concl[2]) in P for m in concl[1][1:]) and len(P) == len(concl[1]) - 1
        return False
    if rule == "У7":  # ⊢(x → y), если x ⊢ y по Д2
        return not cited and concl[0] == "imp" and follows("Д2", [concl[1]], concl[2])
    if rule == "Rк":  # с. 171: (x → (R¹x)y) ⊢ (~y → (R²~y)~x)
        c = cited[0]
        return len(cited) == 1 and c[0] == "rimp" and c[1] == "R^1" and concl == ("rimp", "R^2", N(c[3]), N(c[2]))
    if rule == "Rт":  # с. 171: (x → (R¹x)y) ∧ (y → (R¹y)z) ⊢ (x → (R¹x)z)
        return any(p[0] == "rimp" and q[0] == "rimp" and p[1] == q[1] == "R^1" and p[3] == q[2]
                   and concl == ("rimp", "R^1", p[2], q[3]) for p in P for q in P)
    if rule == "К1":
        return len(cited) == 1 and cited[0][0] == "all" and concl == cited[0][2]
    if rule == "К2":
        return len(cited) == 1 and concl[0] == "ex" and concl[2] == cited[0]
    if rule == "К14":
        c = cited[0]
        return len(cited) == 1 and c[0] == "ex" and c[2][0] == "and" and concl == A(*[("ex", c[1], m) for m in c[2][1:]])
    if rule == "К17":
        c = cited[0]
        return len(cited) == 1 and c[0] == "all" and c[2][0] == "all" and concl == ("all", c[2][1], ("all", c[1], c[2][2]))
    if rule == "К19":
        c = cited[0]
        return len(cited) == 1 and c[0] == "ex" and c[2][0] == "all" and concl == ("all", c[2][1], ("ex", c[1], c[2][2]))
    if rule.startswith("К22/"):  # если x ⊢ y, то (∀a)x ⊢ (∀a)y
        inner = rule[4:]
        c = cited[0]
        return len(cited) == 1 and c[0] == "all" and concl[0] == "all" and c[1] == concl[1] and \
            follows(inner, [c[2]], concl[2])
    if rule.startswith("К23/"):  # если x ⊢ y, то (∃a)x ⊢ (∃a)y
        inner = rule[4:]
        c = cited[0]
        return len(cited) == 1 and c[0] == "ex" and concl[0] == "ex" and c[1] == concl[1] and \
            follows(inner, [c[2]], concl[2])
    if "+" in rule:  # правило и затем замена по Д11 (например, «У3+Д1»: У3, затем снятие ~~)
        r1, r2 = rule.split("+")
        c = cited[0]
        if r1 == "У3" and len(cited) == 1 and c[0] == "imp":
            mid = I(N(c[2]), N(c[1]))
            return concl == mid or follows("Д11/" + r2, [mid], concl)
        return False
    if rule == "с185":  # с. 185: из (1) следует ~(2), из (2) следует ~(1)
        return len(cited) == 1 and ((cited[0] == "(1)" and concl == N("(2)")) or (cited[0] == "(2)" and concl == N("(1)")))
    if rule.startswith("Д8:"):  # цепочка правил: x ⊢ y по первому, y ⊢ z по второму
        r1, r2 = rule[3:].split(">")
        # промежуточное звено ищется среди простых кандидатов: для К1 > К2
        c = cited[0]
        if r1 == "К1" and c[0] == "all":
            mid = c[2]
            return follows(r2, [mid], concl)
        return False
    raise ValueError(rule)


def check_lines(lines, premises=()):
    """lines: [(формула, правило, (номера строк))]. Возвращает список номеров неверных строк."""
    bad = []
    for i, (f, rule, refs) in enumerate(lines, 1):
        if rule == "посылка":
            if premises and f not in premises:
                bad.append(i)
            continue
        if any(r >= i or r < 1 for r in refs):
            bad.append(i)
            continue
        cited = [lines[r - 1][0] for r in refs]
        try:
            ok = follows(rule, cited, f)
        except (IndexError, TypeError, ValueError):
            ok = False
        if not ok:
            bad.append(i)
    return bad


# ------------------------------------------------------------------ трёхзначные значения § 36 (с. 177–178)

def values36(P, Q, fact_S, fact_T):
    """P, Q — истинность P(a), Q(a) (двузначны; не обе истинны). fact_S — на самом деле S(a) (True) или ¬S(a) (False);
    то же fact_T. Возвращает значения S, ¬S, T, ¬T: 'и' / 'л' / 'н'."""
    assert not (P and Q)
    v = {}
    if P:
        v["S"] = "и" if fact_S else "л"
        v["nS"] = "л" if fact_S else "и"
    else:
        v["S"] = v["nS"] = "н"
    if Q:
        v["T"] = "и" if fact_T else "л"
        v["nT"] = "л" if fact_T else "и"
    else:
        v["T"] = v["nT"] = "н"
    return v


def conj36(a, b):
    """Конъюнкция по с. 178: ложна, если один член ложен; иначе неопределённа, если хотя бы один неопределён."""
    if "л" in (a, b):
        return "л"
    if "н" in (a, b):
        return "н"
    return "и"
