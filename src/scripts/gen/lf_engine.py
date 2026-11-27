"""Небольшая машина выводов для задач раздела 18 («Логическая физика», гл. 2).

Факты — кортежи; правило — (имя, число посылок, функция). Функция получает кортеж посылок и возвращает заключение
или None. closure() строит все выводимые факты (поиск в ширину), proof() — вывод факта списком строк
(формула, основание, номера строк посылок). check() проверяет вывод: каждая строка — посылка или следует по правилу.
"""
import itertools


def closure(premises, rules, limit=400, extra=()):
    """{факт: (правило, посылки)} для всех фактов, выводимых из premises (не более limit)."""
    how = {p: ("посылка", ()) for p in premises}
    for f in extra:
        how.setdefault(f, extra[f] if isinstance(extra, dict) else ("аксиома", ()))
    changed = True
    while changed and len(how) < limit:
        changed = False
        facts = list(how)
        new = {}
        for name, n, fn in rules:
            for combo in itertools.product(facts, repeat=n):
                c = fn(combo)
                if c is not None and c not in how and c not in new:
                    new[c] = (name, combo)
        if new:
            how.update(new)
            changed = True
    return how


def proof(fact, how):
    """Строки вывода [(факт, правило, (номера посылок))] в порядке зависимости."""
    order = []
    seen = set()

    def visit(f):
        if f in seen:
            return
        for p in how[f][1]:
            visit(p)
        seen.add(f)
        order.append(f)

    visit(fact)
    # посылки — в начало, в порядке появления
    prem = [f for f in order if how[f][0] == "посылка"]
    rest = [f for f in order if how[f][0] != "посылка"]
    order = prem + rest
    num = {f: i + 1 for i, f in enumerate(order)}
    return [(f, how[f][0], tuple(num[p] for p in how[f][1])) for f in order]


def check(lines, rules, premises):
    """Список номеров строк, основание которых неверно."""
    by = {name: (n, fn) for name, n, fn in rules}
    bad = []
    for i, (f, name, refs) in enumerate(lines, 1):
        if name == "посылка":
            if f not in premises:
                bad.append(i)
            continue
        if name not in by or any(r >= i or r < 1 for r in refs):
            bad.append(i)
            continue
        n, fn = by[name]
        if len(refs) != n or fn(tuple(lines[r - 1][0] for r in refs)) != f:
            bad.append(i)
    return bad
