#!/usr/bin/env python3
"""Проверка содержания карточек (сверх validate.py): разметка формул, подпункты, повторы, ссылки.

  python3 scripts/lint.py            — сводка по видам замечаний
  python3 scripts/lint.py -v KIND    — все замечания вида KIND
  python3 scripts/lint.py -k         — то же для задач контрольных (data/kontrolnye)
  python3 scripts/lint.py -t         — то же для задач входных тестов (data/vhodnye)
"""
import re
import sys
from collections import Counter, defaultdict

from common import load_problems

ITEM = re.compile(r"^([а-з])\) ", re.M)
ANS_ITEM = re.compile(r"(?:^|[;\s(])([а-з])\)")


def parts(body):
    out, ps = {}, re.split(r"^## (.+)$", body, flags=re.M)
    for t, x in zip(ps[1::2], ps[2::2]):
        out[t.strip()] = x.strip()
    return out


def maths(text):
    return re.findall(r"\$([^$]*)\$", text)


def balanced(s):
    st = []
    pairs = {")": "(", "]": "[", "}": "{"}
    s = re.sub(r"\\[{}]", "", s)  # \{ \}
    s = re.sub(r"\\(left|right|big|Big)[()\[\]]", "", s)
    for ch in s:
        if ch in "([{":
            st.append(ch)
        elif ch in ")]}":
            if not st or st[-1] != pairs[ch]:
                return False
            st.pop()
    return not st


def check(p):
    issues = []
    m, b = p.meta, p.body
    pp = parts(b)
    cond, ans, sol = pp.get("Условие", ""), pp.get("Ответ", ""), pp.get("Решение", "")
    for name, text in (("Условие", cond), ("Ответ", ans), ("Решение", sol)):
        if not text.strip():
            issues.append(("пустой-раздел", name))
        for line in text.split("\n"):
            if line.count("$") % 2:
                issues.append(("нечётные-$", f"{name}: {line[:100]}"))
        for f in maths(text):
            if not balanced(f):
                issues.append(("скобки", f"{name}: ${f[:100]}$"))
            if re.search(r"\\\\[a-zA-Z]", f):
                issues.append(("двойной-слэш", f"{name}: {f[:80]}"))
        if re.search(r"TODO|XXX|None\b|St\(|<__|\{\}|\bnan\b", text):
            issues.append(("утечка-кода", f"{name}: {re.search(r'.{0,40}(TODO|XXX|None|St\(|<__|\{\}|nan).{0,40}', text).group(0)}"))
    its = ITEM.findall(cond)
    if its:
        if its != list("абвгдежз"[:len(its)]):
            issues.append(("порядок-подпунктов", " ".join(its)))
        lines = re.findall(r"^[а-з]\) (.+)$", cond, re.M)
        if len(lines) != len(set(lines)):
            issues.append(("повтор-подпункта", "; ".join(x for x, n in Counter(lines).items() if n > 1)[:120]))
        a_its = sorted(set(ANS_ITEM.findall(ans)))
        if a_its and len(a_its) != len(its) and "см." not in ans:
            issues.append(("подпункты-ответа", f"в условии {len(its)}, в ответе {''.join(a_its)}"))
    if m.get("type") == "E":
        if not re.search(r"\b(A|D|R|MT|T|S|AI|AV|R\*)\s?[IVX\d]|с\. \d|§", ans + sol):
            issues.append(("E-без-правила", ans[:100]))
    if not re.search(r"[сС]\. \d|§|D\d|A\d|T\d|R\d|MT\d|Очерки", sol) and int(m.get("level", 0)) < 10:
        issues.append(("решение-без-ссылки", sol[:80]))
    if len(sol) < 12:
        issues.append(("короткое-решение", sol))
    if ans.strip() and ans.strip() in cond and len(ans) > 15:
        issues.append(("ответ-в-условии", ans[:80]))
    return issues


def main():
    if "-k" in sys.argv:  # задачи контрольных работ
        from build import load_kontrol
        probs = [p for cards in load_kontrol().values() for p in cards]
    elif "-t" in sys.argv:  # задачи входных тестов
        from build import load_vhod
        probs = [p for cards in load_vhod().values() for p in cards]
    else:
        probs = [p for p in load_problems() if "id" in p.meta]
    found = defaultdict(list)
    for p in probs:
        for kind, msg in check(p):
            found[kind].append((p.meta["id"], msg))
    conds = defaultdict(list)
    for p in probs:
        conds[parts(p.body).get("Условие", "")].append(p.meta["id"])
    for c, ids in conds.items():
        if len(ids) > 1:
            found["повтор-условия"].append((",".join(map(str, ids)), c[:100]))
    cmds = Counter(c for p in probs for f in maths(p.body) for c in re.findall(r"\\[a-zA-Z]+", f))
    if "-v" in sys.argv:
        kind = sys.argv[sys.argv.index("-v") + 1]
        if kind == "команды":
            for c, n in sorted(cmds.items()):
                print(n, c)
        for pid, msg in found.get(kind, []):
            print(pid, "|", msg)
        return
    for k, v in sorted(found.items(), key=lambda kv: -len(kv[1])):
        print(f"{k}: {len(v)}")
    print(f"Задач: {len(probs)}; команд LaTeX: {len(cmds)}")


if __name__ == "__main__":
    main()
