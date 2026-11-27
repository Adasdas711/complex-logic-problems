#!/usr/bin/env python3
"""Проверка ссылок на книгу: стоит ли метка из решения (A5, D2, MT3, AIV …) на указанной странице.

  python3 scripts/check_refs.py          — сводка и список неподтверждённых ссылок
  python3 scripts/check_refs.py -v       — то же с номерами задач

Ссылка — метка, за которой в той же фразе стоит «(с. N)» или «(с. N–M)». Страницы «Комплексной логики»
распознаются tesseract'ом один раз и кешируются в .cache/ocr/ (кеш в репозиторий не входит,
CLAUDE.md: распознанный текст не хранить). Распознавание меток неточно, поэтому:
  1) сравнение нечёткое (кириллические двойники, похожие цифры);
  2) data/metki.yaml — проверенные по изображениям страниц метки, которых распознавание не видит;
  3) неподтверждённая ссылка — не обязательно ошибка, а повод открыть страницу.
Ссылки на «Очерки» и LSR не проверяются.
"""
import os
import re
import signal
import subprocess
import sys
from collections import defaultdict

import yaml

from common import ROOT, load_problems

BOOK = ROOT / "books" / "zinoviev-kompleksnaya-logika-1970.pdf"
CACHE = ROOT / ".cache" / "ocr"
MANUAL = ROOT / "data" / "metki.yaml"

LAB = (r"MT\*?\d+|R\^\{?[dk*]\}?\d+|R\*\d+|A\^\{?[cn\d]\}?[IVX]*\.?\d+|A\*?[IVX]+\.?\d+|A\*\d+"
       r"|A\d+|R\d+|T\d+|D\*?\d+|L\d+")
PAT = re.compile(r"(?<![\w^{])\$?(" + LAB + r")\$?(?:[^()\n.;$]{0,40}?)\(с\. (\d+)(?:[–-](\d+))?\)")

# классы символов для нечёткого сравнения с распознанным текстом
CLS = {"A": "AА", "D": "DД", "M": "MМ", "T": "TТ", "R": "RКЯ", "L": "L", "I": "I1lІ|",
       "V": "VУ", "X": "XХ", "1": "1lI|", "3": "3З", "0": "0OО", "5": "5", "6": "6б", "8": "8",
       "2": "2", "4": "4", "7": "7", "9": "9"}


def ocr(page):
    f = CACHE / f"kl-{page:03d}.txt"
    if f.exists():
        return f.read_text()
    CACHE.mkdir(parents=True, exist_ok=True)
    img = f"/tmp/kl-ocr-{page}"
    subprocess.run(["pdftoppm", "-f", str(page + 1), "-l", str(page + 1), "-r", "400", "-gray", "-png",
                    "-singlefile", str(BOOK), img], check=True)
    t = subprocess.run(["tesseract", img + ".png", "stdout", "-l", "rus+eng", "--psm", "4"],
                       capture_output=True, text=True).stdout
    f.write_text(t)
    return t


def core(lab):
    """Что ищется на странице: AIV.7 → группа AIV; A^28 → A…8; R^d2 → R…2."""
    lab = lab.replace("{", "").replace("}", "")
    m = re.fullmatch(r"(A\*?)([IVX]+)\.?(\d+)", lab)
    if m:
        return m[1].replace("*", "") + m[2]
    m = re.fullmatch(r"([AR])\^[cnkd\d*]?([IVX]*)\.?(\d+)", lab)
    if m:
        return m[1] + "~" + (m[2] or m[3])
    return lab.replace("*", "")


def fuzzy(lab):
    out = []
    for ch in core(lab):
        if ch == "~":
            out.append(r".{0,3}?")
        else:
            out.append("[" + re.escape(CLS.get(ch, ch)) + "]")
    return re.compile("(?<![A-Za-zА-Яа-я0-9])" + r"\s?".join(out) + "(?![0-9])")


def manual():
    if not MANUAL.exists():
        return {}
    data = yaml.safe_load(MANUAL.read_text()) or {}
    return {int(p): set(map(str, v)) for p, v in data.items()}


def main():
    man = manual()
    cites = defaultdict(list)
    for p in load_problems():
        if "id" not in p.meta:
            continue
        body = p.body.split("## Ответ", 1)[-1]
        for m in PAT.finditer(body):
            lab = m[1].replace("{", "").replace("}", "")
            a = int(m[2])
            b = int(m[3]) if m[3] else a
            if a > 198 or b - a > 6:
                continue
            cites[(lab, a, b)].append(p.meta["id"])
    bad = []
    for (lab, a, b), ids in sorted(cites.items(), key=lambda kv: (kv[0][1], kv[0][0])):
        rx = fuzzy(lab)
        pages = range(max(a - 1, 1), b + 1)  # метка могла начаться на предыдущей странице
        ok = any(lab in man.get(q, ()) or core(lab) in man.get(q, ()) for q in pages)
        ok = ok or any(rx.search(ocr(q)) for q in pages)
        if not ok:
            bad.append((lab, a, b, ids))
    n = sum(len(v) for v in cites.values())
    print(f"Ссылок: {n} (различных пар «метка — страница»: {len(cites)}); не подтверждено: {len(bad)}")
    for lab, a, b, ids in bad:
        rng = f"{a}" if a == b else f"{a}–{b}"
        tail = ", ".join(ids[:6]) + (" …" if len(ids) > 6 else "") if "-v" in sys.argv else f"{len(ids)} зад."
        print(f"  с. {rng}: {lab} — {tail}")
    return 1 if bad and "--strict" in sys.argv else 0


if __name__ == "__main__":
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    sys.exit(main())
