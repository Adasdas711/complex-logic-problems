#!/usr/bin/env python3
"""Печатная версия: PDF для каждого занятия и контрольной из zanyatiya/*.md.

Задачи и примеры — на первых страницах; «Ответы и решения» начинаются с новой страницы, ответы — тоже с новой.
Скрытые решения примеров в печатной версии показаны полностью.

  python3 src/scripts/pdf.py            — все документы в pdf/
  python3 src/scripts/pdf.py 01 08к     — только указанные (по началу имени файла)

Нужны pandoc и xelatex; шрифты DejaVu.
"""
import concurrent.futures as cf
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]   # корень репозитория
SRC = ROOT / "zanyatiya"
OUT = ROOT / "pdf"

HEADER = r"""
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\fancyfoot[C]{\thepage}
\renewcommand{\headrulewidth}{0pt}
\setlength{\parskip}{0.45em}
\setlength{\emergencystretch}{3em}
\providecommand{\urcorner}{\ulcorner}
\let\oldsection\section
"""


def prepare(md: str) -> str:
    md = re.sub(r"<!--.*?-->\n*", "", md, flags=re.S)
    md = md.replace("<details>\n<summary>Решение</summary>\n\n", "").replace("</details>\n", "")
    md = re.sub(r"\n---\n\n(&nbsp;\n\n)+", "\n", md)
    md = md.replace("\n## Ответы и решения\n", "\n\\newpage\n\n## Ответы и решения\n")
    md = md.replace("\n### Ответы\n", "\n\\newpage\n\n### Ответы\n")
    # Номера задач «1\.» — обычный текст, а не список.
    return md


def build(src: Path) -> str:
    OUT.mkdir(exist_ok=True)
    out = OUT / (src.stem + ".pdf")
    with tempfile.TemporaryDirectory() as tmp:
        md = Path(tmp) / "doc.md"
        md.write_text(prepare(src.read_text(encoding="utf-8")), encoding="utf-8")
        hdr = Path(tmp) / "hdr.tex"
        hdr.write_text(HEADER, encoding="utf-8")
        title = src.read_text(encoding="utf-8").split("\n# ", 1)[1].split("\n", 1)[0]
        cmd = ["pandoc", str(md), "-o", str(out), "--pdf-engine=xelatex", "-H", str(hdr),
               "-V", "mainfont=DejaVu Serif", "-V", "sansfont=DejaVu Sans", "-V", "monofont=DejaVu Sans Mono",
               "-V", "mathfont=DejaVu Math TeX Gyre", "-V", "lang=ru", "-V", "geometry:margin=2cm",
               "-V", "fontsize=11pt", "-V", "papersize=a4", "-M", f"pagetitle={title}",
               "--from", "markdown+tex_math_dollars-implicit_figures"]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode:
            return f"{src.name}: ОШИБКА\n{r.stderr[-1500:]}"
    return f"{src.name}: ok"


def main():
    pick = sys.argv[1:]
    files = sorted(f for f in SRC.glob("*.md") if not pick or any(f.name.startswith(p) for p in pick))
    with cf.ThreadPoolExecutor(max_workers=6) as ex:
        res = list(ex.map(build, files))
    bad = [r for r in res if "ОШИБКА" in r]
    print("\n".join(bad) if bad else "", f"PDF: {len(res) - len(bad)} из {len(res)}", sep="\n")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
