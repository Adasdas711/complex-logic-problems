"""Общие функции: загрузка содержания, классификации, задач; расчёт квот."""
from __future__ import annotations

import math
import re
from dataclasses import dataclass, field
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data"
PROBLEMS = ROOT / "problems"
DOCS = ROOT / "docs"

ID_RE = re.compile(r"^(\d{2})\.(\d{2})-(\d{3})$")
FRONT_RE = re.compile(r"^---\n(.*?)\n---\n", re.S)


def load_yaml(name: str):
    with open(DATA / name, encoding="utf-8") as f:
        return yaml.safe_load(f)


@dataclass
class Section:
    chapter: int
    num: int
    title: str
    page: int
    profile: str
    weight: float = 1.0
    fixed: int | None = None
    end_page: int = 0
    quota: int = 0
    level_quota: dict = field(default_factory=dict)

    @property
    def key(self) -> str:
        return f"{self.chapter:02d}.{self.num:02d}"

    @property
    def label(self) -> str:
        return "без §" if self.num == 0 else f"§ {self.num}"


@dataclass
class Chapter:
    num: int
    slug: str
    title: str
    page: int | None
    sections: list
    systems: list = field(default_factory=list)
    extra: bool = False
    fixed_quota: int = 0

    @property
    def label(self) -> str:
        if self.num == 0:
            return "Введение"
        if self.extra:
            return "Сквозные"
        if self.num == 15:
            return "Приложение"
        return f"Глава {self.num}"


def load_book() -> list[Chapter]:
    toc = load_yaml("toc.yaml")
    chapters: list[Chapter] = []
    for ch in toc["chapters"]:
        secs = [
            Section(ch["num"], s["num"], s["title"], s["page"], s["profile"],
                    s.get("weight", 1.0), s.get("quota"))
            for s in ch["sections"]
        ]
        chapters.append(Chapter(ch["num"], ch["slug"], ch["title"], ch["page"], secs, ch.get("systems", [])))
    flat = [s for c in chapters for s in c.sections]
    # Приложение кончается перед Заключением (с. 198); остальные — началом следующего параграфа.
    ends = [s.page for s in flat[1:]] + [198]
    for s, e in zip(flat, ends):
        s.end_page = e
    for ex in toc.get("extra", []):
        sec = Section(ex["num"], 0, ex["title"], 0, "X")
        sec.quota = ex["quota"]
        chapters.append(Chapter(ex["num"], ex["slug"], ex["title"], None, [sec], extra=True, fixed_quota=ex["quota"]))
    return chapters


def _largest_remainder(weights: dict, total: int) -> dict:
    s = sum(weights.values())
    if s == 0 or total == 0:
        return {k: 0 for k in weights}
    raw = {k: w / s * total for k, w in weights.items()}
    out = {k: math.floor(v) for k, v in raw.items()}
    rest = total - sum(out.values())
    for k in sorted(raw, key=lambda k: raw[k] - out[k], reverse=True)[:rest]:
        out[k] += 1
    return out


def compute_quotas(chapters: list[Chapter]) -> None:
    tax = load_yaml("taxonomy.yaml")
    total = tax["total"]
    qmin, qmax = tax["quota"]["min_per_section"], tax["quota"]["max_per_section"]
    secs = [s for c in chapters if not c.extra for s in c.sections]
    fixed = {s.key: s.fixed for s in secs if s.fixed is not None}
    secs_free = [s for s in secs if s.fixed is None]
    budget = total - sum(c.fixed_quota for c in chapters if c.extra) - sum(fixed.values())
    weight = {s.key: max(s.end_page - s.page, 0.5) * s.weight for s in secs_free}

    # Ищем множитель k: quota = clamp(k * pages) так, чтобы сумма равнялась бюджету.
    lo, hi = 0.0, 100.0
    for _ in range(200):
        k = (lo + hi) / 2
        tot = sum(min(qmax, max(qmin, k * w)) for w in weight.values())
        lo, hi = (k, hi) if tot < budget else (lo, k)
    raw = {key: min(qmax, max(qmin, k * w)) for key, w in weight.items()}
    q = _largest_remainder(raw, budget)
    q.update(fixed)
    for s in secs:
        s.quota = q[s.key]
    profiles = tax["profiles"]
    for c in chapters:
        for s in c.sections:
            mix = {int(l): p for l, p in profiles[s.profile]["levels"].items()}
            s.level_quota = _largest_remainder(mix, s.quota)


@dataclass
class Problem:
    path: Path
    meta: dict
    body: str


def load_problems() -> list[Problem]:
    out = []
    for p in sorted(PROBLEMS.glob("*/*.md")):
        if p.name == "README.md":
            continue
        text = p.read_text(encoding="utf-8")
        m = FRONT_RE.match(text)
        meta = yaml.safe_load(m.group(1)) if m else None
        out.append(Problem(p, meta or {}, text[m.end():] if m else text))
    return out


def problem_title(pr: Problem) -> str:
    """Первая строка условия — для оглавлений."""
    m = re.search(r"## Условие\s*\n+(.+)", pr.body)
    line = m.group(1).strip() if m else ""
    return (line[:90] + "…") if len(line) > 90 else line
