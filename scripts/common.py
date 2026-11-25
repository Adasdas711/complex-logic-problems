"""Общие функции: загрузка содержания, классификации, задач; расчёт квот и занятий."""
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

ID_RE = re.compile(r"^(\d{2})\.(\d{2})-(\d{3,4})$")
FRONT_RE = re.compile(r"^---\n(.*?)\n---\n", re.S)


def load_yaml(name: str):
    with open(DATA / name, encoding="utf-8") as f:
        return yaml.safe_load(f)


@dataclass
class Section:
    chapter: int
    num: int
    title: str
    profile: str
    page: int | None = None
    source: str = ""
    weight: float = 1.0
    fixed: int | None = None
    end_page: int = 0
    quota: int = 0
    level_quota: dict = field(default_factory=dict)
    diag_quota: int = 0
    covers: int | None = None

    @property
    def key(self) -> str:
        return f"{self.chapter:02d}.{self.num:02d}"

    @property
    def label(self) -> str:
        return "без §" if self.num == 0 else f"§ {self.num}"

    @property
    def pages(self) -> str:
        if self.page is None:
            return self.source
        if self.end_page <= self.page + 1:
            return f"с. {self.page}"
        return f"с. {self.page}–{self.end_page - 1}"


@dataclass
class Chapter:
    num: int
    slug: str
    title: str
    sections: list
    systems: list = field(default_factory=list)
    extra: bool = False
    mixed: bool = False
    order_after: int | None = None
    sources: list = field(default_factory=list)

    @property
    def label(self) -> str:
        if self.num == 0:
            return "Введение"
        if self.num == 15:
            return "Приложение"
        if self.extra:
            return f"Раздел {self.num}"
        return f"Глава {self.num}"

    @property
    def full_title(self) -> str:
        return self.title if self.num in (0, 15) else f"{self.label}. {self.title}"


def load_book() -> list[Chapter]:
    toc = load_yaml("toc.yaml")
    chapters: list[Chapter] = []
    for ch in toc["chapters"]:
        secs = [Section(ch["num"], s["num"], s["title"], s["profile"], page=s["page"],
                        weight=s.get("weight", 1.0), fixed=s.get("quota"))
                for s in ch["sections"]]
        chapters.append(Chapter(ch["num"], ch["slug"], ch["title"], secs, ch.get("systems", [])))
    flat = [s for c in chapters for s in c.sections]
    for s, e in zip(flat, [s.page for s in flat[1:]] + [198]):   # Приложение кончается перед Заключением
        s.end_page = e
    for ex in toc.get("extra", []):
        c = Chapter(ex["num"], ex["slug"], ex["title"], [], extra=True, mixed=ex.get("mixed", False),
                    order_after=ex.get("order_after"), sources=ex.get("sources", []))
        if c.mixed:
            c.sections = [Section(c.num, 0, "", "X", fixed=ex["quota"])]   # разворачивается в compute_quotas
        else:
            c.sections = [Section(c.num, s["num"], s["title"], s["profile"], source=s.get("source", ""),
                                  fixed=s["quota"]) for s in ex["sections"]]
        chapters.append(c)
    return chapters


def study_order(chapters: list[Chapter]) -> list[Chapter]:
    """Порядок прохождения: главы книги, дополнительные разделы — после указанной главы."""
    out = []
    for c in (c for c in chapters if not c.extra):
        out.append(c)
        out.extend(x for x in chapters if x.extra and not x.mixed and x.order_after == c.num)
    return out


def _largest_remainder(weights: dict, total: int) -> dict:
    s = sum(weights.values())
    if s == 0 or total == 0:
        return {k: 0 for k in weights}
    raw = {k: w / s * total for k, w in weights.items()}
    out = {k: math.floor(v) for k, v in raw.items()}
    for k in sorted(raw, key=lambda k: raw[k] - out[k], reverse=True)[: total - sum(out.values())]:
        out[k] += 1
    return out


def compute_quotas(chapters: list[Chapter]) -> None:
    tax = load_yaml("taxonomy.yaml")
    qmin, qmax = tax["quota"]["min_per_section"], tax["quota"]["max_per_section"]
    mixed = next((c for c in chapters if c.mixed), None)
    extra_fixed = sum(s.fixed for c in chapters if c.extra for s in c.sections)
    book_secs = [s for c in chapters if not c.extra for s in c.sections]
    fixed = {s.key: s.fixed for s in book_secs if s.fixed is not None}
    free = [s for s in book_secs if s.fixed is None]
    budget = tax["total"] - extra_fixed - sum(fixed.values())
    weight = {s.key: max(s.end_page - s.page, 0.5) * s.weight for s in free}
    lo, hi = 0.0, 1000.0
    for _ in range(200):
        k = (lo + hi) / 2
        tot = sum(min(qmax, max(qmin, k * w)) for w in weight.values())
        lo, hi = (k, hi) if tot < budget else (lo, k)
    q = _largest_remainder({key: min(qmax, max(qmin, k * w)) for key, w in weight.items()}, budget)
    q.update(fixed)
    for c in chapters:
        for s in c.sections:
            s.quota = q.get(s.key, s.fixed or 0) if not c.extra else s.fixed

    # Смешанные наборы: по одному после каждой главы/раздела, пропорционально объёму этапа.
    if mixed:
        total_mixed = mixed.sections[0].fixed
        stages = study_order(chapters)
        sizes = _largest_remainder({c.num: sum(s.quota for s in c.sections) for c in stages}, total_mixed)
        mixed.sections = []
        for i, c in enumerate(stages, 1):
            mixed.sections.append(Section(mixed.num, i, f"После: {c.full_title}", "X",
                                          quota=sizes[c.num], covers=c.num))

    profiles, share = tax["profiles"], tax["diagnostic_share"]
    for c in chapters:
        for s in c.sections:
            mix = {int(l): p for l, p in profiles[s.profile]["levels"].items()}
            s.level_quota = _largest_remainder(mix, s.quota)
            s.diag_quota = s.quota if s.profile == "E" else round(s.quota * share / 100)


def compute_sessions(chapters: list[Chapter]) -> list[dict]:
    """Расписание занятий: в каждом занятии новый материал и смешанное повторение пройденного."""
    tax = load_yaml("taxonomy.yaml")
    size = tax["sessions"]["size"]
    mixed = next((c for c in chapters if c.mixed), None)
    total = sum(s.quota for c in chapters for s in c.sections)
    mixed_total = sum(s.quota for s in mixed.sections) if mixed else 0
    per_mixed = round(size * mixed_total / total)

    new_stream = [(c, s) for c in study_order(chapters) for s in c.sections]
    left = {s.key: s.quota for _, s in new_stream}
    mixed_left = {s.key: s.quota for s in (mixed.sections if mixed else [])}
    unlocked: list = []
    done: set = set()
    sessions = []
    while any(left.values()) or any(mixed_left.values()):
        sess = {"num": len(sessions) + 1, "new": [], "mixed": []}
        avail = [m for m in unlocked if mixed_left[m.key]]
        want = (per_mixed if any(left.values()) else size) if avail else 0
        for m in avail:
            if want <= 0:
                break
            take = min(want, mixed_left[m.key])
            mixed_left[m.key] -= take
            want -= take
            sess["mixed"].append((m, take))
        room = size - sum(t for _, t in sess["mixed"])
        for c, s in new_stream:
            if room > 0 and left[s.key]:
                take = min(room, left[s.key])
                left[s.key] -= take
                room -= take
                sess["new"].append((c, s, take))
            if c.num not in done and all(left[x.key] == 0 for x in c.sections):
                done.add(c.num)
                if mixed:
                    unlocked += [m for m in mixed.sections if m.covers == c.num]
        # Если нового материала не хватило, место заполняется повторением.
        for m in [m for m in unlocked if mixed_left[m.key]]:
            if room <= 0:
                break
            take = min(room, mixed_left[m.key])
            mixed_left[m.key] -= take
            room -= take
            sess["mixed"].append((m, take))
        if not sess["new"] and not sess["mixed"]:
            break
        sessions.append(sess)
    # Короткий хвост (меньше половины занятия) присоединяется к предыдущему занятию.
    if len(sessions) > 1:
        last = sessions[-1]
        if sum(t for *_, t in last["new"]) + sum(t for _, t in last["mixed"]) < size / 2:
            sessions[-2]["new"] += last["new"]
            sessions[-2]["mixed"] += last["mixed"]
            sessions.pop()
    return sessions


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
