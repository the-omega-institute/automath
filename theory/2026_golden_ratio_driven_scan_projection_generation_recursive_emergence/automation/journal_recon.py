#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Online journal reconnaissance for recent-paper notes and style signals."""

from __future__ import annotations

import argparse
import difflib
import html
import json
import math
import re
import statistics
from dataclasses import asdict, dataclass
from datetime import date, timedelta
from pathlib import Path
from typing import Any, Iterable
from urllib.error import HTTPError, URLError
from urllib.parse import unquote, urlencode, urljoin
from urllib.request import Request, urlopen

from automation_paths import export_dir


USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/124.0 Safari/537.36 automath-journal-recon/1.0"
)
TAG_RE = re.compile(r"<[^>]+>")
META_TAG_RE = re.compile(r"<meta\b[^>]*>", re.IGNORECASE)
INPUT_TAG_RE = re.compile(r"<input\b[^>]*>", re.IGNORECASE)
ATTR_RE = re.compile(r"([A-Za-z_:.-]+)\s*=\s*(\"[^\"]*\"|'[^']*'|[^\s>]+)")
TITLE_RE = re.compile(r"<title[^>]*>(.*?)</title>", re.IGNORECASE | re.DOTALL)
WORD_RE = re.compile(r"[^\W\d_][\w-]*", re.UNICODE)
META_REFRESH_URL_RE = re.compile(r"url\s*=\s*(.+)$", re.IGNORECASE)
MOJIBAKE_MARKERS = ("Ã", "Â", "â")
STOPWORDS = {
    "a",
    "an",
    "about",
    "above",
    "across",
    "after",
    "again",
    "against",
    "all",
    "among",
    "any",
    "as",
    "at",
    "also",
    "and",
    "are",
    "be",
    "been",
    "before",
    "because",
    "between",
    "both",
    "by",
    "can",
    "for",
    "from",
    "have",
    "how",
    "in",
    "is",
    "into",
    "it",
    "its",
    "new",
    "not",
    "of",
    "on",
    "or",
    "more",
    "most",
    "only",
    "over",
    "paper",
    "prove",
    "proves",
    "result",
    "results",
    "show",
    "shows",
    "study",
    "that",
    "the",
    "their",
    "them",
    "they",
    "then",
    "there",
    "these",
    "this",
    "those",
    "through",
    "to",
    "toward",
    "under",
    "using",
    "via",
    "was",
    "were",
    "what",
    "which",
    "who",
    "with",
    "within",
    "without",
    "we",
    "journal",
}
JOURNAL_TITLE_STOPWORDS = {
    "and",
    "bulletin",
    "communications",
    "international",
    "journal",
    "letters",
    "letter",
    "of",
    "proceedings",
    "review",
    "reviews",
    "the",
    "transactions",
}
REQUIRED_RECON_FILES = (
    "recon_profile.json",
    "recent_papers.json",
    "recent_paper_notes.md",
    "style_summary.md",
)


@dataclass(frozen=True)
class PaperRecord:
    title: str
    journal: str
    year: int
    published: str
    doi: str
    url: str
    publisher: str
    article_type: str
    abstract: str
    abstract_source: str


def slugify(text: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9]+", "_", text).strip("_").lower()
    return slug or "journal_recon"


def default_output_dir(slug: str) -> Path:
    return export_dir() / "journal_recon" / slug


def normalize_space(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def repair_common_mojibake(text: str) -> str:
    cleaned = normalize_space(text)
    if not cleaned or not any(marker in cleaned for marker in MOJIBAKE_MARKERS):
        return cleaned
    for encoding in ("latin-1", "cp1252"):
        try:
            candidate = cleaned.encode(encoding).decode("utf-8")
        except UnicodeError:
            continue
        if candidate and candidate.count("\ufffd") <= cleaned.count("\ufffd"):
            return normalize_space(candidate)
    return cleaned


def clean_html_text(text: str) -> str:
    cleaned = re.sub(r"</?(jats:)?[^>]+>", " ", text)
    cleaned = TAG_RE.sub(" ", cleaned)
    cleaned = html.unescape(cleaned)
    return repair_common_mojibake(cleaned)


def normalize_text(text: str) -> str:
    return repair_common_mojibake(html.unescape(text))


def normalize_journal_name(text: str) -> str:
    return normalize_space(re.sub(r"[^A-Za-z0-9]+", " ", text)).lower()


def journal_tokens(text: str) -> set[str]:
    return {
        token
        for token in normalize_journal_name(text).split()
        if token not in JOURNAL_TITLE_STOPWORDS
    }


def journal_match(requested: str, actual: str) -> bool:
    lhs = normalize_journal_name(requested)
    rhs = normalize_journal_name(actual)
    if not lhs or not rhs:
        return False
    if lhs == rhs or lhs in rhs or rhs in lhs:
        return True
    lhs_tokens = journal_tokens(requested)
    rhs_tokens = journal_tokens(actual)
    if not lhs_tokens or not rhs_tokens:
        return False
    overlap = lhs_tokens & rhs_tokens
    min_required = len(lhs_tokens) if len(lhs_tokens) <= 2 else max(2, math.ceil(0.6 * len(lhs_tokens)))
    ratio = difflib.SequenceMatcher(None, lhs, rhs).ratio()
    return len(overlap) >= min_required and ratio >= 0.55


def date_string_from_parts(parts: Iterable[int]) -> str:
    values = list(parts)
    if not values:
        return ""
    year = values[0]
    month = values[1] if len(values) >= 2 else 1
    day = values[2] if len(values) >= 3 else 1
    return f"{year:04d}-{month:02d}-{day:02d}"


def fetch_json(url: str) -> Any:
    request = Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "application/json",
        },
    )
    with urlopen(request, timeout=30) as response:
        charset = response.headers.get_content_charset() or "utf-8"
        return json.loads(response.read().decode(charset))


def fetch_text(url: str) -> tuple[str, str]:
    request = Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml",
            "Accept-Language": "en-US,en;q=0.9",
        },
    )
    with urlopen(request, timeout=30) as response:
        charset = response.headers.get_content_charset() or "utf-8"
        return response.read().decode(charset, errors="replace"), response.geturl()


def parse_tag_attributes(tag: str) -> dict[str, str]:
    attrs: dict[str, str] = {}
    for key, value in ATTR_RE.findall(tag):
        cleaned = value.strip().strip("\"'")
        attrs[key.lower()] = html.unescape(cleaned)
    return attrs


def extract_meta(html_text: str) -> dict[str, str]:
    meta: dict[str, str] = {}
    for tag in META_TAG_RE.findall(html_text):
        attrs = parse_tag_attributes(tag)
        lowered = (attrs.get("name") or attrs.get("property") or "").strip().lower()
        cleaned = normalize_text(attrs.get("content", ""))
        if lowered and cleaned and lowered not in meta:
            meta[lowered] = cleaned
    title_match = TITLE_RE.search(html_text)
    if title_match:
        meta.setdefault("html_title", clean_html_text(title_match.group(1)))
    return meta


def extract_redirect_target(html_text: str, current_url: str) -> str:
    for tag in INPUT_TAG_RE.findall(html_text):
        attrs = parse_tag_attributes(tag)
        key = (attrs.get("name") or attrs.get("id") or "").strip().lower()
        if key == "redirecturl":
            target = unquote(attrs.get("value", "").strip())
            if target:
                return urljoin(current_url, target)
    for tag in META_TAG_RE.findall(html_text):
        attrs = parse_tag_attributes(tag)
        http_equiv = attrs.get("http-equiv", "").strip().lower()
        if http_equiv != "refresh":
            continue
        content = attrs.get("content", "")
        match = META_REFRESH_URL_RE.search(content)
        if match:
            target = match.group(1).strip().strip("\"'")
            if target:
                return urljoin(current_url, target)
    return ""


def fetch_html_with_redirects(url: str, max_hops: int = 4) -> tuple[str, str]:
    current_url = url
    html_text = ""
    final_url = url
    for _ in range(max_hops):
        html_text, final_url = fetch_text(current_url)
        redirect_target = extract_redirect_target(html_text, final_url)
        if not redirect_target or redirect_target == current_url or redirect_target == final_url:
            return html_text, final_url
        current_url = redirect_target
    return html_text, final_url


def extract_year(published: str) -> int:
    match = re.match(r"(\d{4})", published)
    return int(match.group(1)) if match else 0


def crossref_journal_identity(journal: str) -> dict[str, str]:
    url = "https://api.crossref.org/journals?" + urlencode({"query": journal, "rows": 5})
    payload = fetch_json(url)
    items = payload.get("message", {}).get("items", [])
    best: dict[str, str] | None = None
    best_score = -1.0
    for item in items:
        title = normalize_space(str(item.get("title") or ""))
        if not title:
            continue
        ratio = difflib.SequenceMatcher(None, normalize_journal_name(journal), normalize_journal_name(title)).ratio()
        if ratio > best_score:
            best_score = ratio
            issn_values = item.get("ISSN") or []
            best = {
                "title": title,
                "issn": str(issn_values[0]) if issn_values else "",
            }
    return best or {"title": journal, "issn": ""}


def crossref_records(*, journal: str, max_papers: int, years_back: int) -> list[PaperRecord]:
    from_date = (date.today() - timedelta(days=max(1, years_back) * 365)).isoformat()
    identity = crossref_journal_identity(journal)
    filter_value = f"from-pub-date:{from_date},type:journal-article"
    if identity["issn"]:
        filter_value = f"issn:{identity['issn']}," + filter_value
    url = "https://api.crossref.org/works?" + urlencode(
        {
            "query.container-title": identity["title"],
            "filter": filter_value,
            "sort": "published",
            "order": "desc",
            "rows": max_papers * 4,
        }
    )
    payload = fetch_json(url)
    items = payload.get("message", {}).get("items", [])
    records: list[PaperRecord] = []
    for item in items:
        journal_title = normalize_text(str((item.get("container-title") or [""])[0] or ""))
        if journal_title and not journal_match(journal, journal_title):
            continue
        title = normalize_text(str((item.get("title") or [""])[0] or ""))
        if not title:
            continue
        doi = str(item.get("DOI") or "").strip()
        url_value = str(item.get("URL") or (f"https://doi.org/{doi}" if doi else "")).strip()
        published_parts = (
            item.get("published-print", {}).get("date-parts")
            or item.get("published-online", {}).get("date-parts")
            or item.get("issued", {}).get("date-parts")
            or [[]]
        )
        published = date_string_from_parts(published_parts[0] if published_parts else [])
        abstract = clean_html_text(str(item.get("abstract") or ""))
        records.append(
            PaperRecord(
                title=title,
                journal=journal_title or journal,
                year=extract_year(published),
                published=published,
                doi=doi,
                url=url_value,
                publisher=normalize_text(str(item.get("publisher") or "")),
                article_type=normalize_text(str(item.get("type") or "")),
                abstract=abstract,
                abstract_source="crossref" if abstract else "",
            )
        )
        if len(records) >= max_papers:
            break
    return records


def enrich_record(record: PaperRecord) -> PaperRecord:
    if record.abstract and record.title and record.journal:
        return record
    if not record.url:
        return record
    try:
        html_text, landing_url = fetch_html_with_redirects(record.url)
    except (HTTPError, URLError, TimeoutError):
        return record
    meta = extract_meta(html_text)
    title = (
        meta.get("citation_title")
        or meta.get("og:title")
        or meta.get("dc.title")
        or record.title
    )
    journal = (
        meta.get("citation_journal_title")
        or meta.get("prism.publicationname")
        or record.journal
    )
    abstract = record.abstract
    abstract_source = record.abstract_source
    if not abstract:
        for key in ("citation_abstract", "description", "og:description", "dc.description"):
            value = meta.get(key)
            if value:
                abstract = clean_html_text(value)
                abstract_source = key
                break
    return PaperRecord(
        title=normalize_text(title),
        journal=normalize_text(journal),
        year=record.year,
        published=record.published,
        doi=record.doi,
        url=landing_url or record.url,
        publisher=record.publisher,
        article_type=record.article_type,
        abstract=abstract,
        abstract_source=abstract_source,
    )


def first_sentence(text: str) -> str:
    cleaned = normalize_space(text)
    if not cleaned:
        return ""
    match = re.split(r"(?<=[.!?])\s+", cleaned, maxsplit=1)
    return match[0][:260]


def tokenize(text: str) -> list[str]:
    return [
        token.lower()
        for token in WORD_RE.findall(text)
        if len(token) >= 2 and token.lower() not in STOPWORDS
    ]


def top_terms(texts: Iterable[str], limit: int = 12) -> list[str]:
    counts: dict[str, int] = {}
    for text in texts:
        for token in tokenize(text):
            counts[token] = counts.get(token, 0) + 1
    ordered = sorted(counts.items(), key=lambda item: (-item[1], item[0]))
    return [token for token, _ in ordered[:limit]]


def median_or_zero(values: list[int]) -> float:
    return float(statistics.median(values)) if values else 0.0


def build_style_summary(records: list[PaperRecord]) -> dict[str, Any]:
    title_word_counts = [len(tokenize(record.title)) for record in records if record.title]
    abstract_word_counts = [len(tokenize(record.abstract)) for record in records if record.abstract]
    first_sentences = [first_sentence(record.abstract) for record in records if record.abstract]
    colon_count = sum(1 for record in records if ":" in record.title)
    article_types: dict[str, int] = {}
    publication_dates = [record.published for record in records if record.published]
    for record in records:
        key = record.article_type or "unknown"
        article_types[key] = article_types.get(key, 0) + 1
    phrase_counts = {
        "we prove": 0,
        "we show": 0,
        "in this paper": 0,
        "this paper": 0,
    }
    for sentence in first_sentences:
        lowered = sentence.lower()
        for phrase in phrase_counts:
            if lowered.startswith(phrase):
                phrase_counts[phrase] += 1

    return {
        "paper_count": len(records),
        "title_word_median": median_or_zero(title_word_counts),
        "title_word_mean": (sum(title_word_counts) / len(title_word_counts)) if title_word_counts else 0.0,
        "title_colon_ratio": (colon_count / len(records)) if records else 0.0,
        "abstract_available_total": len(abstract_word_counts),
        "abstract_coverage_ratio": (len(abstract_word_counts) / len(records)) if records else 0.0,
        "abstract_word_median": median_or_zero(abstract_word_counts),
        "abstract_word_mean": (sum(abstract_word_counts) / len(abstract_word_counts)) if abstract_word_counts else 0.0,
        "common_title_terms": top_terms(record.title for record in records),
        "common_abstract_terms": top_terms(record.abstract for record in records if record.abstract),
        "opening_phrases": phrase_counts,
        "article_types": article_types,
        "publication_window": {
            "latest": max(publication_dates) if publication_dates else "",
            "earliest": min(publication_dates) if publication_dates else "",
        },
        "appendix_ratio_inferable": False,
    }


def render_recent_paper_notes(*, journal: str, records: list[PaperRecord], summary: dict[str, Any]) -> str:
    lines = [
        f"# Recent Paper Notes: {journal}",
        "",
        "## Auto-Filled Style Signals",
        f"- Sample size: {summary['paper_count']} recent papers.",
        f"- Median title length: {summary['title_word_median']:.1f} content words.",
        f"- Titles with a colon: {summary['title_colon_ratio']:.0%}.",
        f"- Papers with abstract text available: {summary['abstract_available_total']}.",
        f"- Abstract coverage ratio: {summary['abstract_coverage_ratio']:.0%}.",
        f"- Median abstract length: {summary['abstract_word_median']:.1f} content words.",
        f"- Common title terms: {', '.join(summary['common_title_terms']) or 'n/a'}.",
        f"- Common abstract terms: {', '.join(summary['common_abstract_terms']) or 'n/a'}.",
        f"- Publication window sampled: {summary['publication_window']['earliest'] or 'n/a'} to {summary['publication_window']['latest'] or 'n/a'}.",
        "",
        "## Inferred Writing Tendencies",
    ]
    phrase_counts = summary["opening_phrases"]
    if max(phrase_counts.values(), default=0) > 0:
        ordered_phrases = sorted(phrase_counts.items(), key=lambda item: (-item[1], item[0]))
        lines.append(
            "- Frequent abstract openings: "
            + ", ".join(f"`{phrase}` ({count})" for phrase, count in ordered_phrases if count > 0)
            + "."
        )
    else:
        lines.append("- Abstract openings are heterogeneous; avoid overfitting a single formulaic first sentence.")
    article_types = summary.get("article_types", {})
    if article_types:
        ordered_types = sorted(article_types.items(), key=lambda item: (-item[1], item[0]))
        lines.append(
            "- Dominant article types in the sample: "
            + ", ".join(f"`{kind}` ({count})" for kind, count in ordered_types)
            + "."
        )
    lines.append("- Treat title and abstract cadence as auto-detected signals only; verify final tone against actual accepted PDFs.")
    lines.append("- Appendix ratio and proof-placement style are not reliably inferable from metadata alone; inspect recent accessible PDFs before final submission.")
    lines.extend(["", "## Recent Papers"])
    for index, record in enumerate(records, start=1):
        lines.append(f"### Paper {index}")
        lines.append(f"- Title: {record.title}")
        lines.append(f"- Journal string: {record.journal}")
        lines.append(f"- Published: {record.published or record.year or 'unknown'}")
        lines.append(f"- DOI: {record.doi or 'n/a'}")
        lines.append(f"- URL: {record.url or 'n/a'}")
        lines.append(f"- Abstract source: {record.abstract_source or 'none'}")
        lines.append(f"- Abstract first sentence: {first_sentence(record.abstract) or 'n/a'}")
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def render_style_summary(*, journal: str, summary: dict[str, Any]) -> str:
    lines = [
        f"# Style Summary: {journal}",
        "",
        f"- Sample size: {summary['paper_count']}",
        f"- Median title length: {summary['title_word_median']:.1f}",
        f"- Mean title length: {summary['title_word_mean']:.1f}",
        f"- Title colon ratio: {summary['title_colon_ratio']:.0%}",
        f"- Abstract availability: {summary['abstract_available_total']}",
        f"- Abstract coverage ratio: {summary['abstract_coverage_ratio']:.0%}",
        f"- Median abstract length: {summary['abstract_word_median']:.1f}",
        f"- Mean abstract length: {summary['abstract_word_mean']:.1f}",
        f"- Common title terms: {', '.join(summary['common_title_terms']) or 'n/a'}",
        f"- Common abstract terms: {', '.join(summary['common_abstract_terms']) or 'n/a'}",
        f"- Publication window: {summary['publication_window']['earliest'] or 'n/a'} to {summary['publication_window']['latest'] or 'n/a'}",
        "",
        "## Limits",
        "- This reconnaissance is metadata-driven.",
        "- Use it to auto-fill recent-paper notes, not to replace full reading of target-journal PDFs.",
        "",
    ]
    return "\n".join(lines)


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def validate_recon_dir(path: Path) -> tuple[bool, list[str]]:
    errors: list[str] = []
    for name in REQUIRED_RECON_FILES:
        target = path / name
        if not target.is_file() or target.stat().st_size == 0:
            errors.append(f"Missing required recon artifact: {name}")
    for json_name in ("recon_profile.json", "recent_papers.json"):
        target = path / json_name
        if target.is_file():
            try:
                json.loads(target.read_text(encoding="utf-8"))
            except json.JSONDecodeError as exc:
                errors.append(f"{json_name} invalid JSON: {exc}")
    return len(errors) == 0, errors


def run_recon(
    *,
    journal: str,
    journal_short: str,
    max_papers: int,
    years_back: int,
    output_dir: Path | None,
    slug: str | None,
    skip_landing_fetch: bool,
) -> dict[str, Any]:
    resolved_slug = slug or slugify(journal_short or journal)
    target_dir = output_dir.resolve() if output_dir else default_output_dir(resolved_slug)
    target_dir.mkdir(parents=True, exist_ok=True)

    records = crossref_records(journal=journal, max_papers=max_papers, years_back=years_back)
    if not skip_landing_fetch:
        records = [enrich_record(record) for record in records]
    summary = build_style_summary(records)
    profile = {
        "journal": journal,
        "journal_short": journal_short or journal,
        "output_dir": str(target_dir),
        "max_papers": max_papers,
        "years_back": years_back,
        "records_total": len(records),
        "records_with_abstract": sum(1 for record in records if record.abstract),
        "skip_landing_fetch": skip_landing_fetch,
    }
    write_json(target_dir / "recon_profile.json", profile)
    write_json(
        target_dir / "recent_papers.json",
        {
            "journal": journal,
            "papers": [asdict(record) for record in records],
            "style_summary": summary,
        },
    )
    (target_dir / "recent_paper_notes.md").write_text(
        render_recent_paper_notes(journal=journal, records=records, summary=summary),
        encoding="utf-8",
    )
    (target_dir / "style_summary.md").write_text(
        render_style_summary(journal=journal, summary=summary),
        encoding="utf-8",
    )

    ok, errors = validate_recon_dir(target_dir)
    if not ok:
        raise RuntimeError("; ".join(errors))
    print(
        "[journal-recon] run:"
        f" journal={journal!r}"
        f" papers={len(records)}"
        f" abstracts={sum(1 for record in records if record.abstract)}"
        f" output={target_dir}"
    )
    return {
        "output_dir": str(target_dir),
        "records_total": len(records),
    }


def cmd_run(args: argparse.Namespace) -> int:
    try:
        run_recon(
            journal=args.journal,
            journal_short=args.journal_short or "",
            max_papers=args.max_papers,
            years_back=args.years_back,
            output_dir=Path(args.output_dir) if args.output_dir else None,
            slug=args.slug,
            skip_landing_fetch=args.skip_landing_fetch,
        )
    except Exception as exc:
        print(f"[journal-recon] run failed: {exc}")
        return 1
    return 0


def cmd_validate(args: argparse.Namespace) -> int:
    target = Path(args.path).resolve()
    ok, errors = validate_recon_dir(target)
    print(
        "[journal-recon] validate:"
        f" path={target}"
        f" ok={ok}"
        f" errors={len(errors)}"
    )
    for error in errors[:50]:
        print(f"  {error}")
    return 0 if ok else 1


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Fetch recent journal papers and auto-fill style notes")
    sub = p.add_subparsers(dest="command", required=True)

    run_p = sub.add_parser("run", help="Fetch recent papers and write style notes")
    run_p.add_argument("--journal", required=True, help="Target journal name")
    run_p.add_argument("--journal-short", help="Optional journal abbreviation")
    run_p.add_argument("--max-papers", type=int, default=6, help="Number of recent papers to sample")
    run_p.add_argument("--years-back", type=int, default=3, help="How many years back to query")
    run_p.add_argument("--slug", help="Override output slug")
    run_p.add_argument("--output-dir", help="Override output directory")
    run_p.add_argument(
        "--skip-landing-fetch",
        action="store_true",
        help="Only use Crossref metadata and skip landing-page enrichment",
    )
    run_p.set_defaults(func=cmd_run)

    validate_p = sub.add_parser("validate", help="Validate one reconnaissance directory")
    validate_p.add_argument("path", help="Path to a generated journal reconnaissance directory")
    validate_p.set_defaults(func=cmd_validate)
    return p


def main() -> int:
    args = parser().parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
