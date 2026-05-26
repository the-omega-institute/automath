#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Deterministic split-overlap harness for publication manuscripts.

The harness is intentionally standalone. It reads paper source files and the
publication board, emits structured JSON/Markdown, and returns a hard gate
status before any agent is allowed to deepen or rewrite a manuscript.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
import sys
from collections import Counter
from datetime import date, datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_PUBLICATION_DIR = REPO_ROOT / "papers" / "publication"
DEFAULT_BOARD_PATH = DEFAULT_PUBLICATION_DIR / "PROGRAM_BOARD.md"
DEFAULT_REPORT_DIR = SCRIPT_DIR / "reports"
DEFAULT_PUBLICATION_YEAR = 2026

PAPER_DIR_PREFIXES = ("2026_", "submitted_2026_")
DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION = "deferred_wait_for_prior_submission"
FAILING_CLASSIFICATIONS = {
    "blocker",
    "needs_human_resolution",
    DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION,
}
SUBMITTED_MARKER_FILES = ("SUBMITTED", "submission_receipt.md")
SUBMISSION_DATE_FILES = ("submission_receipt.md", "SUBMITTED")

THEOREM_ENVIRONMENTS = (
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "definition",
)

SKIP_TEX_DIR_NAMES = {
    ".git",
    "_minted-main",
    "build",
    "dist",
    "out",
    "submission_package",
    "submitted_package",
    "pipeline_artifacts",
    "oracle_reviews",
}

STOPWORDS = {
    "about",
    "above",
    "after",
    "again",
    "against",
    "also",
    "among",
    "and",
    "another",
    "any",
    "are",
    "around",
    "because",
    "been",
    "before",
    "being",
    "between",
    "both",
    "can",
    "case",
    "cases",
    "condition",
    "conditions",
    "contains",
    "could",
    "defined",
    "denote",
    "does",
    "each",
    "equation",
    "every",
    "exist",
    "exists",
    "following",
    "for",
    "from",
    "given",
    "have",
    "here",
    "hence",
    "into",
    "let",
    "map",
    "may",
    "more",
    "not",
    "one",
    "only",
    "other",
    "our",
    "over",
    "paper",
    "proof",
    "result",
    "results",
    "section",
    "set",
    "show",
    "shows",
    "such",
    "than",
    "that",
    "the",
    "then",
    "there",
    "these",
    "this",
    "those",
    "through",
    "under",
    "using",
    "where",
    "which",
    "with",
}

MAJOR_CLAIM_MARKERS = {
    "m_ge_3_threshold",
    "finite_memory_conjugacy",
    "fischer_cover",
    "residue_window_decoder",
    "m2_branch_locus",
    "dynamical_zeta_finite_part",
    "homological_visibility_pullback",
    "finite_observation_escape_rates",
    "scan_error_prefix_partition",
}

HARD_MARKER_BUNDLES = {
    "finite_window_conjugacy_core": {
        "sliding_overlap_reconstruction",
        "m_ge_3_threshold",
        "finite_memory_conjugacy",
        "residue_window_decoder",
    },
    "fibonacci_three_window_conjugacy": {
        "fibonacci_finite_window_fold",
        "sliding_overlap_reconstruction",
        "m_ge_3_threshold",
        "finite_memory_conjugacy",
        "residue_window_decoder",
    },
    "zeckendorf_normalization_rigidity": {
        "fibonacci_finite_window_fold",
        "zeckendorf_normalization",
        "sliding_overlap_reconstruction",
        "m_ge_3_threshold",
    },
    "dynamical_zeta_finite_part": {
        "dynamical_zeta_finite_part",
        "finite_observation_escape_rates",
        "cyclotomic_resonance",
    },
    "homological_visibility_gluing": {
        "homological_visibility_pullback",
        "visible_quotient_gluing",
    },
    "scan_error_prefix_partitions": {
        "scan_error_prefix_partition",
        "residue_window_decoder",
    },
}

SOFT_MARKERS = {
    "bernoulli_markov_transport",
    "parry_mismatch_or_divergence",
    "prime_languages_finite_state",
    "spectral_rigidity",
}


def _mojibake(text: str) -> str:
    """Return the common UTF-8-as-Latin-1 mojibake form of text."""
    try:
        return text.encode("utf-8").decode("latin-1")
    except UnicodeError:
        return text


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _clean_latex(text: str, *, max_len: int = 500) -> str:
    text = re.sub(r"%.*", " ", text)
    text = re.sub(r"\\(?:cite|ref|eqref|label|url)\{[^}]*\}", " ", text)
    text = re.sub(r"\\[a-zA-Z*]+(?:\[[^\]]*\])?", " ", text)
    text = text.replace("{", " ").replace("}", " ")
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) > max_len:
        return text[: max_len - 3].rstrip() + "..."
    return text


def parse_board_entries(board_path: Path = DEFAULT_BOARD_PATH) -> dict[str, dict[str, str]]:
    """Parse PROGRAM_BOARD.md rows keyed by backtick-wrapped directory name."""
    text = _read_text(board_path)
    entries: dict[str, dict[str, str]] = {}
    for match in re.finditer(
        r"\|\s*`([^`]+)`\s*\|\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|\s*([^|]*?)\s*\|",
        text,
    ):
        name = match.group(1).strip()
        entries[name] = {
            "journal": match.group(2).strip(),
            "status": match.group(3).strip(),
            "reroute": match.group(4).strip(),
        }
    return entries


def board_row_text(entry: dict[str, str] | None) -> str:
    if not entry:
        return ""
    return " | ".join(entry.get(key, "") for key in ("journal", "status", "reroute"))


MONTH_NAMES = {
    "jan": 1,
    "january": 1,
    "feb": 2,
    "february": 2,
    "mar": 3,
    "march": 3,
    "apr": 4,
    "april": 4,
    "may": 5,
    "jun": 6,
    "june": 6,
    "jul": 7,
    "july": 7,
    "aug": 8,
    "august": 8,
    "sep": 9,
    "sept": 9,
    "september": 9,
    "oct": 10,
    "october": 10,
    "nov": 11,
    "november": 11,
    "dec": 12,
    "december": 12,
}


def _iso_date(year: int, month: int, day: int) -> str:
    try:
        return date(year, month, day).isoformat()
    except ValueError:
        return ""


def extract_submission_date(text: str) -> str:
    """Extract an explicit submission date, returning ISO format when present."""
    if not text:
        return ""

    match = re.search(r"\b(20\d{2})[-/](0?[1-9]|1[0-2])[-/](0?[1-9]|[12]\d|3[01])\b", text)
    if match:
        return _iso_date(int(match.group(1)), int(match.group(2)), int(match.group(3)))

    match = re.search(r"\b(0?[1-9]|1[0-2])[-/](0?[1-9]|[12]\d|3[01])\b", text)
    if match:
        return _iso_date(DEFAULT_PUBLICATION_YEAR, int(match.group(1)), int(match.group(2)))

    month_pattern = "|".join(sorted(MONTH_NAMES, key=len, reverse=True))
    match = re.search(
        rf"\b(0?[1-9]|[12]\d|3[01])\s+({month_pattern})\.?,?\s+(20\d{{2}})\b",
        text,
        flags=re.IGNORECASE,
    )
    if match:
        return _iso_date(
            int(match.group(3)),
            MONTH_NAMES[match.group(2).lower().rstrip(".")],
            int(match.group(1)),
        )

    match = re.search(
        rf"\b({month_pattern})\.?\s+(0?[1-9]|[12]\d|3[01]),?\s+(20\d{{2}})\b",
        text,
        flags=re.IGNORECASE,
    )
    if match:
        return _iso_date(
            int(match.group(3)),
            MONTH_NAMES[match.group(1).lower().rstrip(".")],
            int(match.group(2)),
        )
    return ""


def paper_submission_date(paper_dir: Path, entry: dict[str, str] | None) -> str:
    row_date = extract_submission_date(board_row_text(entry))
    if row_date:
        return row_date
    for filename in SUBMISSION_DATE_FILES:
        marker_date = extract_submission_date(_read_text(paper_dir / filename))
        if marker_date:
            return marker_date
    return ""


def _marker_variants(*markers: str) -> tuple[str, ...]:
    variants: list[str] = []
    for marker in markers:
        variants.append(marker)
        variants.append(_mojibake(marker))
    return tuple(dict.fromkeys(variants))


SUBMITTED_STATUS_MARKERS = _marker_variants(
    "\u5df2\u6295",
    "\u5df2\u63a5\u6536",
    "\u63a5\u6536",
    "\u5df2\u53d1\u8868",
    "\u62d2\u7a3f",
    "\u5ba1\u7a3f",
    "\u8f6c\u6295",
    "\u5f52\u6863",
    "submitted",
    "under review",
    "peer review",
    "accepted",
    "published",
    "rejected",
    "reroute",
    "retarget",
)

RESOLVED_OVERLAP_MARKERS = _marker_variants(
    "\u8def\u7ebf\u5173\u95ed",
    "\u4e0d\u56de stage a",
    "\u5df2\u5e76\u5165",
    "\u5e76\u5165",
    "\u5f52\u6863",
    "\u505c\u7528",
    "\u5173\u95ed",
    "superseded",
    "closed",
    "merged into",
    "parked",
    "do not resubmit",
    "do not retarget",
)


def board_overlap_resolved(text: str) -> bool:
    low = text.lower()
    return any(marker in text or marker in low for marker in RESOLVED_OVERLAP_MARKERS)


def paper_requires_resolution(name: str, entry: dict[str, str] | None) -> bool:
    row_text = board_row_text(entry)
    if board_overlap_resolved(row_text):
        return False
    if name.startswith("submitted_"):
        return True
    low = row_text.lower()
    return any(marker in row_text or marker in low for marker in SUBMITTED_STATUS_MARKERS)


def has_submission_marker_file(paper_dir: Path) -> bool:
    return any((paper_dir / marker).exists() for marker in SUBMITTED_MARKER_FILES)


def paper_has_prior_submission(
    name: str,
    entry: dict[str, str] | None,
    paper_dir: Path,
) -> bool:
    row_text = board_row_text(entry)
    if board_overlap_resolved(row_text):
        return False
    if name.startswith("submitted_") or has_submission_marker_file(paper_dir):
        return True
    low = row_text.lower()
    return any(marker in row_text or marker in low for marker in SUBMITTED_STATUS_MARKERS)


def _iter_tex_files(paper_dir: Path) -> list[Path]:
    files: list[Path] = []
    for path in paper_dir.rglob("*.tex"):
        if any(part in SKIP_TEX_DIR_NAMES for part in path.relative_to(paper_dir).parts[:-1]):
            continue
        files.append(path)
    return sorted(files)


def paper_text(paper_dir: Path) -> str:
    return "\n".join(_read_text(path) for path in _iter_tex_files(paper_dir))


def _first_latex_argument(text: str, command: str) -> str:
    pattern = re.compile(rf"\\{re.escape(command)}(?:\[[^\]]*\])?\{{(.*?)\}}", re.DOTALL)
    match = pattern.search(text)
    if not match:
        return ""
    return _clean_latex(match.group(1), max_len=300)


def extract_abstract(text: str) -> str:
    match = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", text, re.DOTALL)
    return _clean_latex(match.group(1), max_len=1000) if match else ""


def extract_keywords(text: str) -> list[str]:
    raw = ""
    for command in ("keywords", "keyword"):
        raw = _first_latex_argument(text, command)
        if raw:
            break
    if not raw:
        match = re.search(r"\\begin\{keywords\}(.*?)\\end\{keywords\}", text, re.DOTALL)
        raw = _clean_latex(match.group(1), max_len=500) if match else ""
    if not raw:
        return []
    return [part.strip(" .;") for part in re.split(r"[;,]", raw) if part.strip(" .;")]


def extract_msc(text: str) -> list[str]:
    raw = ""
    for command in ("subjclass", "classification", "MSC"):
        raw = _first_latex_argument(text, command)
        if raw:
            break
    if not raw:
        return []
    return sorted(set(re.findall(r"\b\d{2}[A-Z]\d{2}\b", raw)))


def extract_theorem_statements(paper_dir: Path) -> list[dict[str, str]]:
    envs = "|".join(re.escape(env) for env in THEOREM_ENVIRONMENTS)
    pattern = re.compile(
        rf"\\begin\{{({envs})\}}(?:\[[^\]]*\])?\s*"
        r"(?:\\label\{([^}]+)\})?"
        r"(.*?)"
        rf"\\end\{{\1\}}",
        re.DOTALL,
    )
    statements: list[dict[str, str]] = []
    for tex_path in _iter_tex_files(paper_dir):
        text = _read_text(tex_path)
        rel = str(tex_path.relative_to(paper_dir)).replace("\\", "/")
        for match in pattern.finditer(text):
            body = re.sub(r"\s+", " ", match.group(3)).strip()
            if len(body) < 40:
                continue
            statements.append(
                {
                    "environment": match.group(1),
                    "label": match.group(2) or f"unlabelled:{rel}:{match.start()}",
                    "file": rel,
                    "snippet": _clean_latex(body, max_len=400),
                    "raw": body,
                }
            )
    return statements


def normalize_for_overlap(text: str) -> str:
    text = text.lower()
    text = text.replace("\\geq", " >= ").replace("\\ge", " >= ")
    text = text.replace("\\leq", " <= ").replace("\\le", " <= ")
    text = text.replace("--", " ")
    text = re.sub(r"\\[a-zA-Z]+", lambda m: " " + m.group(0)[1:] + " ", text)
    text = re.sub(r"[^a-z0-9_<>=$+\-]+", " ", text)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def source_fingerprint(text: str) -> str:
    norm = normalize_for_overlap(text)
    norm = re.sub(r"\b\d{4}-\d{2}-\d{2}\b", " ", norm)
    norm = re.sub(r"\s+", " ", norm).strip()
    return hashlib.sha256(norm.encode("utf-8")).hexdigest()


def claim_markers_for_text(text: str) -> set[str]:
    """Extract high-signal, deterministic theorem-package markers."""
    norm = normalize_for_overlap(text)

    def any_term(*terms: str) -> bool:
        return any(term in norm for term in terms)

    markers: set[str] = set()
    if "fibonacci" in norm and any_term(
        "finite-window", "finite window", "fold_m", "normalization", "stabilization"
    ):
        markers.add("fibonacci_finite_window_fold")
    if "zeckendorf" in norm and "normalization" in norm:
        markers.add("zeckendorf_normalization")
    if any_term("sliding", "overlap", "overlapping") and any_term(
        "recover", "reconstruct", "determine", "inject"
    ):
        markers.add("sliding_overlap_reconstruction")
    if any_term("m >= 3", "m>=3", "m ge 3") and any_term(
        "threshold", "inject", "conjug", "recover", "reconstruct", "invert"
    ):
        markers.add("m_ge_3_threshold")
    if any_term("finite-memory", "finite memory") and any_term(
        "conjugacy", "inverse", "decoder"
    ):
        markers.add("finite_memory_conjugacy")
    if "fischer cover" in norm:
        markers.add("fischer_cover")
    if "residue" in norm and any_term("decoder", "window", "congruence", "modulo"):
        markers.add("residue_window_decoder")
    if any_term("m = 2", "m=2") and "branch" in norm:
        markers.add("m2_branch_locus")
    if "bernoulli" in norm and "markov" in norm:
        markers.add("bernoulli_markov_transport")
    if "metallic" in norm and any_term("golden", "a >= 2", "a>=2"):
        markers.add("metallic_golden_exception")
    if "zeta" in norm and "finite" in norm and any_term("shift of finite type", "sft"):
        markers.add("dynamical_zeta_finite_part")
    if "prime" in norm and any_term("language", "languages") and "finite" in norm:
        markers.add("prime_languages_finite_state")
    if "homological" in norm and "visibility" in norm:
        markers.add("homological_visibility_pullback")
    if "visible quotient" in norm or "visible quotients" in norm:
        markers.add("visible_quotient_gluing")
    if "finite observation" in norm and any_term("escape rate", "escape rates"):
        markers.add("finite_observation_escape_rates")
    if "cyclotomic" in norm and any_term("resonance", "resonances"):
        markers.add("cyclotomic_resonance")
    if "fredholm" in norm and "determinant" in norm:
        markers.add("fredholm_determinant")
    if "spectral" in norm and "rigidity" in norm:
        markers.add("spectral_rigidity")
    if any_term("self-dual", "self dual") and any_term("synchronisation", "synchronization"):
        markers.add("self_dual_synchronisation")
    if "scan error" in norm and any_term("prefix partition", "prefix partitions"):
        markers.add("scan_error_prefix_partition")
    if "parry" in norm and any_term("mismatch", "divergence"):
        markers.add("parry_mismatch_or_divergence")
    if "berstel" in norm and "adder" in norm:
        markers.add("berstel_adder")
    return markers


def claim_tokens(text: str) -> set[str]:
    norm = normalize_for_overlap(text)
    raw_tokens = re.findall(r"[a-z][a-z0-9_+\-]{2,}", norm)
    return {
        token.strip("-_")
        for token in raw_tokens
        if token.strip("-_") and token not in STOPWORDS and len(token.strip("-_")) >= 4
    }


def _ngram_counter(statements: list[dict[str, str]], n: int = 8) -> Counter[str]:
    counter: Counter[str] = Counter()
    for stmt in statements:
        tokens = [
            token
            for token in re.findall(r"[a-z0-9_+\-]{3,}", normalize_for_overlap(stmt.get("raw", "")))
            if token not in STOPWORDS
        ]
        for idx in range(0, max(0, len(tokens) - n + 1)):
            gram = " ".join(tokens[idx : idx + n])
            if len(gram) >= 45 and not _is_boilerplate_ngram(gram):
                counter[gram] += 1
    return counter


def _is_boilerplate_ngram(gram: str) -> bool:
    boilerplate_fragments = (
        "begin enumerate label",
        "enumerate label roman",
        "label roman leftmargin",
        "leftmargin itemsep",
        "begin itemize",
        "end enumerate",
        "end itemize",
        "begin align",
        "end align",
        "begin equation",
        "end equation",
        "proof",
        "cite",
        "ref thm",
        "theorem ref",
        "proposition ref",
        "corollary ref",
    )
    if any(fragment in gram for fragment in boilerplate_fragments):
        return True
    tokens = gram.split()
    latex_tokens = {
        "begin",
        "end",
        "label",
        "leftmargin",
        "itemsep",
        "roman",
        "alph",
        "arabic",
        "ref",
        "cite",
        "eqref",
    }
    return sum(1 for token in tokens if token in latex_tokens) >= 3


def shared_theorem_phrases(
    a_statements: list[dict[str, str]],
    b_statements: list[dict[str, str]],
    *,
    limit: int = 8,
) -> list[str]:
    a_grams = _ngram_counter(a_statements)
    b_grams = _ngram_counter(b_statements)
    shared = sorted(a_grams.keys() & b_grams.keys(), key=lambda item: (-len(item), item))
    return shared[:limit]


def shared_hard_bundles(shared_markers: set[str]) -> list[str]:
    bundles: list[str] = []
    for name, markers in HARD_MARKER_BUNDLES.items():
        if markers <= shared_markers:
            bundles.append(name)
    return sorted(bundles)


def build_paper_record(
    paper_dir: Path,
    board_entries: dict[str, dict[str, str]],
) -> dict[str, Any]:
    text = paper_text(paper_dir)
    statements = extract_theorem_statements(paper_dir)
    entry = board_entries.get(paper_dir.name)
    row_text = board_row_text(entry)
    submission_date = paper_submission_date(paper_dir, entry)
    theorem_text = "\n".join(stmt.get("raw", "") for stmt in statements)
    marker_text = "\n".join([text, theorem_text])
    tokens = claim_tokens("\n".join([extract_abstract(text), theorem_text]))
    return {
        "dir": paper_dir.name,
        "path": str(paper_dir),
        "title": _first_latex_argument(text, "title"),
        "journal": entry.get("journal", "") if entry else "",
        "status": entry.get("status", "") if entry else "",
        "reroute": entry.get("reroute", "") if entry else "",
        "board_row": row_text,
        "board_overlap_resolved": board_overlap_resolved(row_text),
        "has_submission_marker_file": has_submission_marker_file(paper_dir),
        "has_prior_submission": paper_has_prior_submission(paper_dir.name, entry, paper_dir),
        "submission_date": submission_date,
        "requires_resolution": paper_requires_resolution(paper_dir.name, entry),
        "abstract": extract_abstract(text),
        "keywords": extract_keywords(text),
        "msc": extract_msc(text),
        "theorem_count": len(statements),
        "theorems": [
            {key: stmt[key] for key in ("environment", "label", "file", "snippet")}
            for stmt in statements
        ],
        "claim_markers": sorted(claim_markers_for_text(marker_text)),
        "_source_fingerprint": source_fingerprint(text),
        "_statements_raw": statements,
        "_claim_tokens": sorted(tokens),
    }


def discover_paper_dirs(publication_dir: Path = DEFAULT_PUBLICATION_DIR) -> list[Path]:
    if not publication_dir.exists():
        return []
    dirs: list[Path] = []
    for child in publication_dir.iterdir():
        if not child.is_dir():
            continue
        if not child.name.startswith(PAPER_DIR_PREFIXES):
            continue
        if not (child / "main.tex").exists():
            continue
        dirs.append(child)
    return sorted(dirs, key=lambda path: path.name)


def _jaccard(a: set[str], b: set[str]) -> float:
    if not a or not b:
        return 0.0
    union = a | b
    if not union:
        return 0.0
    return len(a & b) / len(union)


def prior_submission_pair(
    paper_a: dict[str, Any],
    paper_b: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]] | None:
    """Return (primary prior submission, deferred later draft) when deterministic."""
    a_prior = bool(paper_a.get("has_prior_submission"))
    b_prior = bool(paper_b.get("has_prior_submission"))
    if a_prior and b_prior:
        date_a = str(paper_a.get("submission_date") or "")
        date_b = str(paper_b.get("submission_date") or "")
        if date_a and date_b and date_a != date_b:
            if date_a < date_b:
                return paper_a, paper_b
            return paper_b, paper_a
        return None
    if a_prior == b_prior:
        return None
    if a_prior:
        return paper_a, paper_b
    return paper_b, paper_a


def overlap_action_fields(
    classification: str,
    paper_a: dict[str, Any],
    paper_b: dict[str, Any],
) -> dict[str, str]:
    if classification == DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION:
        pair = prior_submission_pair(paper_a, paper_b)
        if pair:
            primary, deferred = pair
            return {
                "primary_paper": primary["dir"],
                "deferred_paper": deferred["dir"],
                "recommended_action": "defer_later_draft_until_prior_submission_feedback",
                "reason": (
                    "submission chronology wins: the later overlapping draft "
                    "must wait until the prior submitted/current route receives "
                    "editorial feedback or the board explicitly closes it"
                ),
            }
    if classification == "resolved":
        return {
            "primary_paper": "",
            "deferred_paper": "",
            "recommended_action": "continue_after_board_resolution",
            "reason": "the board explicitly resolves the overlapping route",
        }
    if classification == "needs_human_resolution":
        return {
            "primary_paper": "",
            "deferred_paper": "",
            "recommended_action": "record_board_resolution_before_advancing",
            "reason": "active drafts overlap without a deterministic chronology winner",
        }
    if classification == "blocker":
        return {
            "primary_paper": "",
            "deferred_paper": "",
            "recommended_action": "resolve_overlap_before_advancing",
            "reason": "substantive overlap is unresolved",
        }
    return {
        "primary_paper": "",
        "deferred_paper": "",
        "recommended_action": "no_action_required",
        "reason": "weak or background overlap only",
    }


def finding_blocks_current_paper(finding: dict[str, Any], current_name: str | None) -> bool:
    classification = finding.get("classification")
    if classification not in FAILING_CLASSIFICATIONS:
        return False
    if not current_name:
        return True
    if classification == DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION:
        return finding.get("deferred_paper") == current_name
    return finding.get("paper_a") == current_name or finding.get("paper_b") == current_name


def compare_paper_records(
    paper_a: dict[str, Any],
    paper_b: dict[str, Any],
    *,
    min_shared_markers: int = 4,
    min_shared_phrases: int = 3,
) -> dict[str, Any] | None:
    markers_a = set(paper_a.get("claim_markers", []))
    markers_b = set(paper_b.get("claim_markers", []))
    shared_markers = sorted(markers_a & markers_b)
    shared_major = sorted(set(shared_markers) & MAJOR_CLAIM_MARKERS)
    hard_bundles = shared_hard_bundles(set(shared_markers))
    substantive_shared_markers = sorted(set(shared_markers) - SOFT_MARKERS)
    phrases = shared_theorem_phrases(
        paper_a.get("_statements_raw", []),
        paper_b.get("_statements_raw", []),
    )
    tokens_a = set(paper_a.get("_claim_tokens", []))
    tokens_b = set(paper_b.get("_claim_tokens", []))
    shared_tokens = sorted(tokens_a & tokens_b)
    token_jaccard = _jaccard(tokens_a, tokens_b)
    exact_source_duplicate = (
        bool(paper_a.get("_source_fingerprint"))
        and paper_a.get("_source_fingerprint") == paper_b.get("_source_fingerprint")
    )

    marker_strong = bool(hard_bundles) or (
        len(substantive_shared_markers) >= max(min_shared_markers + 1, 5)
        and len(shared_major) >= 3
        and token_jaccard >= 0.18
    )
    phrase_strong = len(phrases) >= min_shared_phrases
    token_strong = token_jaccard >= 0.34 and len(shared_tokens) >= 25
    weak_overlap = len(shared_markers) >= 2 or len(phrases) > 0 or (
        token_jaccard >= 0.24 and len(shared_tokens) >= 18
    )

    if not (exact_source_duplicate or marker_strong or phrase_strong or token_strong or weak_overlap):
        return None

    if paper_a.get("board_overlap_resolved") or paper_b.get("board_overlap_resolved"):
        classification = "resolved"
    elif exact_source_duplicate or marker_strong or phrase_strong or token_strong:
        if prior_submission_pair(paper_a, paper_b):
            classification = DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION
        elif paper_a.get("requires_resolution") or paper_b.get("requires_resolution"):
            classification = "blocker"
        else:
            classification = "needs_human_resolution"
    else:
        classification = "informational"

    action = overlap_action_fields(classification, paper_a, paper_b)

    return {
        "classification": classification,
        "paper_a": paper_a["dir"],
        "paper_b": paper_b["dir"],
        "title_a": paper_a.get("title", ""),
        "title_b": paper_b.get("title", ""),
        "status_a": paper_a.get("status", ""),
        "status_b": paper_b.get("status", ""),
        "journal_a": paper_a.get("journal", ""),
        "journal_b": paper_b.get("journal", ""),
        "submission_date_a": paper_a.get("submission_date", ""),
        "submission_date_b": paper_b.get("submission_date", ""),
        "board_a": paper_a.get("board_row", ""),
        "board_b": paper_b.get("board_row", ""),
        "requires_resolution_a": bool(paper_a.get("requires_resolution")),
        "requires_resolution_b": bool(paper_b.get("requires_resolution")),
        "has_prior_submission_a": bool(paper_a.get("has_prior_submission")),
        "has_prior_submission_b": bool(paper_b.get("has_prior_submission")),
        "has_submission_marker_file_a": bool(paper_a.get("has_submission_marker_file")),
        "has_submission_marker_file_b": bool(paper_b.get("has_submission_marker_file")),
        "resolved_a": bool(paper_a.get("board_overlap_resolved")),
        "resolved_b": bool(paper_b.get("board_overlap_resolved")),
        **action,
        "shared_claim_markers": shared_markers,
        "shared_major_markers": shared_major,
        "shared_hard_bundles": hard_bundles,
        "shared_theorem_phrases": phrases[:5],
        "shared_claim_tokens": shared_tokens[:40],
        "claim_token_jaccard": round(token_jaccard, 4),
        "evidence": {
            "exact_source_duplicate": exact_source_duplicate,
            "marker_strong": marker_strong,
            "phrase_strong": phrase_strong,
            "token_strong": token_strong,
            "weak_overlap": weak_overlap,
        },
    }


def _public_paper_record(record: dict[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in record.items()
        if not key.startswith("_")
    }


def build_overlap_report(
    *,
    publication_dir: Path = DEFAULT_PUBLICATION_DIR,
    board_path: Path = DEFAULT_BOARD_PATH,
    current_paper: Path | None = None,
    min_shared_markers: int = 4,
    min_shared_phrases: int = 3,
) -> dict[str, Any]:
    publication_dir = publication_dir.resolve()
    board_path = board_path.resolve()
    board_entries = parse_board_entries(board_path)
    paper_dirs = discover_paper_dirs(publication_dir)

    if current_paper is not None:
        current_paper = current_paper.resolve()
        if not (current_paper / "main.tex").exists():
            raise FileNotFoundError(f"current paper has no main.tex: {current_paper}")
        if not any(path.resolve() == current_paper for path in paper_dirs):
            paper_dirs.append(current_paper)
            paper_dirs = sorted(set(paper_dirs), key=lambda path: path.name)

    records = [build_paper_record(path, board_entries) for path in paper_dirs]
    by_dir = {record["dir"]: record for record in records}

    if current_paper is None:
        pairs = itertools.combinations(records, 2)
    else:
        current_record = by_dir.get(current_paper.name)
        if current_record is None:
            current_record = build_paper_record(current_paper, board_entries)
        pairs = ((current_record, record) for record in records if record["dir"] != current_record["dir"])

    findings: list[dict[str, Any]] = []
    for paper_a, paper_b in pairs:
        finding = compare_paper_records(
            paper_a,
            paper_b,
            min_shared_markers=min_shared_markers,
            min_shared_phrases=min_shared_phrases,
        )
        if finding:
            findings.append(finding)

    severity_order = {
        "blocker": 0,
        DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION: 1,
        "needs_human_resolution": 2,
        "resolved": 3,
        "informational": 4,
    }
    findings.sort(
        key=lambda item: (
            severity_order.get(item["classification"], 99),
            item["paper_a"],
            item["paper_b"],
        )
    )

    summary = {
        "blocker": 0,
        DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION: 0,
        "needs_human_resolution": 0,
        "resolved": 0,
        "informational": 0,
    }
    for finding in findings:
        summary[finding["classification"]] = summary.get(finding["classification"], 0) + 1

    current_name = current_paper.name if current_paper else None
    gate_failed = any(finding_blocks_current_paper(finding, current_name) for finding in findings)
    return {
        "schema_version": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "publication_dir": str(publication_dir),
        "board_path": str(board_path),
        "current_paper": current_paper.name if current_paper else "",
        "thresholds": {
            "min_shared_markers": min_shared_markers,
            "min_shared_phrases": min_shared_phrases,
            "failing_classifications": sorted(FAILING_CLASSIFICATIONS),
        },
        "gate_failed": gate_failed,
        "summary": summary,
        "papers": [_public_paper_record(record) for record in records],
        "findings": findings,
    }


def _md_cell(value: Any) -> str:
    text = str(value or "")
    text = text.replace("\n", " ")
    text = text.replace("|", "\\|")
    if len(text) > 220:
        text = text[:217].rstrip() + "..."
    return text


def render_markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# Split Overlap Report",
        "",
        f"- Generated: `{report.get('generated_at', '')}`",
        f"- Publication dir: `{report.get('publication_dir', '')}`",
        f"- Current paper: `{report.get('current_paper') or 'ALL'}`",
        f"- Gate failed: `{str(bool(report.get('gate_failed'))).lower()}`",
        "",
        "## Summary",
        "",
        "| classification | count |",
        "|---|---:|",
    ]
    for key in (
        "blocker",
        DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION,
        "needs_human_resolution",
        "resolved",
        "informational",
    ):
        lines.append(f"| `{key}` | {int(report.get('summary', {}).get(key, 0) or 0)} |")
    lines.extend(["", "## Findings", ""])
    findings = report.get("findings", [])
    if not findings:
        lines.append("No deterministic split-overlap findings.")
    else:
        lines.extend(
            [
                "| class | paper A | paper B | action | primary | deferred | shared markers | token Jaccard | board A | board B |",
                "|---|---|---|---|---|---|---|---:|---|---|",
            ]
        )
        for finding in findings:
            markers = ", ".join(finding.get("shared_claim_markers", []))
            lines.append(
                "| {classification} | `{paper_a}` | `{paper_b}` | {action} | `{primary}` | `{deferred}` | {markers} | {jaccard:.4f} | {board_a} | {board_b} |".format(
                    classification=_md_cell(finding.get("classification")),
                    paper_a=_md_cell(finding.get("paper_a")),
                    paper_b=_md_cell(finding.get("paper_b")),
                    action=_md_cell(finding.get("recommended_action")),
                    primary=_md_cell(finding.get("primary_paper")),
                    deferred=_md_cell(finding.get("deferred_paper")),
                    markers=_md_cell(markers),
                    jaccard=float(finding.get("claim_token_jaccard", 0.0) or 0.0),
                    board_a=_md_cell(finding.get("board_a")),
                    board_b=_md_cell(finding.get("board_b")),
                )
            )
    lines.extend(["", "## Policy", ""])
    lines.append(
        "A split is publishable only when its theorem package is distinct, or when "
        "the board explicitly records that the overlapping route is closed, merged, "
        "superseded, or parked. When an earlier overlapping paper has already been "
        "submitted or is under review, submission chronology wins: the later draft "
        "is deferred until the prior route receives feedback. Renaming, journal "
        "reframing, or prose rewriting is not enough to pass this gate."
    )
    lines.append("")
    return "\n".join(lines)


def write_report(report: dict[str, Any], report_dir: Path = DEFAULT_REPORT_DIR) -> tuple[Path, Path]:
    report_dir.mkdir(parents=True, exist_ok=True)
    json_path = report_dir / "split_overlap_report.json"
    md_path = report_dir / "split_overlap_report.md"
    json_path.write_text(json.dumps(report, indent=2, ensure_ascii=False), encoding="utf-8")
    md_path.write_text(render_markdown_report(report), encoding="utf-8")
    return json_path, md_path


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Deterministic publication split-overlap gate")
    parser.add_argument("--publication-dir", type=Path, default=DEFAULT_PUBLICATION_DIR)
    parser.add_argument("--board", type=Path, default=DEFAULT_BOARD_PATH)
    parser.add_argument("--current-paper", type=Path)
    parser.add_argument("--report-dir", type=Path, default=DEFAULT_REPORT_DIR)
    parser.add_argument("--min-shared-markers", type=int, default=4)
    parser.add_argument("--min-shared-phrases", type=int, default=3)
    parser.add_argument(
        "--report-only",
        action="store_true",
        help="Always exit zero after writing reports, even if the gate fails.",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    report = build_overlap_report(
        publication_dir=args.publication_dir,
        board_path=args.board,
        current_paper=args.current_paper,
        min_shared_markers=args.min_shared_markers,
        min_shared_phrases=args.min_shared_phrases,
    )
    json_path, md_path = write_report(report, args.report_dir)
    summary = report.get("summary", {})
    print(
        "split-overlap gate: "
        f"gate_failed={report['gate_failed']} "
        f"blocker={summary.get('blocker', 0)} "
        f"deferred_wait_for_prior_submission={summary.get(DEFERRED_PRIOR_SUBMISSION_CLASSIFICATION, 0)} "
        f"needs_human_resolution={summary.get('needs_human_resolution', 0)} "
        f"resolved={summary.get('resolved', 0)} "
        f"informational={summary.get('informational', 0)} "
        f"json={json_path} md={md_path}"
    )
    if args.report_only:
        return 0
    return 1 if report["gate_failed"] else 0


if __name__ == "__main__":
    sys.exit(main())
