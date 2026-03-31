#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Automated quality gate checker for publication papers.

Usage:
    python3 pub_check.py <paper_dir> [--stage P0|P1|...|P7] [--json]
    python3 pub_check.py <paper_dir> --cite --xref --size --style --proof
    python3 pub_check.py <paper_dir> --all

Exit code 0 = all checks pass, 1 = at least one failure.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional


# ---------- Regexes ----------

CITE_RE = re.compile(r"\\cite[a-zA-Z*]*\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\(?:ref|cref|Cref|eqref|autoref)\{([^}]+)\}")
BIB_KEY_RE = re.compile(r"@\w+\{([^,\s]+)")
CLAIM_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|conjecture)\}"
    r"(?:\[([^\]]*)\])?"
)
CLAIM_LABEL_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|conjecture)\}"
    r".*?\\label\{([^}]+)\}",
    re.DOTALL,
)
ABSTRACT_RE = re.compile(
    r"\\begin\{abstract\}(.*?)\\end\{abstract\}", re.DOTALL
)
MSC_RE = re.compile(r"\\subjclass|\\keywords|MSC\s*2020")
REVISION_TRACE_WORDS = [
    r"\bnew\b.*\b(?:version|revision)\b",
    r"\brevised\b",
    r"\bpreviously\b",
    r"\bupdated\b",
    r"\bin this version\b",
    r"\bwe now\b",
    r"\bnow we\b",
    r"\bfixed\b.*\b(?:bug|error|typo)\b",
]
AI_VOICE_WORDS = [
    r"\bremarkably\b",
    r"\bsurprisingly\b",
    r"\belegant(?:ly)?\b",
    r"\bbeautiful(?:ly)?\b",
    r"\bcrucially\b",
    r"\bfascinating(?:ly)?\b",
    r"\bstriking(?:ly)?\b",
]
PROOF_INCOMPLETE_PATTERNS = [
    r"\bproof\s+omitted\b",
    r"\bleft\s+to\s+(?:the\s+)?reader\b",
    r"\bTODO\b",
    r"\bFIXME\b",
    r"\bXXX\b",
    r"\bplaceholder\b",
]
COMMENT_RE = re.compile(r"(?<!\\)%.*$", re.MULTILINE)


# ---------- Data structures ----------

@dataclass
class CheckResult:
    name: str
    passed: bool
    details: list[str] = field(default_factory=list)


@dataclass
class Report:
    paper_dir: str
    checks: list[CheckResult] = field(default_factory=list)
    all_passed: bool = True

    def add(self, result: CheckResult):
        self.checks.append(result)
        if not result.passed:
            self.all_passed = False


# ---------- Helpers ----------

def get_tex_files(paper_dir: Path) -> list[Path]:
    return sorted(paper_dir.glob("*.tex"))


def read_tex_content(path: Path, strip_comments: bool = True) -> str:
    text = path.read_text(encoding="utf-8", errors="replace")
    if strip_comments:
        text = COMMENT_RE.sub("", text)
    return text


def get_bib_file(paper_dir: Path) -> Optional[Path]:
    bibs = list(paper_dir.glob("*.bib"))
    return bibs[0] if bibs else None


def word_count(text: str) -> int:
    # Strip LaTeX commands for rough word count
    cleaned = re.sub(r"\\[a-zA-Z]+\{[^}]*\}", " ", text)
    cleaned = re.sub(r"\\[a-zA-Z]+", " ", cleaned)
    cleaned = re.sub(r"\$[^$]+\$", " MATH ", cleaned)
    cleaned = re.sub(r"[{}\\~]", " ", cleaned)
    return len(cleaned.split())


# ---------- Check implementations ----------

def check_citations(paper_dir: Path) -> CheckResult:
    """Verify every \\cite has a bib entry, every bib entry is cited."""
    result = CheckResult(name="citation_completeness", passed=True)

    bib_path = get_bib_file(paper_dir)
    if not bib_path:
        result.passed = False
        result.details.append("No .bib file found")
        return result

    bib_keys = set(BIB_KEY_RE.findall(bib_path.read_text(encoding="utf-8", errors="replace")))
    cited_keys: set[str] = set()
    for tex in get_tex_files(paper_dir):
        content = read_tex_content(tex)
        for match in CITE_RE.findall(content):
            for key in match.split(","):
                cited_keys.add(key.strip())

    uncited = bib_keys - cited_keys
    missing = cited_keys - bib_keys

    if uncited:
        result.passed = False
        result.details.append(f"Uncited bib entries ({len(uncited)}): {', '.join(sorted(uncited))}")
    if missing:
        result.passed = False
        result.details.append(f"Missing bib entries ({len(missing)}): {', '.join(sorted(missing))}")
    if not uncited and not missing:
        result.details.append(f"OK: {len(bib_keys)} bib entries, all cited and present")

    return result


def check_crossrefs(paper_dir: Path) -> CheckResult:
    """Verify every \\ref has a matching \\label."""
    result = CheckResult(name="crossref_integrity", passed=True)

    labels: set[str] = set()
    refs: set[str] = set()

    for tex in get_tex_files(paper_dir):
        content = read_tex_content(tex)
        labels.update(LABEL_RE.findall(content))
        for match in REF_RE.findall(content):
            for ref in match.split(","):
                refs.add(ref.strip())

    undefined = refs - labels
    if undefined:
        result.passed = False
        result.details.append(f"Undefined refs ({len(undefined)}): {', '.join(sorted(undefined))}")
    else:
        result.details.append(f"OK: {len(refs)} refs, {len(labels)} labels, all resolved")

    return result


def check_file_size(paper_dir: Path, max_lines: int = 800) -> CheckResult:
    """Verify all .tex files are under max_lines."""
    result = CheckResult(name="file_size", passed=True)

    for tex in get_tex_files(paper_dir):
        lines = tex.read_text(encoding="utf-8", errors="replace").count("\n") + 1
        if lines > max_lines:
            result.passed = False
            result.details.append(f"OVER: {tex.name} = {lines} lines (max {max_lines})")
        else:
            result.details.append(f"OK: {tex.name} = {lines} lines")

    return result


def check_style(paper_dir: Path) -> CheckResult:
    """Check for revision-trace language and AI-voice markers."""
    result = CheckResult(name="style", passed=True)

    for tex in get_tex_files(paper_dir):
        content = read_tex_content(tex)
        for pattern in REVISION_TRACE_WORDS:
            matches = re.findall(pattern, content, re.IGNORECASE)
            if matches:
                result.passed = False
                for m in matches:
                    result.details.append(f"Revision-trace in {tex.name}: '{m}'")

        for pattern in AI_VOICE_WORDS:
            matches = re.findall(pattern, content, re.IGNORECASE)
            if matches:
                result.passed = False
                for m in matches:
                    result.details.append(f"AI-voice in {tex.name}: '{m}'")

    if result.passed:
        result.details.append("OK: no revision-trace or AI-voice issues")

    return result


def check_proof_completeness(paper_dir: Path) -> CheckResult:
    """Check for incomplete proofs, TODOs, placeholders."""
    result = CheckResult(name="proof_completeness", passed=True)

    for tex in get_tex_files(paper_dir):
        content = read_tex_content(tex, strip_comments=False)
        for pattern in PROOF_INCOMPLETE_PATTERNS:
            matches = re.findall(pattern, content, re.IGNORECASE)
            if matches:
                result.passed = False
                for m in matches:
                    result.details.append(f"Incomplete in {tex.name}: '{m}'")

    if result.passed:
        result.details.append("OK: no incomplete proofs or placeholders")

    return result


def check_abstract(paper_dir: Path, max_words: int = 250) -> CheckResult:
    """Check abstract exists and is under word limit."""
    result = CheckResult(name="abstract", passed=True)

    for tex in get_tex_files(paper_dir):
        content = tex.read_text(encoding="utf-8", errors="replace")
        match = ABSTRACT_RE.search(content)
        if match:
            abstract_text = match.group(1)
            wc = word_count(abstract_text)
            if wc > max_words:
                result.passed = False
                result.details.append(f"Abstract in {tex.name}: {wc} words (max {max_words})")
            else:
                result.details.append(f"OK: abstract in {tex.name} = {wc} words")
            return result

    result.passed = False
    result.details.append("No abstract found in any .tex file")
    return result


def check_msc(paper_dir: Path) -> CheckResult:
    """Check MSC codes are present."""
    result = CheckResult(name="msc_codes", passed=True)

    for tex in get_tex_files(paper_dir):
        content = tex.read_text(encoding="utf-8", errors="replace")
        if MSC_RE.search(content):
            result.details.append(f"OK: MSC codes found in {tex.name}")
            return result

    result.passed = False
    result.details.append("No MSC codes found")
    return result


def check_pipeline_md(paper_dir: Path) -> CheckResult:
    """Check PIPELINE.md exists and has required sections."""
    result = CheckResult(name="pipeline_md", passed=True)

    pipeline = paper_dir / "PIPELINE.md"
    if not pipeline.exists():
        result.passed = False
        result.details.append("PIPELINE.md not found")
        return result

    content = pipeline.read_text(encoding="utf-8", errors="replace")
    required_sections = ["Stage Progress", "Theorem Inventory", "Source Map"]
    for section in required_sections:
        if section not in content:
            result.passed = False
            result.details.append(f"Missing section in PIPELINE.md: '{section}'")

    if result.passed:
        result.details.append("OK: PIPELINE.md has all required sections")

    return result


def check_claim_labels(paper_dir: Path) -> CheckResult:
    """Check every theorem environment has a \\label."""
    result = CheckResult(name="claim_labels", passed=True)

    for tex in get_tex_files(paper_dir):
        content = read_tex_content(tex)
        # Find all claim environments
        envs = list(CLAIM_ENV_RE.finditer(content))
        labeled = set()
        for match in CLAIM_LABEL_RE.finditer(content):
            labeled.add(match.start())

        unlabeled_count = 0
        for env_match in envs:
            # Check if there's a label within 500 chars after the begin
            start = env_match.start()
            snippet = content[start:start + 500]
            if not LABEL_RE.search(snippet):
                unlabeled_count += 1
                line_num = content[:start].count("\n") + 1
                result.details.append(
                    f"Unlabeled {env_match.group(1)} in {tex.name}:{line_num}"
                )

        if unlabeled_count > 0:
            result.passed = False

    if result.passed:
        result.details.append("OK: all theorem environments have labels")

    return result


# ---------- Stage presets ----------

STAGE_CHECKS = {
    "P0": ["file_size", "pipeline_md"],
    "P1": ["file_size", "pipeline_md", "claim_labels"],
    "P2": ["file_size", "pipeline_md", "claim_labels"],
    "P3": ["file_size", "pipeline_md", "claim_labels", "abstract", "msc", "style", "citations"],
    "P4": ["file_size", "pipeline_md", "claim_labels", "abstract", "msc", "style",
           "citations", "crossrefs", "proof_completeness"],
    "P5": ["file_size", "pipeline_md", "claim_labels", "abstract", "msc", "style",
           "citations", "crossrefs", "proof_completeness"],
    "P6": ["file_size", "pipeline_md", "claim_labels", "abstract", "msc", "style",
           "citations", "crossrefs", "proof_completeness"],
    "P7": ["file_size", "pipeline_md", "claim_labels", "abstract", "msc", "style",
           "citations", "crossrefs", "proof_completeness"],
    "all": ["file_size", "pipeline_md", "claim_labels", "abstract", "msc", "style",
            "citations", "crossrefs", "proof_completeness"],
}

CHECK_FUNCTIONS = {
    "citations": check_citations,
    "crossrefs": check_crossrefs,
    "file_size": check_file_size,
    "style": check_style,
    "proof_completeness": check_proof_completeness,
    "abstract": check_abstract,
    "msc": check_msc,
    "pipeline_md": check_pipeline_md,
    "claim_labels": check_claim_labels,
}


# ---------- Main ----------

def run_checks(paper_dir: Path, check_names: list[str]) -> Report:
    report = Report(paper_dir=str(paper_dir))
    for name in check_names:
        fn = CHECK_FUNCTIONS.get(name)
        if fn:
            result = fn(paper_dir)
            report.add(result)
    return report


def print_report(report: Report, as_json: bool = False):
    if as_json:
        data = {
            "paper_dir": report.paper_dir,
            "all_passed": report.all_passed,
            "checks": [asdict(c) for c in report.checks],
        }
        print(json.dumps(data, indent=2))
        return

    status = "PASS" if report.all_passed else "FAIL"
    print(f"\n{'='*60}")
    print(f"  pub_check: {report.paper_dir}")
    print(f"  Result: {status}")
    print(f"{'='*60}\n")

    for check in report.checks:
        icon = "+" if check.passed else "X"
        print(f"  [{icon}] {check.name}")
        for detail in check.details:
            print(f"      {detail}")
        print()


def main():
    parser = argparse.ArgumentParser(description="Publication quality gate checker")
    parser.add_argument("paper_dir", type=Path, help="Path to paper directory")
    parser.add_argument("--stage", choices=STAGE_CHECKS.keys(), default=None,
                        help="Run checks appropriate for this pipeline stage")
    parser.add_argument("--all", action="store_true", help="Run all checks")
    parser.add_argument("--cite", action="store_true", help="Citation completeness")
    parser.add_argument("--xref", action="store_true", help="Cross-reference integrity")
    parser.add_argument("--size", action="store_true", help="File size check")
    parser.add_argument("--style", action="store_true", help="Style check")
    parser.add_argument("--proof", action="store_true", help="Proof completeness")
    parser.add_argument("--abstract-check", action="store_true", help="Abstract word count")
    parser.add_argument("--msc-check", action="store_true", help="MSC codes")
    parser.add_argument("--pipeline", action="store_true", help="PIPELINE.md validation")
    parser.add_argument("--labels", action="store_true", help="Claim labels check")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    if not args.paper_dir.is_dir():
        print(f"Error: {args.paper_dir} is not a directory", file=sys.stderr)
        sys.exit(2)

    # Determine which checks to run
    if args.all or args.stage:
        stage = args.stage or "all"
        check_names = STAGE_CHECKS[stage]
    else:
        check_names = []
        if args.cite: check_names.append("citations")
        if args.xref: check_names.append("crossrefs")
        if args.size: check_names.append("file_size")
        if args.style: check_names.append("style")
        if args.proof: check_names.append("proof_completeness")
        if args.abstract_check: check_names.append("abstract")
        if args.msc_check: check_names.append("msc")
        if args.pipeline: check_names.append("pipeline_md")
        if args.labels: check_names.append("claim_labels")

    if not check_names:
        check_names = STAGE_CHECKS["all"]

    report = run_checks(args.paper_dir, check_names)
    print_report(report, as_json=args.json)
    sys.exit(0 if report.all_passed else 1)


if __name__ == "__main__":
    main()
