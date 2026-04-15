#!/usr/bin/env python3
"""Generate a target manifest for the Omega autoresearch overnight loop.

Wraps omega_ci.py's paper-coverage and inventory to produce a prioritized
JSONL file of un-formalized theorems, ready for run_overnight.py to consume.

Usage:
    python prepare.py                          # default: write manifest.jsonl
    python prepare.py -o targets.jsonl         # custom output path
    python prepare.py --section body           # only body section
    python prepare.py --top 50                 # limit to top 50 targets
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
LEAN_ROOT = REPO_ROOT / "lean4"
OMEGA_CI = LEAN_ROOT / "scripts" / "omega_ci.py"

sys.path.insert(0, str(LEAN_ROOT / "scripts"))
import omega_ci  # noqa: E402


LEANPARTIAL_RE = omega_ci.re.compile(r"\\leanpartial\b")
LEANVERIFIED_RE = omega_ci.re.compile(r"\\leanverified\b")

MODULE_HINT = {
    "pom": "Omega/Folding",
    "fold": "Omega/Folding",
    "fiber": "Omega/Folding",
    "spg": "Omega/SPG",
    "circle": "Omega/CircleDimension",
    "zeta": "Omega/Zeta",
    "gu": "Omega/GU",
    "graph": "Omega/Graph",
    "ea": "Omega/EA",
    "conclusion": "Omega/Conclusion",
    "frontier": "Omega/Frontier",
}


def guess_target_module(label: str) -> str:
    """Map a paper label like 'thm:pom-stable-addition' to a module directory."""
    parts = label.split(":", 1)
    if len(parts) < 2:
        return "Omega/Frontier"
    slug = parts[1].lower()
    for key, module in MODULE_HINT.items():
        if key in slug:
            return module
    return "Omega/Frontier"


def scan_leanpartial_labels(claims: list[omega_ci.PaperClaimRecord]) -> set[str]:
    """Find labels that appear near \\leanpartial in the LaTeX source."""
    partial_labels: set[str] = set()
    seen_files: dict[str, str] = {}
    for claim in claims:
        tex_path = omega_ci.THEORY_ROOT / claim.file
        if not tex_path.exists():
            continue
        fname = str(tex_path)
        if fname not in seen_files:
            seen_files[fname] = omega_ci.read_text_file(tex_path)
        text = seen_files[fname]
        if LEANPARTIAL_RE.search(text):
            partial_labels.add(claim.label)
    return partial_labels


def find_leanverified_neighbors(
    claims: list[omega_ci.PaperClaimRecord],
    matched_labels: set[str],
) -> set[str]:
    """Find missing labels that are in the same file as matched (verified) labels."""
    file_to_claims: dict[str, list[str]] = {}
    for claim in claims:
        file_to_claims.setdefault(claim.file, []).append(claim.label)

    neighbor_labels: set[str] = set()
    for fname, labels in file_to_claims.items():
        has_verified = any(l in matched_labels for l in labels)
        if has_verified:
            for l in labels:
                if l not in matched_labels:
                    neighbor_labels.add(l)
    return neighbor_labels


def extract_claim_body(claim: omega_ci.PaperClaimRecord) -> str:
    """Extract the LaTeX body of a claim environment."""
    tex_path = omega_ci.THEORY_ROOT / claim.file
    if not tex_path.exists():
        return ""
    text = omega_ci.read_text_file(tex_path)
    lines = text.split("\n")
    start_line = claim.line - 1
    env = claim.environment
    begin_marker = f"\\begin{{{env}}}"
    end_marker = f"\\end{{{env}}}"

    body_lines = []
    depth = 0
    collecting = False
    for i in range(start_line, len(lines)):
        line = lines[i]
        if begin_marker in line:
            depth += 1
            collecting = True
        if collecting:
            body_lines.append(line)
        if end_marker in line:
            depth -= 1
            if depth <= 0:
                break
    return "\n".join(body_lines)


def generate_manifest(
    section: str = "body",
    top: int | None = None,
) -> list[dict]:
    """Generate a prioritized list of un-formalized theorem targets."""
    declarations, _ = omega_ci.build_inventory()
    claims, unlabeled = omega_ci.collect_paper_claims(section)
    coverage = omega_ci.coverage_payload(
        declarations, claims, unlabeled, section=section,
    )

    missing_labels = set(coverage["missing_in_lean"])
    if not missing_labels:
        return []

    matched_labels = set(coverage["matched_registry_labels"])
    claim_by_label = {c.label: c for c in claims}

    partial_labels = scan_leanpartial_labels(claims)
    neighbor_labels = find_leanverified_neighbors(claims, matched_labels)

    targets = []
    for label in sorted(missing_labels):
        claim = claim_by_label.get(label)
        if claim is None:
            continue

        if label in partial_labels:
            priority = 1
        elif label in neighbor_labels:
            priority = 2
        else:
            priority = 3

        target_module = guess_target_module(label)
        body = extract_claim_body(claim)

        targets.append({
            "label": label,
            "environment": claim.environment,
            "tex_file": claim.file,
            "tex_line": claim.line,
            "body": body,
            "target_module": target_module,
            "priority": priority,
        })

    targets.sort(key=lambda t: (t["priority"], t["label"]))
    if top is not None:
        targets = targets[:top]
    return targets


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate target manifest for Omega autoresearch",
    )
    parser.add_argument(
        "-o", "--output",
        default=str(SCRIPT_DIR / "manifest.jsonl"),
        help="Output JSONL file path (default: manifest.jsonl)",
    )
    parser.add_argument(
        "--section",
        default="body",
        choices=["body", "appendix", "all"],
        help="Which paper section to scan (default: body)",
    )
    parser.add_argument(
        "--top",
        type=int,
        default=None,
        help="Limit to top N targets by priority",
    )
    parser.add_argument(
        "--stats",
        action="store_true",
        help="Print summary statistics",
    )
    args = parser.parse_args()

    targets = generate_manifest(section=args.section, top=args.top)

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w") as f:
        for target in targets:
            f.write(json.dumps(target, ensure_ascii=False) + "\n")

    if args.stats or True:
        p1 = sum(1 for t in targets if t["priority"] == 1)
        p2 = sum(1 for t in targets if t["priority"] == 2)
        p3 = sum(1 for t in targets if t["priority"] == 3)
        print(f"[prepare] Generated {len(targets)} targets:")
        print(f"  Priority 1 (leanpartial):         {p1}")
        print(f"  Priority 2 (verified neighbors):  {p2}")
        print(f"  Priority 3 (other missing):        {p3}")
        print(f"  Output: {output_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
