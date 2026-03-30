#!/usr/bin/env python3
"""Lean automation helpers for the Omega formalization.

Subcommands:
  - audit: scan Lean sources for forbidden constructs and malformed label blocks
  - inventory: build a lightweight declaration / paper-label inventory
  - verify-files: run ``lake env lean`` on one or more Lean files
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent
OMEGA_ROOT = LEAN_ROOT / "Omega"
REPO_ROOT = LEAN_ROOT.parent
THEORY_ROOT = (
    LEAN_ROOT.parent
    / "theory"
    / "2026_golden_ratio_driven_scan_projection_generation_recursive_emergence"
)
THEORY_SECTION_ROOTS = {
    "body": THEORY_ROOT / "sections" / "body",
    "appendix": THEORY_ROOT / "sections" / "appendix",
}

PAPER_LABEL_PREFIXES = ("thm", "prop", "cor", "lem", "def", "con", "bridge")
REGISTRY_LABEL_PREFIXES = PAPER_LABEL_PREFIXES + ("cond", "cert", "aux", "infra")
PAPER_LABEL_RE = re.compile(
    r"\b(?:"
    + "|".join(PAPER_LABEL_PREFIXES)
    + r"):[A-Za-z0-9_.-]+\b"
)
REGISTRY_LABEL_RE = re.compile(
    r"\b(?:"
    + "|".join(REGISTRY_LABEL_PREFIXES)
    + r"):[A-Za-z0-9_.-]+\b"
)
DECL_RE = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|scoped|mutual)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\s+"
    r"(?P<name>«[^»]+»|[A-Za-z0-9_'.]+)?"
)

FORBIDDEN_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"\baxiom\b"),
}
SEARCH_TOKEN_RE = re.compile(r"[A-Za-z0-9_.+-]{2,}")
CLAIM_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
CLAIM_ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|conjecture)\}"
    r"(?:\[[^\]]*\])?",
    re.DOTALL,
)
CLAIM_ENV_TO_PREFIX = {
    "theorem": "thm",
    "lemma": "lem",
    "proposition": "prop",
    "corollary": "cor",
    "definition": "def",
    "conjecture": "con",
}
SEARCH_STOPWORDS = {
    "the",
    "and",
    "for",
    "with",
    "from",
    "into",
    "that",
    "this",
    "these",
    "those",
    "over",
    "under",
    "then",
    "than",
    "true",
    "false",
    "type",
    "prop",
    "theorem",
    "lemma",
    "definition",
    "proposition",
    "corollary",
    "conjecture",
}


@dataclass(frozen=True)
class DeclarationRecord:
    module: str
    file: str
    line: int
    kind: str
    name: str
    registry_labels: tuple[str, ...]
    paper_labels: tuple[str, ...]


@dataclass(frozen=True)
class LabelBlock:
    start_line: int
    end_line: int
    registry_labels: tuple[str, ...]


@dataclass(frozen=True)
class PaperClaimRecord:
    file: str
    line: int
    environment: str
    label: str


@dataclass(frozen=True)
class SearchIndex:
    declarations: tuple[DeclarationRecord, ...]
    doc_tokens: tuple[tuple[str, ...], ...]
    idf: dict[str, float]


def lean_files() -> list[Path]:
    return sorted(OMEGA_ROOT.rglob("*.lean"))


def _io_string(path: Path) -> str:
    resolved = str(path.resolve())
    if os.name != "nt":
        return resolved
    if resolved.startswith("\\\\?\\"):
        return resolved
    if resolved.startswith("\\\\"):
        return "\\\\?\\UNC\\" + resolved.lstrip("\\")
    return "\\\\?\\" + resolved


def read_text_file(path: Path, *, encoding: str = "utf-8") -> str:
    with open(_io_string(path), "r", encoding=encoding) as handle:
        return handle.read()


def write_text_file(path: Path, text: str, *, encoding: str = "utf-8") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(_io_string(path), "w", encoding=encoding, newline="") as handle:
        handle.write(text)


def module_name(path: Path) -> str:
    rel = path.relative_to(LEAN_ROOT).with_suffix("")
    return ".".join(rel.parts)


def display_path(path: Path, *, root_hint: Path | None = None) -> str:
    for base in (root_hint, THEORY_ROOT, REPO_ROOT):
        if base is None:
            continue
        try:
            return str(path.relative_to(base))
        except ValueError:
            continue
    return str(path)


def strip_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    n = len(text)
    while i < n:
        if block_depth > 0:
            if text.startswith("/-", i):
                block_depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                ch = text[i]
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            ch = text[i]
            if ch == "\\" and i + 1 < n:
                out.extend("  ")
                i += 2
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue

        if text.startswith("/-", i):
            block_depth = 1
            out.extend("  ")
            i += 2
            continue

        if text[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(text[i])
        i += 1

    return "".join(out)


def line_col(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    last_nl = text.rfind("\n", 0, offset)
    col = offset + 1 if last_nl < 0 else offset - last_nl
    return line, col


def collect_forbidden_tokens(path: Path) -> list[dict[str, object]]:
    text = read_text_file(path, encoding="utf-8")
    stripped = strip_comments_and_strings(text)
    violations: list[dict[str, object]] = []
    for token, pattern in FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(stripped):
            line, col = line_col(stripped, match.start())
            violations.append(
                {
                    "file": str(path.relative_to(LEAN_ROOT)),
                    "line": line,
                    "column": col,
                    "token": token,
                }
            )
    return violations


def find_label_blocks(lines: list[str]) -> list[LabelBlock]:
    blocks: list[LabelBlock] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if "/--" not in line:
            i += 1
            continue

        start = i + 1
        block_lines = [line]
        while "-/" not in lines[i]:
            i += 1
            if i >= len(lines):
                break
            block_lines.append(lines[i])
        end = min(i + 1, len(lines))
        labels = tuple(dict.fromkeys(REGISTRY_LABEL_RE.findall("\n".join(block_lines))))
        if labels:
            blocks.append(LabelBlock(start_line=start, end_line=end, registry_labels=labels))
        i += 1
    return blocks


def declaration_at_or_after(lines: list[str], start_idx: int) -> tuple[int, re.Match[str]] | None:
    i = start_idx
    while i < len(lines):
        line = lines[i]
        if line.strip().startswith("/-"):
            while i < len(lines) and "-/" not in lines[i]:
                i += 1
            i += 1
            continue
        if not line.strip() or line.lstrip().startswith("--"):
            i += 1
            continue
        window = "\n".join(lines[i : min(i + 4, len(lines))])
        match = DECL_RE.match(window)
        if match:
            return i + 1, match
        i += 1
    return None


def collect_declarations(path: Path) -> tuple[list[DeclarationRecord], list[dict[str, object]]]:
    text = read_text_file(path, encoding="utf-8")
    lines = text.splitlines()
    labels_by_line: dict[int, tuple[str, ...]] = {}
    orphans: list[dict[str, object]] = []
    for block in find_label_blocks(lines):
        decl_info = declaration_at_or_after(lines, block.end_line)
        if decl_info is None:
            orphans.append(
                {
                    "file": str(path.relative_to(LEAN_ROOT)),
                    "line": block.start_line,
                    "labels": list(block.registry_labels),
                    "reason": "label block not followed by a declaration",
                }
            )
            continue
        decl_line, _ = decl_info
        labels_by_line[decl_line] = block.registry_labels

    stripped_lines = strip_comments_and_strings(text).splitlines()
    declarations: list[DeclarationRecord] = []
    for idx, line in enumerate(stripped_lines, start=1):
        match = DECL_RE.match(line)
        if not match:
            continue
        kind = match.group("kind")
        name = (match.group("name") or f"<anonymous_{kind}_{idx}>").strip()
        declarations.append(
            DeclarationRecord(
                module=module_name(path),
                file=str(path.relative_to(LEAN_ROOT)),
                line=idx,
                kind=kind,
                name=name,
                registry_labels=labels_by_line.get(idx, ()),
                paper_labels=tuple(
                    label for label in labels_by_line.get(idx, ())
                    if PAPER_LABEL_RE.fullmatch(label)
                ),
            )
        )
    return declarations, orphans


def build_inventory() -> tuple[list[DeclarationRecord], list[dict[str, object]]]:
    declarations: list[DeclarationRecord] = []
    orphans: list[dict[str, object]] = []
    for path in lean_files():
        file_decls, file_orphans = collect_declarations(path)
        declarations.extend(file_decls)
        orphans.extend(file_orphans)
    return declarations, orphans


def tokenize_search_text(text: str) -> list[str]:
    return [
        token.lower()
        for token in SEARCH_TOKEN_RE.findall(text)
        if token.lower() not in SEARCH_STOPWORDS
    ]


def declaration_search_text(decl: DeclarationRecord) -> str:
    return " ".join(
        [
            decl.name,
            decl.kind,
            decl.module,
            decl.file,
            " ".join(decl.registry_labels),
            " ".join(decl.paper_labels),
        ]
    )


def build_search_index(declarations: Iterable[DeclarationRecord]) -> SearchIndex:
    decls = tuple(declarations)
    doc_tokens = tuple(
        tuple(tokenize_search_text(declaration_search_text(decl)))
        for decl in decls
    )
    doc_freq = Counter(token for tokens in doc_tokens for token in set(tokens))
    num_docs = max(len(doc_tokens), 1)
    idf = {
        token: math.log((1.0 + num_docs) / (1.0 + freq)) + 1.0
        for token, freq in doc_freq.items()
    }
    return SearchIndex(
        declarations=decls,
        doc_tokens=doc_tokens,
        idf=idf,
    )


def search_declarations(
    declarations: Iterable[DeclarationRecord], query: str, top_k: int, *, search_index: SearchIndex | None = None
) -> list[dict[str, object]]:
    index = search_index or build_search_index(declarations)
    decls = list(index.declarations)
    query_tokens = tokenize_search_text(query)
    if not query_tokens:
        raise ValueError("query produced no searchable tokens")

    doc_tokens = list(index.doc_tokens)
    idf = index.idf

    query_counts = Counter(query_tokens)
    query_vec = {
        token: (count / len(query_tokens)) * idf.get(token, 0.0)
        for token, count in query_counts.items()
    }
    query_norm = math.sqrt(sum(weight * weight for weight in query_vec.values()))
    query_lower = query.lower().strip()

    scored: list[dict[str, object]] = []
    for decl, tokens in zip(decls, doc_tokens):
        if not tokens:
            continue
        token_counts = Counter(tokens)
        doc_vec = {
            token: (count / len(tokens)) * idf.get(token, 0.0)
            for token, count in token_counts.items()
        }
        dot = sum(query_vec.get(token, 0.0) * weight for token, weight in doc_vec.items())
        doc_norm = math.sqrt(sum(weight * weight for weight in doc_vec.values()))
        score = dot / (query_norm * doc_norm) if query_norm > 0 and doc_norm > 0 else 0.0

        exact_labels = {label.lower() for label in decl.registry_labels}
        if query_lower == decl.name.lower():
            score += 5.0
        if query_lower in exact_labels:
            score += 4.0
        if query_lower and query_lower in decl.name.lower():
            score += 1.5
        if query_lower and any(query_lower in label for label in exact_labels):
            score += 1.0
        if query_lower and query_lower in decl.module.lower():
            score += 0.5

        if score <= 0.0:
            continue

        scored.append(
            {
                "score": score,
                "module": decl.module,
                "file": decl.file,
                "line": decl.line,
                "kind": decl.kind,
                "name": decl.name,
                "registry_labels": list(decl.registry_labels),
                "paper_labels": list(decl.paper_labels),
            }
        )

    scored.sort(key=lambda item: (-float(item["score"]), str(item["name"])))
    return scored[:top_k]


def theory_files(section: str, tex_root: Path | None = None) -> list[Path]:
    if tex_root is not None:
        if not tex_root.exists():
            return []
        return sorted(tex_root.rglob("*.tex"))
    if section == "all":
        roots = THEORY_SECTION_ROOTS.values()
    else:
        roots = (THEORY_SECTION_ROOTS[section],)
    out: list[Path] = []
    for root in roots:
        if root.exists():
            out.extend(sorted(root.rglob("*.tex")))
    return sorted(out)


def collect_paper_claims(
    section: str,
    tex_root: Path | None = None,
) -> tuple[list[PaperClaimRecord], list[dict[str, object]]]:
    claims: list[PaperClaimRecord] = []
    unlabeled: list[dict[str, object]] = []
    scan_files = theory_files(section, tex_root)
    root_hint = tex_root if tex_root is not None else THEORY_ROOT
    for path in scan_files:
        text = read_text_file(path, encoding="utf-8")
        for match in CLAIM_ENV_RE.finditer(text):
            env = match.group(1)
            end_marker = f"\\end{{{env}}}"
            end_idx = text.find(end_marker, match.end())
            if end_idx < 0:
                end_idx = len(text)
            body = text[match.end() : end_idx]
            line = text.count("\n", 0, match.start()) + 1
            label_match = CLAIM_LABEL_RE.search(body)
            rel = display_path(path, root_hint=root_hint)
            if label_match is None:
                unlabeled.append(
                    {
                        "file": rel,
                        "line": line,
                        "environment": env,
                        "reason": "claim environment has no \\label",
                    }
                )
                continue
            claims.append(
                PaperClaimRecord(
                    file=rel,
                    line=line,
                    environment=env,
                    label=label_match.group(1).strip(),
                )
            )
    return claims, unlabeled


def coverage_payload(
    declarations: Iterable[DeclarationRecord],
    claims: Iterable[PaperClaimRecord],
    unlabeled_claims: Iterable[dict[str, object]],
    *,
    section: str,
    tex_root: Path | None = None,
) -> dict[str, object]:
    decls = list(declarations)
    claim_list = list(claims)
    unlabeled = list(unlabeled_claims)
    lean_registry_labels = {
        label
        for decl in decls
        for label in decl.registry_labels
    }
    paper_labels_only = {
        label
        for decl in decls
        for label in decl.paper_labels
    }
    claim_labels = [claim.label for claim in claim_list]
    claim_env_counts = Counter(claim.environment for claim in claim_list)
    claim_prefix_counts = Counter(label.split(":", 1)[0] for label in claim_labels if ":" in label)
    duplicate_claim_labels = {
        label: count
        for label, count in Counter(claim_labels).items()
        if count > 1
    }

    claim_label_set = set(claim_labels)
    matched_registry = sorted(claim_label_set & lean_registry_labels)
    missing_in_lean = sorted(claim_label_set - lean_registry_labels)
    extra_registry = sorted(
        label
        for label in lean_registry_labels
        if label.split(":", 1)[0] in CLAIM_ENV_TO_PREFIX.values() and label not in claim_label_set
    )
    scan_root = str(tex_root.resolve()) if tex_root is not None else str(THEORY_ROOT.resolve())

    return {
        "section": section,
        "scan_root": scan_root,
        "files_scanned": len(theory_files(section, tex_root)),
        "claim_environments_total": len(claim_list),
        "claim_labels_total": len(claim_labels),
        "claim_labels_unique": len(claim_label_set),
        "claim_environment_counts": dict(sorted(claim_env_counts.items())),
        "claim_prefix_counts": dict(sorted(claim_prefix_counts.items())),
        "claim_duplicate_labels": dict(sorted(duplicate_claim_labels.items())),
        "unlabeled_claims": unlabeled,
        "unlabeled_claims_total": len(unlabeled),
        "lean_registry_labels_total": len(lean_registry_labels),
        "lean_paper_labels_total": len(paper_labels_only),
        "matched_registry_labels_total": len(matched_registry),
        "missing_in_lean_total": len(missing_in_lean),
        "extra_registry_labels_total": len(extra_registry),
        "coverage_rate_registry": (
            len(matched_registry) / len(claim_label_set) if claim_label_set else 0.0
        ),
        "matched_registry_labels": matched_registry,
        "missing_in_lean": missing_in_lean,
        "extra_registry_labels": extra_registry,
        "claims": [
            {
                "file": claim.file,
                "line": claim.line,
                "environment": claim.environment,
                "label": claim.label,
            }
            for claim in claim_list
        ],
    }


def inventory_payload(declarations: Iterable[DeclarationRecord]) -> dict[str, object]:
    decls = list(declarations)
    kind_counts = Counter(decl.kind for decl in decls)
    attached_registry_labels = [label for decl in decls for label in decl.registry_labels]
    attached_paper_labels = [label for decl in decls for label in decl.paper_labels]
    all_registry_mentions: list[str] = []
    all_paper_mentions: list[str] = []
    for path in lean_files():
        text = read_text_file(path, encoding="utf-8")
        all_registry_mentions.extend(REGISTRY_LABEL_RE.findall(text))
        all_paper_mentions.extend(PAPER_LABEL_RE.findall(text))
    prefix_counts = Counter(label.split(":", 1)[0] for label in attached_registry_labels)
    module_counts = Counter(decl.module for decl in decls if decl.registry_labels)
    duplicate_labels = {
        label: count
        for label, count in Counter(attached_registry_labels).items()
        if count > 1
    }
    return {
        "files_scanned": len(lean_files()),
        "declarations_total": len(decls),
        "declaration_kinds": dict(sorted(kind_counts.items())),
        "registry_labeled_declarations": sum(1 for decl in decls if decl.registry_labels),
        "paper_labeled_declarations": sum(1 for decl in decls if decl.paper_labels),
        "registry_labels_attached_total": len(attached_registry_labels),
        "registry_labels_attached_unique": len(set(attached_registry_labels)),
        "registry_labels_mentions_total": len(all_registry_mentions),
        "registry_labels_mentions_unique": len(set(all_registry_mentions)),
        "paper_labels_attached_total": len(attached_paper_labels),
        "paper_labels_attached_unique": len(set(attached_paper_labels)),
        "paper_labels_mentions_total": len(all_paper_mentions),
        "paper_labels_mentions_unique": len(set(all_paper_mentions)),
        "registry_label_prefixes": dict(sorted(prefix_counts.items())),
        "modules_with_labels": dict(sorted(module_counts.items())),
        "duplicate_labels": dict(sorted(duplicate_labels.items())),
        "declarations": [
            {
                "module": decl.module,
                "file": decl.file,
                "line": decl.line,
                "kind": decl.kind,
                "name": decl.name,
                "registry_labels": list(decl.registry_labels),
                "paper_labels": list(decl.paper_labels),
            }
            for decl in decls
        ],
    }


def cmd_audit(_: argparse.Namespace) -> int:
    violations: list[dict[str, object]] = []
    for path in lean_files():
        violations.extend(collect_forbidden_tokens(path))
    declarations, orphans = build_inventory()
    payload = inventory_payload(declarations)

    print(
        "[omega-ci] audit summary:"
        f" files={payload['files_scanned']}"
        f" declarations={payload['declarations_total']}"
        f" registry_labeled={payload['registry_labeled_declarations']}"
        f" registry_mentions={payload['registry_labels_mentions_total']}"
        f" paper_mentions={payload['paper_labels_mentions_total']}"
        f" paper_unique={payload['paper_labels_mentions_unique']}"
    )

    if orphans:
        print(f"[omega-ci] orphan label blocks: {len(orphans)}")
        for orphan in orphans[:20]:
            print(
                f"  {orphan['file']}:{orphan['line']}: "
                f"{', '.join(orphan['labels'])} ({orphan['reason']})"
            )

    if violations:
        print(f"[omega-ci] forbidden tokens: {len(violations)}")
        for violation in violations[:50]:
            print(
                f"  {violation['file']}:{violation['line']}:{violation['column']}: "
                f"{violation['token']}"
            )

    if violations or orphans:
        return 1
    return 0


def cmd_inventory(args: argparse.Namespace) -> int:
    declarations, orphans = build_inventory()
    payload = inventory_payload(declarations)
    payload["orphan_label_blocks"] = orphans

    print(
        "[omega-ci] inventory:"
        f" files={payload['files_scanned']}"
        f" declarations={payload['declarations_total']}"
        f" registry_labeled={payload['registry_labeled_declarations']}"
        f" paper_labeled={payload['paper_labeled_declarations']}"
        f" labels_attached={payload['registry_labels_attached_total']}"
        f" labels_mentions={payload['paper_labels_mentions_total']}"
        f" unique_labels={payload['paper_labels_mentions_unique']}"
    )

    if args.json:
        out_path = Path(args.json).resolve()
        write_text_file(out_path, json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[omega-ci] wrote inventory JSON: {out_path}")

    if args.strict and orphans:
        print(f"[omega-ci] strict mode failed: {len(orphans)} orphan label blocks detected")
        return 1
    return 0


def cmd_search(args: argparse.Namespace) -> int:
    declarations, _ = build_inventory()
    results = search_declarations(declarations, args.query, args.top_k)
    payload = {
        "query": args.query,
        "top_k": args.top_k,
        "results": results,
    }

    print(
        "[omega-ci] search:"
        f" query={args.query!r}"
        f" matches={len(results)}"
    )
    for item in results:
        labels = item["registry_labels"] or item["paper_labels"]
        label_text = ", ".join(labels[:3]) if labels else "<no labels>"
        print(
            f"  score={float(item['score']):.3f} "
            f"{item['kind']} {item['name']} "
            f"({item['module']}:{item['line']})"
        )
        print(f"    labels: {label_text}")

    if args.json:
        out_path = Path(args.json).resolve()
        write_text_file(out_path, json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[omega-ci] wrote search JSON: {out_path}")
    return 0


def resolve_tex_root(raw_path: str | None) -> Path | None:
    if not raw_path:
        return None
    path = Path(raw_path)
    if not path.is_absolute():
        path = (REPO_ROOT / path).resolve()
    if not path.exists():
        raise FileNotFoundError(f"TeX root not found: {raw_path}")
    if not path.is_dir():
        raise ValueError(f"Expected a directory for --tex-root: {raw_path}")
    return path


def p6_gate_payload(
    coverage: dict[str, object],
    *,
    paper_id: str,
) -> dict[str, object]:
    blocking_labels = list(coverage["missing_in_lean"])
    unlabeled_claims = list(coverage["unlabeled_claims"])
    return {
        "paper_id": paper_id,
        "scan_root": coverage["scan_root"],
        "claim_labels_unique": coverage["claim_labels_unique"],
        "matched_registry_labels_total": coverage["matched_registry_labels_total"],
        "missing_in_lean_total": coverage["missing_in_lean_total"],
        "unlabeled_claims_total": coverage["unlabeled_claims_total"],
        "blocking_labels": blocking_labels,
        "blocking_unlabeled_claims": unlabeled_claims,
        "coverage_rate_registry": coverage["coverage_rate_registry"],
        "pass": not blocking_labels and not unlabeled_claims,
    }


def cmd_paper_coverage(args: argparse.Namespace) -> int:
    declarations, _ = build_inventory()
    tex_root = resolve_tex_root(args.tex_root)
    scan_label = args.sections if tex_root is None else "custom"
    claims, unlabeled_claims = collect_paper_claims(args.sections, tex_root)
    payload = coverage_payload(
        declarations,
        claims,
        unlabeled_claims,
        section=scan_label,
        tex_root=tex_root,
    )
    paper_id = args.paper_id or (tex_root.name if tex_root is not None else args.sections)

    print(
        "[omega-ci] paper-coverage:"
        f" section={scan_label}"
        f" paper_id={paper_id}"
        f" files={payload['files_scanned']}"
        f" claim_labels={payload['claim_labels_unique']}"
        f" matched={payload['matched_registry_labels_total']}"
        f" missing={payload['missing_in_lean_total']}"
        f" unlabeled={payload['unlabeled_claims_total']}"
        f" coverage={float(payload['coverage_rate_registry']):.3%}"
    )

    missing = payload["missing_in_lean"]
    if missing:
        print("[omega-ci] top missing labels:")
        for label in missing[: args.top_missing]:
            print(f"  {label}")

    unlabeled = payload["unlabeled_claims"]
    if unlabeled:
        print("[omega-ci] unlabeled claim environments:")
        for item in unlabeled[: args.top_missing]:
            print(f"  {item['file']}:{item['line']} ({item['environment']})")

    if args.json:
        out_path = Path(args.json).resolve()
        write_text_file(out_path, json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[omega-ci] wrote paper coverage JSON: {out_path}")

    if args.gate_json:
        gate = p6_gate_payload(payload, paper_id=paper_id)
        out_path = Path(args.gate_json).resolve()
        write_text_file(out_path, json.dumps(gate, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[omega-ci] wrote P6 gate JSON: {out_path}")

    if args.fail_on_missing and (missing or unlabeled):
        print("[omega-ci] fail-on-missing triggered", file=sys.stderr)
        return 1
    return 0


def resolve_lean_file(raw_path: str) -> Path:
    path = Path(raw_path)
    if not path.is_absolute():
        path = (LEAN_ROOT / path).resolve()
    if not path.exists():
        raise FileNotFoundError(f"Lean file not found: {raw_path}")
    if path.suffix != ".lean":
        raise ValueError(f"Expected a .lean file: {raw_path}")
    return path


def cmd_verify_files(args: argparse.Namespace) -> int:
    lean_files_to_check = [resolve_lean_file(p) for p in args.paths]
    overall_rc = 0
    for lean_file in lean_files_to_check:
        rel = lean_file.relative_to(LEAN_ROOT)
        print(f"[omega-ci] verifying {rel}")
        result = subprocess.run(
            ["lake", "env", "lean", str(lean_file)],
            cwd=LEAN_ROOT,
            text=True,
            capture_output=True,
        )
        if result.stdout:
            print(result.stdout, end="")
        if result.stderr:
            print(result.stderr, end="", file=sys.stderr)
        if result.returncode != 0:
            overall_rc = result.returncode
            print(f"[omega-ci] verification failed: {rel}", file=sys.stderr)
    return overall_rc


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Omega Lean automation helpers")
    sub = p.add_subparsers(dest="command", required=True)

    audit_p = sub.add_parser("audit", help="Run zero-axiom / no-sorry audit")
    audit_p.set_defaults(func=cmd_audit)

    inv_p = sub.add_parser("inventory", help="Summarize declarations and paper labels")
    inv_p.add_argument("--json", help="Write JSON inventory to this path")
    inv_p.add_argument(
        "--strict",
        action="store_true",
        help="Fail if a doc-label block is not attached to a declaration",
    )
    inv_p.set_defaults(func=cmd_inventory)

    search_p = sub.add_parser("search", help="Search Lean declarations via local TF-IDF scoring")
    search_p.add_argument("query", help="Free-text query or exact paper label")
    search_p.add_argument("--top-k", type=int, default=10, help="Maximum search hits to show")
    search_p.add_argument("--json", help="Write search results to this path")
    search_p.set_defaults(func=cmd_search)

    coverage_p = sub.add_parser(
        "paper-coverage",
        help="Compare theorem-like LaTeX claim labels against Lean registry labels",
    )
    coverage_p.add_argument(
        "--sections",
        choices=("body", "appendix", "all"),
        default="body",
        help="Which paper sections to scan",
    )
    coverage_p.add_argument(
        "--tex-root",
        help="Scan a specific TeX directory (for example theory/publication/<paper>) instead of the parent monograph",
    )
    coverage_p.add_argument(
        "--paper-id",
        help="Override the paper identifier used in summaries and gate JSON output",
    )
    coverage_p.add_argument("--json", help="Write coverage report to this path")
    coverage_p.add_argument(
        "--gate-json",
        help="Write a compact machine-readable P6 gate artifact to this path",
    )
    coverage_p.add_argument(
        "--top-missing",
        type=int,
        default=20,
        help="How many missing labels to print",
    )
    coverage_p.add_argument(
        "--fail-on-missing",
        action="store_true",
        help="Return non-zero if paper labels are missing from Lean or claim environments lack labels",
    )
    coverage_p.set_defaults(func=cmd_paper_coverage)

    verify_p = sub.add_parser("verify-files", help="Run lake env lean on selected files")
    verify_p.add_argument("paths", nargs="+", help="Lean file paths, relative to lean4/")
    verify_p.set_defaults(func=cmd_verify_files)
    return p


def main() -> int:
    args = parser().parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
