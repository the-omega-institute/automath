#!/usr/bin/env python3
"""Phase D mechanical post-rebase lints for Lean rounds.

Runs after lake build / check-axioms / audit / axiom-purity, before merge.
Three checks on declarations introduced in this round
(`<base-branch>..HEAD` under `lean4/BEDC/`):

  1. Mechanical-arity suffix on a new declaration name
     (`_two`, `_three`, `_four`, `_five`, `_six`, `_*_step`,
     `_*_witness_chain`).
  2. Parameter-echo schema: signature binds a hypothesis
     `(name : forall … hsame …)` — i.e. quantifies over an hsame law as
     input rather than proving anything specific about a concrete BEDC
     kernel object.
  3. BHist-anchor: every new theorem under `BEDC.Derived.*` must mention
     at least one concrete BEDC kernel symbol in its signature
     (BHist / BMark / hsame / ProbeBundle / SigRel / NameCert / Pkg /
     etc).

Used by `codex_formalize.py::run_phase_d_lints` via subprocess. Splitting
the lint into its own script means the regex set can be tightened
without restarting the pipeline — the next call (next round's pre-merge
gate) picks up the change.

Usage:

    python3 lean4/scripts/phase_d_lint.py \
        --worktree /path/to/round_R1234 \
        --base-branch codex-auto-dev

Exit code 0 = clean. Exit code 1 = at least one violation; details on
stdout suitable for inclusion in a codex recovery prompt.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

DECL_RE = re.compile(
    r"^\s*(theorem|lemma|def|inductive|structure|class)\s+(\w+)"
)
MECHANICAL_ARITY_RE = re.compile(
    r"_(two|three|four|five|six)(?:_step)?(?:_witness_chain)?\b"
)
PARAMETER_ECHO_BIND_RE = re.compile(
    r"\(\s*(\w+)\s*:\s*(?:∀|forall)\b[^)]*hsame\b", re.DOTALL
)
PARAMETER_ECHO_CONCL_RE = re.compile(
    r"(?:∀|forall)\b[^,]*,[^.]*hsame\b", re.DOTALL
)


def _strip_hsame_tokens(text: str) -> str:
    """Drop `hsame` and the bare `BHist` type token so the residual anchor
    scan only fires on substantive constructors (Empty/e0/e1/Cont/NameCert/…)."""
    text = re.sub(r"\bhsame\b", "", text)
    text = re.sub(r"\bBHist\b", "", text)
    return text


def _extract_conclusion(sig: str) -> str:
    """Return the part of `sig` after the last top-level `:` (the goal type)."""
    depth = 0
    last_colon = -1
    for i, ch in enumerate(sig):
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        elif ch == ":" and depth == 0:
            last_colon = i
    return sig[last_colon + 1:] if last_colon >= 0 else sig
BHIST_CONSTRUCTOR_RE = re.compile(
    r"\b("
    # FKernel primitive constructors (the original kernel layer)
    r"BHist|BMark|Empty|e0|e1|cons|append|sameSig|"
    r"ProbeBundle|SigRel|InGap|NameCert|SemanticNameCert|Pkg|hsame|msame|"
    r"Cont|Ext|InBundle|SameSig|UnaryHistory|StageInterface|"
    r"SealEvent|SealInterface|AskEvent|AskPolicy|BundleAskPolicy|"
    r"DescentCertificate|StableTransformation|ThreadFamily|"
    r"bundleAppend|bundleLength|bwordLength|"
    # BEDC-defined typeclasses that derived chapters routinely instance —
    # mentioning these counts as anchoring because the typeclass itself
    # is BHist-grounded (BHistCarrier requires toEventFlow into EventFlow,
    # ChapterTasteGate requires round_trip + layer_separation, etc.)
    r"BHistCarrier|ChapterTasteGate|FieldFaithful|"
    # Any \w+Up identifier — derived chapter carriers and their projections.
    # By BEDC convention every chapter under BEDC/Derived/ exposes <Name>Up
    # as its carrier. A theorem/instance mentioning any <X>Up name is
    # transitively anchored through that chapter's BHist carrier definition.
    r"\w+Up"
    r")\b"
)
DERIVED_PATH_PREFIX = "lean4/BEDC/Derived"
SIGNATURE_BLOCK_LIMIT = 40


def diff_added_decls(worktree: Path, base_branch: str) -> list[tuple[str, str]]:
    """Return [(name, signature_block)] for theorem/lemma/def added in
    this worktree relative to base_branch, scoped to lean4/BEDC/."""
    res = subprocess.run(
        [
            "git", "log", "-p", "--no-color", "--reverse",
            f"{base_branch}..HEAD", "--", "lean4/BEDC/",
        ],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    text = res.stdout or ""
    out: list[tuple[str, str]] = []
    pending: list[str] = []
    pending_name: str | None = None
    for raw in text.splitlines():
        if not raw.startswith("+") or raw.startswith("+++"):
            if pending_name is not None and pending:
                out.append((pending_name, "\n".join(pending)))
                pending_name = None
                pending = []
            continue
        line = raw[1:]
        m = DECL_RE.match(line)
        if m:
            if pending_name is not None and pending:
                out.append((pending_name, "\n".join(pending)))
            pending_name = m.group(2)
            pending = [line]
        elif pending_name is not None:
            pending.append(line)
            if len(pending) > SIGNATURE_BLOCK_LIMIT:
                out.append((pending_name, "\n".join(pending)))
                pending_name = None
                pending = []
    if pending_name is not None and pending:
        out.append((pending_name, "\n".join(pending)))
    return out


def declaration_in_derived(worktree: Path, name: str) -> bool:
    res = subprocess.run(
        ["git", "grep", "-l", "-F", f"theorem {name}", "--", DERIVED_PATH_PREFIX],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    return bool(res.stdout.strip())


# Same regex as codex_formalize.py's _BEDC_TOUCHPOINT_RE — used for the
# SHALLOW GROWTH dup-conclusion preview so codex's self-check sees the
# exact same set as Phase D's reject.
_BEDC_TOUCHPOINT_RE = re.compile(
    r"\b(BHist|BMark|hsame|msame|ProbeBundle|SigRel|InGap|NameCert|"
    r"SemanticNameCert|Cont|Ext|InBundle|UnaryHistory|Pkg|sameSig|"
    r"DescentCertificate|StableTransformation|ThreadFamily|"
    r"AskEvent|AskPolicy|BundleAskPolicy|SealEvent|SealInterface|"
    r"StageInterface|bundleAppend|bundleLength|bwordLength)\b"
)


def _diff_added_blocks_per_file(worktree: Path, base_branch: str) -> dict[str, list[tuple[str, str]]]:
    """Group `diff_added_decls` results by source file (rel path), so the
    SHALLOW GROWTH check can compare conclusions WITHIN one file (matching
    codex_formalize.py's `detect_shallow_growth_patterns` semantics)."""
    # Re-parse the same git log, but track which file each + line lives in.
    res = subprocess.run(
        [
            "git", "log", "-p", "--no-color", "--reverse",
            f"{base_branch}..HEAD", "--", "lean4/BEDC/",
        ],
        cwd=worktree, capture_output=True, text=True, check=False,
    )
    text = res.stdout or ""
    grouped: dict[str, list[tuple[str, str]]] = {}
    current_file: str | None = None
    pending: list[str] = []
    pending_name: str | None = None

    def flush(rel: str | None) -> None:
        nonlocal pending, pending_name
        if rel and pending_name is not None and pending:
            grouped.setdefault(rel, []).append((pending_name, "\n".join(pending)))
        pending_name = None
        pending = []

    for raw in text.splitlines():
        if raw.startswith("+++ b/"):
            flush(current_file)
            current_file = raw[len("+++ b/"):]
            continue
        if not raw.startswith("+") or raw.startswith("+++"):
            flush(current_file)
            continue
        line = raw[1:]
        m = DECL_RE.match(line)
        if m:
            flush(current_file)
            pending_name = m.group(2)
            pending = [line]
        elif pending_name is not None:
            pending.append(line)
            if len(pending) > SIGNATURE_BLOCK_LIMIT:
                flush(current_file)
    flush(current_file)
    return grouped


def _decl_conclusion(block: str) -> str:
    """Extract the conclusion (after the final `:` before `:=`) from a
    declaration's signature block. Same heuristic as codex_formalize.py."""
    header = block.split(":=", 1)[0]
    idx = header.rfind(":")
    if idx == -1:
        return ""
    return " ".join(header[idx + 1:].split())


def detect_shallow_growth_dups(worktree: Path, base_branch: str) -> list[str]:
    """Detect duplicate-conclusion theorems among the round's added decls
    (same algorithm as `codex_formalize.py::detect_shallow_growth_patterns`,
    abbreviated to dup-conclusion only — anchor-missing / parameter-echo
    are already caught by main()). Designed for Phase C self-check use.
    """
    violations: list[str] = []
    grouped = _diff_added_blocks_per_file(worktree, base_branch)
    for rel, blocks in grouped.items():
        conclusion_owner: dict[str, str] = {}
        for name, block in blocks:
            kind_match = re.match(r"\s*(?:protected\s+)?(theorem|lemma)\b", block)
            if not kind_match:
                continue
            conclusion = _decl_conclusion(block)
            if not conclusion:
                continue
            if not _BEDC_TOUCHPOINT_RE.search(conclusion):
                continue
            if conclusion in conclusion_owner:
                violations.append(
                    f"{rel}: duplicate theorem conclusion in "
                    f"{conclusion_owner[conclusion]} and {name}"
                )
            else:
                conclusion_owner[conclusion] = name
    return violations


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--worktree", type=Path, required=True)
    p.add_argument("--base-branch", type=str, required=True)
    p.add_argument("--include-shallow", action="store_true",
                    help="Also detect duplicate-conclusion theorems "
                          "(matches codex_formalize.detect_shallow_growth_patterns).")
    args = p.parse_args()

    decls = diff_added_decls(args.worktree, args.base_branch)
    if not decls and not args.include_shallow:
        return 0

    arity_hits: list[str] = []
    echo_hits: list[str] = []
    anchor_hits: list[str] = []
    for name, body in decls:
        if MECHANICAL_ARITY_RE.search(name):
            arity_hits.append(name)
            continue
        sig = body.split(":=")[0]
        is_derived = declaration_in_derived(args.worktree, name)
        if PARAMETER_ECHO_BIND_RE.search(sig):
            conclusion = _extract_conclusion(sig)
            if PARAMETER_ECHO_CONCL_RE.search(conclusion):
                concl_no_hsame = _strip_hsame_tokens(conclusion)
                if not BHIST_CONSTRUCTOR_RE.search(concl_no_hsame):
                    echo_hits.append(name)
        # Anchor check matches the orchestrator's
        # detect_decls_without_kernel_touchpoint (codex_formalize.py:2138):
        # scan the full block including body comments, not just the
        # signature. The two gates were previously inconsistent — adding
        # a `-- BEDC touchpoint anchor: BHist BMark` comment satisfied
        # the orchestrator gate but not phase_d_lint, so typeclass
        # instances like `instance fooChapterTasteGate : ChapterTasteGate
        # FooUp` whose signature has no bare `BHist` token would pass
        # orchestrator and fail Phase D. Use the full block here too.
        if is_derived and not BHIST_CONSTRUCTOR_RE.search(body):
            anchor_hits.append(name)

    shallow_hits: list[str] = []
    if args.include_shallow:
        shallow_hits = detect_shallow_growth_dups(args.worktree, args.base_branch)

    if not (arity_hits or echo_hits or anchor_hits or shallow_hits):
        return 0

    msgs: list[str] = []
    if arity_hits:
        msgs.append(
            "Mechanical arity suffix on new declaration(s) (NAMING.md §3 forbids"
            " _two/_three/_four/_five/_six/_*_step/_*_witness_chain): "
            + ", ".join(arity_hits[:5])
        )
    if echo_hits:
        msgs.append(
            "Parameter-echo schema: signature binds (name : forall … hsame …) "
            "without anchoring on a concrete BEDC kernel object: "
            + ", ".join(echo_hits[:5])
        )
    if anchor_hits:
        msgs.append(
            "Derived theorem missing a BHist / BMark / hsame / ProbeBundle / "
            "SigRel / NameCert anchor in its signature: "
            + ", ".join(anchor_hits[:5])
        )
    if shallow_hits:
        msgs.append(
            "SHALLOW GROWTH PATTERN — duplicate theorem conclusion(s) "
            "(Phase D will reject):\n  " + "\n  ".join(shallow_hits[:8])
        )
    print("\n".join(msgs))
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
