#!/usr/bin/env python3
"""Batch re-queue papers to oracle for gate review.

Compiles each paper's PDF and submits to oracle_server.py queue.
Papers are queued in order and processed sequentially by Tampermonkey.

Usage:
    python batch_requeue.py                    # queue all papers needing review
    python batch_requeue.py --only paper1 paper2  # queue specific papers
    python batch_requeue.py --dry-run          # show what would be queued
"""

import argparse
import base64
import json
import re
import subprocess
import sys
import urllib.request
from pathlib import Path

SERVER = "http://localhost:8765"
PUB_DIR = Path(__file__).parent
ORACLE_DONE = PUB_DIR / "oracle" / "done"

PROMPT = """Please review the attached paper as a journal editor/referee.

Provide:
1. **Overall assessment**: Accept / Major revision / Minor revision / Reject
2. **Novelty rating** for each theorem: HIGH / MEDIUM / LOW with one-line justification
3. **Issue table**: ID | Section | Severity (BLOCKER/MEDIUM/LOW) | Description | Suggested fix
4. **Missing references**: List any important related work not cited
5. **Specific improvements** needed to reach acceptance
6. **Concrete fixes**: For each BLOCKER and MEDIUM issue, provide an actionable solution.

Be rigorous. Focus on what needs to change."""

# Short names for paper dirs
PAPER_MAP = {}
for d in sorted(PUB_DIR.glob("2026_*/")):
    if not (d / "main.tex").exists():
        continue
    name = d.name
    # Extract short name: 2026_foo_bar_... -> foo_bar or known alias
    short = re.sub(r"^2026_", "", name)
    # Known aliases
    aliases = {
        "circle_dimension_haar_pullback_cauchy_weight_jfa": "circle_dim",
        "conservative_extension_chain_state_forcing_apal_focused": "conservative_ext_focused",
        "conservative_extension_chain_state_forcing_apal": "conservative_ext",
        "cubical_stokes_inverse_boundary_readout_jdsgt": "cubical_stokes",
        "dynamical_zeta_finite_part_spectral_fingerprint_etds": "dynamical_zeta",
        "fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints": "fibonacci_folding",
        "fold_truncation_defect_stokes_dynamical_systems": "fold_truncation",
        "fredholm_witt_cyclic_block_spectral_rigidity_symbolic_zeta": "fredholm_witt",
        "gluing_failure_visible_quotients_pure_ext_blind_spots_apal": "gluing_failure",
        "JphisComm": "JphisComm",
        "JphisComm_待投稿": "JphisComm",
        "prefix_scan_error_boundary_rates_dynamical_systems": "prefix_scan",
        "prime_languages_sofic_obstructions_dynamical_zeta": "prime_languages",
        "projection_ontological_mathematics_core_tams": "projection_ontological",
        "recursive_addressing_prefix_sites_tac": "recursive_addressing",
        "scan_projection_address_semantics_sigma_nonexpansion_etds": "scan_projection",
        "self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists": "self_dual_sync",
        "yang_lee_quartic_spectral_curve_discriminant_factorization_lee_yang_edge_singularity": "yang_lee",
        "joukowsky_elliptic_godel_lorentz_mahler_capacity": "joukowsky_elliptic",
        "window6_spectral_rigidity_hypercube_lumpability_fold_gauge": "window6_spectral",
        "zeckendorf_stable_arithmetic_fibonacci_congruence_online": "zeckendorf_arith",
        "chebotarev_quotient_entropy_fold_groupoid_rigidity": "chebotarev_entropy",
    }
    alias = aliases.get(short, short[:30])
    PAPER_MAP[alias] = d


def get_latest_review(short_name: str) -> tuple[str | None, int]:
    """Get latest review file and its size for a paper."""
    reviews = sorted(ORACLE_DONE.glob(f"{short_name}_gate_R*.md"))
    if not reviews:
        return None, 0
    latest = reviews[-1]
    return latest.name, latest.stat().st_size


def get_round_number(short_name: str) -> int:
    """Get next round number for a paper."""
    reviews = sorted(ORACLE_DONE.glob(f"{short_name}_gate_R*.md"))
    if not reviews:
        return 1
    # Extract max round number
    max_r = 0
    for r in reviews:
        m = re.search(r"_gate_R(\d+)", r.name)
        if m:
            max_r = max(max_r, int(m.group(1)))
    return max_r + 1


def compile_paper(paper_dir: Path) -> Path | None:
    """Compile main.tex to PDF."""
    main_tex = paper_dir / "main.tex"
    if not main_tex.exists():
        return None

    # Check if we need xelatex (Chinese content)
    content = main_tex.read_text(encoding="utf-8", errors="replace")
    compiler = "xelatex" if "xeCJK" in content or "ctex" in content or "fontspec" in content else "pdflatex"

    for i in range(2):
        subprocess.run(
            [compiler, "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            cwd=str(paper_dir), capture_output=True, text=True, timeout=120
        )

    if (paper_dir / "references.bib").exists():
        subprocess.run(
            ["bibtex", "main"], cwd=str(paper_dir),
            capture_output=True, text=True, timeout=60
        )
        for _ in range(2):
            subprocess.run(
                [compiler, "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                cwd=str(paper_dir), capture_output=True, text=True, timeout=120
            )

    pdf = paper_dir / "main.pdf"
    return pdf if pdf.exists() else None


def submit_to_queue(task_id: str, prompt: str, pdf_path: Path) -> bool:
    """Submit a task to oracle_server queue."""
    with open(pdf_path, "rb") as f:
        pdf_b64 = base64.b64encode(f.read()).decode("ascii")

    payload = {
        "task_id": task_id,
        "prompt": prompt,
        "model": "chatgpt-5.4-pro-extended",
        "pdf_base64": pdf_b64,
        "pdf_name": pdf_path.name,
    }

    req = urllib.request.Request(
        f"{SERVER}/submit",
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    try:
        resp = urllib.request.urlopen(req, timeout=15)
        result = json.loads(resp.read().decode("utf-8"))
        print(f"  -> Queued: {result}")
        return True
    except Exception as e:
        print(f"  -> ERROR: {e}", file=sys.stderr)
        return False


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--only", nargs="+", help="Only queue these papers (short names)")
    parser.add_argument("--dry-run", action="store_true", help="Show plan without submitting")
    parser.add_argument("--force", action="store_true", help="Re-queue even if last review was real")
    args = parser.parse_args()

    # Check server
    if not args.dry_run:
        try:
            resp = urllib.request.urlopen(f"{SERVER}/status", timeout=5)
            status = json.loads(resp.read().decode("utf-8"))
            print(f"Oracle server: queue={status['queue_length']}, completed={status['completed']}")
        except Exception:
            print("ERROR: Oracle server not running at", SERVER, file=sys.stderr)
            sys.exit(1)

    # Determine which papers to queue
    to_queue = []
    for short, paper_dir in sorted(PAPER_MAP.items()):
        if args.only and short not in args.only:
            continue

        latest_review, size = get_latest_review(short)
        is_stub = size < 1500  # stubs are ~749 or ~1097 chars
        is_real = size > 5000
        next_round = get_round_number(short)

        reason = None
        if latest_review is None:
            reason = "no review yet"
        elif is_stub:
            reason = f"stub review ({size}B)"
        elif not is_real and size < 2000:
            reason = f"partial capture ({size}B)"
        elif args.force:
            reason = "forced re-queue"
        # Skip papers with real reviews unless forced
        # (they should be fixed first, then re-queued)

        if reason:
            to_queue.append((short, paper_dir, next_round, reason))

    if not to_queue:
        print("No papers need re-queueing.")
        if not args.force:
            print("Use --force to re-queue papers with real reviews.")
        return

    print(f"\nPapers to queue ({len(to_queue)}):")
    for short, paper_dir, rnd, reason in to_queue:
        print(f"  {short}_gate_R{rnd}: {reason}")

    if args.dry_run:
        print("\n(dry run — nothing submitted)")
        return

    print()
    queued = 0
    for short, paper_dir, rnd, reason in to_queue:
        task_id = f"{short}_gate_R{rnd}"
        print(f"[{queued+1}/{len(to_queue)}] {task_id}...")

        pdf = compile_paper(paper_dir)
        if not pdf:
            print(f"  -> SKIP: compilation failed")
            continue

        print(f"  -> PDF: {pdf.stat().st_size // 1024} KB")
        if submit_to_queue(task_id, PROMPT, pdf):
            queued += 1

    print(f"\nDone: {queued}/{len(to_queue)} papers queued.")


if __name__ == "__main__":
    main()
