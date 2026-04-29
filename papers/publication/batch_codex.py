#!/usr/bin/env python3
"""Batch Codex review+fix for all papers.

Dispatches codex_fix.py for every paper in parallel.
Papers without real ChatGPT reviews get a combined review+fix prompt.

Usage:
    python batch_codex.py                   # all papers
    python batch_codex.py --only circle_dim fredholm_witt
    python batch_codex.py --dry-run         # show plan
"""

import argparse
import json
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PUB_DIR = Path(__file__).parent
ORACLE_DONE = PUB_DIR / "oracle" / "done"
CODEX_FIX = PUB_DIR / "codex_fix.py"
LOG_DIR = PUB_DIR / "oracle" / "codex_logs"

# Same alias map as batch_requeue.py
PAPER_MAP = {}
ALIASES = {
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

for d in sorted(PUB_DIR.glob("2026_*/")):
    if not (d / "main.tex").exists():
        continue
    short = re.sub(r"^2026_", "", d.name)
    alias = ALIASES.get(short, short[:30])
    PAPER_MAP[alias] = d


def find_latest_real_review(short_name: str) -> Path | None:
    """Find the latest real (>5000 bytes) gate review for a paper.

    Prefers the most recent review (by round number), not the largest.
    """
    candidates = []
    for f in ORACLE_DONE.glob(f"{short_name}_gate_R*.md"):
        size = f.stat().st_size
        if size > 5000:
            # Extract round number for sorting
            m = re.search(r"_gate_R(\d+)", f.name)
            rnd = int(m.group(1)) if m else 0
            candidates.append((rnd, f))
    if candidates:
        candidates.sort(key=lambda x: x[0], reverse=True)
        return candidates[0][1]
    return None


REVIEW_FIX_PROMPT = """You are a mathematics journal referee AND editor.

TASK: Review this paper thoroughly, then fix every issue you find.

PHASE 1 — REVIEW:
Identify all issues: mathematical errors, proof gaps, missing definitions,
unclear exposition, missing references, structural problems.
Classify each as BLOCKER / MEDIUM / LOW.

PHASE 2 — FIX:
For every BLOCKER and MEDIUM issue, edit the .tex files directly to fix it.
- Fix proof gaps by adding the missing argument.
- Fix mathematical errors by correcting the statement/proof.
- Add missing definitions where needed.
- Add missing citations to references.bib.
- Improve unclear exposition.

CONSTRAINTS:
- Only edit .tex and .bib files in this directory.
- Do NOT add revision markers, changelogs, or "fixed issue" comments.
- Preserve the paper's voice and style.
- Write clean, publication-ready LaTeX.
"""


def run_one_paper(short_name: str, paper_dir: Path, review_path: Path | None,
                  timeout: int = 3600, model: str | None = None) -> dict:
    """Run codex fix for one paper. Returns result dict."""
    log_file = LOG_DIR / f"{short_name}_codex_{int(time.time())}.log"
    start = time.time()

    if review_path:
        # Use existing review with codex_fix.py
        cmd = [
            sys.executable, str(CODEX_FIX),
            "--paper", str(paper_dir),
            "--review", str(review_path),
            "--timeout", str(timeout),
        ]
        if model:
            cmd += ["--model", model]
        mode = f"fix from {review_path.name}"
    else:
        # No real review — run codex directly with combined review+fix prompt
        import shutil
        codex_bin = shutil.which("codex") or "codex"
        if sys.platform == "win32":
            npm_codex = Path.home() / "AppData" / "Roaming" / "npm" / "codex.cmd"
            if npm_codex.exists():
                codex_bin = str(npm_codex)
        cmd = [codex_bin, "exec", "--full-auto", "-"]
        mode = "review+fix (no prior review)"

    print(f"[{short_name}] Starting: {mode}")

    try:
        if review_path:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout,
                encoding="utf-8", errors="replace",
                shell=(sys.platform == "win32"),
            )
        else:
            result = subprocess.run(
                cmd, cwd=str(paper_dir),
                input=REVIEW_FIX_PROMPT,
                capture_output=True, text=True, timeout=timeout,
                encoding="utf-8", errors="replace",
                shell=(sys.platform == "win32" and str(cmd[0]).endswith(".cmd")),
            )

        elapsed = time.time() - start
        log_file.write_text(
            f"=== {short_name} ({mode}) ===\n"
            f"Elapsed: {elapsed:.0f}s\n"
            f"Return code: {result.returncode}\n\n"
            f"=== STDOUT ===\n{result.stdout}\n\n"
            f"=== STDERR ===\n{result.stderr}\n",
            encoding="utf-8",
        )

        success = result.returncode == 0
        print(f"[{short_name}] {'OK' if success else 'FAIL'} ({elapsed:.0f}s)")
        return {
            "paper": short_name,
            "success": success,
            "elapsed": elapsed,
            "mode": mode,
            "log": str(log_file),
        }

    except subprocess.TimeoutExpired:
        elapsed = time.time() - start
        print(f"[{short_name}] TIMEOUT ({elapsed:.0f}s)")
        return {
            "paper": short_name,
            "success": False,
            "elapsed": elapsed,
            "mode": mode,
            "error": "timeout",
        }
    except Exception as e:
        elapsed = time.time() - start
        print(f"[{short_name}] ERROR: {e}")
        return {
            "paper": short_name,
            "success": False,
            "elapsed": elapsed,
            "mode": mode,
            "error": str(e),
        }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--only", nargs="+", help="Only these papers (short names)")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--workers", type=int, default=6,
                        help="Max parallel codex processes (default 6)")
    parser.add_argument("--timeout", type=int, default=3600,
                        help="Per-paper timeout in seconds (default 3600)")
    parser.add_argument("--model", default=None,
                        help="Codex model override (e.g. gpt-5-codex)")
    args = parser.parse_args()

    global MODEL_OVERRIDE
    MODEL_OVERRIDE = args.model

    LOG_DIR.mkdir(parents=True, exist_ok=True)

    # Build task list
    tasks = []
    for short, paper_dir in sorted(PAPER_MAP.items()):
        if args.only and short not in args.only:
            continue
        review = find_latest_real_review(short)
        tasks.append((short, paper_dir, review))

    print(f"Codex batch: {len(tasks)} papers, {args.workers} workers\n")
    for short, paper_dir, review in tasks:
        r_info = review.name if review else "(no review — will self-review)"
        print(f"  {short:30s} review={r_info}")

    if args.dry_run:
        print("\n(dry run)")
        return

    print()
    results = []
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {
            pool.submit(run_one_paper, short, pdir, rev, args.timeout, args.model): short
            for short, pdir, rev in tasks
        }
        for future in as_completed(futures):
            name = futures[future]
            try:
                res = future.result()
                results.append(res)
            except Exception as e:
                print(f"[{name}] EXCEPTION: {e}")
                results.append({"paper": name, "success": False, "error": str(e)})

    # Summary
    ok = sum(1 for r in results if r.get("success"))
    print(f"\n{'='*60}")
    print(f"Codex batch complete: {ok}/{len(results)} succeeded")
    for r in sorted(results, key=lambda x: x["paper"]):
        status = "OK" if r.get("success") else "FAIL"
        elapsed = r.get("elapsed", 0)
        print(f"  {r['paper']:30s} {status} ({elapsed:.0f}s) {r.get('mode', '')}")


if __name__ == "__main__":
    main()
