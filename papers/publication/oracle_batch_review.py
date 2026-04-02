#!/usr/bin/env python3
"""Batch submit all papers for ChatGPT editorial review, one at a time."""

import subprocess
import sys
import os
import time
from pathlib import Path

PUBLICATION_DIR = Path(__file__).parent
ORACLE_DISPATCH = PUBLICATION_DIR / "oracle_dispatch.py"

# Papers to review (order: already-compiled PDFs)
PAPERS = [
    "2026_conservative_extension_chain_state_forcing_apal_focused",
    "2026_cubical_stokes_inverse_boundary_readout_jdsgt",
    "2026_dynamical_zeta_finite_part_spectral_fingerprint_etds",
    "2026_fibonacci_folding_zeckendorf_normalization_gauge_anomaly_spectral_fingerprints",
    "2026_fold_truncation_defect_stokes_dynamical_systems",
    "2026_gluing_failure_visible_quotients_pure_ext_blind_spots_apal",
    "2026_prefix_scan_error_boundary_rates_dynamical_systems",
    "2026_prime_languages_sofic_obstructions_dynamical_zeta",
    "2026_projection_ontological_mathematics_core_tams",
    "2026_recursive_addressing_prefix_sites_tac",
    "2026_scan_projection_address_semantics_sigma_nonexpansion_etds",
    "2026_self_dual_synchronisation_kernel_completed_determinant_cyclotomic_twists",
]

def short_name(paper):
    """Extract a short review name from the paper directory name."""
    # Remove '2026_' prefix, take first 3 words
    name = paper.replace("2026_", "")
    parts = name.split("_")
    return "_".join(parts[:3]) + "_review"

def has_review(paper):
    """Check if this paper already has a review result (non-error, >500 chars)."""
    done_dir = PUBLICATION_DIR / "oracle" / "done"
    prefix = short_name(paper).replace("_review", "")
    for f in done_dir.glob(f"{prefix}*review*.md"):
        try:
            content = f.read_text(encoding="utf-8")
            # Skip error results and very short captures
            if "ERROR:" in content[:200] and len(content) < 300:
                continue
            if len(content) > 500:
                return True
        except:
            pass
    return False

def main():
    total = len(PAPERS)
    done = 0
    skipped = 0
    failed = 0

    print(f"=== Oracle Batch Review: {total} papers ===")
    print(f"Started at {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    for i, paper in enumerate(PAPERS, 1):
        paper_dir = PUBLICATION_DIR / paper
        pdf = paper_dir / "main.pdf"
        name = short_name(paper)

        print(f"[{i}/{total}] {paper}")

        # Check PDF exists
        if not pdf.exists():
            print(f"  SKIP: no main.pdf")
            skipped += 1
            continue

        # Check if already reviewed
        if has_review(paper):
            print(f"  SKIP: already has review")
            skipped += 1
            continue

        # Submit
        print(f"  Submitting as '{name}'...")
        start = time.time()

        try:
            result = subprocess.run(
                [
                    sys.executable, str(ORACLE_DISPATCH),
                    "--paper", str(paper_dir),
                    "--task", "editorial_review",
                    "--name", name,
                    "--no-compile",
                    "--wait",
                    "--timeout", "7200",
                ],
                capture_output=True,
                text=True,
                timeout=7500,  # slightly longer than internal timeout
                encoding="utf-8",
                errors="replace",
            )

            elapsed = int(time.time() - start)
            output = result.stdout + result.stderr

            if result.returncode == 0:
                # Check result file
                result_file = PUBLICATION_DIR / "oracle" / "done" / f"{name}.md"
                if result_file.exists():
                    size = result_file.stat().st_size
                    print(f"  DONE: {size} bytes, {elapsed}s")
                    done += 1
                else:
                    print(f"  DONE (exit 0) but no result file, {elapsed}s")
                    done += 1
            else:
                print(f"  FAILED (exit {result.returncode}), {elapsed}s")
                # Print last few lines of output for debugging
                lines = output.strip().split("\n")
                for line in lines[-3:]:
                    print(f"    {line}")
                failed += 1

        except subprocess.TimeoutExpired:
            print(f"  TIMEOUT (7500s)")
            failed += 1
        except Exception as e:
            print(f"  ERROR: {e}")
            failed += 1

        # Brief pause between submissions
        if i < total:
            print(f"  Waiting 30s before next submission...")
            time.sleep(30)

    print()
    print(f"=== Batch complete ===")
    print(f"Done: {done}, Skipped: {skipped}, Failed: {failed}")
    print(f"Finished at {time.strftime('%Y-%m-%d %H:%M:%S')}")

if __name__ == "__main__":
    main()
