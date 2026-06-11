#!/usr/bin/env python3
import json
import pathlib
import re
import subprocess
import sys
import time


SESSION_DATE = "2026-06-11"
BRANCH = "codex/section-2-3-bridge-bundle"
DEFAULT_TIMEOUT_SEC = 60
VERDICT_RE = re.compile(r"^VERDICT:\s*(\S+)")

SCRIPT_PATH = pathlib.Path(__file__).resolve()
OUTREACH_DIR = SCRIPT_PATH.parent
REPO_ROOT = OUTREACH_DIR.parent.parent
OUTPUT_JSON = OUTREACH_DIR / "session_2026_06_11_regression_consolidator_output.json"

# The session request labels this as a 19-validator inventory, but the supplied
# concrete inventory contains 18 validator filenames. Keep the runnable source
# of truth as the listed filenames only.
VALIDATORS = [
    {
        "track": "T_32_K1",
        "target_dir": "tools/community-outreach/targets/cand_litt_common_finite_etale_cover",
        "validator": "check_litt3_20260610_jy4_group_law_validator.py",
        "expected_verdict": "PASS",
    },
    {
        "track": "E6_paper",
        "target_dir": "tools/community-outreach/targets/e6_cubic_threefolds_followup",
        "validator": "check_2604_20970_fermat_jacobian_stage1.py",
        "expected_verdict": "INCONCLUSIVE_NEED_PDF_DEEP_READ",
    },
    {
        "track": "E6_paper",
        "target_dir": "tools/community-outreach/targets/e6_cubic_threefolds_followup",
        "validator": "check_2604_20970_prop_3_6_corrected_rank_stage1_5.py",
        "expected_verdict": "PASS_RANK_50",
    },
    {
        "track": "E6_paper",
        "target_dir": "tools/community-outreach/targets/e6_cubic_threefolds_followup",
        "validator": "check_2604_20970_prop_3_6_multifield_stage1_6.py",
        "expected_verdict": "PASS_LARGE_PRIMES_50",
    },
    {
        "track": "E6_paper",
        "target_dir": "tools/community-outreach/targets/e6_cubic_threefolds_followup",
        "validator": "check_2604_20970_prop_3_6_equivariance_decomposition_stage1_7.py",
        "expected_verdict": "PASS_EQUIVARIANCE_RANK_50",
    },
    {
        "track": "E6_paper",
        "target_dir": "tools/community-outreach/targets/e6_cubic_threefolds_followup",
        "validator": "check_2604_20970_prop_3_6_full_G_block_certificate_stage2.py",
        "expected_verdict": "PASS_FULL_G_BLOCK_CERTIFICATE",
    },
    {
        "track": "E6_paper",
        "target_dir": "tools/community-outreach/targets/e6_cubic_threefolds_followup",
        "validator": "check_2604_20970_E6_branching_exclusion_stage3.py",
        "expected_verdict": "PASS_E_6_BRANCHING_EXCLUSION",
    },
    {
        "track": "Erdos_paper",
        "target_dir": "tools/community-outreach/targets/erdos_unit_distance_disproof_followup",
        "validator": "check_2605_20695_LT_construction_stage1.py",
        "expected_verdict": "PASS_WITH_INFRASTRUCTURE_NOTE",
    },
    {
        "track": "Erdos_paper",
        "target_dir": "tools/community-outreach/targets/erdos_unit_distance_disproof_followup",
        "validator": "check_2605_20695_LT_CM_extension_stage2_sympy.py",
        "expected_verdict": "PASS",
    },
    {
        "track": "Erdos_paper",
        "target_dir": "tools/community-outreach/targets/erdos_unit_distance_disproof_followup",
        "validator": "check_2605_20695_LT_genuine_layer_stage3.py",
        "expected_verdict": "FAIL",
    },
    {
        "track": "Erdos_paper",
        "target_dir": "tools/community-outreach/targets/erdos_unit_distance_disproof_followup",
        "validator": "check_2605_20695_CRT_translation_stage4.py",
        "expected_verdict": "PASS",
        "timeout_sec": 300,
    },
    {
        "track": "Erdos_paper",
        "target_dir": "tools/community-outreach/targets/erdos_unit_distance_disproof_followup",
        "validator": "check_2605_20695_split_prime_robustness_stage5.py",
        "expected_verdict": "PASS_SPLIT_PRIME_ROBUSTNESS",
    },
    {
        "track": "Erdos_paper",
        "target_dir": "tools/community-outreach/targets/erdos_unit_distance_disproof_followup",
        "validator": "check_2605_20695_split_prime_robustness_m8_stage5b.py",
        "expected_verdict": "PASS",
        "timeout_sec": 200,
    },
    {
        "track": "p_curvature_paper",
        "target_dir": "tools/community-outreach/targets/litt_pcurvature_followup",
        "validator": "check_2601_07933_genus2_serre_pairing_stage1.py",
        "expected_verdict": "FAIL_DEGENERATE_PAIRING",
    },
    {
        "track": "p_curvature_paper",
        "target_dir": "tools/community-outreach/targets/litt_pcurvature_followup",
        "validator": "check_2601_07933_genus2_serre_pairing_stage1b.py",
        "expected_verdict": "PASS_STAGE_1B",
    },
    {
        "track": "p_curvature_paper",
        "target_dir": "tools/community-outreach/targets/litt_pcurvature_followup",
        "validator": "check_2601_07933_genus2_serre_residue_certificate_stage2.py",
        "expected_verdict": "PASS_GENUINE_SERRE_RESIDUE_CERTIFICATE",
    },
    {
        "track": "p_curvature_paper",
        "target_dir": "tools/community-outreach/targets/litt_pcurvature_followup",
        "validator": "check_2601_07933_genus3_serre_residue_certificate_stage3.py",
        "expected_verdict": "PARTIAL_GATE_3_TRIVIAL_DEFORMATION_BOUNDARY",
    },
    {
        "track": "p_curvature_paper",
        "target_dir": "tools/community-outreach/targets/litt_pcurvature_followup",
        "validator": "check_2601_07933_genus3_deg7_serre_residue_certificate_stage4.py",
        "expected_verdict": "PASS_GENUINE_SERRE_RESIDUE_CERTIFICATE_G3_DEG7",
    },
]


def parse_verdict(output):
    verdict = None
    for line in output.splitlines():
        match = VERDICT_RE.match(line)
        if match:
            verdict = match.group(1)
    return verdict


def run_validator(entry, index, total):
    validator = entry["validator"]
    target_dir = REPO_ROOT / entry["target_dir"]
    timeout_sec = entry.get("timeout_sec", DEFAULT_TIMEOUT_SEC)
    print(f"[{index}/{total}] running {validator}...", flush=True)

    started = time.time()
    try:
        completed = subprocess.run(
            ["python3", validator],
            cwd=str(target_dir),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout_sec,
        )
        runtime_sec = round(time.time() - started, 3)
        actual_verdict = parse_verdict(completed.stdout)
        if actual_verdict is None:
            if completed.returncode != 0:
                actual_verdict = f"ERROR_EXIT_{completed.returncode}"
            else:
                actual_verdict = "NO_VERDICT_LINE"
    except subprocess.TimeoutExpired:
        runtime_sec = round(time.time() - started, 3)
        actual_verdict = "TIMEOUT"

    matches_expected = actual_verdict == entry["expected_verdict"]
    print(f"  -> {actual_verdict} ({runtime_sec}s)", flush=True)
    return {
        "track": entry["track"],
        "validator": validator,
        "expected_verdict": entry["expected_verdict"],
        "actual_verdict": actual_verdict,
        "matches_expected": matches_expected,
        "runtime_sec": runtime_sec,
    }


def build_per_track(rows):
    per_track = {}
    for entry in VALIDATORS:
        per_track.setdefault(entry["track"], {"count": 0, "matched": 0, "all_match": False})
        per_track[entry["track"]]["count"] += 1
    for row in rows:
        if row["matches_expected"]:
            per_track[row["track"]]["matched"] += 1
    for summary in per_track.values():
        summary["all_match"] = summary["count"] == summary["matched"]
    return per_track


def print_table(rows):
    headers = ["track", "validator", "expected", "actual", "match", "runtime_sec"]
    table_rows = []
    for row in rows:
        table_rows.append(
            [
                row["track"],
                truncate(row["validator"], 55),
                row["expected_verdict"],
                row["actual_verdict"],
                "yes" if row["matches_expected"] else "no",
                f"{row['runtime_sec']:.3f}",
            ]
        )
    widths = []
    for idx, header in enumerate(headers):
        widths.append(max(len(header), max(len(row[idx]) for row in table_rows)))
    print("")
    print(" | ".join(headers[idx].ljust(widths[idx]) for idx in range(len(headers))))
    print("-+-".join("-" * width for width in widths))
    for row in table_rows:
        print(" | ".join(row[idx].ljust(widths[idx]) for idx in range(len(headers))))


def truncate(value, limit):
    if len(value) <= limit:
        return value
    return value[: limit - 3] + "..."


def build_payload(rows):
    mismatch_count = sum(1 for row in rows if not row["matches_expected"])
    all_match_expected = mismatch_count == 0
    verdict = (
        "PASS_SESSION_REGRESSION"
        if all_match_expected
        else f"DIVERGENCE_{mismatch_count}_MISMATCHES"
    )
    return {
        "session_date": SESSION_DATE,
        "branch": BRANCH,
        "total_validators": len(VALIDATORS),
        "per_track": build_per_track(rows),
        "per_validator": rows,
        "all_match_expected": all_match_expected,
        "total_pass_count": sum(
            1 for row in rows if row["actual_verdict"].startswith("PASS")
        ),
        "total_partial_count": sum(
            1 for row in rows if row["actual_verdict"].startswith("PARTIAL")
        ),
        "total_fail_expected_count": sum(
            1
            for row in rows
            if row["expected_verdict"].startswith("FAIL") and row["matches_expected"]
        ),
        "verdict": verdict,
    }


def main():
    rows = []
    total = len(VALIDATORS)
    for index, entry in enumerate(VALIDATORS, 1):
        rows.append(run_validator(entry, index, total))

    payload = build_payload(rows)
    OUTPUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print_table(rows)
    print(f"FINAL VERDICT: {payload['verdict']}")
    return 0 if payload["all_match_expected"] else 1


if __name__ == "__main__":
    sys.exit(main())
