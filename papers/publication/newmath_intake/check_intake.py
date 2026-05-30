#!/usr/bin/env python3
"""Deterministic guard for newmath intake seeds.

The newmath intake area is intentionally not an active paper pipeline.  This
script fails if a seed contains active-paper trigger files or if the intake
index no longer states the non-active boundary.
"""

from __future__ import annotations

import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parent
PUBLICATION_ROOT = ROOT.parent
SEEDS = ROOT / "seeds"
REQUIRED_SEEDS = {
    "bedc_automation_pipeline",
    "bedc_finite_kernel_calculus",
    "bedc_rule110_finite_witness",
}
KNOWN_P1_SEEDS = {
    "metacic_closed_normal_consistency",
    "observer_state_semantics",
}
KNOWN_SEEDS = REQUIRED_SEEDS | KNOWN_P1_SEEDS
REQUIRED_SEED_FILES = {
    "bedc_automation_pipeline": {
        "active_creation_dry_run.md",
        "case_table_seed.md",
        "cicm_two_page_packet.md",
        "promotion_checklist.md",
        "source_decision_note.md",
        "source_verification_note.md",
    },
    "bedc_finite_kernel_calculus": {
        "current_declaration_map.md",
        "exact_statement_note.md",
        "groundcompiler_placement_decision.md",
        "promotion_checklist.md",
        "theorem_spine_selection.md",
        "upstream_packaging_work_order.md",
    },
    "bedc_rule110_finite_witness": {
        "artifact_rerun_packet.md",
        "current_static_status_map.md",
        "limitation_ledger.md",
        "promotion_checklist.md",
        "recheck_results.md",
    },
}
ACTIVE_TRIGGER_FILES = {"main.tex", "PIPELINE.md"}


def iter_seed_dirs(seed_root: Path) -> list[Path]:
    if not seed_root.exists():
        return []
    return sorted(p for p in seed_root.iterdir() if p.is_dir())


def check_seed(seed_dir: Path) -> list[str]:
    problems: list[str] = []
    for path in seed_dir.rglob("*"):
        rel = path.relative_to(ROOT).as_posix()
        if path.is_file() and path.name in ACTIVE_TRIGGER_FILES:
            problems.append(f"{rel}: active-paper trigger file is forbidden in intake")
        if path.is_dir() and path.name.startswith("2026_"):
            problems.append(f"{rel}: active-paper directory name is forbidden in intake")

    required_files = REQUIRED_SEED_FILES.get(seed_dir.name, set())
    for filename in sorted(required_files):
        if not (seed_dir / filename).is_file():
            rel = (seed_dir / filename).relative_to(ROOT).as_posix()
            problems.append(f"{rel}: missing required P0 intake evidence file")
    return problems


def check_index_file(path: Path, required_phrases: list[str]) -> list[str]:
    try:
        display_path = path.relative_to(ROOT).as_posix()
    except ValueError:
        display_path = path.relative_to(PUBLICATION_ROOT).as_posix()
    if not path.exists():
        return [f"{display_path}: missing required intake index"]
    text = path.read_text(encoding="utf-8", errors="replace")
    missing = [phrase for phrase in required_phrases if phrase not in text]
    return [
        f"{display_path}: missing boundary phrase {phrase!r}"
        for phrase in missing
    ]


def run_check() -> tuple[list[str], list[str]]:
    warnings: list[str] = []
    errors: list[str] = []

    seed_dirs = iter_seed_dirs(SEEDS)
    found = {p.name for p in seed_dirs}
    for name in sorted(KNOWN_SEEDS - found):
        errors.append(f"seeds/{name}: missing required intake seed directory")

    for seed_dir in seed_dirs:
        errors.extend(check_seed(seed_dir))

    errors.extend(
        check_index_file(
            ROOT / "README.md",
            ["not an active paper pipeline", "must not run Stage A"],
        )
    )
    errors.extend(
        check_index_file(
            ROOT / "BOARD.md",
            ["INTAKE-NOT-ACTIVE", "must not be picked up"],
        )
    )
    errors.extend(
        check_index_file(
            ROOT / "P0_GATE_AUDIT.md",
            [
                "promotion-decision gate",
                "source-theorem gate",
                "artifact-rerun gate",
                "Do not promote",
                "must not promote or queue",
            ],
        )
    )
    errors.extend(
        check_index_file(
            ROOT / "AGENT_WORK_QUEUE.md",
            ["P0_GATE_AUDIT.md", "not a daemon queue"],
        )
    )
    seed_row_phrases = [
        f"newmath_intake/seeds/{name}" for name in sorted(KNOWN_SEEDS)
    ]
    errors.extend(
        check_index_file(
            PUBLICATION_ROOT / "PROGRAM_BOARD.md",
            seed_row_phrases + ["active paper track", "Stage A/P0-P7"],
        )
    )
    errors.extend(
        check_index_file(
            PUBLICATION_ROOT / "PROGRAM_BOARD_MACHINE.md",
            seed_row_phrases + ["INTAKE-NOT-ACTIVE", "do not run Stage A"],
        )
    )

    for seed_dir in seed_dirs:
        if seed_dir.name not in KNOWN_SEEDS:
            warnings.append(
                f"seeds/{seed_dir.name}: unrecognized intake seed; verify priority manually"
            )

    return errors, warnings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true", help="only print failures")
    args = parser.parse_args()

    errors, warnings = run_check()

    if not args.quiet:
        print(f"newmath_intake={ROOT}")
        print(f"seed_count={len(iter_seed_dirs(SEEDS))}")

    for warning in warnings:
        print(f"WARN: {warning}")
    for error in errors:
        print(f"ERROR: {error}")

    if errors:
        return 1
    if not args.quiet:
        print("OK: newmath intake seeds are not active paper tracks")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
