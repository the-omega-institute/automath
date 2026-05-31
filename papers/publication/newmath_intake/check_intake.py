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
        "bibliography_scope_seed.md",
        "blocker_ledger.md",
        "current_declaration_map.md",
        "exact_statement_note.md",
        "groundcompiler_placement_decision.md",
        "promotion_checklist.md",
        "short_note_route_memo.md",
        "theorem_spine_selection.md",
        "upstream_packaging_work_order.md",
    },
    "bedc_rule110_finite_witness": {
        "artifact_rerun_packet.md",
        "current_static_status_map.md",
        "diagnostic_route_memo.md",
        "evidence_separation_note.md",
        "limitation_ledger.md",
        "promotion_checklist.md",
        "recheck_results.md",
        "trust_chain_template.md",
    },
}
P0_SEED_PROMOTION_CHECKLISTS = {
    "bedc_automation_pipeline": "promotion_checklist.md",
    "bedc_finite_kernel_calculus": "promotion_checklist.md",
    "bedc_rule110_finite_witness": "promotion_checklist.md",
}
CASE_INSENSITIVE_ACTIVE_TRIGGER_FILES = {
    "main.tex",
    "pipeline.md",
    "research_directive.md",
}
EXACT_ACTIVE_TRIGGER_FILES = {
    "ARTIFACT_INVENTORY.md",
    "BIB_SCOPE.md",
    "SOURCE_MAP.md",
    "THEOREM_LIST.md",
}


def iter_seed_dirs(seed_root: Path) -> list[Path]:
    if not seed_root.exists():
        return []
    return sorted(p for p in seed_root.iterdir() if p.is_dir())


def check_seed(seed_dir: Path, root: Path = ROOT) -> list[str]:
    problems: list[str] = []
    for path in seed_dir.rglob("*"):
        rel = path.relative_to(root).as_posix()
        if path.is_file() and (
            path.name.lower() in CASE_INSENSITIVE_ACTIVE_TRIGGER_FILES
            or path.name in EXACT_ACTIVE_TRIGGER_FILES
        ):
            problems.append(f"{rel}: active-paper trigger file is forbidden in intake")
        if path.is_dir() and path.name.startswith("2026_"):
            problems.append(f"{rel}: active-paper directory name is forbidden in intake")

    required_files = REQUIRED_SEED_FILES.get(seed_dir.name, set())
    for filename in sorted(required_files):
        if not (seed_dir / filename).is_file():
            rel = (seed_dir / filename).relative_to(root).as_posix()
            problems.append(f"{rel}: missing required P0 intake evidence file")
    return problems


def check_index_file(
    path: Path,
    required_phrases: list[str],
    *,
    root: Path = ROOT,
    publication_root: Path = PUBLICATION_ROOT,
) -> list[str]:
    try:
        display_path = path.relative_to(root).as_posix()
    except ValueError:
        display_path = path.relative_to(publication_root).as_posix()
    if not path.exists():
        return [f"{display_path}: missing required intake index"]
    text = path.read_text(encoding="utf-8", errors="replace")
    missing = [phrase for phrase in required_phrases if phrase not in text]
    return [
        f"{display_path}: missing boundary phrase {phrase!r}"
        for phrase in missing
    ]


def run_check(root: Path = ROOT) -> tuple[list[str], list[str]]:
    publication_root = root.parent
    seeds = root / "seeds"
    warnings: list[str] = []
    errors: list[str] = []

    seed_dirs = iter_seed_dirs(seeds)
    found = {p.name for p in seed_dirs}
    for name in sorted(KNOWN_SEEDS - found):
        errors.append(f"seeds/{name}: missing required intake seed directory")

    for seed_dir in seed_dirs:
        errors.extend(check_seed(seed_dir, root=root))
        checklist_name = P0_SEED_PROMOTION_CHECKLISTS.get(seed_dir.name)
        if checklist_name:
            errors.extend(
                check_index_file(
                    seed_dir / checklist_name,
                    ["promotion <seed> as <active_slug>"],
                    root=root,
                    publication_root=publication_root,
                )
            )

    errors.extend(
        check_index_file(
            root / "README.md",
            ["not an active paper pipeline", "must not run Stage A", "CURRENT_STATUS.md"],
            root=root,
            publication_root=publication_root,
        )
    )
    errors.extend(
        check_index_file(
            root / "CURRENT_STATUS.md",
            [
                "not a promotion command",
                "promotion <seed> as <active_slug>",
                "bedc_automation_pipeline",
                "bedc_finite_kernel_calculus",
                "bedc_rule110_finite_witness",
                "do not run Stage A",
            ],
            root=root,
            publication_root=publication_root,
        )
    )
    errors.extend(
        check_index_file(
            root / "BOARD.md",
            ["INTAKE-NOT-ACTIVE", "must not be picked up"],
            root=root,
            publication_root=publication_root,
        )
    )
    errors.extend(
        check_index_file(
            root / "P0_GATE_AUDIT.md",
            [
                "promotion-decision gate",
                "source-theorem gate",
                "artifact-rerun gate",
                "Do not promote",
                "must not promote or queue",
                "promotion <seed> as <active_slug>",
            ],
            root=root,
            publication_root=publication_root,
        )
    )
    errors.extend(
        check_index_file(
            root / "P0_DECISION_PACKET.md",
            [
                "not a promotion command",
                "bedc_automation_pipeline",
                "bedc_finite_kernel_calculus",
                "bedc_rule110_finite_witness",
                "promotion bedc_automation_pipeline as 2026_auditable_theory_to_paper_pipeline",
                "do not create `papers/publication/2026_*`",
            ],
            root=root,
            publication_root=publication_root,
        )
    )
    errors.extend(
        check_index_file(
            root / "AGENT_WORK_QUEUE.md",
            ["P0_GATE_AUDIT.md", "CURRENT_STATUS.md", "not a daemon queue"],
            root=root,
            publication_root=publication_root,
        )
    )
    errors.extend(
        check_index_file(
            root / "PROMOTION_HANDOFF.md",
            [
                "not a promotion command",
                "do not create any `papers/publication/2026_*`",
                "do not add `main.tex`",
                "do not add `PIPELINE.md`",
                "promotion <seed> as <active_slug>",
            ],
            root=root,
            publication_root=publication_root,
        )
    )
    seed_row_phrases = [
        f"newmath_intake/seeds/{name}" for name in sorted(KNOWN_SEEDS)
    ]
    errors.extend(
        check_index_file(
            publication_root / "PROGRAM_BOARD.md",
            seed_row_phrases + ["active paper track", "Stage A/P0-P7"],
            root=root,
            publication_root=publication_root,
        )
    )
    errors.extend(
        check_index_file(
            publication_root / "PROGRAM_BOARD_MACHINE.md",
            seed_row_phrases + ["INTAKE-NOT-ACTIVE", "do not run Stage A"],
            root=root,
            publication_root=publication_root,
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
