#!/usr/bin/env python3
"""Verify finite publication certificate records for the review bundle.

This script intentionally performs schema-level checks only. It verifies the
machine-readable certificate interface used by Proposition V in the supplement;
it does not rerun Lean, publication daemons, or Rule110 dynamic artifacts.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / "review_bundle"


def load_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8-sig"))
    except FileNotFoundError as exc:
        raise SystemExit(f"missing required file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid JSON in {path}: {exc}") from exc


def ensure(condition: bool, message: str, errors: list[str]) -> None:
    if not condition:
        errors.append(message)


def assigned_gates(kinds: list[str], dispatch: dict[str, list[str]]) -> set[str]:
    gates: set[str] = set()
    for kind in kinds:
        gates.update(dispatch[kind])
    return gates


def pointer_allowed(pointer: str, evidence_surface: list[str], accepted_patterns: list[str]) -> bool:
    if pointer in evidence_surface:
        return True
    if any(pointer.startswith(prefix[:-1]) for prefix in accepted_patterns if prefix.endswith("*")):
        return True
    prefixes = ("manifest:", "table:", "proposition:", "lemma:", "theorem:", "corollary:", "explicit-historical-boundary:")
    if pointer.startswith(prefixes):
        return True
    candidate = ROOT / pointer
    if candidate.exists():
        return True
    return False


def verify_records() -> list[str]:
    schema = load_json(BUNDLE / "certificate_schema.json")
    ledger = load_json(BUNDLE / "current_package_pass_records.json")
    interface_map = load_json(BUNDLE / "submission_interface_map.json")
    primary_claims = load_json(BUNDLE / "primary_claim_inventory.json")
    manifest = load_json(BUNDLE / "REVIEW_BUNDLE_MANIFEST.json")

    errors: list[str] = []
    domain = set(schema["claim_kind_domain"])
    levels = set(schema["evidence_levels"])
    dispatch = schema["gate_dispatch"]
    required_record_fields = set(schema["record_required_fields"])
    required_pass_fields = set(schema["pass_record_required_fields"])
    accepted_patterns = schema["accepted_artifact_patterns"]

    expected_manifest_keys = {
        "certificate_schema",
        "current_package_pass_records",
        "submission_interface_map",
        "primary_claim_inventory",
        "verifier_script",
        "verifier_run_log",
    }
    for key in sorted(expected_manifest_keys):
        ensure(key in manifest, f"manifest missing key {key}", errors)

    entries = ledger.get("entries", [])
    ensure(len(entries) == 6, "current package ledger must contain entries a1-a6", errors)
    seen_entries = {entry.get("entry") for entry in entries}
    ensure(seen_entries == {"a1", "a2", "a3", "a4", "a5", "a6"}, f"unexpected entries: {sorted(seen_entries)}", errors)

    for entry in entries:
        name = entry.get("entry", "<missing>")
        ensure(required_record_fields.issubset(entry.keys()), f"{name}: missing record fields", errors)
        kinds = entry.get("claim_kind_set", [])
        ensure(isinstance(kinds, list) and bool(kinds), f"{name}: claim_kind_set must be nonempty list", errors)
        ensure(set(kinds).issubset(domain), f"{name}: claim kinds outside domain", errors)
        level = entry.get("evidence_level")
        ensure(level in levels, f"{name}: invalid evidence_level {level}", errors)
        evidence_surface = entry.get("evidence_surface", [])
        ensure(isinstance(evidence_surface, list) and bool(evidence_surface), f"{name}: evidence_surface must be nonempty list", errors)
        pass_records = entry.get("pass_records", [])
        ensure(isinstance(pass_records, list) and bool(pass_records), f"{name}: pass_records must be nonempty list", errors)
        present_gates = {record.get("gate_name") for record in pass_records}
        needed_gates = assigned_gates(kinds, dispatch)
        ensure(needed_gates.issubset(present_gates), f"{name}: missing gates {sorted(needed_gates - present_gates)}", errors)
        has_discovery = "discovery" in kinds
        ensure((entry.get("discovery_interface") is not None) == has_discovery, f"{name}: discovery_interface presence mismatch", errors)
        boundary = entry.get("boundary", {})
        if level == "path-verified":
            ensure("no_command_run_assertion" in boundary, f"{name}: path-verified boundary missing no_command_run_assertion", errors)
        if level == "command-run":
            fields = set(boundary.get("command_run_fields", {}).keys())
            ensure({"command", "source_commit", "environment", "exit_code", "log_path"}.issubset(fields), f"{name}: command-run fields incomplete", errors)
        for record in pass_records:
            gate = record.get("gate_name", "<missing-gate>")
            ensure(required_pass_fields.issubset(record.keys()), f"{name}/{gate}: missing pass fields", errors)
            ensure(record.get("evidence_level") == level, f"{name}/{gate}: evidence_level mismatch", errors)
            ensure(record.get("decision") in schema["pass_decisions"], f"{name}/{gate}: invalid decision", errors)
            pointer = record.get("evidence_pointer", "")
            ensure(pointer_allowed(pointer, evidence_surface, accepted_patterns), f"{name}/{gate}: evidence pointer not allowed: {pointer}", errors)

    map_rows = interface_map.get("rows", [])
    ensure(len(map_rows) == 4, "submission interface map must contain four rows", errors)
    ensure({row.get("id") for row in map_rows} == {"sim1", "sim2", "sim3", "sim4"}, "submission interface map ids must be sim1-sim4", errors)

    claim_rows = primary_claims.get("rows", [])
    ensure(len(claim_rows) >= 12, "primary claim inventory must enumerate concrete primary assertions", errors)
    for row in claim_rows:
        row_id = row.get("id", "<missing>")
        ensure("claim" in row and row["claim"], f"{row_id}: missing claim", errors)
        ensure("status" in row and row["status"], f"{row_id}: missing status", errors)
        if not str(row.get("status", "")).startswith("non-load-bearing"):
            ensure("certificate" in row and row["certificate"], f"{row_id}: load-bearing row missing certificate", errors)
            ensure("evidence_level" in row and row["evidence_level"], f"{row_id}: load-bearing row missing evidence level", errors)

    return errors


def main() -> int:
    errors = verify_records()
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("certificate verification passed")
    print("checked: certificate_schema.json")
    print("checked: current_package_pass_records.json entries a1-a6")
    print("checked: submission_interface_map.json rows sim1-sim4")
    print("checked: primary_claim_inventory.json")
    print("boundary: schema-level verification only; no Lean, daemon, or Rule110 rerun")
    return 0


if __name__ == "__main__":
    sys.exit(main())
