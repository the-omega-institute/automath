#!/usr/bin/env python3
"""Replay the submitted Stage-A Horn audit certificate.

This script is intentionally a small checker, not a generator.  It reads the
paper-local files in certificates/, compiles manifest rows to typed atoms,
forward-chains the submitted Horn rules, checks the digest table, and verifies
that the recomputed six-coordinate vector is exactly the vector displayed in
the replay report.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / "certificates"

MANIFEST = CERT / "stage_a_manifest.json"
SCHEMA = CERT / "stage_a_horn_schema.json"
CERTIFICATE = CERT / "stage_a_horn_audit_certificate.json"
REPORT = CERT / "stage_a_replay_report.json"
DIGEST_TABLE = CERT / "stage_a_digest_table.json"
MAIN_TEX = ROOT / "main.tex"
INVENTORY_JSON = ROOT / "theorem_inventory.json"
INVENTORY_MD = ROOT / "theorem_inventory.md"
STATIC_SOURCE_LABEL_SCAN = CERT / "static_source_label_scan.json"

COORDINATES = ["qinv", "qrgs", "qsrc", "qart", "qext", "qven"]
REQUIRED_DIGEST_PATHS = {
    "certificates/stage_a_manifest.json",
    "certificates/stage_a_horn_schema.json",
    "certificates/stage_a_horn_audit_certificate.json",
    "certificates/stage_a_replay_report.json",
    "certificates/stage_a_replay_environment.json",
    "certificates/replay_stage_a_audit.py",
    "certificates/replay_case_rows.py",
    "certificates/case_rows_expected.json",
    "certificates/scan_tex_source_labels.py",
    "certificates/static_source_label_scan.json",
    "review_bundle/certificate_schema.json",
    "review_bundle/current_package_pass_records.json",
    "review_bundle/submission_interface_map.json",
    "review_bundle/primary_claim_inventory.json",
    "review_bundle/REVIEW_BUNDLE_MANIFEST.json",
}
EXPECTED_NEGATIVE_UPGRADES = {
    "qsrc": "freshFormalSourceUpgrade",
    "qart": "dynamicArtifactSemanticUpgrade",
    "qext": "externalUploadArchiveUpgrade",
    "qven": "uploadTimeVenueAcceptanceUpgrade",
}
ENV_PATTERN = re.compile(r"\\begin\{(definition|lemma|proposition|theorem|corollary)\}(?:\[([^\]]*)\])?")
LABEL_PATTERN = re.compile(r"\\label\{([^}]*)\}")
COORDINATE_RULES = {
    "qinv": "R1_inventory_closure_to_qinv",
    "qrgs": "R3_replay_tuple_to_qrgs",
    "qsrc": "R5_qsrc_upgrade_to_qsrc",
    "qart": "R6_qart_upgrade_to_qart",
    "qext": "R7_qext_upgrade_to_qext",
    "qven": "R8_qven_upgrade_to_qven",
}
EXPECTED_POSITIVE_PREMISES = {
    "qinv": ["mainTex", "invJson", "invMd", "finalDigest", "scanOK"],
    "qrgs": [
        "stageAHornSchema",
        "stageAManifest",
        "stageAHornCertificate",
        "stageAReplayReport",
        "finalDigest",
        "RecordGateOK",
        "CertDAGOK",
        "DigestOKstage_a",
        "ScriptOKstage_a",
        "qrgsReplayUpgrade",
    ],
}


def load_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise SystemExit(f"missing required replay artifact: {rel(path)}") from exc
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid JSON in {rel(path)}: {exc}") from exc


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT.resolve()).as_posix()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def check_relative(path_text: str) -> None:
    path = Path(path_text)
    if path.is_absolute():
        raise SystemExit(f"absolute path rejected by atom compiler: {path_text}")
    if "\\" in path_text:
        raise SystemExit(f"backslash path rejected by atom compiler: {path_text}")
    if ".." in path.parts:
        raise SystemExit(f"dot-dot path rejected by atom compiler: {path_text}")


def check_digest_table(table: dict) -> dict[str, str]:
    rows = table.get("rows")
    if not isinstance(rows, list):
        raise SystemExit("digest table rows must be a list")
    seen: dict[str, str] = {}
    for row in rows:
        path_text = row.get("path")
        expected = row.get("sha256")
        if not isinstance(path_text, str) or not isinstance(expected, str):
            raise SystemExit("digest row must contain string path and sha256")
        check_relative(path_text)
        if path_text == rel(DIGEST_TABLE):
            raise SystemExit("digest table must not self-bind")
        actual = sha256_file(ROOT / path_text)
        if actual != expected:
            raise SystemExit(
                f"digest mismatch for {path_text}: expected {expected}, got {actual}"
            )
        seen[path_text] = expected
    missing = sorted(REQUIRED_DIGEST_PATHS - set(seen))
    if missing:
        raise SystemExit(f"digest table missing rows: {missing}")
    return seen


def inventory_labels(value: object) -> set[str]:
    labels: set[str] = set()
    if isinstance(value, dict):
        for key, child in value.items():
            if isinstance(key, str) and "label" in key.lower() and isinstance(child, str):
                labels |= set(re.findall(r"\b(?:def|lem|prop|thm|cor):[A-Za-z0-9_.:-]+", child))
            labels |= inventory_labels(child)
    elif isinstance(value, list):
        for child in value:
            labels |= inventory_labels(child)
    elif isinstance(value, str):
        labels |= set(re.findall(r"\b(?:def|lem|prop|thm|cor):[A-Za-z0-9_.:-]+", value))
    return labels


def scan_tex_labels(path: Path) -> set[str]:
    try:
        text = path.read_bytes().decode("utf-8-sig")
    except UnicodeDecodeError as exc:
        raise SystemExit(f"main.tex is not utf-8-sig decodable: {exc}") from exc
    labels: list[str] = []
    lines = text.splitlines()
    for index, line in enumerate(lines):
        match = ENV_PATTERN.search(line)
        if not match:
            continue
        env_name = match.group(1)
        end_pattern = f"\\end{{{env_name}}}"
        end_index = len(lines) - 1
        for candidate in range(index, len(lines)):
            if end_pattern in lines[candidate]:
                end_index = candidate
                break
        body = "\n".join(lines[index : end_index + 1])
        label_match = LABEL_PATTERN.search(body)
        if not label_match:
            raise SystemExit(f"ScanOK failed: unlabeled {env_name} beginning on line {index + 1}")
        labels.append(label_match.group(1))
    if len(labels) != len(set(labels)):
        raise SystemExit("ScanOK failed: duplicate theorem-like labels in main.tex")
    return set(labels)


def check_scan_ok() -> None:
    scanned = scan_tex_labels(MAIN_TEX)
    inventory_json = load_json(INVENTORY_JSON)
    static_scan = load_json(STATIC_SOURCE_LABEL_SCAN)
    inventory_text = INVENTORY_MD.read_text(encoding="utf-8-sig")
    json_labels = inventory_labels(inventory_json)
    scan_labels = inventory_labels(static_scan)
    md_labels = set(re.findall(r"\\label\{([^}]*)\}|label[:= ]+([A-Za-z0-9_:\-.]+)", inventory_text))
    flat_md_labels = {item for pair in md_labels for item in pair if item}
    inventory = json_labels | scan_labels | flat_md_labels
    if not scanned:
        raise SystemExit("ScanOK failed: no theorem-like labels detected")
    missing = sorted(scanned - inventory)
    if missing:
        raise SystemExit(f"ScanOK failed: labels absent from digest-bound inventory: {missing[:10]}")


def check_record_gate_ok(schema: dict, manifest: dict, report: dict) -> None:
    rule_ids = {rule.get("rule_id") for rule in schema.get("rules", [])}
    expected_rule_ids = {
        "R0_single_route_surface",
        "R1_inventory_closure_to_qinv",
        "R2_qinv_to_local_inventory_closed",
        "R3_replay_tuple_to_qrgs",
        "R4_qrgs_to_bounded_record_gate_soundness",
        "R5_qsrc_upgrade_to_qsrc",
        "R6_qart_upgrade_to_qart",
        "R7_qext_upgrade_to_qext",
        "R8_qven_upgrade_to_qven",
        "R9_source_interface_to_bounded_source_interface",
        "R10_case_artifacts_to_bounded_artifact_rows",
        "R11_venue_readiness_to_dated_venue_readiness",
        "R12_route_surface_quotient",
    }
    if rule_ids != expected_rule_ids:
        raise SystemExit("RecordGateOK failed: Stage-A rule-id set mismatch")
    atoms = [row.get("atom") for row in manifest.get("compiler_rows", [])]
    if len(atoms) != len(set(atoms)):
        raise SystemExit("RecordGateOK failed: duplicate manifest atoms")
    accepted = report.get("accepted_coordinates")
    if set(accepted) != set(COORDINATES):
        raise SystemExit("RecordGateOK failed: report coordinate set mismatch")


def check_schema_premises(schema: dict) -> None:
    rules = {rule.get("conclusion"): rule for rule in schema.get("rules", [])}
    for coordinate, rule_id in COORDINATE_RULES.items():
        rule = rules.get(coordinate)
        if rule is None or rule.get("rule_id") != rule_id:
            raise SystemExit(f"RecordGateOK failed: coordinate rule missing for {coordinate}")
    for coordinate, premises in EXPECTED_POSITIVE_PREMISES.items():
        if rules[coordinate].get("premises") != premises:
            raise SystemExit(f"RecordGateOK failed: premise list mismatch for {coordinate}")


def check_scriptok_assumption(manifest: dict) -> None:
    rows = manifest.get("compiler_rows", [])
    matches = [row for row in rows if row.get("atom") == "ScriptOKstage_a"]
    if len(matches) != 1 or matches[0].get("sort") != "tcb_assumption":
        raise SystemExit("ScriptOKstage_a must be an explicit single TCB assumption row")
    if matches[0].get("path") != "certificates/replay_stage_a_audit.py":
        raise SystemExit("ScriptOKstage_a row must name the Stage-A replay script")


def compile_atoms(manifest: dict, certificate: dict) -> set[str]:
    rows = manifest.get("compiler_rows")
    if not isinstance(rows, list):
        raise SystemExit("manifest compiler_rows must be a list")
    atoms: set[str] = set()
    declared_sorts = set(manifest.get("coordinate_scope", {}).keys())
    if declared_sorts != set(COORDINATES):
        raise SystemExit("manifest coordinate_scope must name exactly the six coordinates")
    for row in rows:
        atom = row.get("atom")
        sort = row.get("sort")
        path_text = row.get("path")
        if not isinstance(atom, str) or not isinstance(sort, str):
            raise SystemExit("compiler row must contain atom and sort strings")
        if path_text is not None:
            if not isinstance(path_text, str):
                raise SystemExit(f"compiler row path must be a string: {atom}")
            check_relative(path_text)
        atoms.add(atom)
    certified_inputs = certificate.get("input_atoms")
    if set(certified_inputs) != atoms:
        raise SystemExit(
            "certificate input_atoms differ from manifest-compiled atoms: "
            f"manifest={sorted(atoms)}, certificate={sorted(certified_inputs)}"
        )
    return atoms


def forward_chain(schema: dict, atoms: set[str]) -> tuple[set[str], list[dict]]:
    rules = schema.get("rules")
    if not isinstance(rules, list):
        raise SystemExit("schema rules must be a list")
    closure = set(atoms)
    proof: list[dict] = []
    changed = True
    while changed:
        changed = False
        for rule in sorted(rules, key=lambda item: item["rule_id"]):
            premises = rule.get("premises")
            conclusion = rule.get("conclusion")
            rule_id = rule.get("rule_id")
            if not isinstance(premises, list) or not isinstance(conclusion, str):
                raise SystemExit(f"malformed rule: {rule}")
            if all(premise in closure for premise in premises) and conclusion not in closure:
                closure.add(conclusion)
                proof.append(
                    {
                        "rule": rule_id,
                        "premises": premises,
                        "conclusion": conclusion,
                    }
                )
                changed = True
    return closure, proof


def validate_certificate(certificate: dict, closure: set[str], proof: list[dict]) -> None:
    proof_by_conclusion = {node["conclusion"]: node for node in proof}
    for coordinate in ["qinv", "qrgs"]:
        dag = certificate.get("derivation_dags", {}).get(coordinate)
        if not dag:
            raise SystemExit(f"certificate missing derivation DAG for {coordinate}")
        if dag.get("conclusion") != coordinate:
            raise SystemExit(f"certificate DAG conclusion mismatch for {coordinate}")
        node = proof_by_conclusion.get(coordinate)
        if node is None:
            raise SystemExit(f"replay did not derive {coordinate}")
        if node["rule"] != dag.get("rule") or node["premises"] != dag.get("premises"):
            raise SystemExit(f"replayed proof node differs from certificate DAG for {coordinate}")
    for coordinate, missing_atom in EXPECTED_NEGATIVE_UPGRADES.items():
        if missing_atom in closure or coordinate in closure:
            raise SystemExit(f"negative coordinate unexpectedly derived: {coordinate}")
        roots = [
            row
            for row in certificate.get("obstruction_basis", [])
            if row.get("coordinate") == coordinate
        ]
        if len(roots) != 1 or roots[0].get("minimal_missing_premises") != [missing_atom]:
            raise SystemExit(f"certificate missing minimal obstruction for {coordinate}")


def main() -> int:
    manifest = load_json(MANIFEST)
    schema = load_json(SCHEMA)
    certificate = load_json(CERTIFICATE)
    report = load_json(REPORT)
    digest_table = load_json(DIGEST_TABLE)

    digests = check_digest_table(digest_table)
    check_scan_ok()
    check_record_gate_ok(schema, manifest, report)
    check_schema_premises(schema)
    check_scriptok_assumption(manifest)
    atoms = compile_atoms(manifest, certificate)
    closure, proof = forward_chain(schema, atoms)
    validate_certificate(certificate, closure, proof)

    recomputed = {coordinate: coordinate in closure for coordinate in COORDINATES}
    displayed = report.get("accepted_coordinates")
    certified = certificate.get("accepted_coordinates")
    if recomputed != displayed:
        raise SystemExit(f"recomputed vector differs from replay report: {recomputed} != {displayed}")
    if recomputed != certified:
        raise SystemExit(f"recomputed vector differs from certificate: {recomputed} != {certified}")

    summary = {
        "command": "python certificates/replay_stage_a_audit.py",
        "digest_rows_checked": sorted(digests),
        "compiled_input_atoms": sorted(atoms),
        "derived_nodes": proof,
        "recomputed_vector": recomputed,
        "status": "accepted",
        "boundary": "fixed Stage-A Horn replay only; no source rebuild, artifact semantics, external upload, venue, or implementation-soundness upgrade",
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
