#!/usr/bin/env python3
"""Regenerate Stage-A replay manifest, certificate, and report artifacts.

The generated records intentionally avoid impossible cyclic SHA-256 claims:
the manifest gives exact digests for non-cyclic inputs and pointer rows for the
certificate, replay report, final digest manifest, and the manifest itself.
The final digest manifest is regenerated after this script and binds the output
bytes.
"""
from __future__ import annotations

import hashlib
import json
import platform
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / "review_bundle" / "stage_a_replay_regeneration_run.log"


COORDINATES = ["qinv", "qrgs", "qsrc", "qart", "qext", "qven"]
ACCEPTED = {
    "qinv": True,
    "qrgs": True,
    "qsrc": False,
    "qart": False,
    "qext": False,
    "qven": False,
}
REJECTED = ["qsrc", "qart", "qext", "qven"]
FINAL_DIGEST_POINTER = "review_bundle/FINAL_DIGESTS_SHA256.md"


def sha256_file(relative: str) -> str:
    digest = hashlib.sha256()
    with (ROOT / relative).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def git_head() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except Exception:
        return "unavailable"


def dump_json(path: str, data: dict) -> None:
    (ROOT / path).write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def canonical_json_bytes(data: dict) -> bytes:
    return (json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n").encode("utf-8")


def build_manifest() -> dict:
    exact_entries = [
        ("public", "submission_abstract.tex", "tex"),
        ("supplement", "main.tex", "tex"),
        ("inventory", "theorem_inventory.json", "json"),
        ("inventory", "theorem_inventory.md", "markdown"),
        ("schema", "stage_a_horn_schema.json", "json"),
        ("source", "source_interface_record.json", "json"),
        ("support", "stage_a_obstruction_basis.json", "json"),
        ("support", "stage_a_audit.json", "json"),
        ("venue", "review_bundle/VENUE_BIBLIOGRAPHY_LIVE_CHECK_2026-06-13.md", "markdown"),
        ("support", "review_bundle/theorem_environment_extraction_run.log", "log"),
        ("support", "review_bundle/certificate_verification_run.log", "log"),
        ("support", "review_bundle/source_interface_verification_run.log", "log"),
        ("support", "review_bundle/primary_claim_inventory_verification_run.log", "log"),
        ("support", "review_bundle/overlap_submission_order_verification_run.log", "log"),
        ("support", "review_bundle/stage_a_audit_verification_run.log", "log"),
        ("support", "review_bundle/regenerate_stage_a_replay_artifacts.py", "python"),
        ("support", "review_bundle/verify_overlap_submission_order.py", "python"),
        ("support", "review_bundle/verify_stage_a_audit.py", "python"),
    ]
    entries = [
        {"role": role, "path": path, "type": typ, "sha256": sha256_file(path)}
        for role, path, typ in exact_entries
    ]
    entries.extend(
        [
            {
                "role": "certificate",
                "path": "stage_a_horn_audit_certificate.json",
                "type": "json",
                "sha256": "cyclic-output-bound-by-final-digest-manifest",
            },
            {
                "role": "report",
                "path": "stage_a_replay_report.json",
                "type": "json",
                "sha256": "cyclic-output-bound-by-final-digest-manifest",
            },
            {
                "role": "digest",
                "path": FINAL_DIGEST_POINTER,
                "type": "markdown",
                "sha256": "terminal-digest-pointer-regenerated-last",
            },
            {
                "role": "support",
                "path": "review_bundle/stage_a_replay_regeneration_run.log",
                "type": "log",
                "sha256": "command-log-output-bound-by-final-digest-manifest",
            },
            {
                "role": "support",
                "path": "stage_a_manifest.json",
                "type": "json",
                "sha256": "self-referential-manifest-row-excluded-from-own-digest",
            },
            {
                "role": "support",
                "path": "review_bundle/",
                "type": "directory",
                "sha256": "directory-role-see-final-digest-manifest",
            },
        ]
    )
    entries = sorted(entries, key=lambda row: (row["role"], row["path"], row["type"], row["sha256"]))
    return {
        "schema_version": "stage-a-canonical-manifest-v2",
        "path_normalization": [
            "use forward slashes",
            "reject absolute paths",
            "reject dot-dot segments",
            "sort by role path type sha256",
        ],
        "excludes_unmanifested_paths": True,
        "cyclic_output_policy": "exact input digests are recorded here; cyclic outputs are bound by the final digest manifest regenerated last",
        "final_digest_pointer": FINAL_DIGEST_POINTER,
        "entries": entries,
        "coordinate_scope": {
            "qinv": "positive-local-inventory-byte-closure",
            "qrgs": "positive-fixed-stage-a-replay-only",
            "qsrc": "negative-no-fresh-formal-source-upgrade",
            "qart": "negative-no-dynamic-artifact-semantic-upgrade",
            "qext": "negative-no-external-upload-archive-upgrade",
            "qven": "negative-no-upload-time-venue-acceptance-upgrade",
        },
    }


RULE_IDS = [
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
]

ATOM_SORTS = [
    "public_surface",
    "supplement_surface",
    "support_surface",
    "schema_file",
    "inventory_row",
    "certificate_file",
    "report_file",
    "digest_row",
    "source_interface_row",
    "artifact_row",
    "venue_row",
    "upgrade_coordinate",
    "claim",
]


INPUT_ATOMS = [
    {"atom": "pubAbs", "sort": "public_surface", "path": "submission_abstract.tex"},
    {"atom": "suppMain", "sort": "supplement_surface", "path": "main.tex"},
    {"atom": "stageAHornSchema", "sort": "schema_file", "path": "stage_a_horn_schema.json"},
    {"atom": "stageAManifest", "sort": "support_surface", "path": "stage_a_manifest.json"},
    {"atom": "stageAHornCertificate", "sort": "certificate_file", "path": "stage_a_horn_audit_certificate.json"},
    {"atom": "stageAReplayReport", "sort": "report_file", "path": "stage_a_replay_report.json"},
    {"atom": "invJson", "sort": "inventory_row", "path": "theorem_inventory.json"},
    {"atom": "invMd", "sort": "inventory_row", "path": "theorem_inventory.md"},
    {"atom": "finalDigest", "sort": "digest_row", "path": FINAL_DIGEST_POINTER},
    {"atom": "srcInterface", "sort": "source_interface_row", "path": "source_interface_record.json"},
    {"atom": "caseArtifacts", "sort": "artifact_row", "path": "review_bundle/case_snapshots/"},
    {"atom": "venueReadiness", "sort": "venue_row", "path": "review_bundle/VENUE_BIBLIOGRAPHY_LIVE_CHECK_2026-06-13.md"},
    {
        "atom": "qrgsReplayUpgrade",
        "sort": "upgrade_coordinate",
        "coordinate": "qrgs",
        "bounded_to": "fixed Stage-A Horn schema, canonical manifest, replay certificate, replay report, final digest tuple",
    },
]


def build_certificate(manifest_digest: str) -> dict:
    return {
        "schema_version": "stage-a-replay-certificate-v2",
        "atom_sorts": ATOM_SORTS,
        "rule_ids": RULE_IDS,
        "input_atoms": INPUT_ATOMS,
        "derived_atoms": [
            "singleRouteSurface",
            "qinv",
            "localInventoryClosed",
            "qrgs",
            "boundedReplayRecordGateSoundness",
            "boundedSourceInterface",
            "boundedArtifactRows",
            "datedVenueReadiness",
            "routeSurfaceQuotient",
        ],
        "derivation_dags": {
            "qinv": {
                "node_id": "dag_qinv",
                "rule": "R1_inventory_closure_to_qinv",
                "premises": ["invJson", "invMd", "finalDigest"],
                "conclusion": "qinv",
            },
            "qrgs": {
                "node_id": "dag_qrgs",
                "rule": "R3_replay_tuple_to_qrgs",
                "premises": [
                    "stageAHornSchema",
                    "stageAManifest",
                    "stageAHornCertificate",
                    "stageAReplayReport",
                    "finalDigest",
                    "qrgsReplayUpgrade",
                ],
                "conclusion": "qrgs",
            },
            "routeSurfaceQuotient": {
                "node_id": "dag_route",
                "rule": "R12_route_surface_quotient",
                "premises": [
                    "pubAbs",
                    "suppMain",
                    "stageAHornSchema",
                    "stageAHornCertificate",
                    "stageAReplayReport",
                    "invJson",
                    "invMd",
                    "finalDigest",
                ],
                "conclusion": "routeSurfaceQuotient",
            },
        },
        "accepted_coordinates": ACCEPTED,
        "rejected_coordinates": REJECTED,
        "obstruction_basis": [
            {
                "coordinate": "qsrc",
                "minimal_missing_premises": ["freshFormalSourceUpgrade"],
                "certificate": "No fresh formal-source rebuild or axiom-purity audit upgrade atom is present.",
            },
            {
                "coordinate": "qart",
                "minimal_missing_premises": ["dynamicArtifactSemanticUpgrade"],
                "certificate": "No dynamic artifact-semantic validation upgrade atom is present.",
            },
            {
                "coordinate": "qext",
                "minimal_missing_premises": ["externalUploadArchiveUpgrade"],
                "certificate": "No external upload receipt or archive-equivalent byte-equality upgrade atom is present.",
            },
            {
                "coordinate": "qven",
                "minimal_missing_premises": ["uploadTimeVenueAcceptanceUpgrade"],
                "certificate": "No upload-time venue-compliance or venue-acceptance upgrade atom is present.",
            },
        ],
        "separating_models": {
            f"{coordinate}_false_model": {
                "preserves": ["qinv", "qrgs", "routeSurfaceQuotient", "admitted_support_atoms"],
                "falsifies": coordinate,
                "false_atoms": [missing, coordinate],
            }
            for coordinate, missing in {
                "qsrc": "freshFormalSourceUpgrade",
                "qart": "dynamicArtifactSemanticUpgrade",
                "qext": "externalUploadArchiveUpgrade",
                "qven": "uploadTimeVenueAcceptanceUpgrade",
            }.items()
        },
        "route_quotient": {
            "route": "CICM presentation-only",
            "public_surface": "submission_abstract.tex",
            "supplement_surface": "main.tex",
            "support_surfaces": [
                "stage_a_horn_schema.json",
                "stage_a_manifest.json",
                "stage_a_horn_audit_certificate.json",
                "stage_a_replay_report.json",
                "theorem_inventory.json",
                "theorem_inventory.md",
                "review_bundle/",
                "source_interface_record.json",
            ],
        },
        "public_surface": "submission_abstract.tex",
        "supplement_surface": "main.tex",
        "support_surfaces": [
            "stage_a_horn_schema.json",
            "stage_a_manifest.json",
            "stage_a_horn_audit_certificate.json",
            "stage_a_replay_report.json",
            "theorem_inventory.json",
            "theorem_inventory.md",
            "source_interface_record.json",
            "review_bundle/",
            FINAL_DIGEST_POINTER,
        ],
        "inventory_digest": {
            "digest_manifest": FINAL_DIGEST_POINTER,
            "evidence_level": "local digest row and fixed replay tuple only",
        },
        "digest_bindings": {
            "manifest_digest": manifest_digest,
            "schema_digest": sha256_file("stage_a_horn_schema.json"),
            "final_digest_pointer": FINAL_DIGEST_POINTER,
            "obstruction_basis_digest": sha256_file("stage_a_obstruction_basis.json"),
            "inventory_json_digest": sha256_file("theorem_inventory.json"),
            "inventory_md_digest": sha256_file("theorem_inventory.md"),
            "theorem_environment_extraction_log_digest": sha256_file("review_bundle/theorem_environment_extraction_run.log"),
            "certificate_verification_log_digest": sha256_file("review_bundle/certificate_verification_run.log"),
            "source_interface_verification_log_digest": sha256_file("review_bundle/source_interface_verification_run.log"),
            "primary_claim_inventory_verification_log_digest": sha256_file("review_bundle/primary_claim_inventory_verification_run.log"),
            "overlap_submission_order_verification_log_digest": sha256_file("review_bundle/overlap_submission_order_verification_run.log"),
            "stage_a_audit_verification_log_digest": sha256_file("review_bundle/stage_a_audit_verification_run.log"),
        },
        "final_digest_pointer": FINAL_DIGEST_POINTER,
        "negative_boundaries_preserved": [
            "no fresh Lean/BEDC rebuild",
            "no axiom-purity audit",
            "no dynamic artifact-semantic validation",
            "no external upload or archive-equivalent byte equality",
            "no upload-time venue compliance",
            "no venue acceptance",
            "no general pipeline implementation soundness",
        ],
    }


def build_report(manifest_digest: str, certificate_digest: str) -> dict:
    input_atoms_digest = sha256_bytes(canonical_json_bytes({"input_atoms": INPUT_ATOMS}))
    return {
        "schema_version": "stage-a-replay-report-v2",
        "manifest_digest": manifest_digest,
        "schema_digest": sha256_file("stage_a_horn_schema.json"),
        "certificate_digest": certificate_digest,
        "input_atoms_digest": input_atoms_digest,
        "accepted_coordinates": ACCEPTED,
        "rejected_coordinates": REJECTED,
        "derivation_root_ids": ["dag_qinv", "dag_qrgs", "dag_route"],
        "obstruction_root_ids": ["obs_qsrc", "obs_qart", "obs_qext", "obs_qven"],
        "separating_model_ids": [
            "qsrc_false_model",
            "qart_false_model",
            "qext_false_model",
            "qven_false_model",
        ],
        "route_quotient_id": "route_cicm_presentation_only_single_surface",
        "final_digest_pointer": FINAL_DIGEST_POINTER,
        "bounded_claim": "qrgs is accepted only for the fixed Stage-A Horn schema, canonical manifest, replay certificate, replay report, and digest-bound source bundle",
    }


def main() -> int:
    manifest = build_manifest()
    dump_json("stage_a_manifest.json", manifest)
    manifest_digest = sha256_file("stage_a_manifest.json")

    certificate = build_certificate(manifest_digest)
    dump_json("stage_a_horn_audit_certificate.json", certificate)
    certificate_digest = sha256_file("stage_a_horn_audit_certificate.json")

    report = build_report(manifest_digest, certificate_digest)
    dump_json("stage_a_replay_report.json", report)
    output = {
        "wrote": [
            "stage_a_manifest.json",
            "stage_a_horn_audit_certificate.json",
            "stage_a_replay_report.json",
            "review_bundle/stage_a_replay_regeneration_run.log",
        ],
        "manifest_digest": manifest_digest,
        "certificate_digest": certificate_digest,
        "report_digest": sha256_file("stage_a_replay_report.json"),
    }
    log_lines = [
        "command=python review_bundle/regenerate_stage_a_replay_artifacts.py",
        f"cwd={ROOT}",
        f"source_commit={git_head()}",
        f"environment=Python {platform.python_version()} on {platform.system()} {platform.release()}",
        "exit_code=0",
        "outputs=stage_a_manifest.json; stage_a_horn_audit_certificate.json; stage_a_replay_report.json",
        f"manifest_digest={manifest_digest}",
        f"certificate_digest={certificate_digest}",
        f"report_digest={sha256_file('stage_a_replay_report.json')}",
        "boundary=fixed Stage-A replay artifact regeneration only; no Lean/BEDC rebuild, dynamic artifact validation, external upload, or venue acceptance",
    ]
    LOG.write_text("\n".join(log_lines) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
