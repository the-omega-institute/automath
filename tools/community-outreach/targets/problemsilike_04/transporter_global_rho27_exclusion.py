#!/usr/bin/env python3
"""Closure-grade transporter audit for the rho_odd_theta_27 route.

This script is intentionally conservative.  It verifies the required local
artifacts and records the formal transporter argument, but it does not promote
the route-scoped chi=e0 obstruction to a global theorem when the local corpus
itself marks the source-side W_chi naturality bridge as missing.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


TARGET_DIR = Path(__file__).resolve().parent
OUTPUT = TARGET_DIR / "transporter_global_rho27_exclusion_output.json"

REQUIRED = {
    "orbit_script": "check_20260525_728_sector_orbitals.py",
    "route_scope": "4fbd_kp2_route_scope_20260525_output.json",
    "sbar_decomposition": "sbar_rho_irrep_decomposition_20260525_output.json",
    "hom_packet_matrices": "hom_s_w_rho_from_packet_matrices_20260525_output.json",
    "stable_points": "stable_points.md",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def closest_matches(name: str) -> list[str]:
    stem_parts = [part for part in name.replace(".", "_").split("_") if part]
    scored: list[tuple[int, str]] = []
    for path in TARGET_DIR.iterdir():
        if not path.is_file():
            continue
        score = sum(1 for part in stem_parts if part in path.name)
        if score:
            scored.append((score, path.name))
    scored.sort(key=lambda item: (-item[0], item[1]))
    return [name for _, name in scored[:8]]


def require_artifacts() -> tuple[dict[str, Path], list[dict[str, Any]]]:
    paths: dict[str, Path] = {}
    missing: list[dict[str, Any]] = []
    for key, filename in REQUIRED.items():
        path = TARGET_DIR / filename
        if path.exists():
            paths[key] = path
        else:
            missing.append(
                {
                    "key": key,
                    "expected_filename": filename,
                    "closest_matches": closest_matches(filename),
                }
            )
    return paths, missing


def phase_a_summaries(paths: dict[str, Path]) -> dict[str, dict[str, str]]:
    route = load_json(paths["route_scope"])
    sbar = load_json(paths["sbar_decomposition"])
    hom = load_json(paths["hom_packet_matrices"])
    orbit_output_path = TARGET_DIR / "sector_728_orbitals_20260525_output.json"
    orbit_summary = (
        "Orbit checker for the 728 nonzero F_3^6 covectors; its paired output "
        "records one 728-point orbit and five ordered-pair orbitals."
    )
    if orbit_output_path.exists():
        orbit_output = load_json(orbit_output_path)
        orbit_summary = (
            "Orbit checker for the 728 nonzero F_3^6 covectors; paired output "
            f"has point_action_transitive={orbit_output.get('point_action_transitive')} "
            f"and orbit size {orbit_output.get('eight_transvection_point_orbit_size')}."
        )

    return {
        paths["orbit_script"].name: {
            "sha256": sha256(paths["orbit_script"]),
            "summary": orbit_summary,
        },
        paths["route_scope"].name: {
            "sha256": sha256(paths["route_scope"]),
            "summary": (
                "Certifies the displayed KP2 route-scoped rho_odd_theta_27 "
                f"Hom obstruction with dim Hom S(W,rho)="
                f"{route.get('direct_four_generator_intertwiner_cross_check', {}).get('dim_Hom_S_W_to_rho')} "
                f"and status {route.get('status')}."
            ),
        },
        paths["sbar_decomposition"].name: {
            "sha256": sha256(paths["sbar_decomposition"]),
            "summary": (
                "Decomposes rho_odd_theta_27 restricted to Sbar ~= S3 x S3 "
                f"with weighted dimension {sbar.get('dimension_check')}."
            ),
        },
        paths["hom_packet_matrices"].name: {
            "sha256": sha256(paths["hom_packet_matrices"]),
            "summary": (
                "Solves exact intertwiner equations for the displayed W matrices "
                f"and finds dim Hom S(W,rho)={hom.get('dim_Hom_S_W_to_rho')}."
            ),
        },
        paths["stable_points"].name: {
            "sha256": sha256(paths["stable_points"]),
            "summary": (
                "Records the active T-44 provenance constraints and the ban on "
                "extending transporter propagation on current Oracle-scaffold matrices."
            ),
        },
    }


def route_scope_hom_zero(route: dict[str, Any]) -> bool:
    direct = route.get("direct_four_generator_intertwiner_cross_check", {})
    return (
        route.get("status") == "PASS_4FBD_ROUTE_SCOPED_KP2_RHO27_EXCLUSION"
        and route.get("route_scoped_exclusion_certified") is True
        and direct.get("dim_Hom_S_W_to_rho") == 0
    )


def build_phase_b_argument() -> str:
    return (
        "Conditional transporter argument: the eight-transvection Sp_6(F_3) "
        "calculation verifies that the 728 nonzero characters of (Z/3)^6 form "
        "one orbit, so for every nonzero chi there is a transporter g with "
        "g.e_0=chi. If the level-3 Prym fiber construction is Sp_6(F_3)-"
        "equivariant, so that the deck-group action commutes with the Sp_6 "
        "action and the transporter identifies W_{e_0} with W_{g.e_0}, and if "
        "rho_odd_theta_27 is intrinsic rather than chosen relative to chi, then "
        "conjugation gives Hom_H(W_chi, rho_27|_H) isomorphic to "
        "Hom_{gHg^-1}(W_{g.chi}, rho_27|_{gHg^-1}). This isomorphism preserves "
        "dimension, so a verified dim Hom at chi=e_0 equal to 0 would imply "
        "dim Hom equal to 0 for every one of the 728 nonzero characters."
    )


def assess_equivariance_gap(
    route: dict[str, Any],
    hom: dict[str, Any],
    stable_text: str,
) -> tuple[bool, list[str]]:
    reasons: list[str] = []

    if route.get("source_derivation_certified") is False:
        reasons.append(
            "4fbd route-scope artifact sets source_derivation_certified=false."
        )
    if route.get("global_kp_exclusion_certified") is False:
        reasons.append(
            "4fbd route-scope artifact sets global_kp_exclusion_certified=false."
        )
    route_noncerts = " ".join(route.get("does_not_certify", []))
    if "source-derived" in route_noncerts or "globally excluded" in route_noncerts:
        reasons.append(
            "4fbd route-scope artifact explicitly does not certify source-derived W matrices or a global exclusion."
        )
    hom_noncerts = " ".join(hom.get("does_not_certify", []))
    if "actual KP2 Prym fiber action" in hom_noncerts or "full H-character" in hom_noncerts:
        reasons.append(
            "packet-matrix Hom artifact explicitly does not certify the actual Prym fiber action."
        )
    if "Do NOT extend the BFS transporter / chi propagation chain further" in stable_text:
        reasons.append(
            "stable_points.md bans extending the BFS transporter/chi propagation chain on current Oracle-scaffold matrices."
        )
    if "W_chi level-3 Fox/Prym fiber 4×4 matrices" in stable_text and "NO citation" in stable_text:
        reasons.append(
            "stable_points.md records that W_chi level-3 Fox/Prym matrices lack a primary-source citation."
        )

    return bool(reasons), reasons


def emit_payload(payload: dict[str, Any]) -> None:
    evidence_text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    evidence_sha = hashlib.sha256(evidence_text.encode()).hexdigest()
    payload["evidence_sha"] = evidence_sha
    OUTPUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def main() -> int:
    paths, missing = require_artifacts()
    generated_utc = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")

    if missing:
        payload: dict[str, Any] = {
            "generated_utc": generated_utc,
            "phase_a": {},
            "phase_a_missing": missing,
            "phase_b_argument": "",
            "phase_b_equivariance_assessment": {
                "sound": False,
                "reasons": ["Required Phase A artifact missing; no equivariance assessment performed."],
            },
            "phase_c_samples": [],
            "phase_d_verdict": "INSUFFICIENT_DATA",
        }
        emit_payload(payload)
        print("INSUFFICIENT_DATA")
        print(f"output={OUTPUT}")
        return 0

    route = load_json(paths["route_scope"])
    hom = load_json(paths["hom_packet_matrices"])
    stable_text = paths["stable_points"].read_text(errors="replace")

    phase_a = phase_a_summaries(paths)
    phase_b_argument = build_phase_b_argument()
    hom_zero = route_scope_hom_zero(route)
    has_gap, gap_reasons = assess_equivariance_gap(route, hom, stable_text)

    if has_gap:
        verdict = "EQUIVARIANCE_GAP"
        samples: list[dict[str, Any]] = []
        sample_note = (
            "Transporter sampling intentionally skipped: the local corpus marks "
            "source-side W_chi equivariance/naturality as unproved and bans "
            "extending the current transporter chain."
        )
    elif not hom_zero:
        verdict = "INSUFFICIENT_DATA"
        samples = []
        sample_note = "Route-scoped chi=e0 Hom=0 was not confirmed from 4fbd output."
    else:
        verdict = "GLOBAL_EXCLUSION_VERIFIED"
        samples = []
        sample_note = (
            "No gap detected; transporter sampling would run here. This branch is "
            "not reached for the present artifact set."
        )

    payload = {
        "generated_utc": generated_utc,
        "phase_a": phase_a,
        "phase_a_missing": [],
        "phase_b_argument": phase_b_argument,
        "phase_b_equivariance_assessment": {
            "sound": not has_gap and hom_zero,
            "chi_e0_route_scoped_hom_zero_confirmed": hom_zero,
            "reasons": gap_reasons,
        },
        "phase_c_samples": samples,
        "phase_c_note": sample_note,
        "phase_d_verdict": verdict,
    }
    emit_payload(payload)

    print(verdict)
    print(f"chi_e0_route_scoped_hom_zero_confirmed={hom_zero}")
    if gap_reasons:
        print("gap_reasons:")
        for reason in gap_reasons:
            print(f"- {reason}")
    print(f"output={OUTPUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
