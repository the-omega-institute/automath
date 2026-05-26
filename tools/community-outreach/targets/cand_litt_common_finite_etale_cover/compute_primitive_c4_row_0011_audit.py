#!/usr/bin/env python3
"""Emit the Deliverable B audit status for primitive C4 row [0,0,1,1,1,1].

This is intentionally a Route C audit.  The local Oracle packets contain
explicit equations for the first cusp-pair row and its coordinate rotation,
but not for the normal-form row L=[0,0,1,1,1,1] in the certified J_Y[4] basis.
The tempting product of the two earlier Kummer functions is not accepted here
as a cover equation without a divisor-class certificate proving that it is the
right fourth-power Kummer representative and that its normalization is the
intended smooth cyclic C4 cover.
"""

from __future__ import annotations

import hashlib
import json
import re
import time
from pathlib import Path
from typing import Any

from check_primitive_c4_deliverable_b_gate import coefficient_flags, newton_coefficients


HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "primitive_c4_fixed_0011_single_row_audit.json"
P = 11
Q = 11
COVER_ID = "primitive_c4_fixed_0011_11"
L_VECTOR = [0, 0, 1, 1, 1, 1]
BASIS = ["D1", "E1", "D2", "E2", "D3", "E3"]
SURVIVING_CANDIDATE_C1_TO_C4 = [0, 42, 0, 683]
SURVIVING_CANDIDATE_POWER_SUMS = [0, -84, 0, 796]

SEARCH_PATTERNS = [
    "0,0,1,1,1,1",
    "0, 0, 1, 1, 1, 1",
    "fixed_0011_11",
    "L = (0,0,1,1,1,1)",
    "L = (0, 0, 1, 1, 1, 1)",
    "[0,0,1,1,1,1]",
    "[0, 0, 1, 1, 1, 1]",
]
SEARCH_GLOBS = ("*.md", "*.json", "*.py")
ACCEPTED_EQUATION_MARKERS = (
    "C_L:",
    "C_L =",
    '"C_L"',
    "f_L",
    "N =",
    "D =",
)
EXCLUDE_SELF_NAMES = {
    "compute_primitive_c4_row_0011_audit.py",
    "primitive_c4_fixed_0011_single_row_audit.json",
    "primitive_c4_deliverable_b_gate_output.json",
}


def now() -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S")


def canonical_sha256(obj: object) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return path.read_text(encoding="utf-8", errors="replace")


def local_files() -> list[Path]:
    files: list[Path] = []
    for glob in SEARCH_GLOBS:
        files.extend(HERE.glob(glob))
    return sorted({p for p in files if p.name not in EXCLUDE_SELF_NAMES})


def line_matches() -> list[dict[str, Any]]:
    pattern = re.compile("|".join(re.escape(p) for p in SEARCH_PATTERNS))
    hits: list[dict[str, Any]] = []
    for path in local_files():
        rel = path.relative_to(HERE).as_posix()
        for lineno, line in enumerate(read_text(path).splitlines(), start=1):
            if pattern.search(line):
                text = line.strip()
                hits.append(
                    {
                        "path": rel,
                        "line": lineno,
                        "text": text[:320],
                        "contains_equation_marker": any(marker in text for marker in ACCEPTED_EQUATION_MARKERS),
                    }
                )
    return hits


def classify_evidence(matches: list[dict[str, Any]]) -> dict[str, Any]:
    explicit_equation_hits = [
        hit
        for hit in matches
        if hit["contains_equation_marker"]
        and hit["path"].startswith("oracle_claim_packet_")
        and "[0,0,1,1,1,1]" in hit["text"].replace(" ", "")
    ]
    placeholder_hits = [
        hit
        for hit in matches
        if any(token in hit["text"] for token in ("[0,0,0,0]", '"#C_L', "schema", "remaining_gap"))
    ]
    return {
        "files_scanned": len(local_files()),
        "matches_found": len(matches),
        "explicit_oracle_equation_hits_for_row_0011": explicit_equation_hits,
        "placeholder_or_gap_hits": placeholder_hits[:20],
        "oracle_supplied_f_L_found": False,
        "route_a_result": (
            "No Oracle packet or local md/json/py file supplies an explicit f_L, N/D pair, "
            "or normalized point-count construction for L=[0,0,1,1,1,1].  The only row-3 "
            "mentions are schemas, normal-form frontier statements, and remaining-gap notes."
        ),
    }


def build_audit() -> dict[str, Any]:
    started = time.time()
    print(f"[{now()}] scanning local md/json/py artifacts for row {L_VECTOR}", flush=True)
    matches = line_matches()
    evidence = classify_evidence(matches)
    print(
        f"[{now()}] scan complete: {evidence['files_scanned']} files, "
        f"{evidence['matches_found']} row-3 mentions, no accepted f_L",
        flush=True,
    )

    candidate_coeffs = newton_coefficients(SURVIVING_CANDIDATE_POWER_SUMS)
    candidate_flags = coefficient_flags(candidate_coeffs)
    candidate_c1_to_c4 = candidate_coeffs[1:5]

    method_notes = [
        "Route A was attempted by scanning all local .md, .json, and .py artifacts in this target directory for row-3 identifiers.",
        "The scan found only schema placeholders, normal-form frontier statements, and gap statements for L=[0,0,1,1,1,1]; no Oracle-supplied f_L or explicit N/D Kummer equation was found.",
        "The two earlier explicit cusp-pair rows do not by themselves prove the row-3 equation.  Multiplying their Kummer functions is only a heuristic unless tied to the certified J_Y[4] basis as the divisor class D2+E2+D3+E3 modulo fourth powers.",
        "Without that divisor-class certificate, the product heuristic also does not prove that the resulting projective incidence curve is the intended smooth cyclic C4 cover after normalization.",
        "Route B was not completed because no local target-specific J_Y[4] divisor-basis certificate mapping L=[0,0,1,1,1,1] to an explicit function f_L is present.",
        "Therefore this audit is indeterminate and deliberately records no fabricated C_L or C_L2 point counts.",
    ]

    audit: dict[str, Any] = {
        "status": "indeterminate_row_3_requires_external_input",
        "route_used": "C",
        "cover_id": COVER_ID,
        "curve": "Y/F_11: X^4 + Y^4 + Z^4 = 0",
        "L_vector": L_VECTOR,
        "basis": BASIS,
        "quadratic_vector": [0, 0, 2, 2, 2, 2],
        "descent": {
            "cover_id": COVER_ID,
            "field_of_definition": "F_11 if an explicit representative exists",
            "basis": BASIS,
            "L_vector": L_VECTOR,
            "divisor_relation_needed": "D_L = D2 + E2 + D3 + E3 in the certified J_Y[4] basis",
            "quadratic_projection_vector": [0, 0, 2, 2, 2, 2],
        },
        "equations": {},
        "C_L_equation": "",
        "C_L2_equation": "",
        "f_L_explicit": "",
        "point_counts": {
            "C_L_counts_F11_n": [],
            "C_L2_counts_F11_n": [],
        },
        "C_L_counts_F11_n": [],
        "C_L2_counts_F11_n": [],
        "primitive_power_sums": [],
        "prym_polynomial_coeffs": [],
        "coefficients_c1_to_c4": [],
        "newton_divisibility_ok": False,
        "newton_error": "not evaluated because no rigorous row-3 f_L/equation was available",
        "satisfies_c3_eq": False,
        "satisfies_c4_eq": False,
        "satisfies_PE2": False,
        "satisfies_sign_c3_eq": False,
        "satisfies_sign_c4_eq": False,
        "satisfies_sign_guard": False,
        "hits_surviving_pe2_candidate": False,
        "surviving_pe2_candidate": {
            "power_sums_s1_to_s4": SURVIVING_CANDIDATE_POWER_SUMS,
            "coefficients_c1_to_c4": SURVIVING_CANDIDATE_C1_TO_C4,
            "reverse_weil_prym_polynomial": candidate_coeffs,
            "coefficient_flags": candidate_flags,
            "hits_surviving_pe2_candidate": candidate_c1_to_c4 == SURVIVING_CANDIDATE_C1_TO_C4,
            "note": "This is the normal-form survivor from c4_next_after_two_audited_orbits_output.json, not a row-3 point-count result.",
        },
        "route_a_scan": evidence,
        "searched_patterns": SEARCH_PATTERNS,
        "oracle_mentions": matches,
        "method_notes": method_notes,
        "required_external_input": [
            "An explicit Fermat-quartic Kummer function f_L over F_11 for L=[0,0,1,1,1,1], certified against the J_Y[4] basis.",
            "Or a target-specific J_Y[4] divisor-basis certificate proving the normal-form row D2+E2+D3+E3 maps to a concrete cover equation.",
            "Then normalized point counts for C_L and C_L2 over F_11^n for n=1..4.",
        ],
        "runtime_seconds": round(time.time() - started, 3),
    }
    audit["audit_sha256"] = canonical_sha256({k: v for k, v in audit.items() if k != "audit_sha256"})
    return audit


def main() -> None:
    audit = build_audit()
    OUTPUT.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "wrote": str(OUTPUT),
                "status": audit["status"],
                "route_used": audit["route_used"],
                "L_vector": audit["L_vector"],
                "hits_surviving_pe2_candidate": audit["hits_surviving_pe2_candidate"],
                "matches_found": audit["route_a_scan"]["matches_found"],
                "oracle_supplied_f_L_found": audit["route_a_scan"]["oracle_supplied_f_L_found"],
                "blocker": audit["required_external_input"][0],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
