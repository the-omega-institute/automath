#!/usr/bin/env python3
"""Gate the primitive C4 single-row Deliverable B evidence.

The stable-point contract now requires an actual point-count audit for
``primitive_c4_fixed_0000_11``: explicit equations plus concrete counts for
``C_L`` and ``C_L2`` over ``F_11^n`` for ``n=1..4``.  Prior Oracle packets
contain useful row/descent contracts; this checker distinguishes those from a
materialized ``primitive_c4_single_row_audit.json`` and then recomputes the
certificate-level arithmetic from whichever audit is on disk.

This checker makes that status reproducible.  If the single-row audit exists,
it recomputes the primitive Prym coefficients from the recorded point counts
and checks the PE2/sign equations.  If it is absent, it verifies the latest
contract artifacts and records the exact missing fields rather than treating
schema-only outputs as mathematical evidence.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "primitive_c4_deliverable_b_gate_output.json"
AUDIT = HERE / "primitive_c4_single_row_audit.json"
ROW_AUDITS = [
    {
        "label": "row_1_fixed_0000_11",
        "path": HERE / "primitive_c4_single_row_audit.json",
        "expected_cover_id": "primitive_c4_fixed_0000_11",
        "expected_L_vector": [0, 0, 0, 0, 1, 1],
    },
    {
        "label": "row_2_fixed_0000_13",
        "path": HERE / "primitive_c4_fixed_0000_13_single_row_audit.json",
        "expected_cover_id": "primitive_c4_fixed_0000_13",
        "expected_L_vector": [0, 0, 0, 0, 1, 3],
    },
    {
        "label": "row_3_fixed_0011_11",
        "path": HERE / "primitive_c4_fixed_0011_single_row_audit.json",
        "expected_cover_id": "primitive_c4_fixed_0011_11",
        "expected_L_vector": [0, 0, 1, 1, 1, 1],
    },
]
Q = 11
TARGET_COVER_ID = "primitive_c4_fixed_0000_11"
TARGET_S = [0, -84, 0, 796]
SURVIVING_ROW3_C1_TO_C4 = [0, 42, 0, 683]

CONTRACT_OUTPUTS = [
    HERE / "oracle_96f13_repaired_single_row_contract_output.json",
    HERE / "oracle_095d_repaired_single_row_contract_output.json",
    HERE / "oracle_803_repaired_single_row_contract_output.json",
    HERE / "c4_required_even_distribution_certificate_output.json",
    HERE / "c4_surviving_candidate_factorization_output.json",
]


def canonical_sha256(obj: object) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def newton_coefficients(power_sums: list[int]) -> list[int]:
    """Return degree-8 reciprocal Prym coefficients from s_1..s_4."""
    c = [1]
    for k in range(1, 5):
        val = sum(power_sums[i - 1] * c[k - i] for i in range(1, k + 1))
        if val % k != 0:
            raise ValueError(f"Newton divisibility failed at k={k}: {val}")
        c.append(-val // k)
    return c + [Q * c[3], Q * Q * c[2], Q**3 * c[1], Q**4]


def coefficient_flags(coeffs: list[int]) -> dict[str, bool]:
    c1, c2, c3, c4 = coeffs[1], coeffs[2], coeffs[3], coeffs[4]
    satisfies_c3_eq = c3 == 30 * c1 - 2 * c2 + 84
    satisfies_c4_eq = c4 == 2 * c1 + 23 * c2 - 283
    satisfies_sign_c3_eq = c3 == 30 * c1 + 2 * c2 - 84
    satisfies_sign_c4_eq = c4 == -2 * c1 + 23 * c2 - 283
    return {
        "satisfies_c3_eq": satisfies_c3_eq,
        "satisfies_c4_eq": satisfies_c4_eq,
        "satisfies_PE2": satisfies_c3_eq and satisfies_c4_eq,
        "satisfies_sign_c3_eq": satisfies_sign_c3_eq,
        "satisfies_sign_c4_eq": satisfies_sign_c4_eq,
        "satisfies_sign_guard": satisfies_sign_c3_eq and satisfies_sign_c4_eq,
    }


def multiply_quadratics_squared() -> list[int]:
    """Compute (1-T+11T^2)^2*(1+T+11T^2)^2 coefficient list."""
    polys = [[1, -1, Q], [1, -1, Q], [1, 1, Q], [1, 1, Q]]
    out = [1]
    for poly in polys:
        nxt = [0] * (len(out) + len(poly) - 1)
        for i, a in enumerate(out):
            for j, b in enumerate(poly):
                nxt[i + j] += a * b
        out = nxt
    return out


def contract_summary() -> list[dict[str, Any]]:
    summaries: list[dict[str, Any]] = []
    for path in CONTRACT_OUTPUTS:
        if not path.exists():
            summaries.append({"path": str(path.relative_to(HERE)), "present": False})
            continue
        data = load_json(path)
        cert = data.get("certificate", {})
        selected = cert.get("selected_row_contract", {})
        normal = cert.get("normal_form_replay", {})
        summaries.append(
            {
                "path": str(path.relative_to(HERE)),
                "present": True,
                "all_local_checks_passed": data.get("all_local_checks_passed"),
                "verification_scope": data.get("verification_scope"),
                "cover_id": selected.get("cover_id"),
                "row_certificate_present": cert.get("row_certificate_present"),
                "row_certificate_path": cert.get("row_certificate_path"),
                "local_point_count_replay_status": cert.get("local_point_count_replay_status"),
                "frobenius_fixed_representatives": normal.get("frobenius_fixed_representatives"),
                "frobenius_two_cycle_representatives": normal.get("frobenius_two_cycle_representatives"),
                "primitive_cyclic_order4_subgroups": normal.get("primitive_cyclic_order4_subgroups"),
                "local_conclusion": data.get("local_conclusion"),
            }
        )
    return summaries


def audit_counts_from_payload(payload: dict[str, Any]) -> tuple[list[int], list[int]]:
    pc = payload.get("point_counts")
    if not isinstance(pc, dict):
        raise ValueError("point_counts must be an object")
    cl = pc.get("C_L_counts_F11_n")
    cl2 = pc.get("C_L2_counts_F11_n")
    if not (isinstance(cl, list) and isinstance(cl2, list)):
        raise ValueError("point_counts must contain C_L_counts_F11_n and C_L2_counts_F11_n lists")
    if len(cl) != 4 or len(cl2) != 4:
        raise ValueError("point-count lists must have length 4")
    if not all(isinstance(x, int) for x in cl + cl2):
        raise ValueError("point counts must be concrete integers")
    return cl, cl2


def payload_counts(payload: dict[str, Any]) -> tuple[list[int], list[int]]:
    pc = payload.get("point_counts")
    if isinstance(pc, dict):
        cl = pc.get("C_L_counts_F11_n")
        cl2 = pc.get("C_L2_counts_F11_n")
    else:
        cl = payload.get("C_L_counts_F11_n")
        cl2 = payload.get("C_L2_counts_F11_n")
    if not (isinstance(cl, list) and isinstance(cl2, list)):
        return [], []
    if not all(isinstance(x, int) for x in cl + cl2):
        return [], []
    return cl, cl2


def row_audit_ledger() -> list[dict[str, Any]]:
    ledger: list[dict[str, Any]] = []
    for spec in ROW_AUDITS:
        path = spec["path"]
        row: dict[str, Any] = {
            "label": spec["label"],
            "audit_path": str(path.relative_to(HERE)),
            "expected_cover_id": spec["expected_cover_id"],
            "expected_L_vector": spec["expected_L_vector"],
            "present": path.exists(),
        }
        if not path.exists():
            row["status"] = "missing"
            ledger.append(row)
            continue

        raw = load_json(path)
        cl, cl2 = payload_counts(raw)
        status = raw.get("status")
        if not status:
            status = "point_count_audit_present" if len(cl) == 4 and len(cl2) == 4 else "audit_present_without_complete_counts"

        row.update(
            {
                "status": status,
                "cover_id": raw.get("cover_id"),
                "L_vector": raw.get("L_vector"),
                "has_descent": isinstance(raw.get("descent"), dict),
                "has_equations": isinstance(raw.get("equations"), dict) and bool(raw.get("equations")),
                "C_L_counts_F11_n": cl,
                "C_L2_counts_F11_n": cl2,
                "hits_surviving_pe2_candidate": bool(raw.get("hits_surviving_pe2_candidate", False)),
            }
        )

        if len(cl) == 4 and len(cl2) == 4:
            s = [cl2[i] - cl[i] for i in range(4)]
            coeffs = newton_coefficients(s)
            flags = coefficient_flags(coeffs)
            row.update(
                {
                    "primitive_power_sums": s,
                    "prym_polynomial_coeffs_recomputed": coeffs,
                    "coefficients_c1_to_c4_recomputed": coeffs[1:5],
                    "hits_surviving_pe2_candidate": coeffs[1:5] == SURVIVING_ROW3_C1_TO_C4,
                    **flags,
                }
            )
        else:
            notes = raw.get("method_notes", [])
            row.update(
                {
                    "primitive_power_sums": raw.get("primitive_power_sums", []),
                    "prym_polynomial_coeffs_recomputed": [],
                    "coefficients_c1_to_c4_recomputed": [],
                    "satisfies_PE2": False,
                    "satisfies_sign_guard": False,
                    "method_notes": notes[:6] if isinstance(notes, list) else notes,
                    "required_external_input": raw.get("required_external_input", []),
                }
            )
        ledger.append(row)
    return ledger


def main() -> None:
    failures: list[str] = []
    forced_coeffs = newton_coefficients(TARGET_S)
    forced_factor_coeffs = multiply_quadratics_squared()
    forced_flags = coefficient_flags(forced_coeffs)
    if forced_coeffs != forced_factor_coeffs:
        failures.append("forced target vector does not match exact quadratic-square factorization")
    if not forced_flags["satisfies_PE2"]:
        failures.append("forced target vector should satisfy PE2 coefficient equations")
    if not forced_flags["satisfies_sign_guard"]:
        failures.append("forced target vector should satisfy sign-guard coefficient equations")

    contracts = contract_summary()
    audit_ledger = row_audit_ledger()
    latest_contracts = [c for c in contracts if c.get("cover_id") == TARGET_COVER_ID]
    if not latest_contracts:
        failures.append(f"no local contract artifact names cover_id={TARGET_COVER_ID}")

    audit_status: dict[str, Any]
    if AUDIT.exists():
        raw = load_json(AUDIT)
        cl, cl2 = audit_counts_from_payload(raw)
        s = [cl2[i] - cl[i] for i in range(4)]
        coeffs = newton_coefficients(s)
        flags = coefficient_flags(coeffs)
        recorded_coeffs = raw.get("prym_polynomial_coeffs")
        if recorded_coeffs is not None and recorded_coeffs != coeffs:
            failures.append("recorded prym_polynomial_coeffs do not match recomputed coefficients")
        audit_status = {
            "status": "point_count_audit_present",
            "audit_path": str(AUDIT.relative_to(HERE)),
            "cover_id": raw.get("cover_id"),
            "has_descent": isinstance(raw.get("descent"), dict),
            "has_equations": isinstance(raw.get("equations"), dict),
            "C_L_counts_F11_n": cl,
            "C_L2_counts_F11_n": cl2,
            "primitive_power_sums": s,
            "prym_polynomial_coeffs_recomputed": coeffs,
            "matches_forced_target_s": s == TARGET_S,
            **flags,
        }
    else:
        audit_status = {
            "status": "incomplete_single_row_audit",
            "audit_path": str(AUDIT.relative_to(HERE)),
            "cover_id": TARGET_COVER_ID,
            "missing_required_fields": [
                "explicit F_11 equations/descent for C_L: T4^4=f_L and C_L2: T2^2=f_L",
                "C_L_counts_F11_n: four concrete integers",
                "C_L2_counts_F11_n: four concrete integers",
                "primitive_power_sums recomputed from counts",
                "prym_polynomial_coeffs recomputed from counts",
                "PE2/sign coefficient booleans from the recomputed coefficients",
            ],
            "schema_contracts_do_not_count_as_deliverable_b": True,
        }

    certificate = {
        "claim_checked": (
            "The currently available primitive C4 single-row artifacts either contain "
            "a concrete Deliverable B point-count audit for primitive_c4_fixed_0000_11, "
            "or must be classified as incomplete schema/descent contracts."
        ),
        "target_cover_id": TARGET_COVER_ID,
        "target_power_sums_s1_to_s4": TARGET_S,
        "forced_prym_polynomial_coeffs": forced_coeffs,
        "forced_factorization_coeffs_PE_squared_times_twist_squared": forced_factor_coeffs,
        "forced_target_flags": forced_flags,
        "contract_artifacts_checked": contracts,
        "audit_status": audit_status,
        "per_row_audit_ledger": audit_ledger,
    }

    has_complete_audit = audit_status["status"] == "point_count_audit_present"
    if has_complete_audit:
        local_conclusion = (
            "A primitive_c4_single_row_audit.json is present and its point counts were "
            "recomputed into the displayed Prym coefficients and PE2/sign flags."
        )
        verification_scope = "deliverable_b_point_count_json_replay_not_independent_curve_point_enumeration"
    else:
        local_conclusion = (
            "No primitive_c4_single_row_audit.json is present locally.  The existing "
            "Oracle contract artifacts identify the row and normal-form counts, but "
            "they do not contain the concrete C_L/C_L2 point counts required by "
            "Deliverable B.  The forced vector s=(0,-84,0,796) still exactly gives "
            "(1-T+11T^2)^2*(1+T+11T^2)^2, so the missing audit is mathematically decisive."
        )
        verification_scope = "deliverable_b_gate_and_forced_newton_factorization_no_actual_point_counts"

    output = {
        "all_local_checks_passed": not failures,
        "certificate_sha256": canonical_sha256(certificate),
        "certificate": certificate,
        "failures": failures,
        "local_conclusion": local_conclusion,
        "remaining_gap": (
            (
                "Independently verify the recorded primitive_c4_single_row_audit.json "
                "by a runnable smooth-projective normalization/desingularization "
                "point counter for C_L and C_L2 over F_11^n, n=1..4; or supply a "
                "target-specific J_Y[4] divisor-basis certificate/representative "
                "enumeration that replaces this row contract."
            )
            if has_complete_audit
            else (
                "Produce a concrete primitive_c4_single_row_audit.json for "
                "primitive_c4_fixed_0000_11 with explicit F_11 equations and integer "
                "counts for C_L and C_L2 over F_11^n, n=1..4; or supply a "
                "target-specific J_Y[4] divisor-basis certificate/representative "
                "enumeration that replaces this row contract."
            )
        ),
        "verification_scope": verification_scope,
    }
    OUTPUT.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(output, indent=2, sort_keys=True))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
