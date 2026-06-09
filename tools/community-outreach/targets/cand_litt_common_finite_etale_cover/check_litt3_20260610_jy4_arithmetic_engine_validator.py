#!/usr/bin/env python3
"""Validate the local JY[4] arithmetic-engine artifact without fabrication."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import jy4_divisor_arithmetic as jy


HERE = Path(__file__).resolve().parent
OUT = HERE / "check_litt3_20260610_jy4_arithmetic_engine_validator_output.json"
AUDIT = HERE / "litt3_20260610_jy4_hard_wall_audit.json"
NONHYPER = HERE / "check_litt3_nonhyperflex_certificate_gap.output.json"


def canonical_sha256_without_self(payload: dict[str, Any]) -> str:
    body = {k: v for k, v in payload.items() if k != "certificate_sha256"}
    encoded = json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def read_json(path: Path) -> dict[str, Any] | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def status(pass_value: bool) -> str:
    return "pass" if pass_value else "fail"


def field_arithmetic_test() -> tuple[str, dict[str, Any]]:
    samples = [
        jy.Fq((1, 2, 3, 4)),
        jy.Fq((0, 1, 0, 0)),
        jy.Fq((7, 0, 8, 3)),
        jy.Fq((10, 10, 10, 10)),
    ]
    inverse_ok = all(a * a.inverse() == jy.ONE for a in samples if a)
    frob4_ok = all(a.frobenius(4) == a for a in samples)
    frob_nontrivial = any(a.frobenius(1) != a for a in samples)
    modulus_ok = jy.T**4 + jy.Fq(4) * jy.T**3 + jy.ONE == jy.ZERO
    return status(inverse_ok and frob4_ok and frob_nontrivial and modulus_ok), {
        "inverse_ok": inverse_ok,
        "frobenius_order_divides_4": frob4_ok,
        "frobenius_nontrivial": frob_nontrivial,
        "modulus_relation": modulus_ok,
    }


def curve_smoothness_test() -> tuple[str, dict[str, Any]]:
    fast_count = jy.count_curve_points_fast()
    points = jy.enumerate_curve_points()
    count_ok = fast_count == len(points) == jy.EXPECTED_Y_F11_4_POINTS
    smooth_split_points = jy.verify_smooth_over_f11_4(points)
    # For Fermat quartic in characteristic 11, singularity equations force
    # X=Y=Z=0 because 4 is invertible, so there is no projective singularity
    # over the algebraic closure.  The enumerated check is a concrete F_11^4
    # replay and the algebraic criterion gives the closure statement.
    algebraic_closure_smooth = jy.P != 2 and jy.P != 0 and jy.P != 4
    return status(count_ok and smooth_split_points and algebraic_closure_smooth), {
        "enumerated_points": len(points),
        "fast_count": fast_count,
        "expected": jy.EXPECTED_Y_F11_4_POINTS,
        "smooth_on_F11_4_points": smooth_split_points,
        "algebraic_closure_reason": "partials are 4X^3,4Y^3,4Z^3; char 11 makes 4 invertible",
        "smooth_over_algebraic_closure": algebraic_closure_smooth,
    }


def divisor_group_law_test() -> tuple[str, dict[str, Any], list[str]]:
    blockers: list[str] = []
    zero = jy.ReducedDivisor.zero()
    zero_law_ok = zero.add(zero) == zero and zero.double() == zero
    hpts = jy.hyperflex_points()
    nontrivial_blocker: dict[str, str] | None = None
    try:
        jy.ReducedDivisor(divisor={hpts[0]: 1, hpts[1]: -1})
    except jy.ArithmeticBlocker as exc:
        nontrivial_blocker = {"substep": exc.substep, "reason": exc.reason}
        blockers.append(f"{exc.substep}: {exc.reason}")
    return status(False), {
        "zero_class_commutative_associative_smoke": zero_law_ok,
        "random_pairs_checked": 0,
        "nontrivial_add_associativity": "blocked",
        "blocker": nontrivial_blocker,
    }, blockers


def jy4_order_check(nonhyper: dict[str, Any] | None) -> dict[str, Any]:
    if nonhyper is None:
        return {"computed": None, "expected": jy.EXPECTED_JY4_ORDER, "pass": False, "source": None}
    computed = int(nonhyper.get("full_JY4_order", -1))
    return {
        "computed": computed,
        "expected": jy.EXPECTED_JY4_ORDER,
        "pass": computed == jy.EXPECTED_JY4_ORDER,
        "source": NONHYPER.name,
        "note": "replayed from prior finite-group certificate; not recomputed by this blocked reducer",
    }


def hyperflex_order_check(nonhyper: dict[str, Any] | None) -> dict[str, Any]:
    if nonhyper is None:
        return {"computed": None, "expected": jy.EXPECTED_HYPERFLEX_ORDER, "pass": False, "source": None}
    computed = int(nonhyper.get("hyperflex_group_order", -1))
    return {
        "computed": computed,
        "expected": jy.EXPECTED_HYPERFLEX_ORDER,
        "pass": computed == jy.EXPECTED_HYPERFLEX_ORDER,
        "source": NONHYPER.name,
        "note": "replayed from prior hyperflex subgroup certificate; not recomputed by this blocked reducer",
    }


def halving_test() -> tuple[dict[str, Any], list[str]]:
    blockers: list[str] = []
    zero = jy.ReducedDivisor.zero()
    try:
        jy.ReducedDivisor.halve(zero)
    except jy.ArithmeticBlocker as exc:
        blockers.append(f"{exc.substep}: {exc.reason}")
        return {
            "T_repr": "not materialized; requested outside-2H two-torsion needs full JY[4] basis",
            "D_L_repr": None,
            "outside_2H": False,
            "status": "blocked",
            "blocker": {"substep": exc.substep, "reason": exc.reason},
        }, blockers
    return {
        "T_repr": "unexpected",
        "D_L_repr": "unexpected",
        "outside_2H": False,
        "status": "fail",
    }, ["halve unexpectedly returned without an outside-2H certificate"]


def main() -> int:
    blockers: list[str] = []
    nonhyper = read_json(NONHYPER)
    audit = read_json(AUDIT)

    field_status, field_detail = field_arithmetic_test()
    curve_status, curve_detail = curve_smoothness_test()
    add_status, add_detail, add_blockers = divisor_group_law_test()
    blockers.extend(add_blockers)
    halve_payload, halve_blockers = halving_test()
    blockers.extend(halve_blockers)

    order_payload = jy4_order_check(nonhyper)
    hyper_payload = hyperflex_order_check(nonhyper)
    if not order_payload["pass"]:
        blockers.append("JY[4] order was not computed by the new reducer")
    if not hyper_payload["pass"]:
        blockers.append("hyperflex subgroup order was not computed by the new reducer")

    div_fL = False
    blockers.append(
        "div_fL_eq_4DL: no D_L or rational f_L exists because halving outside 2H is blocked"
    )

    payload: dict[str, Any] = {
        "Y_equation": jy.Y_EQUATION,
        "Y_provenance": {
            "local_files": [
                "claude_worker_jy4_F11_4_grouplaw_halving_basis_E3.py",
                "claude_worker_jy4_F11_4_4division_missing6_exhaustive_E3_output.json",
                "check_index1_row2_kummer_counts.py",
            ],
            "point_counts": {"F_121": 188, "F_11^4": jy.EXPECTED_Y_F11_4_POINTS},
        },
        "base_field": "F_{11^4}",
        "base_field_model": jy.BASE_FIELD,
        "tests": {
            "field_arith": field_status,
            "field_arith_detail": field_detail,
            "curve_smooth": curve_status,
            "curve_smooth_detail": curve_detail,
            "add_associative": add_status,
            "add_associative_detail": add_detail,
            "JY4_order_check": order_payload,
            "hyperflex_order_check": hyper_payload,
            "halve_outside_2H": halve_payload,
            "div_fL_eq_4DL": div_fL,
        },
        "blockers": blockers,
        "audit_replay": {
            "hard_wall_audit_present": audit is not None,
            "group_law_failed_substep": None
            if audit is None
            else audit.get("computed_facts", {}).get("group_law_failed_substep"),
            "hard_wall_certificate_sha256": None
            if audit is None
            else audit.get("certificate_sha256"),
        },
        "next_subtarget": (
            "Implement a real non-hyperelliptic genus-3 plane-quartic reducer "
            "(Khuri-Makdisi K1/K2 or Volcheck/flex-secant) over F_11^4, then "
            "use it to solve 2D=T outside 2H and construct f_L with div(f_L)=4D."
        ),
        "certificate_sha256": "",
    }
    payload["certificate_sha256"] = canonical_sha256_without_self(payload)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
