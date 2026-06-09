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


PASS = "PASS"
FAIL = "FAIL"
BLOCKED = "BLOCKED_AT_SUBSTEP"


def status(pass_value: bool) -> str:
    return PASS if pass_value else FAIL


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


def k1_subspace_multiplication() -> tuple[str, dict[str, Any]]:
    ambient4 = jy.h0_dimension(4)
    ambient8 = jy.h0_dimension(8)
    basis4 = [
        tuple(jy.ONE if i == j else jy.ZERO for j in range(ambient4))
        for i in range(ambient4)
    ]
    W_A = jy.Subspace(basis4[:3], ambient4)
    W_B = jy.Subspace(basis4[-3:], ambient4)

    W_prod = jy.multiply_subspaces(W_A, W_B, target_degree=8)
    valid_subspace = isinstance(W_prod, jy.Subspace) and W_prod.ambient_dim == ambient8
    dimension_bounded = W_prod.dimension <= ambient8
    nontrivial_product = W_prod.dimension >= 1

    zero_product = jy.multiply_subspaces(jy.Subspace.zero(ambient4), W_B, target_degree=8)
    zero_bilinear = zero_product.dimension == 0 and zero_product.ambient_dim == ambient8

    poly_a0 = jy.HomogPoly.from_vector(4, W_A.rows[0])
    poly_b0 = jy.HomogPoly.from_vector(4, W_B.rows[0])
    witness_vector = (poly_a0 * poly_b0).reduce_fermat().to_vector()
    witness_contained = W_prod.contains(witness_vector)

    passed = (
        valid_subspace
        and dimension_bounded
        and nontrivial_product
        and zero_bilinear
        and witness_contained
    )
    return status(passed), {
        "summary": (
            f"{status(passed)}: dim W_A={W_A.dimension}, dim W_B={W_B.dimension}, "
            f"dim W_prod={W_prod.dimension}, ambient_degree_8={ambient8}"
        ),
        "ambient_degree_4": ambient4,
        "ambient_degree_8": ambient8,
        "dim_W_A": W_A.dimension,
        "dim_W_B": W_B.dimension,
        "dim_W_prod": W_prod.dimension,
        "valid_subspace": valid_subspace,
        "dimension_bounded": dimension_bounded,
        "nontrivial_product": nontrivial_product,
        "zero_bilinear": zero_bilinear,
        "witness_contained": witness_contained,
    }


def divisor_group_law_test() -> tuple[str, dict[str, Any], list[str]]:
    blockers: list[str] = []
    base_points = jy.base_divisor_points()
    zero = jy.K1Divisor.zero()
    zero_constructed = (
        len(base_points) == 8
        and zero.W.ambient_dim == jy.h0_dimension(4) == 14
        and zero.W.dimension == 6
        and zero == jy.K1Divisor.from_effective_divisor(base_points)
    )

    random_rows: list[dict[str, Any]] = []
    add_blocker: dict[str, str] | None = None
    constructed = 0
    attempted_associativity = 0
    for seed in range(1, 6):
        a = jy.K1Divisor.from_effective_divisor(jy.random_effective_divisor(1000 + 3 * seed))
        b = jy.K1Divisor.from_effective_divisor(jy.random_effective_divisor(1001 + 3 * seed))
        c = jy.K1Divisor.from_effective_divisor(jy.random_effective_divisor(1002 + 3 * seed))
        constructed += 3
        row: dict[str, Any] = {
            "seed": seed,
            "W_dimensions": [a.W.dimension, b.W.dimension, c.W.dimension],
            "ambient_dimensions": [a.W.ambient_dim, b.W.ambient_dim, c.W.ambient_dim],
            "pair_intersection_dimensions": [
                a.W.intersection(b.W).dimension,
                b.W.intersection(c.W).dimension,
                a.W.intersection(c.W).dimension,
            ],
        }
        try:
            attempted_associativity += 1
            left = a.add(b).add(c)
            right = a.add(b.add(c))
            row["associative"] = left == right
        except jy.ArithmeticBlocker as exc:
            add_blocker = {"substep": exc.substep, "reason": exc.reason}
            row["status"] = BLOCKED
            row["blocker"] = add_blocker
            blockers.append(f"{exc.substep}: {exc.reason}")
            random_rows.append(row)
            break
        random_rows.append(row)

    if add_blocker is None:
        return status(all(row.get("associative") is True for row in random_rows)), {
            "zero_K1_constructed": zero_constructed,
            "random_effective_divisors_constructed": constructed,
            "random_triples_requested": 5,
            "random_triples_attempted": attempted_associativity,
            "rows": random_rows,
        }, blockers

    return BLOCKED, {
        "zero_K1_constructed": zero_constructed,
        "base_divisor_degree": len(base_points),
        "H0_O4_dimension": jy.h0_dimension(4),
        "zero_W_dimension": zero.W.dimension,
        "random_effective_divisors_constructed": constructed,
        "random_triples_requested": 5,
        "random_triples_attempted_before_block": attempted_associativity,
        "rows": random_rows,
        "blocker": add_blocker,
    }, blockers


def legacy_reduced_divisor_blocker_test() -> dict[str, Any]:
    hpts = jy.hyperflex_points()
    try:
        jy.ReducedDivisor(divisor={hpts[0]: 1, hpts[1]: -1})
    except jy.ArithmeticBlocker as exc:
        return {"status": BLOCKED, "substep": exc.substep, "reason": exc.reason}
    return {"status": FAIL, "reason": "legacy ReducedDivisor unexpectedly accepted a nontrivial class"}


def jy4_order_check(nonhyper: dict[str, Any] | None) -> dict[str, Any]:
    if nonhyper is None:
        return {
            "status": BLOCKED,
            "computed": None,
            "expected": jy.EXPECTED_JY4_ORDER,
            "source": None,
            "blocker": "full K1 add/double/reduce is needed before exact 4096-class enumeration",
        }
    computed = int(nonhyper.get("full_JY4_order", -1))
    return {
        "status": BLOCKED,
        "computed": computed,
        "expected": jy.EXPECTED_JY4_ORDER,
        "prior_replay_matches_expected": computed == jy.EXPECTED_JY4_ORDER,
        "source": NONHYPER.name,
        "blocker": "not recomputed by this K1 partial engine; requires completed add/double/reduce and equality enumeration",
    }


def hyperflex_order_check(nonhyper: dict[str, Any] | None) -> dict[str, Any]:
    if nonhyper is None:
        return {
            "status": BLOCKED,
            "computed": None,
            "expected": jy.EXPECTED_HYPERFLEX_ORDER,
            "source": None,
            "blocker": "hyperflex subgroup generation needs completed group law",
        }
    computed = int(nonhyper.get("hyperflex_group_order", -1))
    return {
        "status": BLOCKED,
        "computed": computed,
        "expected": jy.EXPECTED_HYPERFLEX_ORDER,
        "prior_replay_matches_expected": computed == jy.EXPECTED_HYPERFLEX_ORDER,
        "source": NONHYPER.name,
        "blocker": "not recomputed by this K1 partial engine; requires completed group law on hyperflex classes",
    }


def halving_test() -> tuple[dict[str, Any], list[str]]:
    blockers: list[str] = []
    zero = jy.K1Divisor.zero()
    try:
        jy.K1Divisor.halve(zero)
    except jy.ArithmeticBlocker as exc:
        blockers.append(f"{exc.substep}: {exc.reason}")
        return {
            "T_repr": "not materialized; requested outside-2H two-torsion needs full JY[4] basis",
            "D_L_repr": None,
            "outside_2H": False,
            "status": BLOCKED,
            "blocker": {"substep": exc.substep, "reason": exc.reason},
        }, blockers
    return {
        "T_repr": "unexpected",
        "D_L_repr": "unexpected",
        "outside_2H": False,
        "status": FAIL,
    }, ["halve unexpectedly returned without an outside-2H certificate"]


def main() -> int:
    blockers: list[str] = []
    nonhyper = read_json(NONHYPER)
    audit = read_json(AUDIT)

    field_status, field_detail = field_arithmetic_test()
    curve_status, curve_detail = curve_smoothness_test()
    k1_mult_status, k1_mult_detail = k1_subspace_multiplication()
    add_status, add_detail, add_blockers = divisor_group_law_test()
    blockers.extend(add_blockers)
    legacy_blocker = legacy_reduced_divisor_blocker_test()
    halve_payload, halve_blockers = halving_test()
    blockers.extend(halve_blockers)

    order_payload = jy4_order_check(nonhyper)
    hyper_payload = hyperflex_order_check(nonhyper)
    blockers.append("JY[4] order was not recomputed by the partial K1 engine")
    blockers.append("hyperflex subgroup order was not recomputed by the partial K1 engine")

    div_fL = {
        "status": BLOCKED,
        "verified": False,
        "blocker": {
            "substep": "k1/materialize_function_principal_relation",
            "reason": "no D_L or rational f_L exists because halving outside 2H is blocked",
        },
    }
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
            "k1_subspace_multiplication": k1_mult_status,
            "k1_subspace_multiplication_detail": k1_mult_detail,
            "add_associative": add_status,
            "add_associative_detail": add_detail,
            "legacy_ReducedDivisor_nontrivial_class": legacy_blocker,
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
