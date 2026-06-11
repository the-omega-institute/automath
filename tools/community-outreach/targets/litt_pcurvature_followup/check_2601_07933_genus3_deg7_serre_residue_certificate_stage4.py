#!/usr/bin/env python3
"""Stage-4 Serre-residue certificate for Lam-Litt arXiv:2601.07933.

Odd genus-3 hyperelliptic model:

    C: y^2 = f(x) = x(x-1)(x-2)(x-3)(x-4)(x-5)(x-6).

The even degree-8 Stage-3 attempt found the right finite-branch residue
formula but failed the boundary gate: q_5 = x^5(dx)^2/y^2 has a pole at the
two points over infinity.  In the odd degree-7 model, infinity is a branch
point.  The regular quadratic-differential basis splits as

    q_j = x^j(dx)^2/y^2,  j = 0,...,4,
    q_* = (dx)^2/y.

The first five columns are invariant under the hyperelliptic involution and
are detected by finite branch residues.  The sixth column q_* is
anti-invariant: it has zero finite-branch residue against polynomial branch
motions and is detected by a local normal residue at infinity.
"""

from __future__ import annotations

import datetime as _datetime
import json
import os
import time
from typing import Any, Callable, Dict, List, Tuple

import sympy as sp


OUTPUT_NAME = "check_2601_07933_genus3_deg7_serre_residue_certificate_stage4_output.json"
CURVE_F_STRING = "f(x) = x(x-1)(x-2)(x-3)(x-4)(x-5)(x-6)"
PAPER = "arXiv:2601.07933"
STAGE = "Stage-4 genuine Serre residue certificate for genus-3 degree-7 Lam-Litt curve"
HEARTBEAT_SECONDS = 20.0
GENUS = 3
DIM_H0_K = 3
DIM_H0_K2 = 3 * GENUS - 3
FINITE_BRANCH_COUNT = 7
TOTAL_BRANCH_COUNT = 8
OMEGA_DEGREES = list(range(GENUS))
INVARIANT_Q_DEGREES = list(range(2 * GENUS - 1))
AFFINE_TRIVIAL_V_DEGREES = [0, 1]
FINITE_TANGENT_H_DEGREES = list(range(2 * GENUS - 1))


def timestamp() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def progress(message: str) -> None:
    print(f"[{timestamp()}] {message}", flush=True)


def rational_to_string(value: Any) -> str:
    return str(sp.Rational(value))


def expr_to_string(value: Any) -> str:
    return str(sp.simplify(value)).replace("**", "^")


def matrix_to_strings(matrix: List[List[sp.Rational]]) -> List[List[str]]:
    return [[rational_to_string(entry) for entry in row] for row in matrix]


def maybe_heartbeat(gate_name: str, start_time: float, last_heartbeat: List[float]) -> None:
    now = time.monotonic()
    if now - last_heartbeat[0] >= HEARTBEAT_SECONDS:
        progress(f"{gate_name}: still running after {now - start_time:.1f}s")
        last_heartbeat[0] = now


def run_gate(gate_name: str, gate_func: Callable[[], Tuple[bool, Dict[str, Any]]]) -> Tuple[bool, Dict[str, Any]]:
    progress(f"{gate_name}: START")
    start_time = time.monotonic()
    result = gate_func()
    elapsed = time.monotonic() - start_time
    progress(f"{gate_name}: END pass={result[0]} elapsed={elapsed:.3f}s")
    return result


def polynomial_setup() -> Tuple[sp.Symbol, sp.Symbol, sp.Symbol, List[sp.Integer], sp.Expr, sp.Expr]:
    x, t, u = sp.symbols("x t u")
    roots = [sp.Integer(root) for root in range(FINITE_BRANCH_COUNT)]
    f = sp.expand(sp.prod(x - root for root in roots))
    f_prime = sp.diff(f, x)
    return x, t, u, roots, f, f_prime


def infinity_denominator(u: sp.Symbol, roots: List[sp.Integer]) -> sp.Expr:
    return sp.expand(sp.prod(1 - root * u**2 for root in roots))


def finite_branch_q_coefficient(x: sp.Symbol, t: sp.Symbol, f: sp.Expr, a: sp.Integer, j: int) -> sp.Expr:
    return sp.cancel(4 * t**2 * (a + t**2) ** j / f.subs(x, a + t**2))


def finite_branch_qstar_coefficient(x: sp.Symbol, t: sp.Symbol, f: sp.Expr, a: sp.Integer) -> sp.Expr:
    g = sp.cancel(f.subs(x, a + t**2) / t**2)
    return 4 * t / sp.sqrt(g)


def leading_exponent_from_series(expr: sp.Expr, variable: sp.Symbol, order: int) -> int | None:
    series = sp.series(expr, variable, 0, order).removeO().expand()
    for power in range(-order, order + 1):
        if sp.simplify(series.coeff(variable, power)) != 0:
            return power
    return None


def gate_1_h0k_basis() -> Tuple[bool, Dict[str, Any]]:
    """Checks dim H^0(K_C)=3 and regularity of x^i dx/y, i=0,1,2."""
    x, t, u, roots, f, f_prime = polynomial_setup()
    d_infty = infinity_denominator(u, roots)
    records: List[Dict[str, Any]] = []
    contrast_records: List[Dict[str, Any]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_regular = True
    for i in OMEGA_DEGREES:
        for a in roots:
            maybe_heartbeat("GATE 1 -- H0(K) basis", start_time, last_heartbeat)
            g = sp.cancel(f.subs(x, a + t**2) / t**2)
            coeff = 2 * (a + t**2) ** i / sp.sqrt(g)
            exponent = leading_exponent_from_series(coeff, t, 8)
            regular = bool(exponent is not None and exponent >= 0)
            all_regular = all_regular and regular
            records.append(
                {
                    "basis_element": f"omega_{i}=x^{i} dx/y",
                    "point": f"finite_branch_{int(a)}",
                    "local_parameter": "t with x=a+t^2",
                    "leading_exponent": exponent,
                    "regular": regular,
                    "leading_coefficient_symbolic": expr_to_string(2 * a**i / sp.sqrt(f_prime.subs(x, a))),
                }
            )

        coeff_infty = -2 * u ** (4 - 2 * i) / sp.sqrt(d_infty)
        exponent_infty = leading_exponent_from_series(coeff_infty, u, 12)
        regular_infty = bool(exponent_infty is not None and exponent_infty >= 0)
        all_regular = all_regular and regular_infty
        records.append(
            {
                "basis_element": f"omega_{i}=x^{i} dx/y",
                "point": "infinity_branch",
                "local_parameter": "u with x=1/u^2",
                "coefficient": expr_to_string(coeff_infty),
                "leading_exponent": exponent_infty,
                "regular": regular_infty,
            }
        )

    for i in [GENUS]:
        coeff_infty = -2 * u ** (4 - 2 * i) / sp.sqrt(d_infty)
        exponent_infty = leading_exponent_from_series(coeff_infty, u, 12)
        contrast_records.append(
            {
                "candidate": f"x^{i} dx/y",
                "point": "infinity_branch",
                "leading_exponent": exponent_infty,
                "regular": bool(exponent_infty is not None and exponent_infty >= 0),
                "purpose": "dimension contrast: the next monomial has a pole at infinity",
            }
        )

    pass_gate = bool(all_regular and len(OMEGA_DEGREES) == DIM_H0_K and not contrast_records[0]["regular"])
    return pass_gate, {
        "1_dim_H0_K_expected": DIM_H0_K,
        "1_dim_H0_K_basis": [f"x^{i} dx/y" for i in OMEGA_DEGREES],
        "1_branch_points": {
            "finite": [rational_to_string(root) for root in roots],
            "infinity": "one branch point because deg(f)=2g+1=7",
            "total": TOTAL_BRANCH_COUNT,
        },
        "1_regular_basis_checks": records,
        "1_dimension_contrast": contrast_records,
    }


def gate_2_h0k2_basis() -> Tuple[bool, Dict[str, Any]]:
    """Checks the six regular quadratic differentials for the odd model."""
    x, t, u, roots, f, f_prime = polynomial_setup()
    d_infty = infinity_denominator(u, roots)
    records: List[Dict[str, Any]] = []
    finite_residue_records: List[Dict[str, Any]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_regular = True
    for j in INVARIANT_Q_DEGREES:
        for a in roots:
            maybe_heartbeat("GATE 2 -- H0(K^2) basis", start_time, last_heartbeat)
            coeff = finite_branch_q_coefficient(x, t, f, a, j)
            series = sp.series(coeff, t, 0, 14).removeO().expand()
            computed_constant = sp.simplify(series.coeff(t, 0))
            predicted_constant = sp.simplify(4 * a**j / f_prime.subs(x, a))
            exponent = leading_exponent_from_series(coeff, t, 14)
            regular = bool(exponent is not None and exponent >= 0 and computed_constant == predicted_constant)
            all_regular = all_regular and regular
            records.append(
                {
                    "basis_element": f"q_{j}=x^{j}(dx)^2/y^2",
                    "point": f"finite_branch_{int(a)}",
                    "leading_exponent": exponent,
                    "computed_constant": rational_to_string(computed_constant),
                    "predicted_constant_4_a_j_over_fprime_a": rational_to_string(predicted_constant),
                    "regular": regular,
                }
            )

        coeff_infty = 4 * u ** (8 - 2 * j) / d_infty
        exponent_infty = leading_exponent_from_series(coeff_infty, u, 18)
        regular_infty = bool(exponent_infty is not None and exponent_infty >= 0)
        all_regular = all_regular and regular_infty
        records.append(
            {
                "basis_element": f"q_{j}=x^{j}(dx)^2/y^2",
                "point": "infinity_branch",
                "coefficient": expr_to_string(coeff_infty),
                "leading_exponent": exponent_infty,
                "regular": regular_infty,
            }
        )

    for a in roots:
        maybe_heartbeat("GATE 2 -- H0(K^2) basis", start_time, last_heartbeat)
        coeff = finite_branch_qstar_coefficient(x, t, f, a)
        exponent = leading_exponent_from_series(coeff, t, 10)
        regular = bool(exponent is not None and exponent >= 0)
        all_regular = all_regular and regular
        records.append(
            {
                "basis_element": "q_star=(dx)^2/y",
                "point": f"finite_branch_{int(a)}",
                "leading_exponent": exponent,
                "regular": regular,
                "structural_note": "coefficient is 4*t/sqrt(f'(a)+O(t^2)), so finite branch contraction has no residue",
            }
        )

        delta_symbol = sp.Symbol(f"delta_{int(a)}")
        one_form_coeff = sp.cancel(coeff * delta_symbol / (2 * t))
        residue_coeff = sp.series(one_form_coeff, t, 0, 6).removeO().expand().coeff(t, -1)
        finite_residue_records.append(
            {
                "basis_element": "q_star=(dx)^2/y",
                "point": f"finite_branch_{int(a)}",
                "contracted_one_form": expr_to_string(one_form_coeff),
                "residue_coefficient_t_minus_1": expr_to_string(residue_coeff),
                "residue_zero": bool(sp.simplify(residue_coeff) == 0),
            }
        )

    qstar_infty = 4 * u / sp.sqrt(d_infty)
    qstar_exponent = leading_exponent_from_series(qstar_infty, u, 12)
    qstar_regular = bool(qstar_exponent is not None and qstar_exponent >= 0)
    all_regular = all_regular and qstar_regular
    records.append(
        {
            "basis_element": "q_star=(dx)^2/y",
            "point": "infinity_branch",
            "coefficient": expr_to_string(qstar_infty),
            "leading_exponent": qstar_exponent,
            "regular": qstar_regular,
        }
    )

    singular_contrast = []
    q5_infty = 4 * u ** (8 - 2 * 5) / d_infty
    q5_exponent = leading_exponent_from_series(q5_infty, u, 18)
    singular_contrast.append(
        {
            "candidate": "x^5(dx)^2/y^2",
            "point": "infinity_branch",
            "coefficient": expr_to_string(q5_infty),
            "leading_exponent": q5_exponent,
            "regular": bool(q5_exponent is not None and q5_exponent >= 0),
            "purpose": "Stage-3 boundary contrast: the polynomial q_5 column is still singular in the odd model",
        }
    )

    pass_gate = bool(
        all_regular
        and len(INVARIANT_Q_DEGREES) + 1 == DIM_H0_K2
        and all(record["residue_zero"] for record in finite_residue_records)
        and not singular_contrast[0]["regular"]
    )
    return pass_gate, {
        "2_dim_H0_K2_expected": DIM_H0_K2,
        "2_basis": [f"x^{j}(dx)^2/y^2" for j in INVARIANT_Q_DEGREES] + ["(dx)^2/y"],
        "2_regular_basis_checks": records,
        "2_qstar_finite_branch_residue_zero_checks": finite_residue_records,
        "2_singular_polynomial_contrast": singular_contrast,
        "2_infinity_denominator_D_u": expr_to_string(d_infty),
    }


def lagrange_sum(m: int) -> sp.Rational:
    x, _t, _u, roots, _f, f_prime = polynomial_setup()
    total = sp.Rational(0)
    for a in roots:
        total += sp.Rational(a**m, sp.Rational(f_prime.subs(x, a)))
    return sp.simplify(total)


def gate_3_trivial_deformation() -> Tuple[bool, Dict[str, Any]]:
    """Checks that affine trivial branch motions annihilate H^0(K^2)."""
    x, _t, _u, roots, _f, f_prime = polynomial_setup()
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    sums_m_0_to_8 = []
    for m in range(9):
        maybe_heartbeat("GATE 3 -- Trivial deformation", start_time, last_heartbeat)
        sums_m_0_to_8.append(lagrange_sum(m))

    lagrange_core_pass = all(value == 0 for value in sums_m_0_to_8[:6])
    lagrange_contrast_pass = bool(sums_m_0_to_8[6] == 1 and sums_m_0_to_8[7] == 21)

    pairings: List[Dict[str, Any]] = []
    all_affine_pairings_zero = True
    for v_degree in AFFINE_TRIVIAL_V_DEGREES:
        for j in INVARIANT_Q_DEGREES:
            maybe_heartbeat("GATE 3 -- Trivial deformation", start_time, last_heartbeat)
            total = sp.Rational(0)
            for a in roots:
                f_prime_at_a = sp.Rational(f_prime.subs(x, a))
                h_at_a = -sp.Integer(a) ** v_degree * f_prime_at_a
                total += sp.Rational(-2) * h_at_a * sp.Integer(a) ** j / (f_prime_at_a**2)
            total = sp.simplify(total)
            is_zero = bool(total == 0)
            all_affine_pairings_zero = all_affine_pairings_zero and is_zero
            pairings.append(
                {
                    "trivial_vector_field_v": "1" if v_degree == 0 else f"x^{v_degree}",
                    "basis_element": f"q_{j}=x^{j}(dx)^2/y^2",
                    "m_v_plus_j": v_degree + j,
                    "pairing_with_h_minus_v_fprime": rational_to_string(total),
                    "zero": is_zero,
                }
            )

        pairings.append(
            {
                "trivial_vector_field_v": "1" if v_degree == 0 else f"x^{v_degree}",
                "basis_element": "q_star=(dx)^2/y",
                "pairing_with_h_minus_v_fprime": "0",
                "zero": True,
                "reason": "q_star finite branch residue is zero for every polynomial branch motion",
            }
        )

    sanity_total = sp.Rational(0)
    for a in roots:
        f_prime_at_a = sp.Rational(f_prime.subs(x, a))
        h_at_a = -sp.Integer(a) ** 2 * f_prime_at_a
        sanity_total += sp.Rational(-2) * h_at_a * sp.Integer(a) ** 4 / (f_prime_at_a**2)
    sanity_total = sp.simplify(sanity_total)

    pass_gate = bool(lagrange_core_pass and lagrange_contrast_pass and all_affine_pairings_zero)
    note = (
        "For monic degree-7 f with finite roots a=0,...,6, "
        "sum_a a^m/f'(a)=0 for m<=5 and equals 1 for m=6.  In the odd model "
        "the branch point at infinity is fixed by the affine normal form, so "
        "the model-preserving trivial vector fields are v=1,x.  Their pairings "
        "with q_j, j<=4, only reach m<=5.  The projective x^2 contrast reaches "
        "m=6; it is recorded as a sanity contrast rather than as a model-fixed "
        "trivial deformation."
    )
    return pass_gate, {
        "3_lagrange_identity_max_zero_m": 5,
        "3_lagrange_sums_m_0_to_8": [rational_to_string(value) for value in sums_m_0_to_8],
        "3_lagrange_core_pass": lagrange_core_pass,
        "3_lagrange_contrast_m6_m7_pass": lagrange_contrast_pass,
        "3_affine_trivial_deformation_pairings": pairings,
        "3_affine_trivial_deformation_all_pairings_zero": all_affine_pairings_zero,
        "3_projective_x2_contrast_pairing_with_q4": rational_to_string(sanity_total),
        "3_structural_note": note,
    }


def finite_m_prime_matrix() -> List[List[sp.Rational]]:
    x, _t, _u, roots, _f, f_prime = polynomial_setup()
    matrix: List[List[sp.Rational]] = []
    for i in FINITE_TANGENT_H_DEGREES:
        row: List[sp.Rational] = []
        for j in INVARIANT_Q_DEGREES:
            entry = sp.Rational(0)
            for a in roots:
                f_prime_at_a = sp.Rational(f_prime.subs(x, a))
                entry += sp.Rational(a ** (i + j), f_prime_at_a**2)
            row.append(sp.simplify(entry))
        matrix.append(row)
    return matrix


def leading_principal_minors(matrix: sp.Matrix) -> List[sp.Rational]:
    return [sp.simplify(matrix[:k, :k].det()) for k in range(1, matrix.rows + 1)]


def boundary_normal_residue(column: str) -> sp.Rational:
    _x, _t, u, roots, _f, _f_prime = polynomial_setup()
    d_infty = infinity_denominator(u, roots)
    normal_vector_coeff = sp.sqrt(d_infty) / (4 * u**2)
    if column == "q_star":
        q_coeff = 4 * u / sp.sqrt(d_infty)
    else:
        j = int(column.split("_")[1])
        q_coeff = 4 * u ** (8 - 2 * j) / d_infty
    one_form_coeff = sp.simplify(q_coeff * normal_vector_coeff)
    series = sp.series(one_form_coeff, u, 0, 8).removeO().expand()
    return sp.simplify(series.coeff(u, -1))


def gate_4_perfect_pairing() -> Tuple[bool, Dict[str, Any]]:
    """Checks rank 6 after adding the infinity-normal q_star row."""
    start_time = time.monotonic()
    last_heartbeat = [start_time]
    maybe_heartbeat("GATE 4 -- Perfect pairing", start_time, last_heartbeat)

    m_prime = finite_m_prime_matrix()
    m_prime_sym = sp.Matrix(m_prime)
    m_prime_det = sp.simplify(m_prime_sym.det())
    m_prime_rank = int(m_prime_sym.rank())
    minors = leading_principal_minors(m_prime_sym)
    finite_positive_definite = all(minor > 0 for minor in minors)

    finite_serre_block = [[sp.simplify(-2 * entry) for entry in row] for row in m_prime]
    full_serre_matrix: List[List[sp.Rational]] = []
    for row in finite_serre_block:
        full_serre_matrix.append(row + [sp.Rational(0)])

    boundary_row = []
    boundary_records = []
    for j in INVARIANT_Q_DEGREES:
        maybe_heartbeat("GATE 4 -- Perfect pairing", start_time, last_heartbeat)
        residue = boundary_normal_residue(f"q_{j}")
        boundary_row.append(residue)
        boundary_records.append(
            {
                "normal_tangent": "sqrt(D(u))/(4u^2) d/du at infinity",
                "basis_element": f"q_{j}=x^{j}(dx)^2/y^2",
                "residue": rational_to_string(residue),
            }
        )
    qstar_residue = boundary_normal_residue("q_star")
    boundary_row.append(qstar_residue)
    boundary_records.append(
        {
            "normal_tangent": "sqrt(D(u))/(4u^2) d/du at infinity",
            "basis_element": "q_star=(dx)^2/y",
            "residue": rational_to_string(qstar_residue),
        }
    )
    full_serre_matrix.append(boundary_row)

    full_matrix_sym = sp.Matrix(full_serre_matrix)
    full_rank = int(full_matrix_sym.rank())
    full_det = sp.simplify(full_matrix_sym.det())
    pass_gate = bool(
        m_prime_rank == len(INVARIANT_Q_DEGREES)
        and m_prime_det != 0
        and finite_positive_definite
        and qstar_residue == 1
        and all(residue == 0 for residue in boundary_row[:-1])
        and full_rank == DIM_H0_K2
        and full_det != 0
    )
    return pass_gate, {
        "4_M_prime_5x5_finite_branch_invariant_block": matrix_to_strings(m_prime),
        "4_M_prime_det": rational_to_string(m_prime_det),
        "4_M_prime_rank": m_prime_rank,
        "4_M_prime_leading_principal_minors": [rational_to_string(minor) for minor in minors],
        "4_M_prime_positive_definite_by_sylvester": finite_positive_definite,
        "4_boundary_normal_residue_checks": boundary_records,
        "4_full_serre_pairing_matrix_rows_h0_to_h4_then_infinity_normal": matrix_to_strings(full_serre_matrix),
        "4_full_serre_pairing_det": rational_to_string(full_det),
        "4_full_serre_pairing_rank": full_rank,
        "4_full_serre_pairing_non_degenerate": bool(full_rank == DIM_H0_K2 and full_det != 0),
    }


def gate_5_hitchin_sanity() -> Tuple[bool, Dict[str, Any]]:
    x, lam, q_star_symbol = sp.symbols("x lambda q_star")
    char_poly_per_q: Dict[str, str] = {}
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_match = True
    q_exprs: List[Tuple[str, sp.Expr]] = [(f"q_{j}", x**j) for j in INVARIANT_Q_DEGREES]
    q_exprs.append(("q_star", q_star_symbol))
    for label, q_expr in q_exprs:
        maybe_heartbeat("GATE 5 -- Hitchin sanity", start_time, last_heartbeat)
        phi = sp.Matrix([[0, q_expr], [1, 0]])
        char_poly = sp.expand((lam * sp.eye(2) - phi).det())
        expected = sp.expand(lam**2 - q_expr)
        match = bool(char_poly == expected)
        all_match = all_match and match
        char_poly_per_q[label] = expr_to_string(char_poly)

    return all_match and len(char_poly_per_q) == DIM_H0_K2, {
        "5_char_poly_per_q_basis": char_poly_per_q,
        "5_hitchin_sanity_note": (
            "formal-only check mirroring Stage-2/3: det(lambda*I - [[0,q],[1,0]]) = lambda^2 - q "
            "for the five invariant columns and for the anti-invariant q_star symbol"
        ),
    }


def verdict_from_gates(gates: Dict[str, bool]) -> str:
    if all(gates.values()):
        return "PASS_GENUINE_SERRE_RESIDUE_CERTIFICATE_G3_DEG7"
    if not gates.get("3_trivial_deformation", False):
        return "PARTIAL_GATE_3_TRIVIAL_DEFORMATION_BOUNDARY_G3_DEG7"
    if not gates.get("4_perfect_pairing", False):
        return "PARTIAL_GATE_4_PAIRING_DEGENERATE_G3_DEG7"
    failing = [name for name, passed in gates.items() if not passed]
    return "FAIL_" + "_".join(failing)


def main() -> int:
    progress("Lam-Litt arXiv:2601.07933 Stage-4 genus-3 deg-7 Serre residue checker")
    progress("Pure Python + sympy exact arithmetic")

    gate_specs: List[Tuple[str, str, Callable[[], Tuple[bool, Dict[str, Any]]]]] = [
        ("1_h0k_basis", "GATE 1 -- H0(K) basis", gate_1_h0k_basis),
        ("2_h0k2_basis", "GATE 2 -- H0(K^2) basis", gate_2_h0k2_basis),
        ("3_trivial_deformation", "GATE 3 -- Trivial deformation", gate_3_trivial_deformation),
        ("4_perfect_pairing", "GATE 4 -- Perfect pairing", gate_4_perfect_pairing),
        ("5_hitchin_sanity", "GATE 5 -- Hitchin sanity", gate_5_hitchin_sanity),
    ]

    gates: Dict[str, bool] = {}
    gate_outputs: Dict[str, Any] = {}
    for gate_key, gate_name, gate_func in gate_specs:
        passed, details = run_gate(gate_name, gate_func)
        gates[gate_key] = passed
        gate_outputs.update(details)

    all_gates_pass = all(gates.values())
    verdict = verdict_from_gates(gates)
    x, _t, _u, roots, f, f_prime = polynomial_setup()

    output: Dict[str, Any] = {
        "paper": PAPER,
        "stage": STAGE,
        "prior_stage_references": {
            "stage_2_pass_commit": "17f4f263d",
            "stage_3_partial_commit": "a4a12478c",
            "stage_3_boundary_issue": (
                "degree-8 q_5=x^5(dx)^2/y^2 has a pole at infinity and reaches "
                "the nonzero Lagrange sum m=7"
            ),
        },
        "curve_f": CURVE_F_STRING,
        "curve_f_expanded": str(f),
        "curve_f_prime_expanded": str(f_prime),
        "finite_branch_points": [rational_to_string(root) for root in roots],
        "branch_point_at_infinity": True,
        "genus": GENUS,
        "dim_H0_K": DIM_H0_K,
        "dim_H0_K2": DIM_H0_K2,
        "basis_summary": {
            "H0_K": [f"x^{i} dx/y" for i in OMEGA_DEGREES],
            "H0_K2": [f"x^{j}(dx)^2/y^2" for j in INVARIANT_Q_DEGREES] + ["(dx)^2/y"],
            "split_note": (
                "The five x^j(dx)^2/y^2 elements are hyperelliptic-invariant. "
                "The sixth element (dx)^2/y is anti-invariant and is detected by "
                "the infinity-normal residue row."
            ),
        },
        "gates": gates,
        "gate_outputs": gate_outputs,
        "all_gates_pass": all_gates_pass,
        "verdict": verdict,
    }

    output_path = os.path.abspath(os.path.join(os.path.dirname(__file__), OUTPUT_NAME))
    progress("writing JSON output")
    with open(output_path, "w", encoding="utf-8") as handle:
        json.dump(output, handle, indent=2, sort_keys=True)
        handle.write("\n")

    progress(f"JSON: {output_path}")
    print(f"VERDICT: {verdict}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
