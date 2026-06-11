#!/usr/bin/env python3
"""Stage-3 Serre-residue certificate for Lam-Litt arXiv:2601.07933.

Curve under test:

    C: y^2 = f(x) = x(x-1)(x-2)(x-3)(x-4)(x-5)(x-6)(x-7).

The requested formal quadratic-differential columns are

    q_j = x^j (dx)^2 / y^2,  j = 0,...,5.

At a finite branch point a, write x = a + t^2. Then dx = 2t dt and
y^2 = f(a+t^2). Hence

    q_j = 4 t^2 (a+t^2)^j / f(a+t^2) * (dt)^2
        = (4 a^j / f'(a) + O(t^2)) * (dt)^2.

For the first-order deformation y^2 = f(x) + eps h(x), the branch point
a moves by delta_a = -h(a)/f'(a). The Cech tangent vector at the branch
disc is delta_a/(2t) d/dt. Contracting with q_j gives the local one-form

    (4 a^j / f'(a) + O(t^2)) * delta_a/(2t) dt,

whose residue is -2 h(a) a^j / f'(a)^2. Summing finite branch residues
therefore gives the requested formula

    <h, q_j> = -2 sum_a h(a) a^j / f'(a)^2.

Honesty note: for an even degree-8 hyperelliptic model, x^j(dx)^2/y^2 is
regular at the two points above infinity only for j <= 4. The formal q_5
column requested in this Stage-3 task is still checked exactly, but the
PGL_2 trivial-deformation gate exposes the boundary term
sum_a a^7/f'(a) = 1, so q_5 does not annihilate the quadratic vector field
v=x^2 under the finite-branch formula.
"""

from __future__ import annotations

import datetime as _datetime
import json
import os
import time
from typing import Any, Callable, Dict, List, Tuple

import sympy as sp


OUTPUT_NAME = "check_2601_07933_genus3_serre_residue_certificate_stage3_output.json"
CURVE_F_STRING = "f(x) = x(x-1)(x-2)(x-3)(x-4)(x-5)(x-6)(x-7)"
PAPER = "arXiv:2601.07933"
STAGE = "3 genus-3 Serre residue certificate"
HEARTBEAT_SECONDS = 20.0
GENUS = 3
DIM_H0_K = 3
DIM_H0_K2_REQUESTED = 6
BRANCH_COUNT = 8
Q_DEGREES = list(range(6))
V_DEGREES = list(range(3))


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


def polynomial_setup() -> Tuple[sp.Symbol, sp.Symbol, List[sp.Integer], sp.Expr, sp.Expr]:
    x, t = sp.symbols("x t")
    roots = [sp.Integer(root) for root in range(BRANCH_COUNT)]
    f = sp.expand(sp.prod(x - root for root in roots))
    f_prime = sp.diff(f, x)
    return x, t, roots, f, f_prime


def finite_branch_q_coefficient(
    x: sp.Symbol,
    t: sp.Symbol,
    f: sp.Expr,
    a: sp.Integer,
    j: int,
) -> sp.Expr:
    return sp.cancel(4 * t**2 * (a + t**2) ** j / f.subs(x, a + t**2))


def gate_1_regularity() -> Tuple[bool, Dict[str, Any]]:
    x, t, roots, f, f_prime = polynomial_setup()
    records: List[Dict[str, Any]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_match = True
    for a in roots:
        f_prime_at_a = sp.Rational(f_prime.subs(x, a))
        for j in Q_DEGREES:
            maybe_heartbeat("GATE 1 -- Regularity", start_time, last_heartbeat)
            coeff = finite_branch_q_coefficient(x, t, f, a, j)
            series = sp.series(coeff, t, 0, 16)
            series_without_o = sp.expand(series.removeO())
            computed_constant = sp.simplify(series_without_o.coeff(t, 0))
            predicted_constant = sp.simplify(4 * a**j / f_prime_at_a)

            lowest_nonzero_order = None
            leading_nonzero_coefficient = sp.Integer(0)
            for power in range(0, 16):
                coefficient = sp.simplify(series_without_o.coeff(t, power))
                if coefficient != 0:
                    lowest_nonzero_order = power
                    leading_nonzero_coefficient = coefficient
                    break

            leading_exponent = coeff.as_leading_term(t).as_coeff_exponent(t)[1]
            regular_no_negative_power = bool(leading_exponent >= 0)
            match = bool(regular_no_negative_power and computed_constant == predicted_constant)
            all_match = all_match and match
            records.append(
                {
                    "a": rational_to_string(a),
                    "j": j,
                    "computed_constant": rational_to_string(computed_constant),
                    "predicted_constant_4_a_j_over_fprime_a": rational_to_string(predicted_constant),
                    "lowest_nonzero_order": lowest_nonzero_order,
                    "leading_nonzero_coefficient": rational_to_string(leading_nonzero_coefficient),
                    "regular_no_negative_power_at_branch": regular_no_negative_power,
                    "match": match,
                }
            )

    return all_match and len(records) == BRANCH_COUNT * len(Q_DEGREES), {
        "1_leading_coefficients_count": len(records),
        "1_leading_coefficients": records,
    }


def gate_2_residue_derivation() -> Tuple[bool, Dict[str, Any]]:
    """Symbolically and numerically checks the finite-branch residue formula.

    With x=a+t^2, q_j has coefficient 4a^j/f'(a)+O(t^2). The deformation
    y^2=f+eps h moves a by delta_a=-h(a)/f'(a), hence the Cech tangent
    vector is delta_a/(2t)d/dt. The residue of q_j contracted with that
    vector is therefore

        Res_{t=0} (4a^j/f'(a))(-h(a)/f'(a))/(2t) dt
        = -2 h(a)a^j/f'(a)^2.
    """
    x, t, roots, f, f_prime = polynomial_setup()
    h_a, p_a, fp_a = sp.symbols("h_a p_a fp_a", nonzero=True)
    delta_symbolic = -h_a / fp_a
    symbolic_residue = sp.simplify((4 * p_a / fp_a) * delta_symbolic / 2)
    symbolic_expected = sp.simplify(-2 * h_a * p_a / fp_a**2)
    symbolic_match = bool(sp.simplify(symbolic_residue - symbolic_expected) == 0)

    records: List[Dict[str, Any]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]
    all_match = symbolic_match

    for i in Q_DEGREES:
        for j in Q_DEGREES:
            for a in roots:
                maybe_heartbeat("GATE 2 -- Residue derivation", start_time, last_heartbeat)
                f_prime_at_a = sp.Rational(f_prime.subs(x, a))
                h_at_a = sp.Integer(a) ** i
                q_monomial_at_a = sp.Integer(a) ** j
                delta_a = sp.simplify(-h_at_a / f_prime_at_a)
                q_dt2_coeff = finite_branch_q_coefficient(x, t, f, a, j)
                one_form_coeff = sp.cancel(q_dt2_coeff * delta_a / (2 * t))
                computed_residue = sp.simplify(sp.residue(one_form_coeff, t, 0))
                predicted_residue = sp.simplify(-2 * h_at_a * q_monomial_at_a / (f_prime_at_a**2))
                match = bool(computed_residue == predicted_residue)
                all_match = all_match and match
                records.append(
                    {
                        "a": rational_to_string(a),
                        "h_degree_i": i,
                        "q_degree_j": j,
                        "h_a": rational_to_string(h_at_a),
                        "a_j": rational_to_string(q_monomial_at_a),
                        "delta_a": rational_to_string(delta_a),
                        "computed_residue": rational_to_string(computed_residue),
                        "predicted_residue": rational_to_string(predicted_residue),
                        "match": match,
                    }
                )

    return all_match and len(records) == BRANCH_COUNT * len(Q_DEGREES) * len(Q_DEGREES), {
        "2_residue_formula": "<h,q_j> = -2 sum_a h(a) a^j / f'(a)^2",
        "2_symbolic_residue_check": {
            "q_constant": "4*p_a/fp_a",
            "delta_a": "-h_a/fp_a",
            "residue": str(symbolic_residue),
            "expected": str(symbolic_expected),
            "match": symbolic_match,
        },
        "2_residue_checks_count": len(records),
        "2_residue_checks": records,
    }


def lagrange_sum(m: int) -> sp.Rational:
    x, _t, roots, _f, f_prime = polynomial_setup()
    total = sp.Rational(0)
    for a in roots:
        total += sp.Rational(a**m, sp.Rational(f_prime.subs(x, a)))
    return sp.simplify(total)


def gate_3_trivial_deformation() -> Tuple[bool, Dict[str, Any]]:
    x, _t, roots, _f, f_prime = polynomial_setup()
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    sums_m_0_to_7 = []
    for m in range(8):
        maybe_heartbeat("GATE 3 -- Trivial deformation", start_time, last_heartbeat)
        sums_m_0_to_7.append(lagrange_sum(m))

    lagrange_core_pass = all(value == 0 for value in sums_m_0_to_7[:7])
    sanity_contrast_pass = bool(sums_m_0_to_7[7] != 0)

    pairings: List[Dict[str, Any]] = []
    all_pairings_zero = True
    first_nonzero_pairing = None
    for v_degree in V_DEGREES:
        for j in Q_DEGREES:
            maybe_heartbeat("GATE 3 -- Trivial deformation", start_time, last_heartbeat)
            total = sp.Rational(0)
            for a in roots:
                f_prime_at_a = sp.Rational(f_prime.subs(x, a))
                h_at_a = -sp.Integer(a) ** v_degree * f_prime_at_a
                total += sp.Rational(-2) * h_at_a * sp.Integer(a) ** j / (f_prime_at_a**2)
            total = sp.simplify(total)
            is_zero = bool(total == 0)
            all_pairings_zero = all_pairings_zero and is_zero
            record = {
                "v": "1" if v_degree == 0 else f"x^{v_degree}",
                "q_j": f"q_{j}",
                "m_v_plus_j": v_degree + j,
                "pairing_with_h_minus_v_fprime": rational_to_string(total),
                "zero": is_zero,
            }
            if not is_zero and first_nonzero_pairing is None:
                first_nonzero_pairing = record
            pairings.append(record)

    pass_gate = bool(lagrange_core_pass and sanity_contrast_pass and all_pairings_zero)
    note = (
        "For monic f of degree 8, sum_a a^m/f'(a)=0 for m<=6 and "
        "sum_a a^7/f'(a)=1. Therefore h=-v f' pairs trivially with q_j "
        "only when deg(v)+j<=6 under the finite-branch formula. The requested "
        "formal q_5 column paired with v=x^2 reaches m=7 and gives pairing 2."
    )

    return pass_gate, {
        "3_lagrange_identity_max_m": 6,
        "3_lagrange_sums_m_0_to_7": [rational_to_string(value) for value in sums_m_0_to_7],
        "3_lagrange_core_pass": lagrange_core_pass,
        "3_lagrange_m_7_nonzero_sanity": sanity_contrast_pass,
        "3_trivial_deformation_pairings": pairings,
        "3_trivial_deformation_all_pairings_zero": all_pairings_zero,
        "3_first_nonzero_pairing": first_nonzero_pairing,
        "3_structural_note": note,
    }


def gate_4_perfect_pairing() -> Tuple[bool, Dict[str, Any]]:
    x, _t, roots, _f, f_prime = polynomial_setup()
    matrix: List[List[sp.Rational]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    for i in Q_DEGREES:
        row: List[sp.Rational] = []
        for j in Q_DEGREES:
            maybe_heartbeat("GATE 4 -- Perfect pairing", start_time, last_heartbeat)
            entry = sp.Rational(0)
            for a in roots:
                f_prime_at_a = sp.Rational(f_prime.subs(x, a))
                entry += sp.Rational(a ** (i + j), f_prime_at_a**2)
            row.append(sp.simplify(entry))
        matrix.append(row)

    progress("GATE 4 -- Perfect pairing: exact M' matrix")
    for row in matrix_to_strings(matrix):
        print("  " + json.dumps(row), flush=True)

    progress("GATE 4 -- Perfect pairing: computing exact determinant")
    determinant = sp.simplify(sp.Matrix(matrix).det())
    det_nonzero = bool(determinant != 0)
    progress(f"GATE 4 -- Perfect pairing: det={rational_to_string(determinant)}")

    return det_nonzero, {
        "4_M_prime_6x6": matrix_to_strings(matrix),
        "4_M_prime_det": rational_to_string(determinant),
        "4_M_prime_det_nonzero": det_nonzero,
    }


def gate_5_hitchin_sanity() -> Tuple[bool, Dict[str, Any]]:
    x, lam = sp.symbols("x lambda")
    char_poly_per_q: Dict[str, str] = {}
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_match = True
    for j in Q_DEGREES:
        maybe_heartbeat("GATE 5 -- Hitchin sanity", start_time, last_heartbeat)
        q_expr = x**j
        phi = sp.Matrix([[0, q_expr], [1, 0]])
        char_poly = sp.expand((lam * sp.eye(2) - phi).det())
        expected = sp.expand(lam**2 - q_expr)
        match = bool(char_poly == expected)
        all_match = all_match and match
        char_poly_per_q[f"q_{j}"] = expr_to_string(char_poly)

    return all_match and len(char_poly_per_q) == len(Q_DEGREES), {
        "5_char_poly_per_q_basis": char_poly_per_q,
    }


def infinity_regular_note() -> str:
    return (
        "With u=1/x at either point above infinity, y~u^-4 and "
        "x^j(dx)^2/y^2 has coefficient u^(4-j)(du)^2. Thus the requested "
        "q_j are regular at infinity for j<=4, while q_5 has a simple pole. "
        "The 6x6 M' requested in Gate 4 is computed exactly as a formal "
        "finite-branch residue matrix, but Gate 3 does not pass for the full "
        "requested q_0,...,q_5 list."
    )


def verdict_from_gates(gates: Dict[str, bool], gate_outputs: Dict[str, Any]) -> str:
    if all(gates.values()):
        return "PASS_GENUS3_GENUINE_SERRE_RESIDUE_CERTIFICATE"
    if not gates.get("4_perfect_pairing", False):
        return "PARTIAL_M_PRIME_DEGENERATE"
    if not gates.get("3_trivial_deformation", False):
        return "PARTIAL_GATE_3_TRIVIAL_DEFORMATION_BOUNDARY"
    failing = [name for name, passed in gates.items() if not passed]
    return "FAIL_" + "_".join(failing)


def main() -> int:
    progress("Lam-Litt arXiv:2601.07933 Stage-3 genus-3 Serre residue checker")
    progress("Pure Python + sympy exact arithmetic")

    gate_specs: List[Tuple[str, str, Callable[[], Tuple[bool, Dict[str, Any]]]]] = [
        ("1_regularity", "GATE 1 -- Regularity", gate_1_regularity),
        ("2_residue_derivation", "GATE 2 -- Residue derivation", gate_2_residue_derivation),
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
    verdict = verdict_from_gates(gates, gate_outputs)
    x, _t, _roots, f, _f_prime = polynomial_setup()

    output: Dict[str, Any] = {
        "paper": PAPER,
        "stage": STAGE,
        "curve_f": CURVE_F_STRING,
        "curve_f_expanded": str(f),
        "genus": GENUS,
        "dim_H0_K": DIM_H0_K,
        "dim_H0_K2": DIM_H0_K2_REQUESTED,
        "gates": gates,
        "gate_outputs": gate_outputs,
        "all_gates_pass": all_gates_pass,
        "verdict": verdict,
    }

    if verdict == "PARTIAL_M_PRIME_DEGENERATE":
        output["structural_note"] = (
            "The requested M' determinant vanished. Inspect the Lagrange sums "
            "and Hankel moments in gate_outputs['4_M_prime_6x6'] for the "
            "specific higher-degree cancellation."
        )
    elif verdict == "PARTIAL_GATE_3_TRIVIAL_DEFORMATION_BOUNDARY":
        output["structural_note"] = infinity_regular_note()

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
