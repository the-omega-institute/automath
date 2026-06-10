#!/usr/bin/env python3
"""Stage-2 genuine Serre-residue certificate for Litt-Lam arXiv:2601.07933.

This checker follows the concrete genus-2 hyperelliptic curve from Stage 1:

    C: y^2 = f(x) = x*(x-1)*(x-2)*(x-3)*(x-4)*(x-5).

It certifies the reinterpretation that the Stage-1b squared-denominator
matrix M' is the genuine branch-residue Serre-duality matrix, up to the
global nonzero scalar -2 arising from the local Cech tangent convention.
"""

from __future__ import annotations

import datetime as _datetime
import json
import os
import time
from typing import Any, Callable, Dict, List, Tuple

import sympy as sp


OUTPUT_NAME = "check_2601_07933_genus2_serre_residue_certificate_stage2_output.json"
CURVE_F_STRING = "f(x) = x*(x-1)*(x-2)*(x-3)*(x-4)*(x-5)"
PAPER = "arXiv:2601.07933"
STAGE = "Stage-2 genuine Serre residue certificate for genus-2 Lam-Litt curve"
EXPECTED_M_PRIME_DET = sp.Rational(49, 14929920)
HEARTBEAT_SECONDS = 20.0


def timestamp() -> str:
    return _datetime.datetime.now(_datetime.timezone.utc).isoformat().replace("+00:00", "Z")


def progress(message: str) -> None:
    print(f"[{timestamp()}] {message}", flush=True)


def rational_to_string(value: Any) -> str:
    return str(sp.Rational(value))


def expr_to_string(value: Any) -> str:
    return str(sp.simplify(value))


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
    roots = [sp.Integer(root) for root in range(6)]
    f = sp.expand(sp.prod(x - root for root in roots))
    f_prime = sp.diff(f, x)
    return x, t, roots, f, f_prime


def gate_1_regularity() -> Tuple[bool, Dict[str, Any]]:
    x, t, roots, f, f_prime = polynomial_setup()
    records: List[Dict[str, Any]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_match = True
    for a in roots:
        f_prime_at_a = sp.Rational(f_prime.subs(x, a))
        for j in range(3):
            maybe_heartbeat("GATE 1 -- Regularity gate", start_time, last_heartbeat)
            expr = sp.cancel(4 * t**2 * (a + t**2) ** j / f.subs(x, a + t**2))
            series = sp.series(expr, t, 0, 8)
            series_without_o = sp.expand(series.removeO())
            computed_constant = sp.simplify(series_without_o.coeff(t, 0))
            predicted = sp.simplify(4 * a**j / f_prime_at_a)

            lowest_nonzero_order = None
            leading_nonzero_coefficient = sp.Integer(0)
            for power in range(0, 8):
                coefficient = sp.simplify(series_without_o.coeff(t, power))
                if coefficient != 0:
                    lowest_nonzero_order = power
                    leading_nonzero_coefficient = coefficient
                    break

            has_no_negative_power = not bool(expr.as_leading_term(t).as_coeff_exponent(t)[1] < 0)
            match = bool(has_no_negative_power and computed_constant == predicted)
            all_match = all_match and match
            records.append(
                {
                    "a": rational_to_string(a),
                    "j": j,
                    "predicted": rational_to_string(predicted),
                    "computed": rational_to_string(computed_constant),
                    "match": match,
                    "series_truncated": str(series),
                    "lowest_nonzero_order": lowest_nonzero_order,
                    "leading_nonzero_coefficient": rational_to_string(leading_nonzero_coefficient),
                    "regular_no_negative_power": bool(has_no_negative_power),
                }
            )

    return all_match and len(records) == 18, {"leading_coefficients": records}


def gate_2_residue_derivation() -> Tuple[bool, Dict[str, Any]]:
    x, t, roots, f, f_prime = polynomial_setup()
    records: List[Dict[str, Any]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_match = True
    for i in range(3):
        for j in range(3):
            for a in roots:
                maybe_heartbeat("GATE 2 -- Residue derivation gate", start_time, last_heartbeat)
                f_prime_at_a = sp.Rational(f_prime.subs(x, a))
                h_at_a = sp.Integer(a) ** i
                p_at_a = sp.Integer(a) ** j
                delta_a = sp.simplify(-h_at_a / f_prime_at_a)
                q_dt2_coeff = sp.cancel(4 * t**2 * (a + t**2) ** j / f.subs(x, a + t**2))
                one_form_coeff = sp.cancel(q_dt2_coeff * delta_a / (2 * t))
                computed_residue = sp.simplify(sp.residue(one_form_coeff, t, 0))
                predicted_residue = sp.simplify(-2 * h_at_a * p_at_a / (f_prime_at_a**2))
                match = bool(computed_residue == predicted_residue)
                all_match = all_match and match
                records.append(
                    {
                        "a": rational_to_string(a),
                        "i": i,
                        "j": j,
                        "h_a": rational_to_string(h_at_a),
                        "P_a": rational_to_string(p_at_a),
                        "delta_a": rational_to_string(delta_a),
                        "computed_residue": rational_to_string(computed_residue),
                        "predicted_residue": rational_to_string(predicted_residue),
                        "match": match,
                    }
                )

    residue_formula = "<x^i, x^j> = -2 * sum_{a in {0,1,2,3,4,5}} a^(i+j) / f'(a)^2"
    return all_match and len(records) == 54, {
        "residue_formula": residue_formula,
        "residue_checks": records,
    }


def gate_3_trivial_deformation() -> Tuple[bool, Dict[str, Any]]:
    x, _t, roots, f, f_prime = polynomial_setup()
    records: List[Dict[str, Any]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_zero = True
    for v_degree in range(3):
        for p_degree in range(3):
            maybe_heartbeat("GATE 3 -- Trivial deformation gate", start_time, last_heartbeat)
            total = sp.Rational(0)
            for a in roots:
                f_prime_at_a = sp.Rational(f_prime.subs(x, a))
                total += sp.Rational(a ** (v_degree + p_degree), f_prime_at_a)
            total = sp.simplify(total)
            is_zero = bool(total == 0)
            all_zero = all_zero and is_zero
            records.append(
                {
                    "v": "1" if v_degree == 0 else f"x^{v_degree}",
                    "P": "1" if p_degree == 0 else f"x^{p_degree}",
                    "degree_vP": v_degree + p_degree,
                    "sum_a_v_a_P_a_over_fprime_a": rational_to_string(total),
                    "match_zero": is_zero,
                }
            )

    lagrange_identity = (
        "For monic f of degree 6 with simple roots a, "
        "sum_a a^m / f'(a) = 0 for m = 0,1,2,3,4 and = 1 for m = 5; "
        "therefore PGL_2 tangent deformations h=-v f' pair trivially with P "
        "when deg(vP) <= 4."
    )
    return all_zero and len(records) == 9, {
        "lagrange_identity": lagrange_identity,
        "trivial_deformation_checks": records,
    }


def gate_4_perfect_pairing() -> Tuple[bool, Dict[str, Any]]:
    x, _t, roots, _f, f_prime = polynomial_setup()
    matrix: List[List[sp.Rational]] = []
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    for i in range(3):
        row: List[sp.Rational] = []
        for j in range(3):
            maybe_heartbeat("GATE 4 -- Perfect pairing gate", start_time, last_heartbeat)
            entry = sp.Rational(0)
            for a in roots:
                f_prime_at_a = sp.Rational(f_prime.subs(x, a))
                entry += sp.Rational(a ** (i + j), f_prime_at_a**2)
            row.append(sp.simplify(entry))
        matrix.append(row)

    determinant = sp.simplify(sp.Matrix(matrix).det())
    pass_gate = bool(determinant != 0 and determinant == EXPECTED_M_PRIME_DET)
    return pass_gate, {
        "M_prime_3x3": matrix_to_strings(matrix),
        "M_prime_det": rational_to_string(determinant),
        "expected_M_prime_det": rational_to_string(EXPECTED_M_PRIME_DET),
        "det_nonzero": bool(determinant != 0),
        "det_matches_stage1b": bool(determinant == EXPECTED_M_PRIME_DET),
    }


def gate_5_hitchin_sanity() -> Tuple[bool, Dict[str, Any]]:
    x, lam = sp.symbols("x lam")
    char_poly_per_q: Dict[str, str] = {}
    start_time = time.monotonic()
    last_heartbeat = [start_time]

    all_match = True
    for q_expr in [sp.Integer(1), x, x**2]:
        maybe_heartbeat("GATE 5 -- Hitchin sanity check", start_time, last_heartbeat)
        phi = sp.Matrix([[0, q_expr], [1, 0]])
        char_poly = sp.expand((lam * sp.eye(2) - phi).det())
        expected = sp.expand(lam**2 - q_expr)
        match = bool(char_poly == expected)
        all_match = all_match and match
        char_poly_per_q[expr_to_string(q_expr)] = expr_to_string(char_poly)

    return all_match and len(char_poly_per_q) == 3, {
        "char_poly_per_q": char_poly_per_q,
        "hitchin_sanity_note": (
            "formal-only check: verifies det(lam*I - [[0,q],[1,0]]) = lam^2 - q "
            "without instantiating the line bundle K^{1/2}"
        ),
    }


def verdict_from_gates(gates: Dict[str, bool]) -> str:
    if all(gates.values()):
        return "PASS_GENUINE_SERRE_RESIDUE_CERTIFICATE"
    failing = [name for name, passed in gates.items() if not passed]
    return "PARTIAL_" + "_".join(failing)


def main() -> int:
    progress("Litt-Lam arXiv:2601.07933 Stage-2 Serre residue checker")
    progress("Pure Python + sympy exact arithmetic")

    gate_specs: List[Tuple[str, str, Callable[[], Tuple[bool, Dict[str, Any]]]]] = [
        ("gate_1_regularity", "GATE 1 -- Regularity gate", gate_1_regularity),
        ("gate_2_residue_derivation", "GATE 2 -- Residue derivation gate", gate_2_residue_derivation),
        ("gate_3_trivial_deformation", "GATE 3 -- Trivial deformation gate", gate_3_trivial_deformation),
        ("gate_4_perfect_pairing", "GATE 4 -- Perfect pairing gate", gate_4_perfect_pairing),
        ("gate_5_hitchin_sanity", "GATE 5 -- Hitchin sanity check", gate_5_hitchin_sanity),
    ]

    gates: Dict[str, bool] = {}
    gate_outputs: Dict[str, Any] = {}
    for gate_key, gate_name, gate_func in gate_specs:
        passed, details = run_gate(gate_name, gate_func)
        gates[gate_key] = passed
        gate_outputs.update(details)

    all_gates_pass = all(gates.values())
    verdict = verdict_from_gates(gates)
    x, _t, _roots, f, _f_prime = polynomial_setup()

    output: Dict[str, Any] = {
        "paper": PAPER,
        "stage": STAGE,
        "curve_f": CURVE_F_STRING,
        "curve_f_expanded": str(f),
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
