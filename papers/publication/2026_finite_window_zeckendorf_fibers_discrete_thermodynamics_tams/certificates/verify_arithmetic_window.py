#!/usr/bin/env python3
"""Verify and export arithmetic-window certificate data.

The script is intentionally self-contained.  It rebuilds the concrete
certificate objects used by the manuscript from the printed recurrence
polynomials and from exact finite-window counting:

* local carry-identity checks for the pinned normalizer table;
* exact moment windows S_q(m) in the arithmetic range q=9,...,17;
* exact Hankel matrices, nullmode checks, rank checks, and Smith witnesses;
* finite-field monic factorizations and Bezout gcd witnesses;
* discriminants and Euler-criterion witnesses for the squareclass table.

The all-tail recurrence theorem still uses the abstract exact-kernel
certification theorem stated in the paper.  The JSON artifact generated here
records the exact finite consequences that are independently rechecked inside
the local supplement.

Run from the paper root:

    python3 certificates/verify_arithmetic_window.py

It writes certificates/arithmetic_window_certificates.json.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "certificates" / "arithmetic_window_certificates.json"


REC_C: dict[int, tuple[int, ...]] = {
    9: (2, 62, 386, 2819, 62, 900, -450),
    10: (2, 96, 830, 7945, 2, 1852, -830, 4, -4),
    11: (2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174),
    12: (2, 243, 3608, 56447, -61236, -667319, 3608, -9582, 61242, 15404, -7216, 8, -8),
    13: (2, 388, 7414, 148038, -317916, -4165856, 136252, 1565891, 318938, 289380, -144690),
    14: (2, 621, 15140, 385463, -1443744, -22761161, 15140, -2116566, 1443750, 63044, -30280, 8, -8),
    15: (2, 1000, 30766, 994458, -6188172, -119408756, 8289820, 134208623, 6186122, 16637076, -8318538),
    16: (2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692, -124624, 8, -8),
    17: (
        2,
        2599,
        125872,
        6569850,
        -96034590,
        -2764163954,
        -643026032,
        -15022392733,
        769974566,
        15329386299,
        642908352,
        1347896340,
        -673948170,
    ),
}


FACTOR_PRIMES: dict[int, dict[str, int]] = {
    9: {"irreducible": 11, "nminus1": 17, "jordan": 13},
    10: {"irreducible": 17, "nminus1": 109, "jordan": 101},
    11: {"irreducible": 37, "nminus1": 17, "jordan": 19},
    12: {"irreducible": 29, "nminus1": 17, "jordan": 97},
    13: {"irreducible": 29, "nminus1": 61, "jordan": 41},
    14: {"irreducible": 37, "nminus1": 47, "jordan": 71},
    15: {"irreducible": 17, "nminus1": 127, "jordan": 37},
    16: {"irreducible": 239, "nminus1": 127, "jordan": 19},
    17: {"irreducible": 31, "nminus1": 59, "jordan": 23},
}


NULLMODES: dict[int, list[list[int]]] = {
    9: [
        [450, -900, -62, -2819, -386, -62, -2, 1, 0],
        [900, -1350, -1024, -5700, -3591, -510, -66, 0, 1],
    ],
    10: [
        [4, -4, 830, -1852, -2, -7945, -830, -96, -2, 1, 0],
        [8, -4, 1656, -2874, -1856, -15892, -9605, -1022, -100, 0, 1],
    ],
    11: [
        [9174, -18348, -1484, -86213, -9432, 21249, 1740, 153, 2, -1, 0],
        [18348, -27522, -21316, -173910, -105077, 33066, 24729, 2046, 157, 0, -1],
    ],
    12: [],
    13: [
        [144690, -289380, -318938, -1565891, -136252, 4165856, 317916, -148038, -7414, -388, -2, 1, 0],
        [289380, -434070, -927256, -3450720, -1838395, 8195460, 4801688, 21840, -162866, -8190, -392, 0, 1],
    ],
    14: [
        [8, -8, 30280, -63044, -1443750, 2116566, -15140, 22761161, 1443744, -385463, -15140, -621, -2, 1, 0],
        [16, -8, 60552, -95808, -2950544, 2789382, 2086286, 45507182, 25648649, 672818, -415743, -16382, -625, 0, 1],
    ],
    15: [
        [8318538, -16637076, -6186122, -134208623, -8289820, 119408756, 6188172, -994458, -30766, -1000, -2, 1, 0, 0, 0],
        [16637076, -24955614, -29009320, -274603368, -150788263, 230527692, 131785100, 4199256, -1055990, -32766, -1004, 0, 1, 0, 0],
        [8351812152, -16686987228, -6235822102, -134774466812, -8597582648, 119735602761, 6443452380, -866650732, -26689808, -2059990, -34774, 0, 0, 1, 0],
        [289268840412, -570185868672, -231803193656, -4673206478304, -423044667492, 4143722498496, 334923095889, -28137830112, -1936507616, -61463808, -2129538, 0, 0, 0, 1],
    ],
    16: [
        [8, -8, 124624, -255692, -24862794, 44606766, -62312, 585266591, 24862788, -2559407, -62312, -1611, -2, 1, 0, 0, 0],
        [16, -8, 249240, -386760, -49981280, 64350738, 44482142, 1170470870, 634992167, 19743974, -2684031, -65534, -1615, 0, 1, 0, 0],
        [12920, -12904, 201267752, -412693340, -40153799070, 71989945810, -36283142, 945250026607, 41323873490, -3498450138, -80889906, -5285796, -68764, 0, 0, 1, 0],
        [550112, -537192, 8569631832, -17381136936, -1710077859956, 3027185858154, 67705123442, 40245235580382, 2654914780639, -134671189458, -7783272506, -191668710, -5423324, 0, 0, 0, 1],
    ],
    17: [
        [673948170, -1347896340, -642908352, -15329386299, -769974566, 15022392733, 643026032, 2764163954, 96034590, -6569850, -125872, -2599, -2, 1, 0, 0, 0],
        [1347896340, -2021844510, -2633713044, -31301680950, -16869335431, 29274810900, 16308444797, 6171353940, 2956233134, 82894890, -6821594, -131070, -2603, 0, 1, 0, 0],
        [1754287086510, -3507226276680, -1675512284766, -39905026249341, -2035545476248, 39086418948568, 1703071572196, 7211427217059, 256149391710, -14145086416, -244749926, -13586791, -136276, 0, 0, 1, 0],
        [91842960814920, -181931634543330, -91120204853832, -2090702959567290, -144834080205557, 2045156046606060, 126715434485400, 378392278567500, 20298637003899, -639163486890, -31298419088, -598931250, -13859343, 0, 0, 0, 1],
    ],
}


SYNC10_STATES = ["000", "001", "002", "010", "100", "101", "0-12", "1-12", "01-1", "11-1"]


def sync10_edges() -> list[dict[str, Any]]:
    rows: list[tuple[str, str, int, int]] = []
    for d in (0, 1, 2):
        rows.append(("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        rows.append(("100", f"00{d}", d, 1))
    rows.extend(
        [
            ("001", "010", 0, 0),
            ("001", "100", 1, 0),
            ("001", "101", 2, 0),
            ("002", "11-1", 0, 0),
            ("002", "000", 1, 1),
            ("002", "001", 2, 1),
            ("010", "100", 0, 0),
            ("010", "101", 1, 0),
            ("010", "0-12", 2, 1),
            ("101", "010", 0, 1),
            ("101", "100", 1, 1),
            ("101", "101", 2, 1),
            ("0-12", "01-1", 0, 0),
            ("0-12", "010", 1, 0),
            ("0-12", "100", 2, 0),
            ("1-12", "01-1", 0, 1),
            ("1-12", "010", 1, 1),
            ("1-12", "100", 2, 1),
            ("01-1", "001", 0, 0),
            ("01-1", "002", 1, 0),
            ("01-1", "1-12", 2, 0),
            ("11-1", "001", 0, 1),
            ("11-1", "002", 1, 1),
            ("11-1", "1-12", 2, 1),
        ]
    )
    return [{"src": s, "input": a, "dst": t, "output": e} for (s, t, a, e) in rows]


def parse_signed_triple(label: str) -> tuple[int, int, int]:
    out: list[int] = []
    i = 0
    while i < len(label):
        if label[i] == "-":
            out.append(-int(label[i + 1]))
            i += 2
        else:
            out.append(int(label[i]))
            i += 1
    if len(out) != 3:
        raise RuntimeError(f"cannot parse state label {label!r}")
    return tuple(out)


def carry_pair(alpha: int, beta: int, gamma: int, digit: int) -> tuple[int, int]:
    # Expand in the basis (F_{n+1}, F_n):
    # F_{n+3}=2 F_{n+1}+F_n and F_{n+2}=F_{n+1}+F_n.
    return (2 * alpha + beta + gamma, alpha + beta + digit)


def normalizer_local_verification() -> dict[str, Any]:
    edges = sync10_edges()
    transition_counts = {(state, digit): 0 for state in SYNC10_STATES for digit in (0, 1, 2)}
    rows = []
    for edge in edges:
        src = edge["src"]
        dst = edge["dst"]
        digit = int(edge["input"])
        output = int(edge["output"])
        if src not in SYNC10_STATES or dst not in SYNC10_STATES:
            raise RuntimeError("transition references unknown state")
        transition_counts[(src, digit)] += 1
        s = parse_signed_triple(src)
        t = parse_signed_triple(dst)
        lhs = carry_pair(s[0], s[1], s[2], digit)
        rhs = carry_pair(output, t[0], t[1], t[2])
        if lhs != rhs:
            raise RuntimeError(f"carry identity failed for edge {src} --{digit}/{output}--> {dst}")
        rows.append(
            {
                "src": src,
                "input": digit,
                "output": output,
                "dst": dst,
                "lhs_basis_coefficients_F_nplus1_F_n": list(lhs),
                "rhs_basis_coefficients_F_nplus1_F_n": list(rhs),
            }
        )
    missing = [(state, digit) for (state, digit), count in transition_counts.items() if count != 1]
    if missing:
        raise RuntimeError(f"transition totality/determinism failed: {missing}")
    return {
        "checked_identity": (
            "alpha F_{n+3}+beta F_{n+2}+gamma F_{n+1}+d F_n"
            " = e F_{n+3}+alpha' F_{n+2}+beta' F_{n+1}+gamma' F_n"
        ),
        "basis_reduction": "all edges are reduced to equality of coefficients in the basis (F_{n+1}, F_n)",
        "total_edges": len(rows),
        "deterministic_total_inputs": [0, 1, 2],
        "verified_edges": rows,
    }


def poly_pq(q: int) -> sp.Poly:
    x = sp.Symbol("x")
    coeffs = REC_C[q]
    d = len(coeffs)
    expr = x**d
    for i, c in enumerate(coeffs, start=1):
        expr -= sp.Integer(c) * x ** (d - i)
    return sp.Poly(expr, x, domain=sp.ZZ)


def coeffs_asc(poly: sp.Poly, p: int | None = None) -> list[int]:
    deg = poly.degree()
    out = [int(poly.nth(i)) for i in range(deg + 1)]
    if p is not None:
        out = [x % p for x in out]
    return out


def poly_asc_from_recurrence(q: int) -> list[int]:
    return [-int(c) for c in reversed(REC_C[q])] + [1]


def fibonacci_numbers(limit: int) -> list[int]:
    fib = [0, 1]
    while len(fib) <= limit:
        fib.append(fib[-1] + fib[-2])
    return fib


def exact_moment_windows(max_m: int, q_values: list[int]) -> dict[int, dict[int, int]]:
    fib = fibonacci_numbers(max_m + 4)
    counts = [1]
    moments = {q: {} for q in q_values}
    power_cache: dict[int, tuple[int, ...]] = {}
    for m in range(max_m + 1):
        if m > 0:
            weight = fib[m + 1]
            new_counts = counts[:] + [0] * weight
            for i, value in enumerate(counts):
                new_counts[i + weight] += value
            counts = new_counts
        modulus = fib[m + 2]
        length = len(counts)
        sums = [0] * len(q_values)
        for residue in range(modulus):
            multiplicity = counts[residue]
            lifted = residue + modulus
            if lifted < length:
                multiplicity += counts[lifted]
            cached = power_cache.get(multiplicity)
            if cached is None:
                powers = []
                current = multiplicity ** q_values[0]
                powers.append(current)
                for _ in q_values[1:]:
                    current *= multiplicity
                    powers.append(current)
                cached = tuple(powers)
                power_cache[multiplicity] = cached
            for i, value in enumerate(cached):
                sums[i] += value
        for i, q in enumerate(q_values):
            moments[q][m] = sums[i]
    return moments


def factor_record(q: int, tag: str, p: int) -> dict[str, Any]:
    P = poly_pq(q)
    x = P.gens[0]
    Fp = sp.Poly(P.as_expr(), x, modulus=p)
    _, facs = sp.factor_list(Fp, modulus=p)
    factors = []
    degs: list[int] = []
    product = sp.Poly(1, x, modulus=p)
    for factor, exp in facs:
        f = sp.Poly(factor, x, modulus=p).monic()
        e = int(exp)
        degs.extend([f.degree()] * e)
        product *= f**e
        factors.append({"degree": int(f.degree()), "exponent": e, "coeffs_ascending_mod_p": coeffs_asc(f, p)})
    product = sp.Poly(product.as_expr(), x, modulus=p).monic()
    if product != Fp.monic():
        raise RuntimeError(f"factor product mismatch for q={q}, p={p}")
    s, t, h = sp.gcdex(Fp, Fp.diff(), x)
    hpoly = sp.Poly(h, x, modulus=p).monic()
    if hpoly.degree() != 0:
        raise RuntimeError(f"nontrivial gcd for q={q}, p={p}")
    s_poly = sp.Poly(s, x, modulus=p)
    t_poly = sp.Poly(t, x, modulus=p)
    bez = sp.Poly(s_poly.as_expr() * Fp.as_expr() + t_poly.as_expr() * Fp.diff().as_expr(), x, modulus=p)
    if sp.Poly(bez.as_expr() - 1, x, modulus=p) != sp.Poly(0, x, modulus=p):
        raise RuntimeError(f"Bezout check failed for q={q}, p={p}")
    return {
        "q": q,
        "tag": tag,
        "p": p,
        "degree_pattern": sorted([int(d) for d in degs], reverse=True),
        "factors": factors,
        "gcd_bezout": {
            "s_coeffs_ascending_mod_p": coeffs_asc(s_poly, p),
            "t_coeffs_ascending_mod_p": coeffs_asc(t_poly, p),
            "identity": "s*P_q + t*P_q_derivative = 1 in F_p[x]",
        },
    }


def recurrence_residuals_from_moments(q: int, moments: dict[int, dict[int, int]]) -> list[int]:
    coeffs = REC_C[q]
    d = len(coeffs)
    n = 2 * (q // 2) + 1
    residuals = []
    for j in range(2, n + 2):
        value = moments[q][j + d]
        for i, c in enumerate(coeffs, start=1):
            value -= c * moments[q][j + d - i]
        residuals.append(value)
    return residuals


def hankel_window_record(q: int, moments: dict[int, dict[int, int]]) -> dict[str, Any]:
    d = len(REC_C[q])
    n = 2 * (q // 2) + 1
    kappa = n - d
    hankel = sp.Matrix([[moments[q][i + j + 2] for j in range(n)] for i in range(n)])
    rank = int(hankel.rank())
    if rank != d:
        raise RuntimeError(f"Hankel rank mismatch for q={q}: expected {d}, got {rank}")
    basis = NULLMODES[q]
    if len(basis) != kappa:
        raise RuntimeError(f"nullmode basis length mismatch for q={q}")
    basis_matrix = sp.Matrix(basis)
    if int(basis_matrix.rank()) != kappa:
        raise RuntimeError(f"nullmode basis is not independent for q={q}")
    annihilation_rows = []
    for alpha in basis:
        vec = sp.Matrix(alpha)
        product = hankel.T * vec
        coords = [int(product[i, 0]) for i in range(product.rows)]
        if any(coords):
            raise RuntimeError(f"nullmode basis vector fails Hankel check for q={q}")
        annihilation_rows.append(coords)
    leading_minor = int(hankel[:d, :d].det())
    if leading_minor == 0:
        raise RuntimeError(f"leading d x d Hankel minor vanished for q={q}")
    residuals = recurrence_residuals_from_moments(q, moments)
    if any(residuals):
        raise RuntimeError(f"moment-window recurrence residuals failed for q={q}")
    return {
        "q": q,
        "n_q": n,
        "d_q": d,
        "kappa_q": kappa,
        "moment_values_m_0_through_2n": [str(moments[q][m]) for m in range(0, 2 * n + 1)],
        "residual_window_j_2_through_nplus1": residuals,
        "hankel_matrix": [[str(hankel[i, j]) for j in range(n)] for i in range(n)],
        "hankel_rank": rank,
        "leading_hankel_minor_det": str(leading_minor),
        "nullmode_basis_annihilation_vectors": annihilation_rows,
    }


def multiplier_for_alpha(alpha: list[int], p_coeffs: list[int], delta: int) -> list[int]:
    x = sp.Symbol("x")
    P = sp.Poly(sum(sp.Integer(c) * x**i for i, c in enumerate(p_coeffs)), x, domain=sp.ZZ)
    A = sp.Poly(sum(sp.Integer(c) * x**i for i, c in enumerate(alpha)), x, domain=sp.ZZ)
    Q, R = sp.div(A, P, domain=sp.QQ)
    if not sp.Poly(R, x, domain=sp.QQ).is_zero:
        raise RuntimeError("nullmode is not divisible by P")
    qcoeffs = [0] * delta
    for i in range(delta):
        val = sp.Rational(Q.nth(i))
        if val.q != 1:
            raise RuntimeError("nonintegral multiplier")
        qcoeffs[i] = int(val.p)
    return qcoeffs


def smith_record(q: int) -> dict[str, Any]:
    d = len(REC_C[q])
    n = 2 * (q // 2) + 1
    delta = n - d
    vectors = NULLMODES[q]
    if delta == 0:
        return {
            "q": q,
            "kappa": 0,
            "basis_change_matrix": [],
            "U": [],
            "V": [],
            "smith_diagonal": [],
            "nullmode_basis": [],
            "multipliers": [],
        }
    if len(vectors) != delta:
        raise RuntimeError(f"nullmode count mismatch for q={q}")
    p_coeffs = poly_asc_from_recurrence(q)
    multipliers = [multiplier_for_alpha(alpha, p_coeffs, delta) for alpha in vectors]
    # Columns are the coordinates of the displayed nullmode basis in the
    # canonical basis {P_q, x P_q, ..., x^{kappa-1}P_q}.
    M = sp.Matrix([[multipliers[col][row] for col in range(delta)] for row in range(delta)])
    det = int(M.det())
    if abs(det) != 1:
        raise RuntimeError(f"basis-change matrix is not unimodular for q={q}: det={det}")
    U = M.inv()
    if any(sp.Rational(x).q != 1 for x in U):
        raise RuntimeError(f"inverse is not integral for q={q}")
    I = sp.eye(delta)
    if U * M != I:
        raise RuntimeError(f"unimodular check failed for q={q}")
    return {
        "q": q,
        "kappa": delta,
        "basis_change_matrix": [[int(M[i, j]) for j in range(delta)] for i in range(delta)],
        "U": [[int(U[i, j]) for j in range(delta)] for i in range(delta)],
        "V": [[1 if i == j else 0 for j in range(delta)] for i in range(delta)],
        "smith_diagonal": [1] * delta,
        "nullmode_basis": vectors,
        "multipliers": multipliers,
        "identity": "U * basis_change_matrix * V = I_kappa",
    }


def discriminant_record(q: int, primes: list[int]) -> dict[str, Any]:
    P = poly_pq(q)
    x = P.gens[0]
    D = int(sp.discriminant(P, x))
    rows = []
    for p in primes:
        residue = D % p
        euler = pow(residue, (p - 1) // 2, p)
        if euler == 1:
            sign = 1
        elif euler == p - 1:
            sign = -1
        else:
            raise RuntimeError(f"zero Legendre symbol for q={q}, p={p}")
        rows.append({"p": p, "disc_mod_p": residue, "euler_witness_mod_p": euler, "legendre_symbol": sign})
    return {"q": q, "degree": P.degree(), "discriminant": str(D), "prime_witnesses": rows}


def stable_hash_payload(obj: Any) -> str:
    data = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    q_values = list(range(9, 18))
    moment_records = exact_moment_windows(34, q_values)
    factor_records = []
    for q, tags in FACTOR_PRIMES.items():
        for tag, p in tags.items():
            factor_records.append(factor_record(q, tag, p))

    square_primes = [31, 37, 43, 61]
    payload: dict[str, Any] = {
        "schema": "finite-window-zeckendorf-arithmetic-window-certificates-v2",
        "supplement_scope": {
            "local_verifier": (
                "checks the pinned normalizer table, exact moment windows, Hankel nullmodes,"
                " Smith witnesses, finite-field factorizations, and discriminant squareclasses"
            ),
            "paper_level_exact_kernel_statement": (
                "the all-tail recurrence theorem is the abstract exact-kernel certification theorem"
                " proved in the manuscript"
            ),
        },
        "polynomials": {
            str(q): {
                "degree": len(cs),
                "recurrence_coefficients_c": list(cs),
                "polynomial_coefficients_ascending": poly_asc_from_recurrence(q),
            }
            for q, cs in sorted(REC_C.items())
        },
        "fixed_normalizer_transition_table": {
            "name": "standard redundant Fibonacci carry table used by the arithmetic-window verifier",
            "states": SYNC10_STATES,
            "input_alphabet": [0, 1, 2],
            "output_alphabet": [0, 1],
            "initial_state": "000",
            "transitions": sync10_edges(),
            "terminal_output_convention": "the verifier applies the terminal flush specified in the paper before visible truncation",
        },
        "normalizer_local_verification": normalizer_local_verification(),
        "exact_moment_window_records": [hankel_window_record(q, moment_records) for q in q_values],
        "smith_unimodular_records": [smith_record(q) for q in range(9, 18)],
        "finite_field_factorization_records": factor_records,
        "discriminant_squareclass_records": [discriminant_record(q, square_primes) for q in [12, 13, 14, 15]],
    }
    payload["payload_sha256"] = stable_hash_payload(payload)
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {OUT}")
    print(f"payload_sha256={payload['payload_sha256']}")


if __name__ == "__main__":
    main()
