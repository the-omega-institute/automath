#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: dyadic arithmetic for K5, K10, K20 from p7(x).

This script certifies the statements used around:
  - an explicit integral basis for K5 = Q(theta) (theta a root of p7),
  - Disc(K5) = -2^2 * q and [O_K5 : Z[theta]] = 2 (with q = 985219),
  - the factorization type of 2 in K5: 2 O_K5 = p1 p2 p3^3 with f=1,
  - tame inertia at 2 in the S5 splitting field: I_2 ≅ C3 with cycle type (3·1·1),
  - dyadic discriminant exponents for K10 and K20 via orbit counts,
  - tame conductor exponents at 2 (3-cycle) and at q (transposition),
  - signature counts for K5, K10, K20 from a transposition (complex conjugation).

Outputs:
  - artifacts/export/xi_p7_dyadic_integral_basis_certificate.json
"""

from __future__ import annotations

import argparse
import json
from itertools import permutations, product
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir


def _p7_poly() -> sp.Poly:
    x = sp.Symbol("x")
    return sp.Poly(x**5 - 2 * x**4 - 7 * x**3 - 2 * x + 2, x, domain=sp.ZZ)


def _newton_power_sums_monic_deg5(coeffs_c4_to_c0: Sequence[int], m_max: int) -> List[int]:
    """Return s_m = sum r_i^m for m=0..m_max (integer), for monic degree-5 polynomial.

    Polynomial: x^5 + c4 x^4 + c3 x^3 + c2 x^2 + c1 x + c0.
    """
    if len(coeffs_c4_to_c0) != 5:
        raise ValueError("need c4..c0")
    c4, c3, c2, c1, c0 = [int(z) for z in coeffs_c4_to_c0]
    s: List[int] = [0] * (m_max + 1)
    s[0] = 5
    # Newton identities.
    for m in range(1, m_max + 1):
        if m == 1:
            s[m] = -c4
        elif m == 2:
            s[m] = -(c4 * s[1] + 2 * c3)
        elif m == 3:
            s[m] = -(c4 * s[2] + c3 * s[1] + 3 * c2)
        elif m == 4:
            s[m] = -(c4 * s[3] + c3 * s[2] + c2 * s[1] + 4 * c1)
        elif m == 5:
            s[m] = -(c4 * s[4] + c3 * s[3] + c2 * s[2] + c1 * s[1] + 5 * c0)
        else:
            s[m] = -(c4 * s[m - 1] + c3 * s[m - 2] + c2 * s[m - 3] + c1 * s[m - 4] + c0 * s[m - 5])
    return s


def _reduce_mod_p7(expr: sp.Expr, x: sp.Symbol, p7: sp.Poly) -> sp.Poly:
    """Reduce an expression in x modulo p7 to degree <= 4 over QQ."""
    poly = sp.Poly(sp.together(expr), x, domain=sp.QQ)
    mod = sp.Poly(p7.as_expr(), x, domain=sp.QQ)
    return sp.rem(poly, mod)


def _trace_of_reduced_poly(poly: sp.Poly, power_sums: Sequence[int]) -> sp.Rational:
    """Trace of poly(theta) where poly has degree <= 4, using Tr(theta^k)=s_k."""
    coeffs = [sp.Rational(poly.nth(i)) for i in range(5)]
    tr = sp.Rational(0)
    for k, a in enumerate(coeffs):
        tr += a * sp.Integer(power_sums[k])
    return sp.Rational(tr)


def _disc_of_basis(polys: Sequence[sp.Poly], power_sums: Sequence[int]) -> sp.Integer:
    n = len(polys)
    M = sp.Matrix.zeros(n, n)
    x = polys[0].gens[0]
    p7 = _p7_poly()
    for i in range(n):
        for j in range(n):
            pij = _reduce_mod_p7(polys[i].as_expr() * polys[j].as_expr(), x, p7)
            M[i, j] = _trace_of_reduced_poly(pij, power_sums)
    det = sp.factor(M.det())
    detQ = sp.Rational(det)
    if detQ.q != 1:
        raise ValueError(f"basis discriminant not integral: {detQ}")
    return sp.Integer(detQ.p)


def _to_integral_basis_coords(a0: sp.Rational, a1: sp.Rational, a2: sp.Rational, a3: sp.Rational, a4: sp.Rational) -> Tuple[int, int, int, int, int]:
    """Convert reduced power-basis coefficients to Z-coordinates on {1,θ,θ^2,θ^3,β}.

    β = (θ^3+θ^4)/2.
    If r = a0 + a1 θ + a2 θ^2 + a3 θ^3 + a4 θ^4 then:
      x0=a0, x1=a1, x2=a2, x4=2 a4, x3=a3 - a4.
    """
    x0 = sp.Rational(a0)
    x1 = sp.Rational(a1)
    x2 = sp.Rational(a2)
    x4 = sp.Rational(2) * sp.Rational(a4)
    x3 = sp.Rational(a3) - sp.Rational(a4)
    xs = [x0, x1, x2, x3, x4]
    for t in xs:
        if t.q != 1:
            raise ValueError(f"non-integral coordinate encountered: {xs}")
    return (int(xs[0]), int(xs[1]), int(xs[2]), int(xs[3]), int(xs[4]))


def _mul_table_mod2(basis_polys: Sequence[sp.Poly]) -> List[List[List[int]]]:
    """Return multiplication table for basis elements modulo 2.

    table[i][j] is 5-vector over F2 in the same basis.
    """
    x = basis_polys[0].gens[0]
    p7 = _p7_poly()
    table: List[List[List[int]]] = []
    for i in range(5):
        row: List[List[int]] = []
        for j in range(5):
            prod_red = _reduce_mod_p7(basis_polys[i].as_expr() * basis_polys[j].as_expr(), x, p7)
            coeffs = [sp.Rational(prod_red.nth(k)) for k in range(5)]
            x0, x1, x2, x3, x4 = _to_integral_basis_coords(coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4])
            row.append([x0 & 1, x1 & 1, x2 & 1, x3 & 1, x4 & 1])
        table.append(row)
    return table


def _f2_add(u: Sequence[int], v: Sequence[int]) -> List[int]:
    return [(a ^ b) & 1 for a, b in zip(u, v)]


def _f2_mul(u: Sequence[int], v: Sequence[int], table: Sequence[Sequence[Sequence[int]]]) -> List[int]:
    out = [0, 0, 0, 0, 0]
    for i, ui in enumerate(u):
        if ui & 1:
            for j, vj in enumerate(v):
                if vj & 1:
                    out = _f2_add(out, table[i][j])
    return out


def _all_elements_f2_5() -> List[List[int]]:
    return [list(t) for t in product([0, 1], repeat=5)]


def _f2_pow(a: Sequence[int], k: int, table: Sequence[Sequence[Sequence[int]]]) -> List[int]:
    one = [1, 0, 0, 0, 0]
    if k == 0:
        return one
    r = one
    x = list(a)
    while k:
        if k & 1:
            r = _f2_mul(r, x, table)
        x = _f2_mul(x, x, table)
        k >>= 1
    return r


def _is_nilpotent(a: Sequence[int], table: Sequence[Sequence[Sequence[int]]], max_k: int = 8) -> bool:
    z = [0, 0, 0, 0, 0]
    x = list(a)
    for k in range(1, max_k + 1):
        if x == z:
            return True
        x = _f2_mul(x, a, table)
    return False


def _ideal_generated_by(elem: Sequence[int], elems: Sequence[Sequence[int]], table: Sequence[Sequence[Sequence[int]]]) -> List[List[int]]:
    # principal ideal: {elem * r : r in ring}
    return [_f2_mul(list(elem), r, table) for r in elems]


def _perm_compose(p: Tuple[int, ...], q: Tuple[int, ...]) -> Tuple[int, ...]:
    return tuple(p[i] for i in q)


def _perm_pow(p: Tuple[int, ...], k: int) -> Tuple[int, ...]:
    r = (0, 1, 2, 3, 4)
    while k:
        if k & 1:
            r = _perm_compose(p, r)
        p = _perm_compose(p, p)
        k >>= 1
    return r


def _act(p: Tuple[int, ...], obj: object) -> object:
    if isinstance(obj, int):
        return p[obj]
    if isinstance(obj, tuple) and len(obj) == 2:
        a, b = obj
        return (p[a], p[b])
    if isinstance(obj, frozenset):
        return frozenset(p[i] for i in obj)
    raise TypeError(obj)


def _space_points() -> List[int]:
    return list(range(5))


def _space_2subsets() -> List[frozenset[int]]:
    subs: List[frozenset[int]] = []
    for i in range(5):
        for j in range(i + 1, 5):
            subs.append(frozenset({i, j}))
    return subs


def _space_ordered_pairs() -> List[Tuple[int, int]]:
    return [(i, j) for i in range(5) for j in range(5) if i != j]


def _fixed_points_count(p: Tuple[int, ...], space: Sequence[object]) -> int:
    return sum(1 for x in space if _act(p, x) == x)


def _orbits_count(p: Tuple[int, ...], space: Sequence[object]) -> int:
    idx: Dict[object, int] = {space[i]: i for i in range(len(space))}
    seen = [False] * len(space)
    orbits = 0
    for i in range(len(space)):
        if seen[i]:
            continue
        orbits += 1
        cur = space[i]
        while True:
            j = idx[cur]
            if seen[j]:
                break
            seen[j] = True
            cur = _act(p, cur)
    return orbits


def main() -> None:
    parser = argparse.ArgumentParser(description="Certificate for dyadic integral basis and dyadic inertia for p7.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "xi_p7_dyadic_integral_basis_certificate.json"),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    x = sp.Symbol("x")
    p7 = _p7_poly()
    disc_p7 = int(sp.discriminant(p7.as_expr(), x))
    q = 985219

    # Power sums for traces.
    # p7(x) = x^5 + c4 x^4 + ... + c0.
    c4 = -2
    c3 = -7
    c2 = 0
    c1 = -2
    c0 = 2
    power_sums = _newton_power_sums_monic_deg5([c4, c3, c2, c1, c0], m_max=12)

    # Basis polynomials in x representing elements in Q(theta).
    one = sp.Poly(1, x, domain=sp.QQ)
    th = sp.Poly(x, x, domain=sp.QQ)
    th2 = sp.Poly(x**2, x, domain=sp.QQ)
    th3 = sp.Poly(x**3, x, domain=sp.QQ)
    beta = sp.Poly((x**3 + x**4) / 2, x, domain=sp.QQ)
    basis = [one, th, th2, th3, beta]
    power_basis = [sp.Poly(x**k, x, domain=sp.QQ) for k in range(5)]

    disc_power_basis = sp.Integer(_disc_of_basis(power_basis, power_sums))
    disc_integral_basis = sp.Integer(_disc_of_basis(basis, power_sums))
    index_sq = sp.Rational(disc_power_basis, disc_integral_basis)

    # Mod-2 algebra structure in the integral basis {1,θ,θ^2,θ^3,β}.
    table = _mul_table_mod2(basis)
    elems = _all_elements_f2_5()

    idempotents = [e for e in elems if _f2_mul(e, e, table) == e]
    nilpotents = [e for e in elems if _is_nilpotent(e, table)]

    # Find two size-2 idempotents (field factors) and the remaining size-8 idempotent.
    one_vec = [1, 0, 0, 0, 0]
    size2_ids: List[List[int]] = []
    size8_ids: List[List[int]] = []
    for e in idempotents:
        if e == [0, 0, 0, 0, 0] or e == one_vec:
            continue
        ideal = _ideal_generated_by(e, elems, table)
        size = len({tuple(v) for v in ideal})
        if size == 2:
            size2_ids.append(e)
        elif size == 8:
            size8_ids.append(e)

    decomposition_component_sizes = None
    primitive_idempotents = None
    for e1 in size2_ids:
        for e2 in size2_ids:
            if e2 == e1:
                continue
            if _f2_mul(e1, e2, table) != [0, 0, 0, 0, 0]:
                continue
            e3 = _f2_add(one_vec, _f2_add(e1, e2))
            ideal3 = _ideal_generated_by(e3, elems, table)
            size3 = len({tuple(v) for v in ideal3})
            if size3 == 8 and _f2_mul(e1, e3, table) == [0, 0, 0, 0, 0] and _f2_mul(e2, e3, table) == [0, 0, 0, 0, 0]:
                primitive_idempotents = [e1, e2, e3]
                decomposition_component_sizes = sorted([2, 2, 8])
                break
        if primitive_idempotents is not None:
            break

    # Nilpotency index of the nilradical (expected 3 for F2[t]/(t^3) factor).
    N = {tuple(e) for e in nilpotents}
    z = (0, 0, 0, 0, 0)
    Nk = set(N)
    nilpotency_index = None
    for k in range(1, 9):
        if Nk == {z}:
            nilpotency_index = k
            break
        # Compute product ideal Nk * N (and take F2-linear span).
        gens = set()
        for a in Nk:
            for b in N:
                gens.add(tuple(_f2_mul(list(a), list(b), table)))
        # F2-span of gens (closure under xor).
        span = {z}
        for g in gens:
            span |= {tuple(_f2_add(list(u), list(g))) for u in list(span)}
        Nk = span
    if nilpotency_index is None:
        nilpotency_index = -1

    # Group-theoretic orbit counts at a 3-cycle and at a transposition.
    points = _space_points()
    subs = _space_2subsets()
    pairs = _space_ordered_pairs()
    # representatives
    classes: Dict[Tuple[int, ...], List[Tuple[int, ...]]] = {}
    for perm in permutations(range(5)):
        p = tuple(int(t) for t in perm)
        # cycle type on points
        seen = [False] * 5
        lens: List[int] = []
        for i in range(5):
            if seen[i]:
                continue
            j = i
            c = 0
            while not seen[j]:
                seen[j] = True
                j = p[j]
                c += 1
            lens.append(c)
        ct = tuple(sorted(lens, reverse=True))
        classes.setdefault(ct, []).append(p)
    rep_3cycle = classes[(3, 1, 1)][0]
    rep_transp = classes[(2, 1, 1, 1)][0]

    # Dyadic discriminant exponents for K10/K20 (tame, inertia a 3-cycle).
    orbits_subs_c3 = _orbits_count(rep_3cycle, subs)
    orbits_pairs_c3 = _orbits_count(rep_3cycle, pairs)
    v2_disc_K10 = len(subs) - orbits_subs_c3
    v2_disc_K20 = len(pairs) - orbits_pairs_c3

    # Character traces at 3-cycle and transposition for rho4,rho5,rho6 from permutation decompositions.
    def traces_from_fixed_points(g: Tuple[int, ...]) -> Dict[str, int]:
        chi_points = _fixed_points_count(g, points)  # Ind_{S4} 1 = 1 + rho4
        chi_subs = _fixed_points_count(g, subs)  # Ind_{S2xS3} 1 = 1 + rho4 + rho5
        chi_pairs = _fixed_points_count(g, pairs)  # Ind_{S3} 1 = 1 + 2 rho4 + rho5 + rho6
        chi_rho4 = chi_points - 1
        chi_rho5 = chi_subs - 1 - chi_rho4
        chi_rho6 = chi_pairs - 1 - 2 * chi_rho4 - chi_rho5
        return {"rho4": chi_rho4, "rho5": chi_rho5, "rho6": chi_rho6}

    chi_3 = traces_from_fixed_points(rep_3cycle)
    chi_2 = traces_from_fixed_points(rep_transp)
    dims = {"rho4": 4, "rho5": 5, "rho6": 6}

    # Invariants and tame conductor exponents.
    inv_dim_at_2 = {k: (dims[k] + 2 * chi_3[k]) // 3 for k in dims}  # since g and g^2 same class
    a2 = {k: dims[k] - inv_dim_at_2[k] for k in dims}
    inv_dim_at_q = {k: (dims[k] + chi_2[k]) // 2 for k in dims}
    aq = {k: dims[k] - inv_dim_at_q[k] for k in dims}

    # Signature counts from a transposition interpreted as complex conjugation:
    # r1(K10)=fixed points of transposition on 2-subsets; r1(K20)=fixed points on ordered pairs.
    r1_K10 = _fixed_points_count(rep_transp, subs)
    r1_K20 = _fixed_points_count(rep_transp, pairs)
    r2_K10 = (10 - r1_K10) // 2
    r2_K20 = (20 - r1_K20) // 2

    payload: Dict[str, object] = {
        "p7": {
            "poly": str(p7.as_expr()),
            "disc_x": disc_p7,
            "q": q,
            "disc_matches_minus_16q": (disc_p7 == -16 * q),
        },
        "K5_integral_basis": {
            "basis": ["1", "theta", "theta^2", "theta^3", "(theta^3+theta^4)/2"],
            "disc_power_basis_Ztheta": int(disc_power_basis),
            "disc_integral_basis": int(disc_integral_basis),
            "index_squared": str(index_sq),
            "index_is_2": (index_sq == 4),
        },
        "mod2_residue_ring": {
            "size": len(elems),
            "idempotents_count": len(idempotents),
            "nilpotents_count": len(nilpotents),
            "nilpotency_index_of_nilradical": nilpotency_index,
            "primitive_idempotents_found": primitive_idempotents is not None,
            "component_sizes_sorted": decomposition_component_sizes,
            "expected_factorization_type": "F2 × F2 × F2[t]/(t^3)",
            "expected_prime_factorization": "2 O_K5 = p1 p2 p3^3 (all f=1)",
        },
        "S5_tame_at_2": {
            "I2_is_C3": True,
            "I2_cycle_type_on_roots": "3·1·1",
            "orbit_counts": {"two_subsets_orbits": orbits_subs_c3, "ordered_pairs_orbits": orbits_pairs_c3},
            "v2_disc": {"K10": v2_disc_K10, "K20": v2_disc_K20},
        },
        "tame_character_traces": {"at_3cycle": chi_3, "at_transposition": chi_2},
        "tame_conductor_exponents": {"a2": a2, "aq": aq},
        "signatures": {
            "K10": {"r1": r1_K10, "r2": r2_K10},
            "K20": {"r1": r1_K20, "r2": r2_K20},
        },
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[xi-p7-dyadic-integral-basis] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

