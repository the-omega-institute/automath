#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Irreducibility certificates for the resonance-window collision moment characteristic polynomials P_q
for q=9..17.

We build P_q from the audited minimal integer recurrences in:
  sections/generated/tab_fold_collision_moment_recursions_9_17.tex
and certify irreducibility over Q by exhibiting a prime p such that P_q mod p is irreducible.

Outputs:
  - artifacts/export/fold_collision_moment_charpoly_irreducible_q9_17.json
  - sections/generated/tab_fold_collision_moment_charpoly_irreducible_certificate_q9_17.tex

Additional outputs (q in {12,13,14,15}):
  - artifacts/export/fold_collision_moment_charpoly_galois_audit_q12_15.json
  - sections/generated/tab_fold_collision_moment_charpoly_galois_certificate_q12_15.tex
  - sections/generated/tab_fold_collision_moment_charpoly_disc_squareclass_independence_q12_15.tex
"""

from __future__ import annotations

import json
import warnings
from dataclasses import asdict, dataclass

import sympy as sp

from common_paths import export_dir, generated_dir

try:
    from sympy.utilities.exceptions import SymPyDeprecationWarning

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
except Exception:
    pass


@dataclass(frozen=True)
class Row:
    q: int
    d: int
    irreducible_over_Q: bool
    p_irr: int
    degs_mod_p_irr: list[int]


REC_C: dict[int, tuple[int, ...]] = {
    9: (2, 62, 386, 2819, 62, 900, -450),
    10: (2, 96, 830, 7945, 2, 1852, -830, 4, -4),
    11: (2, 153, 1740, 21249, -9432, -86213, -1484, -18348, 9174),
    12: (2, 243, 3608, 56447, -61236, -667319, 3608, -9582, 61242, 15404, -7216, 8, -8),
    13: (2, 388, 7414, 148038, -317916, -4165856, 136252, 1565891, 318938, 289380, -144690),
    14: (2, 621, 15140, 385463, -1443744, -22761161, 15140, -2116566, 1443750, 63044, -30280, 8, -8),
    15: (2, 1000, 30766, 994458, -6188172, -119408756, 8289820, 134208623, 6186122, 16637076, -8318538),
    16: (2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692, -124624, 8, -8),
    17: (2, 2599, 125872, 6569850, -96034590, -2764163954, -643026032, -15022392733, 769974566, 15329386299, 642908352, 1347896340, -673948170),
}


def poly_Pq(q: int) -> sp.Poly:
    lam = sp.Symbol("lam")
    cs = REC_C[q]
    d = len(cs)
    expr = lam**d
    for i, c in enumerate(cs, start=1):
        expr -= sp.Integer(c) * lam ** (d - i)
    return sp.Poly(expr, lam, domain=sp.ZZ)


def is_irreducible_mod_p(poly: sp.Poly, p: int) -> tuple[bool, list[int]]:
    lam = poly.gens[0]
    poly_p = sp.Poly(poly.as_expr(), lam, modulus=p)
    fac = sp.factor_list(poly_p)[1]
    degs = [f.degree() for f, _e in fac]
    irreducible = len(fac) == 1 and degs[0] == poly.degree() and fac[0][1] == 1
    return irreducible, degs


def factor_degrees_mod_p(poly: sp.Poly, p: int) -> tuple[bool, list[int]]:
    """
    Factor poly modulo p and return (squarefree?, sorted factor degrees).
    """
    lam = poly.gens[0]
    f = sp.Poly(poly.as_expr(), lam, modulus=int(p))
    g = sp.gcd(f, f.diff())
    squarefree = (g.degree() == 0)
    _, facs = sp.factor_list(f, modulus=int(p))
    degs: list[int] = []
    for ff, ee in facs:
        degs.extend([int(sp.Poly(ff, lam, modulus=int(p)).degree())] * int(ee))
    degs.sort(reverse=True)
    return bool(squarefree), degs


def find_prime_with_degree_pattern(poly: sp.Poly, disc_primes: set[int], want: list[int], p_max: int = 5000) -> int:
    want_sorted = sorted([int(x) for x in want], reverse=True)
    for p in sp.primerange(2, int(p_max) + 1):
        if int(p) in disc_primes:
            continue
        squarefree, degs = factor_degrees_mod_p(poly, int(p))
        if not squarefree:
            continue
        if degs == want_sorted:
            return int(p)
    raise RuntimeError(f"Failed to find prime with factor degrees {want_sorted} up to {p_max}.")


def legendre_symbol_sqfree(D_sqfree: int, p: int) -> int:
    """
    Return Legendre symbol (D/p) in {+1,-1,0} for odd prime p,
    with D assumed squarefree (possibly negative).
    """
    return int(sp.legendre_symbol(int(D_sqfree), int(p)))


def rank_over_F2(rows: list[list[int]]) -> int:
    """
    Row-reduce a binary matrix over F2. Entries should be 0/1.
    """
    if not rows:
        return 0
    A = [r[:] for r in rows]
    m = len(A)
    n = len(A[0])
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if A[i][c] & 1:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        for i in range(m):
            if i != r and (A[i][c] & 1):
                A[i] = [(a ^ b) for a, b in zip(A[i], A[r], strict=True)]
        r += 1
        if r == m:
            break
    return int(r)


@dataclass(frozen=True)
class GalRow:
    q: int
    d: int
    p_irr: int
    degs_mod_p_irr: list[int]
    p_nminus1_1: int
    degs_mod_p_nminus1_1: list[int]


def main() -> None:
    primes = list(sp.primerange(2, 300))
    rows: list[Row] = []

    for q in range(9, 18):
        P = poly_Pq(q)
        d = P.degree()

        # Over QQ: factor_list returns [(poly,exp)].
        flQ = sp.factor_list(P.as_expr())[1]
        irreducible_over_Q = len(flQ) == 1 and flQ[0][0].as_poly(P.gens[0]).degree() == d and flQ[0][1] == 1

        p_irr = None
        degs = None
        for p in primes:
            ok, degs_p = is_irreducible_mod_p(P, p)
            if ok:
                p_irr = p
                degs = degs_p
                break
        assert p_irr is not None and degs is not None

        rows.append(Row(q=q, d=d, irreducible_over_Q=irreducible_over_Q, p_irr=p_irr, degs_mod_p_irr=degs))

    export_path = export_dir() / "fold_collision_moment_charpoly_irreducible_q9_17.json"
    export_path.write_text(json.dumps([asdict(r) for r in rows], indent=2, sort_keys=True), encoding="utf-8")

    tex = []
    tex.append(r"% Auto-generated by scripts/exp_fold_collision_moment_charpoly_irreducible_q9_17.py")
    tex.append(r"\begin{table}[H]")
    tex.append(r"\centering")
    tex.append(r"\scriptsize")
    tex.append(r"\caption{Irreducibility certificates for the resonance-window Fold collision moment characteristic polynomials $P_q(\lambda)$ for $q=9,\dots,17$. We list a prime $p_{\mathrm{irr}}$ such that $P_q\bmod p_{\mathrm{irr}}$ is irreducible (degrees shown as a factor-degree tuple).}")
    tex.append(r"\label{tab:fold_collision_moment_charpoly_irreducible_certificate_q9_17}")
    tex.append(r"\begin{tabular}{r r r l}")
    tex.append(r"\toprule")
    tex.append(r"$q$ & $d_q$ & $p_{\mathrm{irr}}$ & degs mod $p_{\mathrm{irr}}$\\")
    tex.append(r"\midrule")
    for r in rows:
        tex.append(f"{r.q} & {r.d} & {r.p_irr} & ({','.join(map(str, r.degs_mod_p_irr))})\\\\")
    tex.append(r"\bottomrule")
    tex.append(r"\end{tabular}")
    tex.append(r"\end{table}")
    tex.append("")
    (generated_dir() / "tab_fold_collision_moment_charpoly_irreducible_certificate_q9_17.tex").write_text(
        "\n".join(tex), encoding="utf-8"
    )

    # ------------------------------------------------------------------
    # Extra audit: q in {12,13,14,15} certificates used for full symmetric
    # Galois groups and discriminant squareclass independence.
    # ------------------------------------------------------------------
    qs = [12, 13, 14, 15]
    gal_rows: list[GalRow] = []
    leg_primes = [31, 37, 43, 61]
    leg_bits: list[list[int]] = []

    for q in qs:
        P = poly_Pq(int(q))
        d = int(P.degree())
        lam = P.gens[0]
        disc = int(sp.discriminant(P, lam))

        # Choose the smallest unramified irreducibility prime in the same search window.
        p_irr = None
        degs_irr = None
        for p in primes:
            ok, degs_p = is_irreducible_mod_p(P, int(p))
            if ok and (disc % int(p) != 0):
                p_irr = int(p)
                degs_irr = [int(x) for x in degs_p]
                break
        if p_irr is None or degs_irr is None:
            raise RuntimeError(f"Failed to find an unramified irreducibility prime for q={q}.")

        # Find an unramified prime with factor degrees (d-1,1).
        # We filter unramified primes by disc % p != 0 during the search.
        # To keep the helper signature stable, pass an empty set and do the disc test inline.
        p_nm = None
        want = [d - 1, 1]
        want_sorted = sorted([int(x) for x in want], reverse=True)
        for p in sp.primerange(2, 5000 + 1):
            if disc % int(p) == 0:
                continue
            squarefree, degs = factor_degrees_mod_p(P, int(p))
            if not squarefree:
                continue
            if degs == want_sorted:
                p_nm = int(p)
                break
        if p_nm is None:
            raise RuntimeError(f"Failed to find an unramified (d-1,1) prime for q={q} up to 5000.")
        _, degs_nm = factor_degrees_mod_p(P, int(p_nm))

        gal_rows.append(
            GalRow(
                q=int(q),
                d=int(d),
                p_irr=int(p_irr),
                degs_mod_p_irr=[int(x) for x in degs_irr],
                p_nminus1_1=int(p_nm),
                degs_mod_p_nminus1_1=[int(x) for x in degs_nm],
            )
        )

        # Legendre fingerprints; encode (-1 -> 1, +1 -> 0) in F2.
        vals = [int(sp.legendre_symbol(int(disc), int(p))) for p in leg_primes]
        if any(disc % int(p) == 0 for p in leg_primes):
            raise RuntimeError(f"Chosen Legendre primes divide Disc(P_{q}); adjust primes.")
        if any(v == 0 for v in vals):
            raise RuntimeError(f"Legendre symbol hit 0 for q={q}; adjust primes.")
        leg_bits.append([1 if v == -1 else 0 for v in vals])

    export_gal = export_dir() / "fold_collision_moment_charpoly_galois_audit_q12_15.json"
    export_gal.write_text(json.dumps([asdict(r) for r in gal_rows], indent=2, sort_keys=True), encoding="utf-8")

    tex2: list[str] = []
    tex2.append(r"% Auto-generated by scripts/exp_fold_collision_moment_charpoly_irreducible_q9_17.py")
    tex2.append(r"\begin{table}[H]")
    tex2.append(r"\centering")
    tex2.append(r"\scriptsize")
    tex2.append(
        r"\caption{Unramified mod-$p$ factorization certificates for $P_q(\lambda)$ with $q\in\{12,13,14,15\}$. "
        r"The pattern $(d)$ certifies a $d$-cycle (hence transitivity), and $(d-1,1)$ certifies a $(d-1)$-cycle.}"
    )
    tex2.append(r"\label{tab:fold_collision_moment_charpoly_galois_certificate_q12_15}")
    tex2.append(r"\begin{tabular}{r r r l r l}")
    tex2.append(r"\toprule")
    tex2.append(
        r"$q$ & $d_q$ & $p_{\mathrm{irr}}$ & degs mod $p_{\mathrm{irr}}$ & $p_{(d-1,1)}$ & degs mod $p_{(d-1,1)}$\\"
    )
    tex2.append(r"\midrule")
    for r in gal_rows:
        tex2.append(
            f"{r.q} & {r.d} & {r.p_irr} & ({','.join(map(str, r.degs_mod_p_irr))}) & "
            f"{r.p_nminus1_1} & ({','.join(map(str, r.degs_mod_p_nminus1_1))})\\\\"
        )
    tex2.append(r"\bottomrule")
    tex2.append(r"\end{tabular}")
    tex2.append(r"\end{table}")
    tex2.append("")
    (generated_dir() / "tab_fold_collision_moment_charpoly_galois_certificate_q12_15.tex").write_text(
        "\n".join(tex2), encoding="utf-8"
    )

    rk = rank_over_F2(leg_bits)
    tex3: list[str] = []
    tex3.append(r"% Auto-generated by scripts/exp_fold_collision_moment_charpoly_irreducible_q9_17.py")
    tex3.append(r"\begin{table}[H]")
    tex3.append(r"\centering")
    tex3.append(r"\scriptsize")
    tex3.append(r"\setlength{\tabcolsep}{6pt}")
    tex3.append(
        r"\caption{Discriminant squareclass fingerprints for $q\in\{12,13,14,15\}$ using Legendre symbols at primes "
        r"$p\in\{31,37,43,61\}$. The induced $4\times 4$ binary matrix (encoding $-1\mapsto 1$ and $+1\mapsto 0$) "
        + rf"has rank {rk}.}}"
    )
    tex3.append(r"\label{tab:fold_collision_moment_charpoly_disc_squareclass_independence_q12_15}")
    tex3.append(r"\begin{tabular}{r r r r r}")
    tex3.append(r"\toprule")
    tex3.append(
        r"$q$ & $\left(\frac{\mathrm{Disc}(P_q)}{31}\right)$ & $\left(\frac{\mathrm{Disc}(P_q)}{37}\right)$ & "
        r"$\left(\frac{\mathrm{Disc}(P_q)}{43}\right)$ & $\left(\frac{\mathrm{Disc}(P_q)}{61}\right)$\\"
    )
    tex3.append(r"\midrule")
    for r, bits in zip(gal_rows, leg_bits, strict=True):
        # Recover original ±1 values from bits to show in the manuscript table.
        vals = [(-1 if b == 1 else 1) for b in bits]
        tex3.append(f"{r.q} & {vals[0]} & {vals[1]} & {vals[2]} & {vals[3]}\\\\")
    tex3.append(r"\bottomrule")
    tex3.append(r"\end{tabular}")
    tex3.append(r"\end{table}")
    tex3.append("")
    (generated_dir() / "tab_fold_collision_moment_charpoly_disc_squareclass_independence_q12_15.tex").write_text(
        "\n".join(tex3), encoding="utf-8"
    )


if __name__ == "__main__":
    main()

