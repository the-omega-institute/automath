#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the two-layer disjointness kernel on the Boolean lattice.

This script is English-only by repository convention.

We certify, for small q and multiple integer parameter pairs (a,b):
  - zeta--mu diagonalization:
      B^{(q)}(a,b) = Z^T Delta(a,b) Z
      mu^T B^{(q)}(a,b) mu = Delta(a,b)
  - Smith normal form over Z:
      SNF(B^{(q)}(a,b)) = diag(g, |d|,...,|d|, |ad|/g) for q>=2,
    with g=gcd(a,b) and d=a-b.
  - inverse support law over Q when a and d are nonzero:
      (B^{-1})_{U,V} is supported on U∪V=[q] and (∅,∅), with explicit values.
  - Möbius Diophantine criterion for integrality of Bx=y.

We also compute the S_q-invariant (q+1)x(q+1) block for B^{(q)}(2,1) and
test irreducibility of its characteristic polynomial for a range of q.

Outputs:
  - artifacts/export/boolean_two_layer_kernel_zeta_mu_snf_inverse_audit.json
  - sections/generated/eq_boolean_two_layer_kernel_zeta_mu_snf_inverse_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _subsets(q: int) -> List[int]:
    return list(range(1 << q))


def _popcount(x: int) -> int:
    return int(x.bit_count())


def _zeta_mu(q: int) -> Tuple[sp.Matrix, sp.Matrix]:
    """Zeta and Möbius matrices on (2^[q], subset). Indices are bitmasks."""
    subs = _subsets(q)
    n = len(subs)
    Z = sp.zeros(n, n)
    Mu = sp.zeros(n, n)
    for i, U in enumerate(subs):
        for j, V in enumerate(subs):
            if U & ~V == 0:  # U ⊆ V
                Z[i, j] = 1
                Mu[i, j] = (-1) ** _popcount(V ^ U)
    return Z, Mu


def _B(q: int, a: int, b: int) -> sp.Matrix:
    subs = _subsets(q)
    n = len(subs)
    M = sp.zeros(n, n)
    for i, U in enumerate(subs):
        for j, V in enumerate(subs):
            M[i, j] = a if (U & V) == 0 else b
    return M


def _Delta(q: int, a: int, b: int) -> sp.Matrix:
    d = a - b
    subs = _subsets(q)
    n = len(subs)
    D = sp.zeros(n, n)
    for i, S in enumerate(subs):
        if S == 0:
            D[i, i] = a
        else:
            D[i, i] = d * ((-1) ** _popcount(S))
    return D


def _snf_expected(q: int, a: int, b: int) -> List[int]:
    assert q >= 2
    n = 1 << q
    d = a - b
    g = math.gcd(a, b)
    return [g] + [abs(d)] * (n - 2) + [abs(a * d) // g]


def _inverse_entry_closed(q: int, a: sp.Rational, b: sp.Rational, U: int, V: int) -> sp.Rational:
    d = a - b
    if U == 0 and V == 0:
        return -b / (a * d)
    if (U | V) == (1 << q) - 1:
        return sp.Rational((-1) ** _popcount(U & V), 1) / d
    return sp.Rational(0, 1)


def _sym_block_A(q: int) -> sp.Matrix:
    """S_q-invariant block for B^{(q)}(2,1) in the weight-layer sum basis."""
    M = sp.zeros(q + 1, q + 1)
    for k in range(q + 1):
        for ell in range(q + 1):
            M[k, ell] = sp.binomial(q, ell) + sp.binomial(q - k, ell)
    return M


@dataclass(frozen=True)
class Payload:
    checked_q: List[int]
    checked_params: List[Tuple[int, int]]
    zeta_diag_ok: bool
    mu_diag_ok: bool
    snf_ok: bool
    inverse_support_ok: bool
    mobius_integrality_ok: bool
    sym_block_irreducible_q: List[int]
    seconds: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit Boolean two-layer kernel identities.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[boolean-two-layer-kernel] start", flush=True)

    checked_q = [2, 3, 4, 5]
    checked_params = [(2, 1), (5, 2), (-3, 7)]

    zeta_diag_ok = True
    mu_diag_ok = True
    snf_ok = True
    inverse_support_ok = True
    mobius_integrality_ok = True

    for q in checked_q:
        Z, Mu = _zeta_mu(q)
        for a, b in checked_params:
            B = _B(q, a, b)
            D = _Delta(q, a, b)

            zeta_diag_ok = zeta_diag_ok and bool(sp.simplify(Z.T * D * Z - B) == sp.zeros(B.rows, B.cols))
            mu_diag_ok = mu_diag_ok and bool(sp.simplify(Mu.T * B * Mu - D) == sp.zeros(B.rows, B.cols))

            # SNF over Z for q>=2
            if q >= 2:
                S = smith_normal_form(B)
                diag = [int(S[i, i]) for i in range(S.rows)]
                diag = [abs(x) for x in diag if x != 0]
                # Smith form is defined up to units and ordering; compare multisets.
                exp = _snf_expected(q, a, b)
                diag.sort()
                exp.sort()
                snf_ok = snf_ok and (diag == exp)

            # Inverse support law over Q for a!=0 and d!=0
            d = a - b
            if a != 0 and d != 0:
                Binv = sp.Matrix(B).inv()
                for U in _subsets(q):
                    for V in _subsets(q):
                        closed = _inverse_entry_closed(q, sp.Rational(a), sp.Rational(b), U, V)
                        inv_ok = sp.simplify(Binv[U, V] - closed) == 0
                        inverse_support_ok = inverse_support_ok and bool(inv_ok)

                # Möbius integrality criterion: Bx=y has integer solution iff divisibility holds.
                # Test a few deterministic y vectors.
                for seed in range(4):
                    y_vec = sp.Matrix([((i + 3 * seed) % 7) - 3 for i in range(B.rows)])
                    hat = Mu.T * y_vec
                    cond = (hat[0] % a == 0) and all((hat[i] % d == 0) for i in range(1, B.rows))
                    x_rat = sp.Matrix(B).LUsolve(y_vec)
                    is_int = all(sp.denom(x_rat[i]) == 1 for i in range(x_rat.rows))
                    mobius_integrality_ok = mobius_integrality_ok and (cond == is_int)

    # Symmetric block conjecture: test irreducibility of charpoly over Q for q up to 10.
    sym_block_irreducible_q: List[int] = []
    x = sp.Symbol("x")
    for q in range(2, 11):
        A = _sym_block_A(q)
        poly = sp.Poly(A.charpoly(x).as_expr(), x, domain=sp.ZZ)
        fac = sp.factor_list(poly.as_expr())
        irreducible = len(fac[1]) == 1 and sp.Poly(fac[1][0][0], x, domain=sp.ZZ).degree() == (q + 1)
        if irreducible:
            sym_block_irreducible_q.append(q)

    seconds = time.time() - t0
    payload = Payload(
        checked_q=checked_q,
        checked_params=checked_params,
        zeta_diag_ok=zeta_diag_ok,
        mu_diag_ok=mu_diag_ok,
        snf_ok=snf_ok,
        inverse_support_ok=inverse_support_ok,
        mobius_integrality_ok=mobius_integrality_ok,
        sym_block_irreducible_q=sym_block_irreducible_q,
        seconds=seconds,
    )

    assert payload.zeta_diag_ok
    assert payload.mu_diag_ok
    assert payload.snf_ok
    assert payload.inverse_support_ok
    assert payload.mobius_integrality_ok

    if not args.no_output:
        _write_json(export_dir() / "boolean_two_layer_kernel_zeta_mu_snf_inverse_audit.json", asdict(payload))

        tex = r"""% Auto-generated by scripts/exp_boolean_two_layer_kernel_zeta_mu_snf_inverse_audit.py
\begin{align}
B^{(q)}(a,b)&=Z_q^{\mathsf T}\Delta_q(a,b)Z_q,
&\mu_q^{\mathsf T}B^{(q)}(a,b)\mu_q&=\Delta_q(a,b),\\
\mathrm{SNF}\!\bigl(B^{(q)}(a,b)\bigr)
&=\operatorname{diag}\Bigl(g,\underbrace{|d|,\dots,|d|}_{2^q-2},\frac{|ad|}{g}\Bigr),
&\det\bigl(B^{(q)}(a,b)\bigr)&=a\,d^{\,2^q-1},\\
\bigl(B^{(q)}(a,b)^{-1}\bigr)_{U,V}
&=
\begin{cases}
-\dfrac{b}{ad},&U=V=\varnothing,\\[4pt]
\dfrac{(-1)^{|U\cap V|}}{d},&U\cup V=[q],\\[4pt]
0,&\text{otherwise},
\end{cases}
&\text{(in } \QQ\text{, if }ad\neq 0\text{)}.
\end{align}
"""
        _write_text(generated_dir() / "eq_boolean_two_layer_kernel_zeta_mu_snf_inverse_audit.tex", tex)

    print(f"[boolean-two-layer-kernel] ok seconds={seconds:.3f}", flush=True)


if __name__ == "__main__":
    main()

