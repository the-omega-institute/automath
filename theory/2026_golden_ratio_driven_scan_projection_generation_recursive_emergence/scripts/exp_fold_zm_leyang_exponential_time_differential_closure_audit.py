#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: exponential-log parameter differential closure for the Lee–Yang spectral quartic.

This script is English-only by repository convention.

We verify (symbolically, with SymPy):
  - For Pi(lam,y)=lam^4-lam^3-(2y+1)lam^2+lam+y(y+1), with y=e^s and lam(s) on Pi=0,
    eliminating y from {Pi=0, d/ds Pi(lam(s),e^s)=0} yields the explicit first-order algebraic ODE
    in (lam, dlam/ds) stated in the manuscript.
  - The discriminant of that quadratic (as a polynomial in dlam/ds) factors as
      (4 lam^3 - 4 lam + 1) * (2 lam^3 + 2 lam^2 - lam + 1)^2.
  - The rational reconstruction formula for y from (lam, dlam/ds) is exactly the
    linear eliminant (F2 - 2*F1) of the two y-quadratics.
  - Finite-jet rigidity: the 13-jet of the Perron branch lam_+(y) at y=1 uniquely
    determines Pi among polynomials with deg_lam<=4, deg_y<=2 and normalized lam^4 term.

Outputs:
  - artifacts/export/fold_zm_leyang_exponential_time_differential_closure_audit.json
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _is_constant_in(expr: sp.Expr, sym: sp.Symbol) -> bool:
    expr = sp.together(sp.simplify(expr))
    num, den = expr.as_numer_denom()
    try:
        deg_num = sp.Poly(num, sym, domain=sp.QQ).degree()
        deg_den = sp.Poly(den, sym, domain=sp.QQ).degree()
    except Exception:
        return False
    return deg_num == 0 and deg_den == 0


def _factorint_int(n: int) -> Dict[str, int]:
    if n == 0:
        return {"0": 1}
    sign = -1 if n < 0 else 1
    fac = {int(p): int(e) for p, e in sp.factorint(abs(int(n))).items()}
    if sign < 0:
        fac[-1] = 1
    return {str(k): int(v) for k, v in sorted(fac.items(), key=lambda kv: int(kv[0]))}


def _rat_mod_p(q: sp.Rational, p: int) -> int:
    """Map a rational number into F_p (p prime)."""
    q = sp.Rational(q)
    num = int(q.p) % p
    den = int(q.q) % p
    if den == 0:
        raise ZeroDivisionError("denominator is 0 mod p")
    inv = pow(den, p - 2, p)
    return (num * inv) % p


def _det_mod_p(A: sp.Matrix, p: int) -> int:
    """Determinant of a square rational matrix mod prime p."""
    n = int(A.rows)
    if n != int(A.cols):
        raise ValueError("Matrix must be square")
    M = [[_rat_mod_p(A[r, c], p) for c in range(n)] for r in range(n)]
    det = 1
    for i in range(n):
        pivot = None
        for r in range(i, n):
            if M[r][i] % p != 0:
                pivot = r
                break
        if pivot is None:
            return 0
        if pivot != i:
            M[i], M[pivot] = M[pivot], M[i]
            det = (-det) % p
        piv = M[i][i] % p
        det = (det * piv) % p
        inv_piv = pow(piv, p - 2, p)
        for r in range(i + 1, n):
            if M[r][i] % p == 0:
                continue
            f = (M[r][i] * inv_piv) % p
            for c in range(i, n):
                M[r][c] = (M[r][c] - f * M[i][c]) % p
    return det % p


@dataclass(frozen=True)
class Payload:
    ode_resultant_ok: bool
    ode_resultant_constant: str
    ode_exact_ok: bool
    ode_discriminant_ok: bool
    ode_discriminant_constant: str
    y_reconstruction_linear_eliminant_ok: bool
    jet_coeffs_ok_z1_3local: bool
    jet_coeffs_denominators_factor: Dict[str, Dict[str, int]]
    jet_rigidity_modulus: int
    jet_rigidity_det_modp: int
    jet_pi_coeffs_satisfy_linear_system_ok: bool
    jet_recovers_pi_ok: bool
    kappa_ok_2power_times_in_Z_1_3: bool
    kappa_denominators_factor: Dict[str, Dict[str, int]]
    elapsed_s: float


def _compute_lambda_jet_at_y1(*, order: int) -> List[sp.Rational]:
    """
    Compute coefficients a_1..a_order in lam_+(1+z)=2+sum_{n>=1} a_n z^n,
    by recursive coefficient solving using Pi(lam,y)=0 and dPi/dlam(2,1) != 0.
    """
    z = sp.Symbol("z")
    lam, y = sp.symbols("lam y")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)

    lam_series = sp.Integer(2)
    coeffs: List[sp.Rational] = []
    for n in range(1, order + 1):
        an = sp.Symbol(f"a{n}")
        lam_tmp = lam_series + an * z**n
        expr = sp.series(Pi.subs({lam: lam_tmp, y: 1 + z}), z, 0, n + 1).removeO()
        cn = sp.Poly(sp.expand(expr), z).coeff_monomial(z**n)
        sol = sp.solve(sp.Eq(cn, 0), an)
        if len(sol) != 1:
            raise RuntimeError(f"Expected unique solution for a{n}, got {sol!r}")
        an_val = sp.Rational(sp.together(sol[0]))
        coeffs.append(an_val)
        lam_series = sp.expand(lam_series + an_val * z**n)
    return coeffs


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit exponential-time differential closure for Pi(lambda,y)=0 (Fold Z_m).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    parser.add_argument("--jet-order", type=int, default=16, help="Compute jets up to this order (default: 16).")
    parser.add_argument("--rigidity-order", type=int, default=13, help="Use this order for rigidity (default: 13).")
    parser.add_argument("--kappa-order", type=int, default=14, help="Check kappa denominators up to this order (default: 14).")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-leyang-exp-time-ode] start", flush=True)

    lam, y, dl = sp.symbols("lam y dl")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    Pi_lam = sp.diff(Pi, lam)
    Pi_y = sp.diff(Pi, y)

    # Eliminate y from {Pi=0, Pi_lam*dl + Pi_y*y = 0} where y'=y (since y=e^s).
    print("[fold-zm-leyang-exp-time-ode] compute resultant ODE", flush=True)
    F1 = sp.expand(Pi)
    F2 = sp.expand(Pi_lam * dl + Pi_y * y)

    Res = sp.resultant(F1, F2, y)
    ode_expected = (
        (16 * lam**4 + 7 * lam**3 - 9 * lam**2 + lam + 1) * dl**2
        + (-16 * lam**5 - 4 * lam**4 + 20 * lam**3 - 5 * lam + 1) * dl
        + (4 * lam**6 - 8 * lam**4 + lam**3 + 4 * lam**2 - lam)
    )
    # The resultant contains an extraneous factor (1-lam), corresponding to the special locus
    # Pi(lam,y)=0 with lam=1 (then y in {0,1}). The Perron branch near (lam,y)=(2,1) avoids it.
    q_raw = sp.factor(sp.together(Res / ode_expected))
    q = sp.factor(sp.together(Res / ((1 - lam) * ode_expected)))
    ode_resultant_ok = _is_constant_in(q, lam) and _is_constant_in(q, dl) and bool(q_raw == 1 - lam)
    ode_resultant_constant = str(sp.factor(q)) if ode_resultant_ok else "nan"
    ode_exact_ok = (
        bool(sp.factor(Res - (1 - lam) * sp.factor(q) * ode_expected) == 0) if ode_resultant_ok else False
    )

    # Discriminant factorization of the ODE quadratic in dl.
    print("[fold-zm-leyang-exp-time-ode] compute discriminant factorization", flush=True)
    disc = sp.factor(sp.discriminant(ode_expected, dl))
    disc_expected = (4 * lam**3 - 4 * lam + 1) * (2 * lam**3 + 2 * lam**2 - lam + 1) ** 2
    qd = sp.together(disc / disc_expected)
    ode_discriminant_ok = _is_constant_in(qd, lam)
    ode_discriminant_constant = str(sp.factor(qd)) if ode_discriminant_ok else "nan"

    # y-reconstruction: linear eliminant of the two y-quadratics.
    denom = -2 * lam**2 + 4 * lam * dl + 1
    num = dl * (4 * lam**3 - 3 * lam**2 - 2 * lam + 1) - 2 * lam * (lam - 1) ** 2 * (lam + 1)
    # F2 is quadratic in y with leading coeff 2; eliminate y^2 by F2 - 2*F1.
    linear_eliminant = sp.expand(F2 - 2 * F1)
    y_reconstruction_linear_eliminant_ok = bool(
        sp.factor(linear_eliminant + (denom * y - num)) == 0 or sp.factor(linear_eliminant - (denom * y - num)) == 0
    )

    # --- Jet integrality and rigidity ---
    jet_order = int(args.jet_order)
    rigidity_order = int(args.rigidity_order)
    kappa_order = int(args.kappa_order)
    if kappa_order > jet_order:
        jet_order = kappa_order
    if rigidity_order > jet_order:
        raise ValueError("rigidity-order must be <= jet-order")

    print(f"[fold-zm-leyang-exp-time-ode] compute lambda_+ jet up to order={jet_order}", flush=True)
    a = _compute_lambda_jet_at_y1(order=jet_order)  # a[0]=a1
    # Check 3-local denominators for a_n (no primes other than 3).
    denom_factors: Dict[str, Dict[str, int]] = {}
    jet_coeffs_ok_z1_3local = True
    for n, an in enumerate(a, start=1):
        den = int(sp.Rational(an).q)
        fac = {int(p): int(e) for p, e in sp.factorint(den).items()}
        denom_factors[str(n)] = {str(k): int(v) for k, v in sorted(fac.items())}
        if any(p not in {3} for p in fac.keys()):
            jet_coeffs_ok_z1_3local = False

    # Rigidity linear system from coefficients up to z^{rigidity_order}.
    print("[fold-zm-leyang-exp-time-ode] build rigidity linear system", flush=True)
    z = sp.Symbol("z")
    lam_series = sp.Integer(2) + sum(a[n - 1] * z**n for n in range(1, rigidity_order + 1))

    # Unknown coefficients c_{ij} for 0<=i<=4,0<=j<=2 excluding (4,0) where coeff is fixed to 1.
    c_syms: List[sp.Symbol] = []
    terms: List[sp.Expr] = []
    for i in range(0, 5):
        for j in range(0, 3):
            if (i, j) == (4, 0):
                continue
            cij = sp.Symbol(f"c_{i}_{j}")
            c_syms.append(cij)
            terms.append(cij * (lam**i) * (y**j))
    Q = lam**4 + sp.Add(*terms)

    exprQ = sp.series(Q.subs({lam: lam_series, y: 1 + z}), z, 0, rigidity_order + 1).removeO()
    Pz = sp.Poly(sp.expand(exprQ), z)  # coefficients are linear forms in c_syms over QQ

    rows: List[List[sp.Rational]] = []
    rhs: List[sp.Rational] = []
    for k in range(0, rigidity_order + 1):
        ck = sp.expand(Pz.coeff_monomial(z**k))
        Pc = sp.Poly(ck, *c_syms, domain=sp.QQ)
        row = [sp.Rational(Pc.coeff_monomial(v)) for v in c_syms]
        const = sp.Rational(Pc.coeff_monomial(1))
        rows.append(row)
        rhs.append(-const)

    A = sp.Matrix(rows)
    b = sp.Matrix(rhs)
    # Prove invertibility by a modular determinant (denominators are powers of 3, so p=5 is safe).
    jet_rigidity_modulus = 5
    print("[fold-zm-leyang-exp-time-ode] compute det(A) mod p", flush=True)
    jet_rigidity_det_modp = int(_det_mod_p(A, jet_rigidity_modulus))

    # Check that Pi's coefficient vector satisfies the linear system A*c=b.
    Pi_tail = sp.Poly(sp.expand(Pi - lam**4), lam, y, domain=sp.QQ)
    c_pi: List[sp.Rational] = []
    for sym in c_syms:
        # sym is c_{i}_{j}; parse i,j from its name.
        _, i_str, j_str = sym.name.split("_")
        i = int(i_str)
        j = int(j_str)
        c_pi.append(sp.Rational(Pi_tail.coeff_monomial(lam**i * y**j)))
    res_vec = A * sp.Matrix(c_pi) - b
    jet_pi_coeffs_satisfy_linear_system_ok = all(sp.Rational(v) == 0 for v in list(res_vec))

    # If det(A) mod p != 0, then det(A) over QQ is nonzero, hence the solution is unique.
    # Since Pi satisfies the system, it must be that unique solution.
    jet_recovers_pi_ok = bool(jet_rigidity_det_modp != 0 and jet_pi_coeffs_satisfy_linear_system_ok)

    # --- kappa_n denominators: verify 2^n * psi^{(n)}(0) has only prime 3 in denominator ---
    print(f"[fold-zm-leyang-exp-time-ode] check kappa denominators up to order={kappa_order}", flush=True)
    # Use the identity (e^s-1)^n = sum_{m>=n} n! S(m,n) s^m/m! (Stirling numbers of second kind),
    # then compute kappa_m = psi^{(m)}(0) from the ordinary-series relation psi' = (lambda/2)' / (lambda/2).
    # This avoids heavy symbolic series for exp/log and keeps the audit fast.
    kappa_den_factors: Dict[str, Dict[str, int]] = {}
    kappa_ok_2power_times_in_Z_1_3 = True
    N = kappa_order
    # Stirling S(m,n) for 0<=m,n<=N.
    S2: List[List[int]] = [[0] * (N + 1) for _ in range(N + 1)]
    S2[0][0] = 1
    for m in range(1, N + 1):
        for n in range(1, m + 1):
            S2[m][n] = S2[m - 1][n - 1] + n * S2[m - 1][n]

    # lambda(s) = 2 + sum_{m>=1} L_m s^m/m!, with L_m = sum_{n<=m} a_n * n! * S(m,n).
    L: List[sp.Rational] = [sp.Rational(0)] * (N + 1)
    for m in range(1, N + 1):
        acc = sp.Rational(0)
        for n in range(1, m + 1):
            acc += sp.Rational(a[n - 1] * sp.factorial(n) * S2[m][n])
        L[m] = sp.Rational(acc)

    # f(s) := lambda(s)/2 as an ordinary power series f(s)=sum_{m>=0} f_m s^m with f_0=1.
    f: List[sp.Rational] = [sp.Rational(0)] * (N + 1)
    f[0] = sp.Rational(1)
    for m in range(1, N + 1):
        f[m] = sp.Rational(L[m] / (2 * sp.factorial(m)))

    # inv_f = 1/f mod s^{N+1}.
    inv_f: List[sp.Rational] = [sp.Rational(0)] * (N + 1)
    inv_f[0] = sp.Rational(1)
    for n in range(1, N + 1):
        acc = sp.Rational(0)
        for k in range(1, n + 1):
            acc += f[k] * inv_f[n - k]
        inv_f[n] = -acc

    # fp(s) = f'(s) = sum_{n>=0} fp_n s^n, where fp_n = (n+1) f_{n+1}.
    fp: List[sp.Rational] = [sp.Rational(0)] * N
    for n in range(0, N):
        fp[n] = sp.Rational((n + 1) * f[n + 1])

    # h(s)=psi'(s)=fp/f = fp * inv_f.
    h: List[sp.Rational] = [sp.Rational(0)] * N
    for n in range(0, N):
        acc = sp.Rational(0)
        for k in range(0, n + 1):
            acc += fp[k] * inv_f[n - k]
        h[n] = sp.Rational(acc)

    # kappa_{n+1} = n! * h_n.
    for m in range(1, N + 1):
        kappa_m = sp.Rational(sp.factorial(m - 1) * h[m - 1])
        scaled = sp.Rational((2**m) * kappa_m)
        den = int(scaled.q)
        fac = {int(p): int(e) for p, e in sp.factorint(den).items()}
        kappa_den_factors[str(m)] = {str(k): int(v) for k, v in sorted(fac.items())}
        if any(p not in {3} for p in fac.keys()):
            kappa_ok_2power_times_in_Z_1_3 = False

    elapsed = time.time() - t0
    payload = Payload(
        ode_resultant_ok=bool(ode_resultant_ok),
        ode_resultant_constant=str(ode_resultant_constant),
        ode_exact_ok=bool(ode_exact_ok),
        ode_discriminant_ok=bool(ode_discriminant_ok),
        ode_discriminant_constant=str(ode_discriminant_constant),
        y_reconstruction_linear_eliminant_ok=bool(y_reconstruction_linear_eliminant_ok),
        jet_coeffs_ok_z1_3local=bool(jet_coeffs_ok_z1_3local),
        jet_coeffs_denominators_factor=denom_factors,
        jet_rigidity_modulus=int(jet_rigidity_modulus),
        jet_rigidity_det_modp=int(jet_rigidity_det_modp),
        jet_pi_coeffs_satisfy_linear_system_ok=bool(jet_pi_coeffs_satisfy_linear_system_ok),
        jet_recovers_pi_ok=bool(jet_recovers_pi_ok),
        kappa_ok_2power_times_in_Z_1_3=bool(kappa_ok_2power_times_in_Z_1_3),
        kappa_denominators_factor=kappa_den_factors,
        elapsed_s=float(elapsed),
    )

    if not args.no_output:
        out = export_dir() / "fold_zm_leyang_exponential_time_differential_closure_audit.json"
        _write_json(out, asdict(payload))
        print(f"[fold-zm-leyang-exp-time-ode] wrote {out}", flush=True)

    print(
        "[fold-zm-leyang-exp-time-ode] checks:"
        f" ode_res={ode_exact_ok} disc={ode_discriminant_ok} yrec={y_reconstruction_linear_eliminant_ok}"
        f" jet3loc={jet_coeffs_ok_z1_3local} jetPi={jet_recovers_pi_ok} kappa2^n={kappa_ok_2power_times_in_Z_1_3}"
        f" seconds={elapsed:.3f}",
        flush=True,
    )
    print("[fold-zm-leyang-exp-time-ode] done", flush=True)


if __name__ == "__main__":
    main()

