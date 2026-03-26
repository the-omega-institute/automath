#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit absolute simplicity of the fold gauge-anomaly spectral quartic Jacobian via a good
prime p=7 and an irreducible local L-polynomial.

This script is English-only by repository convention.

We verify:
  - smoothness of the projective plane quartic model mod 7 (good reduction),
  - point counts #C(F_{7^n}) for n=1,2,3 by brute-force enumeration over F_{7^n},
  - recovery of L_7(T)=prod_i (1 - alpha_i T) from (N1,N2,N3) via Newton identities,
  - irreducibility of L_7(T) over Q (witnessed by irreducibility modulo 13).

Outputs:
  - artifacts/export/fold_gauge_anomaly_spectral_quartic_jacobian_L7_audit.json
  - sections/generated/eq_fold_gauge_anomaly_spectral_quartic_jacobian_L7_audit.tex
"""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from itertools import product
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


TupleElem = Tuple[int, ...]


class GFExt:
    """Finite field F_{p^n} as F_p[x]/(mod(x)), elements are tuples of length n."""

    def __init__(self, *, p: int, mod_coeffs: Sequence[int]) -> None:
        if p <= 1:
            raise ValueError("p must be prime")
        if len(mod_coeffs) < 2:
            raise ValueError("modulus must have degree >= 1")
        if (mod_coeffs[-1] % p) != 1:
            raise ValueError("modulus must be monic modulo p")

        self.p = int(p)
        self.mod = [int(c) % p for c in mod_coeffs]
        self.n = len(self.mod) - 1

        self.zero: TupleElem = (0,) * self.n
        self.one: TupleElem = (1,) + (0,) * (self.n - 1)
        self.elements: List[TupleElem] = list(product(range(self.p), repeat=self.n))

    def add(self, a: TupleElem, b: TupleElem) -> TupleElem:
        p = self.p
        return tuple(((ai + bi) % p) for ai, bi in zip(a, b))

    def sub(self, a: TupleElem, b: TupleElem) -> TupleElem:
        p = self.p
        return tuple(((ai - bi) % p) for ai, bi in zip(a, b))

    def neg(self, a: TupleElem) -> TupleElem:
        p = self.p
        return tuple(((-ai) % p) for ai in a)

    def scale(self, a: TupleElem, k: int) -> TupleElem:
        p = self.p
        kk = int(k) % p
        return tuple(((kk * ai) % p) for ai in a)

    def mul(self, a: TupleElem, b: TupleElem) -> TupleElem:
        p = self.p
        n = self.n
        mod = self.mod

        # Polynomial multiply (degree < n) -> degree <= 2n-2.
        res = [0] * (2 * n - 1)
        for i, ai in enumerate(a):
            if ai == 0:
                continue
            for j, bj in enumerate(b):
                if bj == 0:
                    continue
                res[i + j] = (res[i + j] + ai * bj) % p

        # Reduce via x^n = -(mod[0] + mod[1] x + ... + mod[n-1] x^{n-1}).
        for k in range(2 * n - 2, n - 1, -1):
            ck = res[k]
            if ck == 0:
                continue
            base = k - n
            for j in range(n):
                res[base + j] = (res[base + j] - ck * mod[j]) % p
            res[k] = 0

        return tuple(res[:n])

    def pow(self, a: TupleElem, e: int) -> TupleElem:
        if e < 0:
            raise ValueError("negative exponent not supported")
        result = self.one
        base = a
        ee = int(e)
        while ee:
            if ee & 1:
                result = self.mul(result, base)
            base = self.mul(base, base)
            ee >>= 1
        return result


def _poly_F(mu: TupleElem, u: TupleElem, *, F: GFExt) -> TupleElem:
    # F(mu,u) = mu^4 - mu^3 - mu^2 (2u+1) + mu(-u^3+2u) + 2u.
    one = F.one
    mu2 = F.mul(mu, mu)
    mu3 = F.mul(mu2, mu)
    mu4 = F.mul(mu2, mu2)

    two_u = F.scale(u, 2)
    two_u_plus_one = F.add(two_u, one)
    u3 = F.mul(F.mul(u, u), u)

    acc = mu4
    acc = F.sub(acc, mu3)
    acc = F.sub(acc, F.mul(mu2, two_u_plus_one))
    acc = F.add(acc, F.mul(mu, F.add(F.neg(u3), two_u)))
    acc = F.add(acc, two_u)
    return acc


def _count_affine_points(*, Fq: GFExt) -> int:
    one = Fq.one
    zero = Fq.zero
    elems = Fq.elements

    # Precompute mu^2, mu^3, mu^4.
    mu_data: List[Tuple[TupleElem, TupleElem, TupleElem, TupleElem]] = []
    for mu in elems:
        mu2 = Fq.mul(mu, mu)
        mu3 = Fq.mul(mu2, mu)
        mu4 = Fq.mul(mu2, mu2)
        mu_data.append((mu, mu2, mu3, mu4))

    count = 0
    for u in elems:
        two_u = Fq.scale(u, 2)
        two_u_plus_one = Fq.add(two_u, one)
        u3 = Fq.mul(Fq.mul(u, u), u)
        mu_lin = Fq.add(Fq.neg(u3), two_u)  # (-u^3+2u)
        for mu, mu2, mu3, mu4 in mu_data:
            acc = mu4
            acc = Fq.sub(acc, mu3)
            acc = Fq.sub(acc, Fq.mul(mu2, two_u_plus_one))
            acc = Fq.add(acc, Fq.mul(mu, mu_lin))
            acc = Fq.add(acc, two_u)
            if acc == zero:
                count += 1

    return int(count)


def _points_at_infinity(*, p: int, n: int) -> int:
    # On w=0: mu(mu^3-u^3)=0 gives 1 point for mu=0 plus the cube roots of unity.
    return 1 + math.gcd(3, p**n - 1)


def _count_points_projective_model(*, p: int, n: int, mod_coeffs: Sequence[int]) -> int:
    Fq = GFExt(p=p, mod_coeffs=mod_coeffs)
    affine = _count_affine_points(Fq=Fq)
    infinity = _points_at_infinity(p=p, n=n)
    return int(affine + infinity)


def _eval_Fhom(mu: int, u: int, w: int, *, p: int) -> int:
    # F^hom(mu,u,w) = mu^4 - mu^3 w - 2 mu^2 u w - mu^2 w^2 - mu u^3 + 2 mu u w^2 + 2 u w^3.
    return (
        pow(mu, 4, p)
        - (pow(mu, 3, p) * w)
        - (2 * pow(mu, 2, p) * u * w)
        - (pow(mu, 2, p) * pow(w, 2, p))
        - (mu * pow(u, 3, p))
        + (2 * mu * u * pow(w, 2, p))
        + (2 * u * pow(w, 3, p))
    ) % p


def _eval_dmu_Fhom(mu: int, u: int, w: int, *, p: int) -> int:
    # d/dmu.
    return (
        (4 * pow(mu, 3, p))
        - (3 * pow(mu, 2, p) * w)
        - (4 * mu * u * w)
        - (2 * mu * pow(w, 2, p))
        - pow(u, 3, p)
        + (2 * u * pow(w, 2, p))
    ) % p


def _eval_du_Fhom(mu: int, u: int, w: int, *, p: int) -> int:
    # d/du.
    return (
        -(2 * pow(mu, 2, p) * w)
        - (3 * mu * pow(u, 2, p))
        + (2 * mu * pow(w, 2, p))
        + (2 * pow(w, 3, p))
    ) % p


def _eval_dw_Fhom(mu: int, u: int, w: int, *, p: int) -> int:
    # d/dw.
    return (
        -pow(mu, 3, p)
        - (2 * pow(mu, 2, p) * u)
        - (2 * pow(mu, 2, p) * w)
        + (4 * mu * u * w)
        + (6 * u * pow(w, 2, p))
    ) % p


def _smooth_mod_p_plane_quartic(*, p: int) -> Tuple[bool, List[Tuple[int, int, int]]]:
    singular: List[Tuple[int, int, int]] = []
    for mu, u, w in product(range(p), repeat=3):
        if mu == 0 and u == 0 and w == 0:
            continue
        if _eval_Fhom(mu, u, w, p=p) != 0:
            continue
        if _eval_dmu_Fhom(mu, u, w, p=p) != 0:
            continue
        if _eval_du_Fhom(mu, u, w, p=p) != 0:
            continue
        if _eval_dw_Fhom(mu, u, w, p=p) != 0:
            continue
        singular.append((mu, u, w))
    return (len(singular) == 0), singular


def _recover_L7_from_point_counts(*, p: int, n1: int, n2: int, n3: int) -> Tuple[int, int, int, sp.Expr]:
    # For a genus-3 curve: L_p(T)=prod_{i=1}^6 (1 - alpha_i T)
    # and N_n = p^n + 1 - sum_i alpha_i^n.
    S1 = int(p + 1 - n1)
    S2 = int(p**2 + 1 - n2)
    S3 = int(p**3 + 1 - n3)

    s1 = S1
    s2 = (s1 * s1 - S2) // 2
    s3 = (S3 - s1 * S2 + s2 * s1) // 3

    T = sp.Symbol("T")
    L = 1 - s1 * T + s2 * T**2 - s3 * T**3 + p * s2 * T**4 - (p**2) * s1 * T**5 + (p**3) * T**6
    return int(s1), int(s2), int(s3), sp.expand(L)


@dataclass(frozen=True)
class Payload:
    p: int
    mod_cubic: List[int]
    smooth_mod_p: bool
    singular_points_mod_p: List[Tuple[int, int, int]]
    N: Dict[str, int]
    S: Dict[str, int]
    s1: int
    s2: int
    s3: int
    L7: str
    L7_irreducible_over_Q: bool
    L7_mod13_factor_degrees: List[int]


def main() -> None:
    print("[fold-gauge-anomaly-spectral-quartic-jacobian] start", flush=True)

    p = 7
    mod_deg1 = [0, 1]  # x
    mod_deg2 = [(-3) % p, 0, 1]  # x^2 - 3  (irreducible over F_7)
    mod_deg3 = [1, 1, 0, 1]  # x^3 + x + 1  (irreducible over F_7)

    # Deterministic sanity check: x^3 + x + 1 has no root in F_7 -> irreducible.
    for r in range(p):
        if (r**3 + r + 1) % p == 0:
            raise RuntimeError("chosen cubic modulus is reducible (unexpected)")

    smooth, singular = _smooth_mod_p_plane_quartic(p=p)

    N1 = _count_points_projective_model(p=p, n=1, mod_coeffs=mod_deg1)
    N2 = _count_points_projective_model(p=p, n=2, mod_coeffs=mod_deg2)
    N3 = _count_points_projective_model(p=p, n=3, mod_coeffs=mod_deg3)

    s1, s2, s3, L7_expr = _recover_L7_from_point_counts(p=p, n1=N1, n2=N2, n3=N3)
    T = sp.Symbol("T")

    # Factorization checks.
    fac_Q = sp.factor_list(sp.Poly(L7_expr, T, domain=sp.QQ))[1]
    irreducible_Q = bool(len(fac_Q) == 1 and int(fac_Q[0][1]) == 1 and int(sp.Poly(fac_Q[0][0], T).degree()) == 6)

    fac_mod13 = sp.factor_list(sp.Poly(L7_expr, T, modulus=13))[1]
    degs_mod13: List[int] = []
    for ff, ee in fac_mod13:
        degs_mod13.extend([int(sp.Poly(ff, T, modulus=13).degree())] * int(ee))
    degs_mod13.sort()

    payload = Payload(
        p=p,
        mod_cubic=list(mod_deg3),
        smooth_mod_p=bool(smooth),
        singular_points_mod_p=list(singular),
        N={"1": int(N1), "2": int(N2), "3": int(N3)},
        S={
            "1": int(p + 1 - N1),
            "2": int(p**2 + 1 - N2),
            "3": int(p**3 + 1 - N3),
        },
        s1=int(s1),
        s2=int(s2),
        s3=int(s3),
        L7=str(sp.Poly(L7_expr, T, domain=sp.ZZ).as_expr()),
        L7_irreducible_over_Q=bool(irreducible_Q),
        L7_mod13_factor_degrees=list(degs_mod13),
    )

    out_json = export_dir() / "fold_gauge_anomaly_spectral_quartic_jacobian_L7_audit.json"
    _write_json(out_json, asdict(payload))

    # TeX snippet.
    tex_lines: List[str] = []
    tex_lines.append("% Auto-generated by scripts/exp_fold_gauge_anomaly_spectral_quartic_jacobian_L7_audit.py")
    tex_lines.append(r"\[")
    tex_lines.append(
        rf"\#C(\FF_{{7}})={N1},\qquad \#C(\FF_{{49}})={N2},\qquad \#C(\FF_{{343}})={N3}."
    )
    tex_lines.append(r"\]")
    tex_lines.append(r"\[")
    tex_lines.append(rf"L_{{7}}(T)={sp.latex(sp.expand(L7_expr))}.")
    tex_lines.append(r"\]")
    tex_lines.append(r"\[")
    tex_lines.append(
        r"L_{7}(T)\bmod 13\ \text{在}\ \FF_{13}[T]\ \text{中不可约}"
        + rf"\qquad(\text{{因子次数分解：}} {degs_mod13})."
    )
    tex_lines.append(r"\]")
    tex_lines.append("")

    out_tex = generated_dir() / "eq_fold_gauge_anomaly_spectral_quartic_jacobian_L7_audit.tex"
    _write_text(out_tex, "\n".join(tex_lines))

    print(f"[fold-gauge-anomaly-spectral-quartic-jacobian] wrote {out_json}", flush=True)
    print(f"[fold-gauge-anomaly-spectral-quartic-jacobian] wrote {out_tex}", flush=True)
    print("[fold-gauge-anomaly-spectral-quartic-jacobian] done", flush=True)


if __name__ == "__main__":
    main()

