#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Arithmetic structure of the Newman sparse-generator field K = Q(theta) (q=4).

We take theta as a root of the 6-term sparse polynomial

  Z(z) = z^8 - 2 z^6 - 2 z^5 - 2 z^4 - 2 z^3 - 2  in Z[z],

which generates the same degree-8 field as the Newman threshold polynomial P_4(t)
via the elimination constraint C(t,z)=0 (see eq_collision_kernel_A4_newman_sparse_generator.tex).

This script certifies:
  - 2-Eisenstein property of Z,
  - maximal order / integral basis (monogenicity),
  - field discriminant and signature,
  - prime ideal decomposition at the four ramified primes 2,7,23,1151,
  - principal-parameter valuations for theta and the shifted uniformizers.

Outputs:
  - artifacts/export/collision_kernel_A4_newman_sparse_generator_arithmetic.json
  - sections/generated/eq_collision_kernel_A4_newman_sparse_generator_arithmetic.tex
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp
from sympy import Poly, QQ

from common_paths import export_dir, generated_dir


def _poly_Z() -> Tuple[sp.Symbol, sp.Poly]:
    z = sp.Symbol("z")
    Z = sp.Poly(z**8 - 2 * z**6 - 2 * z**5 - 2 * z**4 - 2 * z**3 - 2, z, domain=sp.ZZ)
    return z, Z


def _is_eisenstein_at_2(Z: sp.Poly) -> bool:
    coeffs = [int(c) for c in Z.all_coeffs()]  # high -> low
    if coeffs[0] % 2 == 0:
        return False
    if any((c % 2) != 0 for c in coeffs[1:]):
        return False
    if coeffs[-1] % 4 == 0:
        return False
    return True


def _vp(n: int, p: int) -> int:
    n = abs(int(n))
    if n == 0:
        return 10**9
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def _factorint_str(n: int) -> Dict[str, int]:
    if n == 0:
        return {"0": 1}
    fac = sp.factorint(abs(int(n)))
    out: Dict[str, int] = {"-1": 1} if n < 0 else {}
    for p, e in fac.items():
        out[str(int(p))] = int(e)
    return out


def _tex_factorization(n: int) -> str:
    if n == 0:
        return "0"
    sign = "-" if n < 0 else ""
    fac = sp.factorint(abs(int(n)))
    parts: List[str] = []
    for p in sorted(fac.keys()):
        e = int(fac[p])
        if e == 1:
            parts.append(f"{int(p)}")
        else:
            parts.append(f"{int(p)}^{{{e}}}")
    return sign + r"\cdot ".join(parts)


def _alpha_poly_latex(alpha_vec: List[int]) -> str:
    """PrimeIdeal.alpha -> LaTeX polynomial in theta (ascending powers)."""
    th = sp.Symbol("theta")
    expr = sp.Integer(0)
    for i, c in enumerate(alpha_vec):
        ci = int(c)
        if ci == 0:
            continue
        expr += sp.Integer(ci) * th**i
    return sp.latex(sp.expand(expr))


def _nroots_signature(Z: sp.Poly, *, dps: int = 120, imag_eps: str = "1e-30") -> Tuple[int, int]:
    roots = Z.nroots(n=dps, maxsteps=200)
    eps = sp.Float(imag_eps)
    r1 = sum(1 for r in roots if abs(sp.im(r)) < eps)
    r2 = (int(Z.degree()) - int(r1)) // 2
    return int(r1), int(r2)


@dataclass(frozen=True)
class PrimeIdealData:
    p: int
    gen_alpha: List[int]
    gen_latex: str
    e: int
    f: int


@dataclass(frozen=True)
class Payload:
    eisenstein_2: bool
    integral_basis_is_power_basis: bool
    disc_poly_Z: int
    disc_field_K: int
    index_Ztheta: int
    disc_factorization: Dict[str, int]
    signature_r1: int
    signature_r2: int
    unit_rank: int
    primes_ramified: List[int]
    prime_decompositions: Dict[str, List[PrimeIdealData]]
    uniformizer_norm_values: Dict[str, int]
    uniformizer_vp_norm: Dict[str, int]
    uniformizer_normalized_valuations: Dict[str, str]


def _write_tex(path: Path, *, disc_K: int, r1: int, r2: int, unit_rank: int, decomp: Dict[int, List[PrimeIdealData]]) -> None:
    # Field generator symbol in TeX.
    th = r"\theta"
    disc_tex = _tex_factorization(disc_K)

    def _ideal(name: str, p: int, alpha_latex: str) -> str:
        return rf"{name}=({p},{alpha_latex})"

    # Extract named prime ideals for stable display.
    # 2
    P2 = decomp[2][0]
    # 7: identify the linear ramified prime (theta-2) and the degree-5 prime.
    P7_lin = next(P for P in decomp[7] if P.e > 1)
    Q7 = next(P for P in decomp[7] if P.f == 5)
    # 23: identify the ramified linear prime (theta-6), the other linear, and the quadratics.
    P23_lin = next(P for P in decomp[23] if P.e > 1)
    A23 = next(P for P in decomp[23] if P.f == 1 and P.e == 1 and P.gen_latex.replace(" ", "") in {r"\theta-7", r"-7+\theta"})
    Q23 = [P for P in decomp[23] if P.f == 2]
    # 1151: identify the ramified linear prime and the three quadratics.
    P1151_lin = next(P for P in decomp[1151] if P.e > 1)
    Q1151 = [P for P in decomp[1151] if P.f == 2]
    p2_label = r"\mathfrak p_2"
    p7_label = r"\mathfrak p_7"
    q7_label = r"\mathfrak q_7"
    p23_label = r"\mathfrak p_{23}"
    a23_label = r"\mathfrak a_{23}"
    b23_label = r"\mathfrak b_{23}"
    c23_label = r"\mathfrak c_{23}"
    p1151_label = r"\mathfrak p_{1151}"
    b1151_label = r"\mathfrak b_{1151}"
    c1151_label = r"\mathfrak c_{1151}"
    d1151_label = r"\mathfrak d_{1151}"

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_collision_kernel_A4_newman_sparse_generator_arithmetic.py")
    lines.append(r"\begin{equation}\label{eq:collision_kernel_A4_newman_sparse_generator_arithmetic}")
    lines.append(r"\begin{aligned}")
    lines.append(rf"\mathcal O_K&=\ZZ[{th}],\qquad \{{1,{th},{th}^2,\dots,{th}^7\}}\ \text{{为}}\ \mathcal O_K\ \text{{的一组整基}},\\")
    lines.append(rf"\mathrm{{Disc}}(K)&={disc_tex},\\")
    lines.append(rf"(r_1,r_2)&=({r1},{r2}),\qquad \mathrm{{rank}}(\mathcal O_K^\times)=r_1+r_2-1={unit_rank},\\")
    lines.append(rf"(2)&=\mathfrak p_2^{{{P2.e}}},\qquad {_ideal(p2_label, 2, th)},\\")
    lines.append(rf"(7)&=\mathfrak p_7^{{{P7_lin.e}}}\mathfrak q_7,\qquad {_ideal(p7_label, 7, P7_lin.gen_latex)},\qquad {_ideal(q7_label, 7, Q7.gen_latex)},\\")
    lines.append(rf"(23)&=\mathfrak p_{{23}}^{{{P23_lin.e}}}\mathfrak a_{{23}}\mathfrak b_{{23}}\mathfrak c_{{23}},\\")
    lines.append(rf"&\qquad {_ideal(p23_label, 23, P23_lin.gen_latex)},\qquad {_ideal(a23_label, 23, A23.gen_latex)},\\")
    lines.append(
        rf"&\qquad {_ideal(b23_label, 23, Q23[0].gen_latex)},\qquad {_ideal(c23_label, 23, Q23[1].gen_latex)},\\"
    )
    lines.append(rf"(1151)&=\mathfrak p_{{1151}}^{{{P1151_lin.e}}}\mathfrak b_{{1151}}\mathfrak c_{{1151}}\mathfrak d_{{1151}},\\")
    lines.append(rf"&\qquad {_ideal(p1151_label, 1151, P1151_lin.gen_latex)},\\")
    lines.append(
        rf"&\qquad {_ideal(b1151_label, 1151, Q1151[0].gen_latex)},\qquad {_ideal(c1151_label, 1151, Q1151[1].gen_latex)},\qquad {_ideal(d1151_label, 1151, Q1151[2].gen_latex)}."
    )
    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Certify the maximal-order arithmetic for the Newman sparse-generator field K=Q(theta).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_newman_sparse_generator_arithmetic.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_collision_kernel_A4_newman_sparse_generator_arithmetic.tex"),
        help="Output TeX path.",
    )
    parser.add_argument("--dps", type=int, default=120, help="Working precision for root counting via nroots.")
    args = parser.parse_args()

    z, Z = _poly_Z()
    eisen2 = _is_eisenstein_at_2(Z)

    # Field as an AlgebraicField; let theta be the generator name.
    theta = sp.Symbol("theta")
    K = QQ.algebraic_field((Z, theta))
    ZK = K.maximal_order()
    n = int(Z.degree())

    # Discriminants and index.
    disc_poly = int(sp.discriminant(Z, z))
    disc_field = int(K.discriminant())
    if disc_poly % disc_field != 0:
        raise RuntimeError("Disc(poly) is not divisible by Disc(field).")
    ratio = disc_poly // disc_field
    if ratio <= 0:
        raise RuntimeError("Expected a positive discriminant ratio.")
    idx = int(math.isqrt(int(ratio)))
    if idx * idx != int(ratio):
        raise RuntimeError("Disc ratio is not a perfect square; cannot form an integer index.")

    # Maximal order is the power basis if and only if its matrix is identity and denom=1.
    is_power_basis = (ZK.denom == 1 and ZK.matrix.to_Matrix() == sp.eye(n))

    # Signature and unit rank.
    r1, r2 = _nroots_signature(Z, dps=int(args.dps))
    unit_rank = int(r1 + r2 - 1)

    # Prime decompositions at ramified primes.
    ram_primes = [2, 7, 23, 1151]
    decomp: Dict[int, List[PrimeIdealData]] = {}
    for p in ram_primes:
        ideals = []
        for P in K.primes_above(p):
            alpha_vec = [int(c) for c in P.alpha.coeffs]
            ideals.append(
                PrimeIdealData(
                    p=int(p),
                    gen_alpha=alpha_vec,
                    gen_latex=_alpha_poly_latex(alpha_vec),
                    e=int(P.e),
                    f=int(P.f),
                )
            )
        # stable sort: higher ramification first, then residue degree
        ideals.sort(key=lambda I: (-I.e, -I.f))
        decomp[int(p)] = ideals

    # Uniformizers (principal parameters) and normalized valuations v_P(·) with v_P(p)=1.
    # Use Norm(theta-a) = (-1)^n Z(a) and the fact that the relevant (p, theta-a) is the only
    # prime above p containing theta-a.
    uniformizers = {
        "p2_theta": (2, 0, 8),  # (p, a, e), parameter theta-a
        "p7_theta_minus_2": (7, 2, 3),
        "p23_theta_minus_6": (23, 6, 3),
        "p1151_theta_plus_499": (1151, -499, 2),
    }
    norm_values: Dict[str, int] = {}
    vp_norm: Dict[str, int] = {}
    v_normalized: Dict[str, str] = {}
    for key, (p, a, e) in uniformizers.items():
        val = int(Z.eval(int(a)))
        norm_values[key] = val
        vp = _vp(val, int(p))
        vp_norm[key] = int(vp)
        # ord_P(theta-a) = v_p(Norm(theta-a)) = v_p(Z(a)) = 1 in this example.
        v_normalized[key] = str(sp.Rational(vp, int(e)))

    payload = Payload(
        eisenstein_2=bool(eisen2),
        integral_basis_is_power_basis=bool(is_power_basis),
        disc_poly_Z=int(disc_poly),
        disc_field_K=int(disc_field),
        index_Ztheta=int(idx),
        disc_factorization=_factorint_str(disc_field),
        signature_r1=int(r1),
        signature_r2=int(r2),
        unit_rank=int(unit_rank),
        primes_ramified=ram_primes,
        prime_decompositions={str(k): v for k, v in decomp.items()},
        uniformizer_norm_values=norm_values,
        uniformizer_vp_norm=vp_norm,
        uniformizer_normalized_valuations=v_normalized,
    )

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[A4-newman-sparse-generator-arithmetic] wrote {out}", flush=True)

    _write_tex(Path(args.tex_out), disc_K=disc_field, r1=r1, r2=r2, unit_rank=unit_rank, decomp=decomp)
    print(f"[A4-newman-sparse-generator-arithmetic] wrote {args.tex_out}", flush=True)

    # Sanity checks expected in the manuscript.
    if not eisen2:
        raise RuntimeError("Z(z) is expected to be 2-Eisenstein.")
    if idx != 1:
        raise RuntimeError("Expected O_K = Z[theta] (index 1) for this sparse generator.")


if __name__ == "__main__":
    main()

