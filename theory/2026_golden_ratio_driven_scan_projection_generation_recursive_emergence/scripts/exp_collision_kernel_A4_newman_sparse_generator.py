#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Sparse generator for the Newman-critical degree-8 field (q=4).

Paper-local context:
  - The edge-weight Newman/RH threshold is certified by the degree-8 polynomial P_4(t)
    in sections/generated/eq_collision_kernel_A4_edge_weight_threshold.tex.
  - Along the negative-real-mode channel (see rem:pom-collision-rh-break-a4-threshold),
    one obtains a degree-8 algebraic integer z satisfying a sparse 6-term polynomial.

This script certifies a short elimination description of the same degree-8 field:

  Z(z) := z^8 - 2 z^6 - 2 z^5 - 2 z^4 - 2 z^3 - 2  in Z[z],
  C(t,z) := z^5 + 2 z^4 - t z^3 - 2 z - 2      in Z[t,z],

and proves by resultant elimination that

  Res_z(Z(z), C(t,z)) = -8 * P_4(t).

It also computes:
  - Disc_z(Z) and Disc_t(P_4) with full integer factorizations,
  - the exact square ratio Disc_t(P_4)/Disc_z(Z),
  - modular factorization patterns used as Galois-group certificates,
  - repeated-root structures at primes in the discriminant support.

Outputs:
  - artifacts/export/collision_kernel_A4_newman_sparse_generator.json
  - sections/generated/eq_collision_kernel_A4_newman_sparse_generator.tex
"""

from __future__ import annotations

import argparse
import json
import math
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp
from sympy.utilities.exceptions import SymPyDeprecationWarning

from common_paths import export_dir, generated_dir


warnings.filterwarnings(
    "ignore",
    message=r"(?s).*Ordered comparisons with modular integers are deprecated.*",
    category=SymPyDeprecationWarning,
)


def _poly_P4() -> sp.Poly:
    t = sp.Symbol("t")
    P4 = t**8 - 10 * t**7 + 72 * t**6 - 24 * t**5 - 1924 * t**4 - 2904 * t**3 + 1312 * t**2 + 1464 * t - 1412
    return sp.Poly(sp.expand(P4), t)


def _poly_Z() -> sp.Poly:
    z = sp.Symbol("z")
    Z = z**8 - 2 * z**6 - 2 * z**5 - 2 * z**4 - 2 * z**3 - 2
    return sp.Poly(sp.expand(Z), z)


def _poly_C() -> Tuple[sp.Symbol, sp.Symbol, sp.Expr]:
    t = sp.Symbol("t")
    z = sp.Symbol("z")
    C = sp.expand(z**5 + 2 * z**4 - t * z**3 - 2 * z - 2)
    return t, z, C


def _factorint_str(n: int) -> Dict[str, int]:
    return {str(int(p)): int(e) for p, e in sp.factorint(int(n)).items()}


def _squarefree_part_signed(n: int) -> int:
    if n == 0:
        return 0
    sign = -1 if n < 0 else 1
    fac = sp.factorint(abs(int(n)))
    out = sign
    for p, e in fac.items():
        if int(e) % 2 == 1:
            out *= int(p)
    return int(out)


def _tex_factorization(n: int) -> str:
    """Return a TeX string like -2^{10}\\cdot 7^{2}\\cdot 1151."""
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


def _factor_degrees_mod_p(poly: sp.Poly, p: int) -> List[int]:
    x = poly.gens[0]
    fac = sp.factor_list(sp.Poly(poly.as_expr(), x, modulus=p))
    degs: List[int] = []
    for f, e in fac[1]:
        deg = int(sp.Poly(f, x, modulus=p).degree())
        degs.extend([deg] * int(e))
    degs.sort(reverse=True)
    return degs


def _linear_root_mod_p(f: sp.Poly, p: int) -> int:
    """For degree-1 f=a*x+b over F_p, return the unique root (-b/a) mod p."""
    x = f.gens[0]
    fp = sp.Poly(f.as_expr(), x, modulus=p)
    if fp.degree() != 1:
        raise ValueError("Expected degree-1 polynomial.")
    a, b = [int(c) % p for c in fp.all_coeffs()]
    inv_a = pow(a, -1, p)
    return int((-b * inv_a) % p)


def _factor_profile_mod_p(poly: sp.Poly, p: int) -> List[Dict[str, object]]:
    """Return a structured factor profile of poly mod p."""
    x = poly.gens[0]
    fl = sp.factor_list(sp.Poly(poly.as_expr(), x, modulus=p))
    out: List[Dict[str, object]] = []
    for f, e in fl[1]:
        fp = sp.Poly(f, x, modulus=p)
        deg = int(fp.degree())
        item: Dict[str, object] = {"degree": deg, "exp": int(e), "poly": str(fp.as_expr())}
        if deg == 1:
            item["root"] = _linear_root_mod_p(fp, p)
        out.append(item)
    # sort: higher multiplicity first, then degree
    out.sort(key=lambda d: (-int(d["exp"]), -int(d["degree"])))
    return out


@dataclass(frozen=True)
class Payload:
    # resultant certificate
    resultant_res_z: str
    resultant_expected: str
    resultant_ok: bool
    # discriminants
    disc_Z: int
    disc_Z_factorization: Dict[str, int]
    disc_P4: int
    disc_P4_factorization: Dict[str, int]
    ratio_disc_P4_over_Z: int
    ratio_is_square: bool
    ratio_sqrt: int
    ratio_sqrt_factorization: Dict[str, int]
    sqf_disc_Z: int
    sqf_disc_P4: int
    # modular factor degrees (Galois certificate inputs)
    Z_mod_13_degrees: List[int]
    Z_mod_3_degrees: List[int]
    Z_mod_5_degrees: List[int]
    # repeated-root / ramification portraits at discriminant primes
    Z_mod_2_profile: List[Dict[str, object]]
    Z_mod_7_profile: List[Dict[str, object]]
    Z_mod_23_profile: List[Dict[str, object]]
    Z_mod_1151_profile: List[Dict[str, object]]


def _write_tex(path: Path, *, disc_Z: int, disc_P4: int, ratio_sqrt: int, resultant_ok: bool, res_const: int) -> None:
    Z_tex = r"z^{8}-2z^{6}-2z^{5}-2z^{4}-2z^{3}-2"
    C_tex = r"z^{5}+2z^{4}-tz^{3}-2z-2"
    discZ_tex = _tex_factorization(disc_Z)
    discP4_tex = _tex_factorization(disc_P4)
    ratio_sqrt_tex = _tex_factorization(ratio_sqrt)

    # Prefer a compact certificate that points to P_4(t) already defined elsewhere.
    res_tex = f"{res_const}\\,P_4(t)"

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_collision_kernel_A4_newman_sparse_generator.py")
    lines.append(r"\begin{equation}\label{eq:collision_kernel_A4_newman_sparse_generator}")
    lines.append(r"\begin{aligned}")
    lines.append(rf"\mathcal Z(z)&:={Z_tex},\\")
    lines.append(rf"\mathcal C(t,z)&:={C_tex},\\")
    lines.append(rf"\mathrm{{Res}}_z\!\bigl(\mathcal Z(z),\mathcal C(t,z)\bigr)&={res_tex},\\")
    lines.append(rf"\mathrm{{Disc}}_z(\mathcal Z)&={discZ_tex},\\")
    lines.append(rf"\mathrm{{Disc}}_t(P_4)&={discP4_tex},\\")
    lines.append(rf"\frac{{\mathrm{{Disc}}_t(P_4)}}{{\mathrm{{Disc}}_z(\mathcal Z)}}&=\Bigl({ratio_sqrt_tex}\Bigr)^2.")
    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Certify the sparse generator and discriminant data for the q=4 Newman-critical degree-8 field.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "collision_kernel_A4_newman_sparse_generator.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_collision_kernel_A4_newman_sparse_generator.tex"),
        help="Output TeX path.",
    )
    args = parser.parse_args()

    # Polynomials
    P4 = _poly_P4()
    Z = _poly_Z()
    t, z, C = _poly_C()

    # Resultant certificate: Res_z(Z(z), C(t,z)) = const * P4(t).
    Res = sp.resultant(Z.as_expr(), C, z)
    Res_poly = sp.Poly(sp.expand(Res), t)

    expected_8 = sp.Poly(8 * P4.as_expr(), t)
    expected_m8 = sp.Poly(-8 * P4.as_expr(), t)
    if Res_poly == expected_8:
        res_const = 8
        expected = expected_8
        res_ok = True
    elif Res_poly == expected_m8:
        res_const = -8
        expected = expected_m8
        res_ok = True
    else:
        res_const = 0
        expected = expected_8
        res_ok = False

    # Discriminants
    disc_Z = int(sp.discriminant(Z, z))
    disc_P4 = int(sp.discriminant(P4, t))

    # Ratio and square check
    if disc_Z == 0:
        raise RuntimeError("Disc(Z) unexpectedly zero.")
    ratio = disc_P4 // disc_Z
    if disc_P4 != disc_Z * ratio:
        raise RuntimeError("Disc(P4) is not an integer multiple of Disc(Z).")
    if ratio <= 0:
        raise RuntimeError("Expected a positive discriminant ratio.")
    s = int(math.isqrt(int(ratio)))
    ratio_is_square = (s * s == int(ratio))
    if not ratio_is_square:
        raise RuntimeError("Expected Disc(P4)/Disc(Z) to be a perfect square.")

    # Squarefree parts (signed)
    sqf_Z = _squarefree_part_signed(disc_Z)
    sqf_P4 = _squarefree_part_signed(disc_P4)

    # Modular factor degrees (for Galois certificates)
    Z_mod_13 = _factor_degrees_mod_p(Z, 13)
    Z_mod_3 = _factor_degrees_mod_p(Z, 3)
    Z_mod_5 = _factor_degrees_mod_p(Z, 5)

    # Discriminant-prime factor profiles (repeated-root portraits)
    prof_2 = _factor_profile_mod_p(Z, 2)
    prof_7 = _factor_profile_mod_p(Z, 7)
    prof_23 = _factor_profile_mod_p(Z, 23)
    prof_1151 = _factor_profile_mod_p(Z, 1151)

    payload = Payload(
        resultant_res_z=str(Res_poly.as_expr()),
        resultant_expected=str(expected.as_expr()),
        resultant_ok=bool(res_ok),
        disc_Z=int(disc_Z),
        disc_Z_factorization=_factorint_str(disc_Z),
        disc_P4=int(disc_P4),
        disc_P4_factorization=_factorint_str(disc_P4),
        ratio_disc_P4_over_Z=int(ratio),
        ratio_is_square=bool(ratio_is_square),
        ratio_sqrt=int(s),
        ratio_sqrt_factorization=_factorint_str(s),
        sqf_disc_Z=int(sqf_Z),
        sqf_disc_P4=int(sqf_P4),
        Z_mod_13_degrees=Z_mod_13,
        Z_mod_3_degrees=Z_mod_3,
        Z_mod_5_degrees=Z_mod_5,
        Z_mod_2_profile=prof_2,
        Z_mod_7_profile=prof_7,
        Z_mod_23_profile=prof_23,
        Z_mod_1151_profile=prof_1151,
    )

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[A4-newman-sparse-generator] wrote {out}", flush=True)

    _write_tex(Path(args.tex_out), disc_Z=disc_Z, disc_P4=disc_P4, ratio_sqrt=s, resultant_ok=res_ok, res_const=res_const)
    print(f"[A4-newman-sparse-generator] wrote {args.tex_out}", flush=True)

    if not res_ok:
        raise RuntimeError("Resultant certificate check failed.")


if __name__ == "__main__":
    main()

