#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the delta-projection discriminant and S5 fingerprints on the Lee--Yang elliptic model.

This script is English-only by repository convention.

We work with the elliptic curve
  E: Y^2 = X^3 - X + 1/4
and the coordinates
  y := X^2 + Y - 1/2,
  delta := dy/du = 4 X Y + 3 X^2 - 1   (for du = dX/(2Y)).

Let F_delta(T;y) be the Abel--Jacobi algebraic ODE quartic:
  F_delta(T;y) = 0 where T represents delta.

We certify:
  - Disc_y(F_delta) = 16 (T-4) A5(T)^2 B5(T) with explicit quintics A5,B5.
  - The singular subscheme elimination:
      Q5(y)=0 and 93 T = P4(y),
      A5(T)=0 and 353664 y + (...) = 0.
  - Galois evidence for A5 and B5: irreducible mod p and a (2)(3) Frobenius type,
    plus nonsquare discriminant, hence Gal = S5.
  - Branch-value resultant identity:
      Res_X(100X^5-136X^4+16X^3+40X^2-13X+1, 3δ+20X^3-9X^2-12X+5) = 4860 B5(δ).
  - Bad-prime collapse:
      B5(δ) ≡ δ^2(δ^3+2δ^2-4δ+3) (mod 37).

Outputs:
  - artifacts/export/fold_zm_delta_projection_a5b5_audit.json
  - sections/generated/eq_fold_zm_delta_projection_a5b5_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _poly_ZZ(expr: sp.Expr, var: sp.Symbol) -> sp.Poly:
    return sp.Poly(sp.expand(expr), var, domain=sp.ZZ)


def _normalize_primitive_ZZ(poly: sp.Poly, var: sp.Symbol) -> sp.Poly:
    if poly.domain != sp.ZZ:
        poly = sp.Poly(poly.as_expr(), var, domain=sp.ZZ)
    _content, prim = poly.primitive()
    if prim.LC() < 0:
        prim = -prim
    return prim


def _factor_degrees_mod_p(poly_ZZ: sp.Poly, *, p: int, var: sp.Symbol) -> List[int]:
    fac = sp.factor_list(poly_ZZ.set_modulus(p).as_expr(), modulus=p)
    degs: List[int] = []
    for f_expr, mult in fac[1]:
        _ = mult
        degs.append(sp.Poly(f_expr, var, modulus=p).degree())
    return sorted(degs)


@dataclass(frozen=True)
class Payload:
    disc_y_factor_ok: bool
    disc_y_deg_T: int
    a5_coeffs_high_to_low: List[int]
    b5_coeffs_high_to_low: List[int]
    q5_coeffs_high_to_low: List[int]
    node_linear_T_ok: bool
    node_linear_y_ok: bool
    a5_mod7_irreducible: bool
    a5_mod61_factor_degrees: List[int]
    a5_disc_is_square: bool
    b5_mod59_irreducible: bool
    b5_mod7_factor_degrees: List[int]
    b5_disc_is_square: bool
    resultant_b5_ok: bool
    resultant_b5_constant: int
    b5_mod37_factor_ok: bool
    seconds: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit delta-projection A5/B5 discriminant and S5 evidence.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    t0 = time.time()
    print("[fold-zm-delta-projection-a5b5] start", flush=True)

    T, y = sp.symbols("T y")

    F = (
        T**4
        + (8 * y - 3) * T**3
        + (2 * y**2 - 34 * y - 4) * T**2
        + 32 * y
        + 133 * y**2
        + 246 * y**3
        - 155 * y**4
        - 256 * y**5
    )

    A5 = _poly_ZZ(4096 * T**5 - 47360 * T**4 + 186992 * T**3 - 231939 * T**2 - 200880 * T + 482112, T)
    B5 = _poly_ZZ(50000 * T**5 + 136112 * T**4 + 60776 * T**3 - 26712 * T**2 + 38961 * T + 35964, T)

    # --- Disc_y factorization ---
    Disc_y = sp.discriminant(F, y)
    Disc_y_ZZ = _poly_ZZ(Disc_y, T)
    disc_y_deg_T = Disc_y_ZZ.degree()
    Disc_expected = 16 * (T - 4) * (A5.as_expr() ** 2) * B5.as_expr()
    disc_y_factor_ok = bool(sp.simplify(Disc_y - Disc_expected) == 0)

    # --- Singular subscheme elimination ---
    Fy = sp.diff(F, y)
    FT = sp.diff(F, T)

    # eliminate T: lex [T, y]
    G_Ty = sp.groebner([F, Fy, FT], [T, y], order="lex", domain=sp.QQ)
    # Q5(y)
    elim_y = [g.as_expr() for g in G_Ty.polys if g.as_expr().free_symbols <= {y}]
    Q5 = _normalize_primitive_ZZ(sp.Poly(elim_y[0], y, domain=sp.QQ).clear_denoms()[1], y)
    # linear relation: 93*T - P4(y)
    linT_expr = None
    for g in G_Ty.polys:
        expr = sp.expand(g.as_expr())
        p = sp.Poly(expr, T, y, domain=sp.QQ)
        if p.degree(T) != 1:
            continue
        # collect a(y), b(y) s.t. a(y)*T + b(y)=0
        a = 0
        b = 0
        ok = True
        for (i, j), c in p.as_dict().items():
            if i == 1:
                a += sp.Rational(c) * y**j
            elif i == 0:
                b += sp.Rational(c) * y**j
            else:
                ok = False
                break
        if ok and sp.Poly(b, y).degree() >= 1:
            # clear denominators to ZZ[T,y]
            pa = sp.Poly(a, y, domain=sp.QQ)
            pb = sp.Poly(b, y, domain=sp.QQ)
            den = 1
            for cc in list(pa.all_coeffs()) + list(pb.all_coeffs()):
                den = sp.ilcm(den, sp.denom(cc))
            linT_expr = sp.expand(den * a * T + den * b)
            break
    node_linear_T_ok = bool(
        sp.Poly(linT_expr, T, y, domain=sp.ZZ).primitive()[1].as_expr()
        == (93 * T - (8192 * y**4 + 5888 * y**3 - 3680 * y**2 - 2848 * y + 152))
    )

    # eliminate y: lex [y, T]
    G_yT = sp.groebner([F, Fy, FT], [y, T], order="lex", domain=sp.QQ)
    elim_T = [g.as_expr() for g in G_yT.polys if g.as_expr().free_symbols <= {T}]
    A5_from_elim = _normalize_primitive_ZZ(sp.Poly(elim_T[0], T, domain=sp.QQ).clear_denoms()[1], T)

    # linear relation for y: 353664*y + ... = 0
    liny_expr = None
    for g in G_yT.polys:
        expr = sp.expand(g.as_expr())
        p = sp.Poly(expr, y, T, domain=sp.QQ)
        if p.degree(y) != 1:
            continue
        coeff_y = 0
        const = 0
        ok = True
        for (i, j), c in p.as_dict().items():
            if i == 1:
                coeff_y += sp.Rational(c) * T**j
            elif i == 0:
                const += sp.Rational(c) * T**j
            else:
                ok = False
                break
        if not ok:
            continue
        # Clear denominators of coeff_y and const.
        py = sp.Poly(coeff_y, T, domain=sp.QQ)
        pc = sp.Poly(const, T, domain=sp.QQ)
        den = 1
        for cc in list(py.all_coeffs()) + list(pc.all_coeffs()):
            den = sp.ilcm(den, sp.denom(cc))
        liny_expr = sp.expand(den * coeff_y * y + den * const)
        break

    liny_prim = sp.Poly(liny_expr, y, T, domain=sp.ZZ).primitive()[1]
    if liny_prim.LC() < 0:
        liny_prim = -liny_prim
    node_linear_y_expected = (
        353664 * y
        + 1863680 * T**4
        - 16240384 * T**3
        + 38835472 * T**2
        + 5074731 * T
        - 77031720
    )
    node_linear_y_ok = bool(sp.expand(liny_prim.as_expr() - node_linear_y_expected) == 0)

    # --- Galois evidence: mod p factorization + nonsquare discriminant ---
    a5_mod7_irreducible = _factor_degrees_mod_p(A5, p=7, var=T) == [5]
    a5_mod61_factor_degrees = _factor_degrees_mod_p(A5, p=61, var=T)
    b5_mod59_irreducible = _factor_degrees_mod_p(B5, p=59, var=T) == [5]
    b5_mod7_factor_degrees = _factor_degrees_mod_p(B5, p=7, var=T)

    disc_A5 = int(sp.discriminant(A5.as_expr(), T))
    disc_B5 = int(sp.discriminant(B5.as_expr(), T))
    a5_disc_is_square = bool(sp.ntheory.primetest.is_square(abs(disc_A5)))
    b5_disc_is_square = bool(sp.ntheory.primetest.is_square(abs(disc_B5)))

    # --- Resultant identity for branch values ---
    X, delta = sp.symbols("X delta")
    f5 = 100 * X**5 - 136 * X**4 + 16 * X**3 + 40 * X**2 - 13 * X + 1
    lin = 3 * delta + 20 * X**3 - 9 * X**2 - 12 * X + 5
    res = sp.resultant(f5, lin, X)
    resultant_b5_constant = int(sp.factor(res / B5.as_expr().xreplace({T: delta})))
    resultant_b5_ok = bool(sp.simplify(res - 4860 * B5.as_expr().xreplace({T: delta})) == 0)

    # --- mod 37 collapse ---
    # Exact reduction in F_37[δ]:
    #   B5(δ) ≡ 13 δ^2(δ^3+2δ^2-4δ+3) (mod 37).
    delta_poly_expected = sp.Poly(
        13 * delta**2 * (delta**3 + 2 * delta**2 - 4 * delta + 3),
        delta,
        modulus=37,
    )
    b5_mod37_poly = sp.Poly(B5.as_expr().xreplace({T: delta}), delta, modulus=37)
    b5_mod37_factor_ok = bool(b5_mod37_poly == delta_poly_expected)

    seconds = time.time() - t0

    payload = Payload(
        disc_y_factor_ok=disc_y_factor_ok,
        disc_y_deg_T=disc_y_deg_T,
        a5_coeffs_high_to_low=[int(c) for c in A5.all_coeffs()],
        b5_coeffs_high_to_low=[int(c) for c in B5.all_coeffs()],
        q5_coeffs_high_to_low=[int(c) for c in Q5.all_coeffs()],
        node_linear_T_ok=node_linear_T_ok,
        node_linear_y_ok=node_linear_y_ok,
        a5_mod7_irreducible=a5_mod7_irreducible,
        a5_mod61_factor_degrees=a5_mod61_factor_degrees,
        a5_disc_is_square=a5_disc_is_square,
        b5_mod59_irreducible=b5_mod59_irreducible,
        b5_mod7_factor_degrees=b5_mod7_factor_degrees,
        b5_disc_is_square=b5_disc_is_square,
        resultant_b5_ok=resultant_b5_ok,
        resultant_b5_constant=resultant_b5_constant,
        b5_mod37_factor_ok=b5_mod37_factor_ok,
        seconds=seconds,
    )

    assert payload.disc_y_factor_ok
    assert payload.node_linear_T_ok
    assert payload.node_linear_y_ok
    assert payload.a5_mod7_irreducible
    assert payload.a5_mod61_factor_degrees == [2, 3]
    assert not payload.a5_disc_is_square
    assert payload.b5_mod59_irreducible
    assert payload.b5_mod7_factor_degrees == [2, 3]
    assert not payload.b5_disc_is_square
    assert payload.resultant_b5_ok
    assert payload.resultant_b5_constant == 4860
    assert payload.b5_mod37_factor_ok
    assert A5_from_elim.as_expr() == A5.as_expr()

    if not args.no_output:
        _write_json(export_dir() / "fold_zm_delta_projection_a5b5_audit.json", asdict(payload))

        tex = r"""% Auto-generated by scripts/exp_fold_zm_delta_projection_a5b5_audit.py
\begin{align}
\mathrm{Disc}_{y}\!\bigl(F_\delta(T;y)\bigr)
&=16\,(T-4)\,A_5(T)^2\,B_5(T),\\
93\,T
&=8192y^{4}+5888y^{3}-3680y^{2}-2848y+152,\\
353664\,y
&=-1863680T^{4}+16240384T^{3}-38835472T^{2}-5074731T+77031720,\\
\mathrm{Res}_X\!\left(
100X^5-136X^4+16X^3+40X^2-13X+1,\ \ 3\delta+20X^3-9X^2-12X+5
\right)
&=4860\,B_5(\delta),\\
B_5(\delta)
&\equiv 13\,\delta^2(\delta^3+2\delta^2-4\delta+3)\pmod{37}.
\end{align}
"""
        _write_text(generated_dir() / "eq_fold_zm_delta_projection_a5b5_audit.tex", tex)

    print(f"[fold-zm-delta-projection-a5b5] ok seconds={seconds:.3f}", flush=True)


if __name__ == "__main__":
    main()

