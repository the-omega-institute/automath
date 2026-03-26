#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit the Q-translation biquartic correspondence in (u,v) weight coordinates.

This script is English-only by repository convention.

Setup:
  E: Y^2 = X^3 - X + 1/4,
  y := X^2 + Y - 1/2,
  Q := (1, -1/2) ∈ E(Q),
  τ_Q(P) := P + Q.

For P ∈ E, define:
  u := y(P),
  v := y(P + Q).

We verify:
  - The claimed biquartic R(u,v)=0 is degree (4,4), and is irreducible over Q
    (via an irreducible specialization at u=2).
  - The discriminant factorization (as a quartic in v):
      Disc_v(R(u,v)) = -u(u-1) P_LY(u) * S(u)^2,
    where P_LY(u)=256u^3+411u^2+165u+32.
  - On many rational points P=nR (R=(0,1/2)), the relation R(u,v)=0 holds with
    u=y(P), v=y(P+Q).
  - The explicit birational recovery X=N(u,v)/D(u,v) and Y=u-X^2+1/2 recovers P
    on a Zariski open set (tested on rational samples where u≠0 and D≠0).

Outputs:
  - artifacts/export/fold_zm_elliptic_translation_q_biquartic_audit.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import sympy as sp

from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


# --- Elliptic curve arithmetic over QQ (exact) ---

Point = Optional[Tuple[sp.Rational, sp.Rational]]  # None denotes O


def _on_curve(P: Point) -> bool:
    if P is None:
        return True
    x, y = P
    return sp.simplify(y * y - (x * x * x - x + sp.Rational(1, 4))) == 0


def _neg(P: Point) -> Point:
    if P is None:
        return None
    x, y = P
    return (x, -y)


def _add(P: Point, Q: Point) -> Point:
    """Group law on E: Y^2 = X^3 - X + 1/4."""
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q

    if x1 == x2 and y1 == -y2:
        return None

    a = sp.Rational(-1, 1)

    if x1 == x2 and y1 == y2:
        if y1 == 0:
            return None
        m = sp.simplify((3 * x1 * x1 + a) / (2 * y1))
        x3 = sp.simplify(m * m - 2 * x1)
        y3 = sp.simplify(m * (x1 - x3) - y1)
        return (sp.Rational(x3), sp.Rational(y3))

    m = sp.simplify((y2 - y1) / (x2 - x1))
    x3 = sp.simplify(m * m - x1 - x2)
    y3 = sp.simplify(m * (x1 - x3) - y1)
    return (sp.Rational(x3), sp.Rational(y3))


def _mul(n: int, P: Point) -> Point:
    if n == 0 or P is None:
        return None
    if n < 0:
        return _mul(-n, _neg(P))
    acc: Point = None
    base: Point = P
    k = n
    while k:
        if k & 1:
            acc = _add(acc, base)
        base = _add(base, base)
        k >>= 1
    return acc


def _weight_y(P: Point) -> sp.Rational:
    if P is None:
        raise ValueError("y is not finite at O")
    X, Y = P
    return sp.Rational(sp.simplify(X * X + Y - sp.Rational(1, 2)))


# --- Claimed closed-form certificates (paper-level) ---


def _R_uv(u: sp.Symbol, v: sp.Symbol) -> sp.Expr:
    return (
        u**4 * v**4
        - 4 * u**3 * v**4
        - 37 * u**3 * v**3
        - 8 * u**3 * v**2
        + 6 * u**2 * v**4
        - 129 * u**2 * v**3
        + 36 * u**2 * v**2
        + 20 * u**2 * v
        + 16 * u**2
        - 4 * u * v**4
        - 79 * u * v**3
        + 44 * u * v**2
        + 79 * u * v
        + 9 * u
        + v**4
        - 11 * v**3
        + 24 * v**2
        + 36 * v
    )


def _N_uv(u: sp.Symbol, v: sp.Symbol) -> sp.Expr:
    return (
        2 * u**3 * v**3
        + 23 * u**2 * v**3
        + 4 * u**2 * v**2
        + 8 * u**2 * v
        + 28 * u * v**3
        + 17 * u * v**2
        + 3 * u * v
        - u
        + 11 * v**3
        + 7 * v**2
        - 4 * v
    )


def _D_uv(u: sp.Symbol, v: sp.Symbol) -> sp.Expr:
    return (
        13 * u**2 * v**3
        + 9 * u**2 * v**2
        + 38 * u * v**3
        + 6 * u * v**2
        - 7 * u * v
        - 4 * u
        + 13 * v**3
        - 3 * v**2
        - 16 * v
    )


def _S_u(u: sp.Symbol) -> sp.Expr:
    return (
        1024 * u**6
        + 20543 * u**5
        + 92840 * u**4
        + 180215 * u**3
        + 167685 * u**2
        + 75958 * u
        + 13671
    )


@dataclass(frozen=True)
class Payload:
    deg_u: int
    deg_v: int
    specialization_u: int
    specialized_factor_degrees: List[int]
    specialized_factor_exponents: List[int]
    specialized_irreducible: bool
    discriminant_factorization_ok: bool
    samples_checked_relation: int
    samples_checked_inverse: int
    sample_ns_relation: List[int]
    sample_ns_inverse: List[int]


def _factor_degrees_over_Q_univariate(poly: sp.Poly) -> Tuple[List[int], List[int]]:
    _c, facs = sp.factor_list(sp.Poly(poly.as_expr(), poly.gens[0], domain=sp.QQ))
    degs: List[int] = []
    exps: List[int] = []
    for f, e in facs:
        degs.append(int(f.degree()))
        exps.append(int(e))
    return degs, exps


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit the Q-translation biquartic correspondence R(u,v)=0.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output.")
    parser.add_argument("--max-n", type=int, default=60, help="Search nR samples up to this n.")
    parser.add_argument("--need-relation", type=int, default=24, help="How many relation samples to check.")
    parser.add_argument("--need-inverse", type=int, default=16, help="How many inverse samples to check.")
    args = parser.parse_args()

    u, v = sp.symbols("u v")
    R = sp.expand(_R_uv(u, v))
    N = sp.expand(_N_uv(u, v))
    D = sp.expand(_D_uv(u, v))

    # Degree sanity.
    Puv = sp.Poly(R, u, v, domain=sp.QQ)
    deg_u = int(Puv.degree(u))
    deg_v = int(Puv.degree(v))

    # Irreducibility witness via specialization u=2.
    u0 = 2
    R_u0 = sp.Poly(sp.expand(R.subs(u, sp.Integer(u0))), v, domain=sp.QQ)
    degs, exps = _factor_degrees_over_Q_univariate(R_u0)
    specialized_irred = (len(degs) == 1 and degs[0] == 4 and exps[0] == 1)

    # Discriminant factorization in QQ[u].
    Rv = sp.Poly(R, v, domain=sp.QQ[u])
    disc = sp.Poly(Rv.discriminant(), u, domain=sp.QQ)
    P_LY = 256 * u**3 + 411 * u**2 + 165 * u + 32
    S = _S_u(u)
    expected = sp.Poly(sp.expand(-u * (u - 1) * P_LY * S * S), u, domain=sp.QQ)
    disc_ok = sp.expand(disc.as_expr() - expected.as_expr()) == 0

    # Rational sample checks.
    Rgen: Point = (sp.Rational(0, 1), sp.Rational(1, 2))
    Qpt: Point = (sp.Rational(1, 1), sp.Rational(-1, 2))
    if not (_on_curve(Rgen) and _on_curve(Qpt)):
        raise AssertionError("internal curve points are not on E")

    checked_relation = 0
    checked_inverse = 0
    ns_relation: List[int] = []
    ns_inverse: List[int] = []

    for n in range(1, int(args.max_n) + 1):
        if checked_relation >= int(args.need_relation) and checked_inverse >= int(args.need_inverse):
            break

        Pn = _mul(n, Rgen)
        if Pn is None:
            continue
        try:
            un = _weight_y(Pn)
        except Exception:
            continue
        PnQ = _add(Pn, Qpt)
        if PnQ is None:
            continue
        try:
            vn = _weight_y(PnQ)
        except Exception:
            continue

        # Relation check always (including special fibers).
        if checked_relation < int(args.need_relation):
            val = sp.simplify(R.subs({u: un, v: vn}))
            if val != 0:
                raise AssertionError(f"R(u,v) != 0 at n={n}: u={un}, v={vn}, got {val}")
            checked_relation += 1
            ns_relation.append(int(n))

        # Inverse check only on the claimed open set.
        if checked_inverse < int(args.need_inverse):
            if un == 0:
                continue
            Dn = sp.simplify(D.subs({u: un, v: vn}))
            if Dn == 0:
                continue
            Xrec = sp.Rational(sp.simplify(sp.together(N.subs({u: un, v: vn}) / Dn)))
            Yrec = sp.Rational(sp.simplify(un - Xrec * Xrec + sp.Rational(1, 2)))
            if (Xrec, Yrec) != Pn:
                raise AssertionError(f"birational recovery failed at n={n}: got {(Xrec, Yrec)} expected {Pn}")
            checked_inverse += 1
            ns_inverse.append(int(n))

    payload = Payload(
        deg_u=deg_u,
        deg_v=deg_v,
        specialization_u=int(u0),
        specialized_factor_degrees=degs,
        specialized_factor_exponents=exps,
        specialized_irreducible=bool(specialized_irred),
        discriminant_factorization_ok=bool(disc_ok),
        samples_checked_relation=int(checked_relation),
        samples_checked_inverse=int(checked_inverse),
        sample_ns_relation=ns_relation,
        sample_ns_inverse=ns_inverse,
    )

    if checked_relation < int(args.need_relation):
        raise AssertionError(f"insufficient relation samples: got {checked_relation}, need {args.need_relation}")
    if checked_inverse < int(args.need_inverse):
        raise AssertionError(f"insufficient inverse samples: got {checked_inverse}, need {args.need_inverse}")
    if not payload.specialized_irreducible:
        raise AssertionError(f"specialization u={u0} did not give an irreducible quartic: degs={degs} exps={exps}")
    if not payload.discriminant_factorization_ok:
        raise AssertionError("discriminant factorization check failed")

    if not args.no_output:
        out = export_dir() / "fold_zm_elliptic_translation_q_biquartic_audit.json"
        _write_json(out, asdict(payload))

    print(
        "[fold-zm-elliptic-translation-q-biquartic] "
        f"deg(u)={payload.deg_u} deg(v)={payload.deg_v} "
        f"irred_u{payload.specialization_u}={payload.specialized_irreducible} "
        f"disc_ok={payload.discriminant_factorization_ok} "
        f"samples_relation={payload.samples_checked_relation} samples_inverse={payload.samples_checked_inverse}",
        flush=True,
    )


if __name__ == "__main__":
    main()

