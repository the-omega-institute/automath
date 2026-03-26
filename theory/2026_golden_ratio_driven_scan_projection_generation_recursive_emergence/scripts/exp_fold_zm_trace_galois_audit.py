#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the field-trace representation of Z_m(y), the integral identity against Newton sums,
and the S4 Galois / discriminant structure for the Fold weight quartic

  Pi(lam,y) = lam^4 - lam^3 - (2y+1) lam^2 + lam + y(y+1).

This script is English-only by repository convention.

We verify:
  - Newton power sums s_m(y) = Tr_{Q(y)(lam)/Q(y)}(lam^m) via Newton identities.
  - Z_m(y) from the rational generating function / 4th-order recurrence.
  - Existence and uniqueness of u(lam) = a0 + a1 lam + a2 lam^2 + a3 lam^3 with a_i(y) in Q(y)
    such that
      Z_m(y) = Tr(u(lam) lam^m) = a0 s_m + a1 s_{m+1} + a2 s_{m+2} + a3 s_{m+3}
    for all m>=0, and we recover the explicit closed forms with denominators y * P_LY(y).
  - The cleared-denominator identity:
      y P_LY(y) Z_m = A0 s_m + A1 s_{m+1} + A2 s_{m+2} + A3 s_{m+3},
    with A_i in Z[y].
  - Cubic resolvent
      R(z,y)= z^3 + (1+2y) z^2 - (1+4y+4y^2) z - (1+5y+13y^2+8y^3),
    and discriminant identities:
      Disc_z(R) = Disc_lam(Pi) = -y(y-1) P_LY(y).
  - At y=2, R(z,2) is irreducible over Q and Disc is not a square, supporting Gal(Pi/Q(y))=S4.
  - Cardano/Kummer resolvent identity: a Groebner-reduction certificate that the
    explicit radical expression z = t + 4A(y)^2/(9t) - A(y)/3 satisfies R(z,y)=0
    under the relations v^2 = 3y(y-1)P_LY(y) and 54 t^3 = Q(y) + 3v.

Outputs:
  - artifacts/export/fold_zm_trace_galois_audit.json
  - sections/generated/eq_fold_zm_trace_galois_audit.tex
"""

from __future__ import annotations

import json
import math
import time
from itertools import product
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _newton_sums_monic(coeffs: List[sp.Expr], k_max: int) -> List[sp.Expr]:
    """
    Newton sums for a monic polynomial of degree n:
      x^n + c_{n-1} x^{n-1} + ... + c_0.

    coeffs = [c_{n-1}, ..., c_0]
    returns p[0..k_max], with p_0 = n.
    """
    n = len(coeffs)
    c = [sp.sympify(0)] + [sp.sympify(ci) for ci in coeffs]  # c[1]=c_{n-1},...,c[n]=c_0
    p: List[sp.Expr] = [sp.Integer(n)]
    for k in range(1, k_max + 1):
        if k <= n:
            s = sp.Integer(0)
            for j in range(1, k):
                s += c[j] * p[k - j]
            s += k * c[k]
            p_k = sp.simplify(-s)
        else:
            s = sp.Integer(0)
            for j in range(1, n + 1):
                s += c[j] * p[k - j]
            p_k = sp.simplify(-s)
        p.append(sp.simplify(p_k))
    return p


def _zm_initial_values(y: sp.Symbol) -> List[sp.Expr]:
    # From generating function:
    #   sum_{m>=0} Z_m t^m = (1 + y t - y t^2 - y^2 t^3) / (1 - t - (2y+1)t^2 + t^3 + y(y+1)t^4)
    Z0 = sp.Integer(1)
    Z1 = sp.Integer(1) + y
    Z2 = 2 * (sp.Integer(1) + y)
    Z3 = y**2 + 5 * y + 2
    return [Z0, Z1, Z2, Z3]


def _zm_by_recurrence(y: sp.Symbol, m_max: int) -> List[sp.Expr]:
    Z = _zm_initial_values(y)
    if m_max <= 3:
        return Z[: m_max + 1]
    for m in range(4, m_max + 1):
        Zm = sp.simplify(Z[m - 1] + (2 * y + 1) * Z[m - 2] - Z[m - 3] - y * (y + 1) * Z[m - 4])
        Z.append(Zm)
    return Z


def _is_square_int(n: int) -> bool:
    if n < 0:
        return False
    r = int(math.isqrt(n))
    return r * r == n


Perm = Tuple[int, int, int, int]  # 0-based images of 0..3


def _perm_id() -> Perm:
    return (0, 1, 2, 3)


def _perm_compose(p: Perm, q: Perm) -> Perm:
    # Composition p ∘ q (apply q, then p).
    return (p[q[0]], p[q[1]], p[q[2]], p[q[3]])


def _perm_inv(p: Perm) -> Perm:
    inv = [0, 0, 0, 0]
    for i, j in enumerate(p):
        inv[j] = i
    return (inv[0], inv[1], inv[2], inv[3])


def _perm_conj(h: Perm, g: Perm) -> Perm:
    return _perm_compose(_perm_compose(h, g), _perm_inv(h))


def _perm_cycle_type(p: Perm) -> Tuple[int, ...]:
    seen = [False] * 4
    lens: List[int] = []
    for i in range(4):
        if seen[i]:
            continue
        j = i
        cyc: List[int] = []
        while not seen[j]:
            seen[j] = True
            cyc.append(j)
            j = p[j]
        if len(cyc) > 1:
            lens.append(len(cyc))
    lens.sort(reverse=True)
    return tuple(lens)


def _perm_to_cycles_1based(p: Perm) -> str:
    # Disjoint cycle notation with 1-based symbols.
    seen = [False] * 4
    cycles: List[str] = []
    for i in range(4):
        if seen[i] or p[i] == i:
            seen[i] = True
            continue
        j = i
        cyc: List[int] = []
        while not seen[j]:
            seen[j] = True
            cyc.append(j)
            j = p[j]
        if len(cyc) > 1:
            cycles.append("(" + ",".join(str(k + 1) for k in cyc) + ")")
    if not cycles:
        return "()"
    return "".join(cycles)


def _subgroup_generated(gens: Sequence[Perm]) -> set[Perm]:
    # In a finite group, the semigroup generated by gens equals the subgroup generated by gens.
    seen: set[Perm] = {_perm_id()}
    q: List[Perm] = [_perm_id()]
    while q:
        a = q.pop()
        for g in gens:
            b = _perm_compose(a, g)
            if b not in seen:
                seen.add(b)
                q.append(b)
    return seen


def _hurwitz_sigma(gs: Tuple[Perm, Perm, Perm, Perm, Perm], i: int) -> Tuple[Perm, Perm, Perm, Perm, Perm]:
    # Right Hurwitz action: (g_i, g_{i+1}) -> (g_{i+1}, g_{i+1}^{-1} g_i g_{i+1})
    gi = gs[i]
    gj = gs[i + 1]
    gi_new = gj
    gj_new = _perm_compose(_perm_compose(_perm_inv(gj), gi), gj)
    out = list(gs)
    out[i] = gi_new
    out[i + 1] = gj_new
    return (out[0], out[1], out[2], out[3], out[4])


def _hurwitz_sigma_inv(gs: Tuple[Perm, Perm, Perm, Perm, Perm], i: int) -> Tuple[Perm, Perm, Perm, Perm, Perm]:
    # Inverse: (g_i, g_{i+1}) -> (g_i g_{i+1} g_i^{-1}, g_i)
    gi = gs[i]
    gj = gs[i + 1]
    gi_new = _perm_compose(_perm_compose(gi, gj), _perm_inv(gi))
    gj_new = gi
    out = list(gs)
    out[i] = gi_new
    out[i + 1] = gj_new
    return (out[0], out[1], out[2], out[3], out[4])


def _s4_nielsen_orbit_audit() -> Dict[str, object]:
    # Enumerate Nielsen data in S4 with passport (4)(2)^5 and test single orbit under B5 × S4.
    import itertools

    S4: List[Perm] = list(itertools.permutations(range(4)))  # type: ignore[arg-type]
    four_cycles = [p for p in S4 if _perm_cycle_type(p) == (4,)]
    transpositions = [p for p in S4 if _perm_cycle_type(p) == (2,)]

    # Canonical representative from the paper statement.
    g_inf: Perm = (1, 2, 3, 0)  # (1,2,3,4)
    g1_0: Perm = (0, 1, 3, 2)  # (3,4)
    g2_0: Perm = (0, 2, 1, 3)  # (2,3)
    g3_0: Perm = (0, 3, 2, 1)  # (2,4)
    g4_0: Perm = (3, 1, 2, 0)  # (1,4)
    g5_0: Perm = (2, 1, 0, 3)  # (1,3)
    gs0 = (g1_0, g2_0, g3_0, g4_0, g5_0)

    # Quick internal consistency checks.
    prod = _perm_id()
    for g in gs0:
        prod = _perm_compose(prod, g)
    if prod != g_inf:
        raise RuntimeError("Canonical tuple does not satisfy product constraint g1*...*g5=g_inf.")
    if _subgroup_generated((g_inf,) + gs0) != set(S4):
        raise RuntimeError("Canonical tuple does not generate S4.")

    F: set[Tuple[Perm, Perm, Perm, Perm, Perm, Perm]] = set()
    for gi in four_cycles:
        for t1, t2, t3, t4 in product(transpositions, repeat=4):
            partial = _perm_id()
            for g in (t1, t2, t3, t4):
                partial = _perm_compose(partial, g)
            t5 = _perm_compose(_perm_inv(partial), gi)
            if t5 not in transpositions:
                continue
            if _subgroup_generated((gi, t1, t2, t3, t4, t5)) != set(S4):
                continue
            F.add((gi, t1, t2, t3, t4, t5))

    # Orbit from the canonical representative under generators of B5 and full simultaneous conjugation by S4.
    start = (g_inf, g1_0, g2_0, g3_0, g4_0, g5_0)
    if start not in F:
        raise RuntimeError("Canonical tuple unexpectedly missing from the enumerated set F.")
    orbit: set[Tuple[Perm, Perm, Perm, Perm, Perm, Perm]] = set()
    q: List[Tuple[Perm, Perm, Perm, Perm, Perm, Perm]] = [start]
    orbit.add(start)

    S4_list = list(S4)
    while q:
        state = q.pop()
        gi, a1, a2, a3, a4, a5 = state
        gs = (a1, a2, a3, a4, a5)

        # B5 generators and inverses.
        for i in range(4):
            for mover in (_hurwitz_sigma, _hurwitz_sigma_inv):
                gs2 = mover(gs, i)
                nxt = (gi,) + gs2
                if nxt in F and nxt not in orbit:
                    orbit.add(nxt)
                    q.append(nxt)

        # Simultaneous conjugation.
        for h in S4_list:
            nxt = (_perm_conj(h, gi),) + tuple(_perm_conj(h, g) for g in gs)  # type: ignore[arg-type]
            if nxt in F and nxt not in orbit:
                orbit.add(nxt)
                q.append(nxt)

    single_orbit = bool(len(orbit) == len(F))
    if not single_orbit:
        # Count full orbit decomposition for debugging (still small).
        remaining = set(F)
        orbit_count = 0
        max_orbit = 0
        while remaining:
            seed = next(iter(remaining))
            sub_orbit: set[Tuple[Perm, Perm, Perm, Perm, Perm, Perm]] = set()
            qq = [seed]
            sub_orbit.add(seed)
            while qq:
                st = qq.pop()
                gi, a1, a2, a3, a4, a5 = st
                gs = (a1, a2, a3, a4, a5)
                for i in range(4):
                    for mover in (_hurwitz_sigma, _hurwitz_sigma_inv):
                        gs2 = mover(gs, i)
                        nxt = (gi,) + gs2
                        if nxt in remaining and nxt not in sub_orbit:
                            sub_orbit.add(nxt)
                            qq.append(nxt)
                for h in S4_list:
                    nxt = (_perm_conj(h, gi),) + tuple(_perm_conj(h, g) for g in gs)  # type: ignore[arg-type]
                    if nxt in remaining and nxt not in sub_orbit:
                        sub_orbit.add(nxt)
                        qq.append(nxt)
            remaining -= sub_orbit
            orbit_count += 1
            max_orbit = max(max_orbit, len(sub_orbit))
        raise RuntimeError(
            f"Expected a single B5×S4 orbit, got orbit_count={orbit_count}, max_orbit_size={max_orbit}."
        )

    # Absolute Nielsen class size is |F|/|S4| since stabilizer is trivial (center of S4).
    F_size = int(len(F))
    Ni_abs_size = int(F_size // 24)
    if 24 * Ni_abs_size != F_size:
        raise RuntimeError(f"Unexpected |F| not divisible by 24: |F|={F_size}.")

    return {
        "passport": "(4)(2)^5",
        "F_size": F_size,
        "Ni_abs_size": Ni_abs_size,
        "single_orbit_B5xS4": bool(single_orbit),
        "canonical": {
            "g_inf": _perm_to_cycles_1based(g_inf),
            "g1": _perm_to_cycles_1based(g1_0),
            "g2": _perm_to_cycles_1based(g2_0),
            "g3": _perm_to_cycles_1based(g3_0),
            "g4": _perm_to_cycles_1based(g4_0),
            "g5": _perm_to_cycles_1based(g5_0),
        },
        "counts": {
            "num_4cycles": int(len(four_cycles)),
            "num_transpositions": int(len(transpositions)),
        },
    }


@dataclass(frozen=True)
class Payload:
    u_coeffs: Dict[str, str]
    u_matches_expected: bool
    trace_identity_ok_up_to_m: int
    disc_pi: str
    disc_resolvent: str
    disc_identity_ok: bool
    resolvent_irreducible_at_y2: bool
    disc_y2: int
    disc_y2_is_square: bool
    cardano_resolvent_identity_ok: bool
    nielsen_orbit_audit: Dict[str, object]


def main() -> None:
    t0 = time.time()
    print("[fold-zm-trace-galois] start", flush=True)

    lam, y, z = sp.symbols("lam y z")
    Pi = lam**4 - lam**3 - (2 * y + 1) * lam**2 + lam + y * (y + 1)
    P_LY = 256 * y**3 + 411 * y**2 + 165 * y + 32

    # Newton sums s_m = Tr(lam^m), m up to 12 (enough for audits).
    # Pi = lam^4 + c3 lam^3 + c2 lam^2 + c1 lam + c0 (monic).
    c3 = sp.Integer(-1)
    c2 = -(2 * y + 1)
    c1 = sp.Integer(1)
    c0 = y * (y + 1)
    s = _newton_sums_monic([c3, c2, c1, c0], k_max=16)  # s[0]=4

    # Z_m via recurrence.
    Z = _zm_by_recurrence(y, m_max=16)

    # Solve for u = a0 + a1 lam + a2 lam^2 + a3 lam^3 by matching m=0..3:
    a0, a1, a2, a3 = sp.symbols("a0 a1 a2 a3")
    eqs = []
    for m in range(0, 4):
        rhs = a0 * s[m] + a1 * s[m + 1] + a2 * s[m + 2] + a3 * s[m + 3]
        eqs.append(sp.Eq(sp.simplify(rhs), sp.simplify(Z[m])))
    sol = sp.solve(eqs, [a0, a1, a2, a3], dict=True)
    if len(sol) != 1:
        raise RuntimeError(f"Unexpected number of solutions for u-coefficients: {len(sol)}")
    sol0 = sol[0]
    a0_sol = sp.together(sol0[a0])
    a1_sol = sp.together(sol0[a1])
    a2_sol = sp.together(sol0[a2])
    a3_sol = sp.together(sol0[a3])

    # Expected closed forms (paper statement).
    a0_exp = sp.together((-19 * y**3 - 75 * y**2 - 42 * y - 8) / P_LY)
    a2_exp = sp.together((87 * y**2 + 48 * y + 9) / P_LY)
    a1_exp = sp.together((80 * y**4 - 20 * y**3 - 82 * y**2 - 42 * y - 8) / (y * P_LY))
    a3_exp = sp.together((-16 * y**3 + 49 * y**2 + 31 * y + 8) / (y * P_LY))

    match = (
        sp.factor(a0_sol - a0_exp) == 0
        and sp.factor(a1_sol - a1_exp) == 0
        and sp.factor(a2_sol - a2_exp) == 0
        and sp.factor(a3_sol - a3_exp) == 0
    )

    # Verify trace identity for a range of m (exact symbolic check).
    ok_upto = 0
    for m in range(0, 13):
        rhs = sp.simplify(a0_sol * s[m] + a1_sol * s[m + 1] + a2_sol * s[m + 2] + a3_sol * s[m + 3])
        if sp.factor(rhs - Z[m]) != 0:
            break
        ok_upto = m

    # Cubic resolvent and discriminants.
    R = z**3 + (1 + 2 * y) * z**2 - (1 + 4 * y + 4 * y**2) * z - (1 + 5 * y + 13 * y**2 + 8 * y**3)
    disc_R = sp.factor(sp.discriminant(R, z))
    disc_Pi = sp.factor(sp.discriminant(Pi, lam))
    disc_expected = sp.factor(-y * (y - 1) * P_LY)
    disc_ok = bool(sp.factor(disc_R - disc_expected) == 0 and sp.factor(disc_Pi - disc_expected) == 0)

    # Specialize y=2 for irreducibility witness and discriminant non-square.
    R2 = sp.Poly(sp.expand(R.subs({y: 2})), z, domain="QQ")
    fac = sp.factor_list(R2)[1]
    irreducible_y2 = bool(len(fac) == 1 and int(fac[0][0].degree()) == 3)
    disc_y2 = int(sp.discriminant(R2.as_expr(), z))
    disc_y2_square = _is_square_int(abs(disc_y2))

    # Cardano/Kummer explicit radical check:
    # Let A(y)=1+2y, Q(y)=16+69y+219y^2+128y^3, and introduce v with
    #   v^2 = 3y(y-1)P_LY(y)  (i.e. v = sqrt(-3)*w on the discriminant ridge curve).
    # If t^3 = (Q+3v)/54 and z = t + 4A^2/(9t) - A/3, then R(z,y)=0.
    v_sym, t_sym = sp.symbols("v t")
    A = 1 + 2 * y
    Q = 16 + 69 * y + 219 * y**2 + 128 * y**3
    z_expr = t_sym + 4 * A**2 / (9 * t_sym) - A / 3
    poly = sp.expand(sp.together(R.subs({z: z_expr}) * t_sym**3))
    rel1 = v_sym**2 - 3 * y * (y - 1) * P_LY
    rel2 = 54 * t_sym**3 - (Q + 3 * v_sym)
    rel3 = Q**2 - 256 * A**6 - 9 * v_sym**2
    G = sp.groebner([rel1, rel2, rel3], t_sym, v_sym, y, order="grevlex", domain=sp.QQ)
    _, rem = G.reduce(poly)
    cardano_ok = bool(sp.factor(rem) == 0)
    if not cardano_ok:
        raise RuntimeError(f"Cardano/Kummer resolvent identity failed, remainder={sp.sstr(rem)}")

    nielsen_orbit_audit = _s4_nielsen_orbit_audit()

    payload = Payload(
        u_coeffs={
            "a0": sp.sstr(a0_sol),
            "a1": sp.sstr(a1_sol),
            "a2": sp.sstr(a2_sol),
            "a3": sp.sstr(a3_sol),
        },
        u_matches_expected=bool(match),
        trace_identity_ok_up_to_m=int(ok_upto),
        disc_pi=sp.sstr(disc_Pi),
        disc_resolvent=sp.sstr(disc_R),
        disc_identity_ok=bool(disc_ok),
        resolvent_irreducible_at_y2=bool(irreducible_y2),
        disc_y2=int(disc_y2),
        disc_y2_is_square=bool(disc_y2_square),
        cardano_resolvent_identity_ok=bool(cardano_ok),
        nielsen_orbit_audit=nielsen_orbit_audit,
    )

    out_json = export_dir() / "fold_zm_trace_galois_audit.json"
    _write_json(out_json, asdict(payload))

    # TeX snippet.
    tex = "\n".join(
        [
            "% Auto-generated by scripts/exp_fold_zm_trace_galois_audit.py",
            "\\[",
            "P_{\\mathrm{LY}}(y):=256y^{3}+411y^{2}+165y+32,",
            "\\]",
            "\\[",
            "u(\\lambda)=a_0+a_1\\lambda+a_2\\lambda^{2}+a_3\\lambda^{3},\\qquad"
            "Z_m(y)=\\mathrm{Tr}(u(\\lambda)\\lambda^{m})=a_0s_m+a_1s_{m+1}+a_2s_{m+2}+a_3s_{m+3},",
            "\\]",
            "\\[",
            "a_0=\\frac{-19y^{3}-75y^{2}-42y-8}{P_{\\mathrm{LY}}(y)},\\quad"
            "a_1=\\frac{80y^{4}-20y^{3}-82y^{2}-42y-8}{yP_{\\mathrm{LY}}(y)},\\quad"
            "a_2=\\frac{87y^{2}+48y+9}{P_{\\mathrm{LY}}(y)},\\quad"
            "a_3=\\frac{-16y^{3}+49y^{2}+31y+8}{yP_{\\mathrm{LY}}(y)}.",
            "\\]",
            "\\[",
            "R(z,y)=z^{3}+(1+2y)z^{2}-(1+4y+4y^{2})z-(1+5y+13y^{2}+8y^{3}),",
            "\\]",
            "\\[",
            "\\mathrm{Disc}_{z}(R)=\\mathrm{Disc}_{\\lambda}(\\Pi)=-y(y-1)P_{\\mathrm{LY}}(y).",
            "\\]",
            "",
        ]
    )
    out_tex = generated_dir() / "eq_fold_zm_trace_galois_audit.tex"
    _write_text(out_tex, tex)

    dt = time.time() - t0
    print(
        "[fold-zm-trace-galois] checks:"
        f" u_match={match} trace_ok_upto={ok_upto} disc_ok={disc_ok} R2_irred={irreducible_y2} disc_y2_square={disc_y2_square}"
        f" cardano_ok={cardano_ok}"
        f" nielsen_single_orbit={nielsen_orbit_audit.get('single_orbit_B5xS4', None)}"
        f" seconds={dt:.3f}",
        flush=True,
    )
    print(f"[fold-zm-trace-galois] wrote {out_json}", flush=True)
    print(f"[fold-zm-trace-galois] wrote {out_tex}", flush=True)
    print("[fold-zm-trace-galois] done", flush=True)


if __name__ == "__main__":
    main()

