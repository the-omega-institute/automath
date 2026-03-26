#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the j(a) sextic discriminant ellipticization and A6 base change.

This script verifies fingerprints used in the xi section:
  - the cubic discriminant / elliptic discriminant of E0: y^2 = (t-1728)(t^2+1862t+161792),
  - the exact rational identities for j(a)-1728 and j(a)^2+1862 j(a)+161792,
  - discriminants and resultant for r(a), H(a), and P(a)=r(a)H(a),
  - an explicit branch cycle tuple: product is 1 and generated group is S6.

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, List, Tuple

import sympy as sp

from common_paths import paper_root, scripts_dir


@dataclass(frozen=True)
class PermutationCheck:
    name: str
    images: List[int]  # 1-indexed images


def _perm_from_cycles(n: int, cycles: List[Tuple[int, ...]]) -> List[int]:
    """Return 1-indexed images list for a permutation on {1..n}."""
    p = list(range(n + 1))
    for cyc in cycles:
        if len(cyc) <= 1:
            continue
        for i in range(len(cyc)):
            p[cyc[i]] = cyc[(i + 1) % len(cyc)]
    return p


def _perm_compose(p: List[int], q: List[int]) -> List[int]:
    """Right action composition: (p followed by q) => q∘p, 1-indexed."""
    n = len(p) - 1
    out = [0] * (n + 1)
    out[0] = 0
    for i in range(1, n + 1):
        out[i] = q[p[i]]
    return out


def _perm_compose_left(p: List[int], q: List[int]) -> List[int]:
    """Left action composition: (p followed by q) => p∘q, 1-indexed."""
    n = len(p) - 1
    out = [0] * (n + 1)
    out[0] = 0
    for i in range(1, n + 1):
        out[i] = p[q[i]]
    return out


def _perm_inv(p: List[int]) -> List[int]:
    n = len(p) - 1
    inv = [0] * (n + 1)
    inv[0] = 0
    for i in range(1, n + 1):
        inv[p[i]] = i
    return inv


def _group_generated(n: int, gens: List[List[int]]) -> List[List[int]]:
    """Naive closure for small permutation groups."""
    ident = list(range(n + 1))
    seen = {tuple(ident)}
    queue: List[List[int]] = [ident]
    # include inverses to accelerate closure
    genset = gens + [_perm_inv(g) for g in gens]
    while queue:
        g = queue.pop()
        for h in genset:
            gh = _perm_compose(g, h)
            t = tuple(gh)
            if t not in seen:
                seen.add(t)
                queue.append(gh)
    return [list(t) for t in seen]


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit j-sextic ellipticization, hyperelliptic model, and A6 base change.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(
            paper_root()
            / "artifacts"
            / "export"
            / "xi_j_sextic_ellipticization_a6_hyperelliptic_audit.json"
        ),
        help="Output JSON path.",
    )
    args = parser.parse_args()

    # --- Elliptic discriminant for E0
    t = sp.Symbol("t")
    f = (t - 1728) * (t**2 + 1862 * t + 161792)
    f_poly = sp.Poly(sp.expand(f), t, domain=sp.ZZ)
    disc_cubic = int(sp.discriminant(f_poly.as_expr(), t))
    # For y^2 = monic cubic, elliptic discriminant is 16*Disc(cubic).
    Delta_E0 = int(16 * disc_cubic)
    Delta_E0_target = int((2**20) * (89**3) * (223**4))

    # --- Rational identities for j(a)
    a = sp.Symbol("a")
    r = 16 * a**3 - 13 * a**2 - 78 * a + 43
    s = 8 * a**3 + 15 * a**2 - 66 * a + 35
    p = 2 * a**2 - 9 * a - 1
    H = (
        2048 * a**8
        - 8752 * a**7
        + 16455 * a**6
        - 5030 * a**5
        - 39667 * a**4
        + 82096 * a**3
        - 74559 * a**2
        + 33406 * a
        - 5869
    )
    j = -4096 * (a**2 - a + 1) ** 3 / ((a - 1) ** 2 * r)

    id1 = sp.simplify(j - 1728 + 64 * s**2 / ((a - 1) ** 2 * r))
    id2 = sp.simplify(j**2 + 1862 * j + 161792 - (2048 * p**2 * H) / ((a - 1) ** 4 * r**2))
    jprime = sp.simplify(sp.diff(j, a))
    id3 = sp.simplify(
        jprime
        + 4096
        * (a**2 - a + 1) ** 2
        * (s * p)
        / ((a - 1) ** 3 * r**2)
    )

    # --- Discriminants and resultant
    disc_r = int(sp.discriminant(sp.Poly(r, a, domain=sp.ZZ).as_expr(), a))
    disc_H = int(sp.discriminant(sp.Poly(H, a, domain=sp.ZZ).as_expr(), a))
    res_rH = int(sp.resultant(sp.Poly(r, a, domain=sp.ZZ), sp.Poly(H, a, domain=sp.ZZ), a))
    P = sp.expand(r * H)
    disc_P = int(sp.discriminant(sp.Poly(P, a, domain=sp.ZZ).as_expr(), a))

    disc_r_target = int((2**6) * (79**3))
    disc_H_target = int(-(2**30) * (79**9) * (89**10) * (223**3))
    res_rH_target = int((2**27) * (79**8))
    disc_P_target = int(-(2**90) * (79**28) * (89**10) * (223**3))

    # --- Branch cycles
    n = 6
    sigma0 = _perm_from_cycles(n, [(1, 3, 4), (2, 6, 5)])
    sigma1728 = _perm_from_cycles(n, [(1, 6), (2, 5), (3, 4)])
    sigmap = _perm_from_cycles(n, [(1, 5)])
    sigmam = _perm_from_cycles(n, [(1, 6)])
    sigmainf = _perm_from_cycles(n, [(1, 3)])

    ident = list(range(n + 1))

    # Product checks under common conventions.
    prod_right_lr = sigma0
    for sgm in [sigma1728, sigmap, sigmam, sigmainf]:
        prod_right_lr = _perm_compose(prod_right_lr, sgm)

    prod_right_rl = sigmainf
    for sgm in [sigmam, sigmap, sigma1728, sigma0]:
        prod_right_rl = _perm_compose(prod_right_rl, sgm)

    prod_left_lr = sigma0
    for sgm in [sigma1728, sigmap, sigmam, sigmainf]:
        prod_left_lr = _perm_compose_left(prod_left_lr, sgm)

    prod_left_rl = sigmainf
    for sgm in [sigmam, sigmap, sigma1728, sigma0]:
        prod_left_rl = _perm_compose_left(prod_left_rl, sgm)

    product_conventions = {
        "right_action_left_to_right": prod_right_lr == ident,
        "right_action_right_to_left": prod_right_rl == ident,
        "left_action_left_to_right": prod_left_lr == ident,
        "left_action_right_to_left": prod_left_rl == ident,
    }
    prod_is_id_some_convention = any(product_conventions.values())

    group = _group_generated(n, [sigma0, sigma1728, sigmap, sigmam, sigmainf])
    group_order = len(group)

    out: Dict[str, object] = {
        "elliptic": {
            "f(t)": str(f_poly.as_expr()),
            "disc_cubic": disc_cubic,
            "Delta_E0": Delta_E0,
            "Delta_E0_target": Delta_E0_target,
            "Delta_E0_matches_target": bool(Delta_E0 == Delta_E0_target),
            "Delta_E0_factorint": {int(k): int(v) for k, v in sp.factorint(Delta_E0).items()},
        },
        "identities": {
            "j(a)": str(sp.simplify(j)),
            "jprime(a)": str(jprime),
            "id_j_minus_1728_residual": str(id1),
            "id_quadratic_factor_residual": str(id2),
            "id_jprime_residual": str(id3),
            "id1_is_zero": bool(id1 == 0),
            "id2_is_zero": bool(id2 == 0),
            "id3_is_zero": bool(id3 == 0),
        },
        "hyperelliptic_branch_poly": {
            "disc_r": disc_r,
            "disc_r_target": disc_r_target,
            "disc_r_matches_target": bool(disc_r == disc_r_target),
            "disc_H": disc_H,
            "disc_H_target": disc_H_target,
            "disc_H_matches_target": bool(disc_H == disc_H_target),
            "res_rH": res_rH,
            "res_rH_target": res_rH_target,
            "res_rH_matches_target": bool(res_rH == res_rH_target),
            "disc_P": disc_P,
            "disc_P_target": disc_P_target,
            "disc_P_matches_target": bool(disc_P == disc_P_target),
        },
        "branch_cycles": {
            "sigma0": asdict(PermutationCheck(name="sigma0", images=sigma0[1:])),
            "sigma1728": asdict(PermutationCheck(name="sigma1728", images=sigma1728[1:])),
            "sigma_plus": asdict(PermutationCheck(name="sigma_plus", images=sigmap[1:])),
            "sigma_minus": asdict(PermutationCheck(name="sigma_minus", images=sigmam[1:])),
            "sigma_infty": asdict(PermutationCheck(name="sigma_infty", images=sigmainf[1:])),
            "product_is_identity_some_convention": bool(prod_is_id_some_convention),
            "product_conventions": product_conventions,
            "generated_group_order": int(group_order),
            "generated_group_is_S6": bool(group_order == 720),
        },
        "meta": {
            "script": Path(__file__).name,
            "scripts_dir": str(scripts_dir()),
        },
    }

    out_path = Path(args.out_json)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Hard assertions for pipeline gating
    assert Delta_E0 == Delta_E0_target, "E0 discriminant does not match target factorization"
    assert id1 == 0, "Identity for j(a)-1728 failed"
    assert id2 == 0, "Identity for quadratic branch factor failed"
    assert disc_r == disc_r_target, "Disc(r) mismatch"
    assert disc_H == disc_H_target, "Disc(H) mismatch"
    assert res_rH == res_rH_target, "Res(r,H) mismatch"
    assert disc_P == disc_P_target, "Disc(P) mismatch"
    assert prod_is_id_some_convention, "Branch cycle product is not identity under standard conventions"
    assert group_order == 720, "Branch cycles do not generate S6"


if __name__ == "__main__":
    main()

