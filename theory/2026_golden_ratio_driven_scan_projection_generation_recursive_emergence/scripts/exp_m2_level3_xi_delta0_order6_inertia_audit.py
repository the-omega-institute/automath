#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Order-6 tame inertia at Xi ∩ Delta_0: cycle types and charpolys.

English-only by repository convention.

We work over F_3 with V = F_3^4 and the standard symplectic form.
We take:
  - a bielliptic involution s of order 2 with V = V_+ ⊕ V_- (2+2) eigensplitting;
  - a transvection tau_v of order 3 (Picard–Lefschetz) with v an s-eigenvector.
Then s and tau_v commute, and rho := tau_v ∘ s has order 6.

We enumerate rho-orbits on:
  - points: P(V), size 40
  - lagrangians: maximal isotropic 2-planes, size 40
  - flags: (line ⊂ lagrangian), size 160

We also compute (via trace/adjacency linear systems) the characteristic polynomials of rho
on the Hecke eigensystem summands:
  - V_24 (common 24-dim summand)
  - V_15^{Kl}, V_15^{Si}
  - Steinberg St_81 (using the building chain complex trace identity)

Outputs:
  - artifacts/export/m2_level3_xi_delta0_order6_inertia_audit.json
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, FrozenSet, List, Sequence, Set, Tuple

from common_paths import export_dir

F = 3


def _mod(x: int) -> int:
    return x % F


Vec = Tuple[int, int, int, int]
Line = Vec
Plane = FrozenSet[Vec]
Flag = Tuple[Line, Plane]


def dot_symplectic(x: Vec, y: Vec) -> int:
    x1, x2, x3, x4 = x
    y1, y2, y3, y4 = y
    return _mod(x1 * y3 + x2 * y4 - x3 * y1 - x4 * y2)


def add(x: Vec, y: Vec) -> Vec:
    return (_mod(x[0] + y[0]), _mod(x[1] + y[1]), _mod(x[2] + y[2]), _mod(x[3] + y[3]))


def smul(a: int, x: Vec) -> Vec:
    return (_mod(a * x[0]), _mod(a * x[1]), _mod(a * x[2]), _mod(a * x[3]))


def all_nonzero_vectors() -> List[Vec]:
    out: List[Vec] = []
    for a in range(F):
        for b in range(F):
            for c in range(F):
                for d in range(F):
                    if a == 0 and b == 0 and c == 0 and d == 0:
                        continue
                    out.append((a, b, c, d))
    return out


def normalize_line(v: Vec) -> Vec:
    for vi in v:
        if vi % F != 0:
            inv = 1 if vi % F == 1 else 2
            return smul(inv, v)
    raise ValueError("zero vector")


def all_lines() -> List[Line]:
    seen: Set[Line] = set()
    out: List[Line] = []
    for v in all_nonzero_vectors():
        rep = normalize_line(v)
        if rep not in seen:
            seen.add(rep)
            out.append(rep)
    out.sort()
    return out


def span2(a: Vec, b: Vec) -> Set[Vec]:
    s: Set[Vec] = set()
    for i in range(F):
        for j in range(F):
            s.add(add(smul(i, a), smul(j, b)))
    return s


def is_lagrangian(plane_vectors: Set[Vec]) -> bool:
    if len(plane_vectors) != 9:
        return False
    basis: List[Vec] = [v for v in plane_vectors if v != (0, 0, 0, 0)]
    for i in range(len(basis)):
        for j in range(i + 1, len(basis)):
            if dot_symplectic(basis[i], basis[j]) != 0:
                return False
    return True


def all_lagrangians() -> List[Plane]:
    planes: Set[Plane] = set()
    vecs = all_nonzero_vectors()
    for a in vecs:
        for b in vecs:
            if a == b:
                continue
            sp = span2(a, b)
            if is_lagrangian(sp):
                planes.add(frozenset(sp))
    out = list(planes)
    out.sort(key=lambda p: sorted(p))
    return out


def lines_in_plane(plane: Plane) -> List[Line]:
    reps: Set[Line] = set()
    for v in plane:
        if v == (0, 0, 0, 0):
            continue
        reps.add(normalize_line(v))
    out = list(reps)
    out.sort()
    return out


def all_flags(lagrangians: Sequence[Plane]) -> List[Flag]:
    out: List[Flag] = []
    for pl in lagrangians:
        for ln in lines_in_plane(pl):
            out.append((ln, pl))
    out.sort(key=lambda f: (f[0], sorted(f[1])))
    return out


def involution_s(x: Vec) -> Vec:
    # +1 on span(e1,e3) and -1 on span(e2,e4).
    x1, x2, x3, x4 = x
    return (_mod(x1), _mod(-x2), _mod(x3), _mod(-x4))


def tau_v(v: Vec, x: Vec) -> Vec:
    return add(x, smul(dot_symplectic(x, v), v))


def compose(f, g):
    return lambda x: f(g(x))


def act_on_line(v: Vec, ln: Line, g) -> Line:
    return normalize_line(g(ln))


def act_on_plane(pl: Plane, g) -> Plane:
    return frozenset(g(v) for v in pl)


def act_on_flag(flag: Flag, g) -> Flag:
    ln, pl = flag
    return (normalize_line(g(ln)), act_on_plane(pl, g))


def cycle_type(elements: Sequence[object], action, max_len: int) -> Dict[int, int]:
    seen: Set[object] = set()
    counts: Dict[int, int] = {}
    for x in elements:
        if x in seen:
            continue
        cur = x
        orb: List[object] = []
        while cur not in seen:
            seen.add(cur)
            orb.append(cur)
            cur = action(cur)
        L = len(orb)
        if L > max_len:
            raise RuntimeError(f"unexpected orbit length {L}")
        counts[L] = counts.get(L, 0) + 1
    return counts


def adjacency_points(lines: Sequence[Line]) -> List[List[int]]:
    # Orthogonal adjacency on P(V): distinct lines with symplectic pairing 0.
    n = len(lines)
    idx = {lines[i]: i for i in range(n)}
    A = [[0] * n for _ in range(n)]
    for i, a in enumerate(lines):
        for j, b in enumerate(lines):
            if i == j:
                continue
            if dot_symplectic(a, b) == 0:
                A[i][j] = 1
    return A


def adjacency_lagrangians(lags: Sequence[Plane]) -> List[List[int]]:
    # Adjacency on Lag(V): two lagrangians adjacent iff intersection has size 3 (a projective line).
    n = len(lags)
    A = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            inter = lags[i].intersection(lags[j])
            # A 1-dim intersection has 3 vectors: {0, ±v}
            if len(inter) == 3:
                A[i][j] = 1
    return A


def trace_perm(elements: Sequence[object], action) -> int:
    return sum(1 for x in elements if action(x) == x)


def trace_perm_adj(elements: Sequence[object], action, Adj: List[List[int]]) -> Tuple[int, int, int]:
    # returns Tr(g), Tr(gA), Tr(gA^2)
    n = len(elements)
    idx = {elements[i]: i for i in range(n)}
    perm = [idx[action(elements[i])] for i in range(n)]
    tr_g = sum(1 for i in range(n) if perm[i] == i)
    tr_gA = sum(Adj[i][perm[i]] for i in range(n))
    # compute A^2 entry for (i,perm[i]) by row-dot-column
    tr_gA2 = 0
    for i in range(n):
        j = perm[i]
        s = 0
        row = Adj[i]
        for k in range(n):
            if row[k]:
                s += Adj[k][j]
        tr_gA2 += s
    return tr_g, tr_gA, tr_gA2


def solve_traces_for_eigenspaces(tr_g: int, tr_gA: int, tr_gA2: int) -> Tuple[int, int]:
    # For SRG eigenvalues 12,2,-4 with multiplicities 1,24,15.
    # Constant space (eigenvalue 12) has trace 1 for any permutation.
    t12 = 1
    # Solve:
    # tr_g = t12 + t2 + tm4
    # tr_gA = 12 t12 + 2 t2 - 4 tm4
    # tr_gA2 = 144 t12 + 4 t2 + 16 tm4
    rhs1 = tr_g - t12
    rhs2 = tr_gA - 12 * t12
    rhs3 = tr_gA2 - 144 * t12
    # equations:
    # t2 + tm4 = rhs1
    # 2 t2 - 4 tm4 = rhs2
    # 4 t2 + 16 tm4 = rhs3
    # Use first two.
    # From second: 2t2 = rhs2 + 4tm4 => t2 = rhs2/2 + 2tm4
    # Plug into first: rhs2/2 + 3tm4 = rhs1 => tm4 = (rhs1 - rhs2/2)/3
    tm4 = (2 * rhs1 - rhs2) // 6
    t2 = rhs1 - tm4
    # sanity check with third
    if 4 * t2 + 16 * tm4 != rhs3:
        raise RuntimeError("trace system inconsistent")
    return t2, tm4


def multiplicities_order6(dim: int, tr1: int, tr2: int, tr3: int) -> Dict[str, int]:
    # eigenvalues: 1,-1, zeta3 pair, zeta6 pair.
    # variables a,b,c,d as described in analysis.
    # equations:
    # dim = a + b + 2c + 2d
    # tr1 = a - b - c + d
    # tr2 = a + b - c - d
    # tr3 = a - b + 2c - 2d
    # Solve integers.
    # Add tr1+tr2: 2a - 2c = tr1+tr2 => a - c = (tr1+tr2)/2
    # tr2 - tr1: 2b - 2d = tr2 - tr1 => b - d = (tr2-tr1)/2
    # Use tr3 - tr1: (a-b+2c-2d) - (a-b-c+d) = 3c - 3d => c - d = (tr3-tr1)/3
    if (tr1 + tr2) % 2 != 0 or (tr2 - tr1) % 2 != 0 or (tr3 - tr1) % 3 != 0:
        raise RuntimeError("non-integral invariants")
    ac = (tr1 + tr2) // 2
    bd = (tr2 - tr1) // 2
    cd = (tr3 - tr1) // 3
    # Let c = d + cd; a = c + ac; b = d + bd.
    # Plug into dim: (c+ac) + (d+bd) + 2c + 2d = dim
    # => 3c + 3d + ac + bd = dim
    # with c = d + cd:
    # => 3(d+cd) + 3d + ac + bd = dim => 6d + 3cd + ac + bd = dim
    d = (dim - (3 * cd + ac + bd)) // 6
    c = d + cd
    a = c + ac
    b = d + bd
    if a + b + 2 * c + 2 * d != dim:
        raise RuntimeError("dimension mismatch")
    return {"m1": a, "m_1": b, "m_zeta3_pair": c, "m_zeta6_pair": d}


def charpoly_from_mult(m: Dict[str, int]) -> Dict[str, int]:
    # Return exponents for factors (T-1),(T+1),(T^2+T+1),(T^2-T+1).
    return {
        "T-1": m["m1"],
        "T+1": m["m_1"],
        "T^2+T+1": m["m_zeta3_pair"],
        "T^2-T+1": m["m_zeta6_pair"],
    }


@dataclass(frozen=True)
class Payload:
    order_rho: int
    cycle_points: Dict[str, int]
    cycle_lagrangians: Dict[str, int]
    cycle_flags: Dict[str, int]
    traces_points: Dict[str, Dict[str, int]]
    traces_lagrangians: Dict[str, Dict[str, int]]
    charpoly_V24: Dict[str, int]
    charpoly_V15_Kl: Dict[str, int]
    charpoly_V15_Si: Dict[str, int]
    charpoly_St81: Dict[str, int]


def main() -> None:
    v = (1, 0, 0, 0)
    s = involution_s
    t = lambda x: tau_v(v, x)
    rho = compose(t, s)

    lines = all_lines()
    lags = all_lagrangians()
    flags = all_flags(lags)

    # orbit counts
    cp = cycle_type(lines, lambda ln: normalize_line(rho(ln)), max_len=6)
    # Order of rho in the permutation action is lcm of cycle lengths.
    ord_r = 1
    for L in cp.keys():
        ord_r = (ord_r * L) // __import__("math").gcd(ord_r, L)

    cl = cycle_type(lags, lambda pl: act_on_plane(pl, rho), max_len=6)
    cf = cycle_type(flags, lambda fl: act_on_flag(fl, rho), max_len=6)

    Apts = adjacency_points(lines)
    Alag = adjacency_lagrangians(lags)

    def power_action(k: int, on):
        def act(x):
            y = x
            for _ in range(k):
                y = on(y)
            return y

        return act

    def traces_for(action, Adj, elements) -> Dict[str, int]:
        tr_g, tr_gA, tr_gA2 = trace_perm_adj(elements, action, Adj)
        return {"Tr(g)": tr_g, "Tr(gA)": tr_gA, "Tr(gA2)": tr_gA2}

    # traces for g, g^2, g^3 on points/lags
    tr_pts = {
        "rho": traces_for(lambda ln: normalize_line(rho(ln)), Apts, lines),
        "rho2": traces_for(power_action(2, lambda ln: normalize_line(rho(ln))), Apts, lines),
        "rho3": traces_for(power_action(3, lambda ln: normalize_line(rho(ln))), Apts, lines),
    }
    tr_lag = {
        "rho": traces_for(lambda pl: act_on_plane(pl, rho), Alag, lags),
        "rho2": traces_for(power_action(2, lambda pl: act_on_plane(pl, rho)), Alag, lags),
        "rho3": traces_for(power_action(3, lambda pl: act_on_plane(pl, rho)), Alag, lags),
    }

    # solve traces on eigenspaces for each power
    def eig_traces(tr: Dict[str, int]) -> Tuple[int, int]:
        return solve_traces_for_eigenspaces(tr["Tr(g)"], tr["Tr(gA)"], tr["Tr(gA2)"])

    t2_1, tm4_1 = eig_traces(tr_pts["rho"])
    t2_2, tm4_2 = eig_traces(tr_pts["rho2"])
    t2_3, tm4_3 = eig_traces(tr_pts["rho3"])

    V24_mult = multiplicities_order6(24, t2_1, t2_2, t2_3)
    V15Kl_mult = multiplicities_order6(15, tm4_1, tm4_2, tm4_3)

    t2s_1, tm4s_1 = eig_traces(tr_lag["rho"])
    t2s_2, tm4s_2 = eig_traces(tr_lag["rho2"])
    t2s_3, tm4s_3 = eig_traces(tr_lag["rho3"])

    V24s_mult = multiplicities_order6(24, t2s_1, t2s_2, t2s_3)
    V15Si_mult = multiplicities_order6(15, tm4s_1, tm4s_2, tm4s_3)

    # Steinberg via building trace identity using fixed points counts.
    def fixed_counts_flags(k: int) -> Tuple[int, int, int]:
        g_line = power_action(k, lambda ln: normalize_line(rho(ln)))
        g_lag = power_action(k, lambda pl: act_on_plane(pl, rho))
        g_flag = power_action(k, lambda fl: act_on_flag(fl, rho))
        Tr_pts = trace_perm(lines, g_line)
        Tr_lag = trace_perm(lags, g_lag)
        Tr_flag = trace_perm(flags, g_flag)
        return Tr_pts, Tr_lag, Tr_flag

    def Tr_St(k: int) -> int:
        Tr_pts, Tr_lag, Tr_flag = fixed_counts_flags(k)
        return Tr_flag - ((Tr_pts + Tr_lag) - 1)

    Tr1 = Tr_St(1)
    Tr2 = Tr_St(2)
    Tr3 = Tr_St(3)
    St_mult = multiplicities_order6(81, Tr1, Tr2, Tr3)

    # sanity: V24 traces should agree on both sides
    if V24_mult != V24s_mult:
        raise RuntimeError("V24 multiplicities disagree between Kl/Si computations")

    payload = Payload(
        order_rho=int(ord_r),
        cycle_points={str(k): int(vv) for k, vv in sorted(cp.items())},
        cycle_lagrangians={str(k): int(vv) for k, vv in sorted(cl.items())},
        cycle_flags={str(k): int(vv) for k, vv in sorted(cf.items())},
        traces_points=tr_pts,
        traces_lagrangians=tr_lag,
        charpoly_V24=charpoly_from_mult(V24_mult),
        charpoly_V15_Kl=charpoly_from_mult(V15Kl_mult),
        charpoly_V15_Si=charpoly_from_mult(V15Si_mult),
        charpoly_St81=charpoly_from_mult(St_mult),
    )

    out = export_dir() / "m2_level3_xi_delta0_order6_inertia_audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

