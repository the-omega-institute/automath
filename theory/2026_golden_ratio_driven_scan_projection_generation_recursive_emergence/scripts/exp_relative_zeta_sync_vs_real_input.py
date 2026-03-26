#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Relative zeta bridge: 10-state sync-kernel B versus 40-state real-input kernel M.

We compute:
  - traces a_n(B), a_n(M) and relative traces r_n = a_n(B) - a_n(M)
  - primitive orbit counts p_n(B), p_n(M) and relative q_n = p_n(B) - p_n(M)
  - the relative residue constant C_{B/M} at z*=1/3:
        zeta_{B/M}(z) := zeta_B(z)/zeta_M(z)
        zeta_{B/M}(z) = C_{B/M}/(1-3z) + O(1)
  - the relative finite-part constant log M_{B/M} at z*=1/3 via Möbius–zeta sampling:
        log M_{B/M} = log C_{B/M} + sum_{m>=2} mu(m)/m * log zeta_{B/M}(3^{-m})

Audits:
  (i) q_n equals the Möbius transform of r_n (linearity audit)
  (ii) for 1<=n<=N, negative q_n occurs only at n=2
  (iii) the fixed 10th-order linear recurrence for r_n holds on computed data

Outputs:
  - artifacts/export/relative_zeta_sync_vs_real_input.json
  - sections/generated/eq_relative_zeta_sync_vs_real_input.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import mpmath as mp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


# -------------------------
# Core matrices (integers)
# -------------------------

B_MATRIX: List[List[int]] = [
    [1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    [1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
    [0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
]


KERNEL_STATES = [
    "000",
    "001",
    "002",
    "010",
    "100",
    "101",
    "0-12",
    "1-12",
    "01-1",
    "11-1",
]


@dataclass(frozen=True)
class KernelEdge:
    src: str
    dst: str
    d: int
    e: int


def build_kernel_edges() -> List[KernelEdge]:
    edges: List[KernelEdge] = []
    for d in (0, 1, 2):
        edges.append(KernelEdge("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(KernelEdge("100", f"00{d}", d, 1))
    edges += [
        KernelEdge("001", "010", 0, 0),
        KernelEdge("001", "100", 1, 0),
        KernelEdge("001", "101", 2, 0),
        KernelEdge("002", "11-1", 0, 0),
        KernelEdge("002", "000", 1, 1),
        KernelEdge("002", "001", 2, 1),
        KernelEdge("010", "100", 0, 0),
        KernelEdge("010", "101", 1, 0),
        KernelEdge("010", "0-12", 2, 1),
        KernelEdge("101", "010", 0, 1),
        KernelEdge("101", "100", 1, 1),
        KernelEdge("101", "101", 2, 1),
        KernelEdge("0-12", "01-1", 0, 0),
        KernelEdge("0-12", "010", 1, 0),
        KernelEdge("0-12", "100", 2, 0),
        KernelEdge("1-12", "01-1", 0, 1),
        KernelEdge("1-12", "010", 1, 1),
        KernelEdge("1-12", "100", 2, 1),
        KernelEdge("01-1", "001", 0, 0),
        KernelEdge("01-1", "002", 1, 0),
        KernelEdge("01-1", "1-12", 2, 0),
        KernelEdge("11-1", "001", 0, 1),
        KernelEdge("11-1", "002", 1, 1),
        KernelEdge("11-1", "1-12", 2, 1),
    ]
    return edges


def build_kernel_map(edges: Sequence[KernelEdge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(edge.src, edge.d): (edge.dst, edge.e) for edge in edges}


def build_real_input_states() -> List[Tuple[str, int, int]]:
    states: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                states.append((s, px, py))
    return states


def build_real_input_matrix_int(
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> List[List[int]]:
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    M = [[0] * n for _ in range(n)]
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, _ = kernel_map[(s, d)]
                nxt = (dst_state, x, y)
                M[idx[(s, px, py)]][idx[nxt]] += 1
    return M


# -------------------------
# Integer linear algebra
# -------------------------


def mat_mul_int(A: List[List[int]], B: List[List[int]]) -> List[List[int]]:
    n = len(A)
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for k in range(n):
            aik = Ai[k]
            if aik == 0:
                continue
            Bk = B[k]
            for j in range(n):
                bkj = Bk[j]
                if bkj:
                    out[i][j] += aik * bkj
    return out


def mat_trace_int(A: List[List[int]]) -> int:
    return sum(A[i][i] for i in range(len(A)))


def mat_pow_traces_int(M: List[List[int]], n_max: int, prog: Progress, label: str) -> List[int]:
    if n_max <= 0:
        return []
    P = [row[:] for row in M]
    out: List[int] = []
    for n in range(1, n_max + 1):
        if n > 1:
            P = mat_mul_int(P, M)
        out.append(mat_trace_int(P))
        prog.tick(f"traces {label} n={n}/{n_max}")
    return out


# -------------------------
# Möbius/Witt interface
# -------------------------


def mobius(n: int) -> int:
    if n == 1:
        return 1
    x = n
    mu = 1
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            mu = -mu
            if x % p == 0:
                return 0
            while x % p == 0:
                x //= p
        p = 3 if p == 2 else p + 2
    if x > 1:
        mu = -mu
    return mu


def divisors(n: int) -> List[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def primitive_counts_from_traces(traces: Sequence[int], prog: Progress, label: str) -> List[int]:
    pvals: List[int] = []
    for n in range(1, len(traces) + 1):
        s = 0
        for d in divisors(n):
            s += mobius(d) * traces[n // d - 1]
        if s % n != 0:
            raise ValueError(f"non-integer primitive count for {label} n={n}: {s}/{n}")
        pvals.append(s // n)
        prog.tick(f"primitive {label} n={n}/{len(traces)}")
    return pvals


# -------------------------
# Rational det / zeta (exact)
# -------------------------


def det_B(z: Fraction) -> Fraction:
    return (z - 1) * (z + 1) * (3 * z - 1) * (z**3 - z**2 + z + 1)


def det_M(z: Fraction) -> Fraction:
    return (1 - z) ** 2 * (1 + z) ** 3 * (1 - 3 * z + z * z) * (1 + z - z * z)


def zeta_rel_B_over_M(z: Fraction) -> Fraction:
    # zeta_{B/M}(z) = zeta_B(z)/zeta_M(z) = det_M(z)/det_B(z)
    return det_M(z) / det_B(z)


def frac_to_mp(x: Fraction) -> mp.mpf:
    return mp.mpf(x.numerator) / mp.mpf(x.denominator)


def tail_bound_geom(q: mp.mpf, N: int) -> mp.mpf:
    # sum_{k>N} q^k/k <= q^{N+1}/((N+1)(1-q)); apply a conservative factor.
    return (mp.mpf("5") * q ** (N + 1)) / (mp.mpf(N + 1) * (1 - q))


# -------------------------
# Fixed relative recurrence (10th order)
# -------------------------


REC_R_COEFFS = [4, 4, -26, 5, 42, -37, -4, 26, -16, 3]
# r_n = sum_{j=1..10} REC_R_COEFFS[j-1] * r_{n-j}, for n>=11 (1-indexed)


def audit_recurrence_r(traces_r: Sequence[int]) -> bool:
    # traces_r is [r_1, r_2, ...]
    if len(traces_r) < 11:
        return True
    for n in range(11, len(traces_r) + 1):
        rhs = 0
        for j, c in enumerate(REC_R_COEFFS, start=1):
            rhs += c * traces_r[n - j - 1]
        if traces_r[n - 1] != rhs:
            return False
    return True


@dataclass(frozen=True)
class Payload:
    n_max: int
    n_sign_audit: int
    traces_B_10: List[int]
    traces_M_10: List[int]
    traces_r_10: List[int]
    prim_B_10: List[int]
    prim_M_10: List[int]
    prim_q_10: List[int]
    q_negative_indices: List[int]
    q_negative_values: List[int]
    audit_q_from_r_ok: bool
    audit_q_sign_ok: bool
    audit_r_recurrence_ok: bool
    C_B_exact: str
    zeta_M_at_1_over_3_exact: str
    C_rel_exact: str
    C_rel_decimal: str
    logM_rel_decimal: str
    M_rel_decimal: str
    logM_tail_bound: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Relative zeta: sync-kernel B vs real-input kernel M.")
    parser.add_argument("--n-max", type=int, default=200, help="Max n for trace/primitive computations.")
    parser.add_argument("--mobius-N", type=int, default=300, help="Truncation N for logM Möbius sum (m>=2..N).")
    parser.add_argument("--dps", type=int, default=120, help="mpmath precision (decimal digits).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "relative_zeta_sync_vs_real_input.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_relative_zeta_sync_vs_real_input.tex"),
    )
    args = parser.parse_args()

    n_max = int(args.n_max)
    mobius_N = int(args.mobius_N)
    mp.mp.dps = int(args.dps)

    prog = Progress("relative_zeta_sync_vs_real_input", every_seconds=20.0)

    # Build M (40-state) adjacency
    kernel_map = build_kernel_map(build_kernel_edges())
    states = build_real_input_states()
    M_MATRIX = build_real_input_matrix_int(states, kernel_map)

    traces_B = mat_pow_traces_int(B_MATRIX, n_max, prog, label="B")
    traces_M = mat_pow_traces_int(M_MATRIX, n_max, prog, label="M")
    traces_r = [b - m for b, m in zip(traces_B, traces_M)]

    prim_B = primitive_counts_from_traces(traces_B, prog, label="B")
    prim_M = primitive_counts_from_traces(traces_M, prog, label="M")
    prim_q = [pb - pm for pb, pm in zip(prim_B, prim_M)]

    # Audit (i): Möbius transform on r_n equals q_n
    q_from_r = primitive_counts_from_traces(traces_r, prog, label="r=B-M")
    audit_q_from_r_ok = (q_from_r == prim_q)

    # Audit (ii): sign pattern for q_n
    q_neg = [(i + 1, v) for i, v in enumerate(prim_q) if v < 0]
    audit_q_sign_ok = (q_neg == [(2, -1)])

    # Audit (iii): 10th-order recurrence for r_n
    audit_r_recurrence_ok = audit_recurrence_r(traces_r)

    # Exact residue constants at z*=1/3
    z = Fraction(1, 3)
    C_B = Fraction(243, 272)  # derived from det(I-zB)
    zeta_M_at_1_over_3 = Fraction(1, 1) / det_M(z)
    C_rel = C_B / zeta_M_at_1_over_3

    # Relative finite-part constant at z*=1/3
    logM_rel = mp.log(frac_to_mp(C_rel))
    for m in range(2, mobius_N + 1):
        mu = mobius(m)
        if mu == 0:
            continue
        zm = Fraction(1, 3**m)
        zeta_rel = zeta_rel_B_over_M(zm)
        logM_rel += mp.mpf(mu) * mp.log(frac_to_mp(zeta_rel)) / mp.mpf(m)
        prog.tick(f"logM_rel m={m}/{mobius_N}")

    # Conservative tail bound (geometric envelope at q=1/3)
    tail_bd = tail_bound_geom(mp.mpf(1) / mp.mpf(3), mobius_N)

    # Write JSON payload
    payload = Payload(
        n_max=n_max,
        n_sign_audit=n_max,
        traces_B_10=traces_B[:10],
        traces_M_10=traces_M[:10],
        traces_r_10=traces_r[:10],
        prim_B_10=prim_B[:10],
        prim_M_10=prim_M[:10],
        prim_q_10=prim_q[:10],
        q_negative_indices=[i for i, _ in q_neg],
        q_negative_values=[v for _, v in q_neg],
        audit_q_from_r_ok=bool(audit_q_from_r_ok),
        audit_q_sign_ok=bool(audit_q_sign_ok),
        audit_r_recurrence_ok=bool(audit_r_recurrence_ok),
        C_B_exact="243/272",
        zeta_M_at_1_over_3_exact=f"{zeta_M_at_1_over_3.numerator}/{zeta_M_at_1_over_3.denominator}",
        C_rel_exact=f"{C_rel.numerator}/{C_rel.denominator}",
        C_rel_decimal=mp.nstr(frac_to_mp(C_rel), 24),
        logM_rel_decimal=mp.nstr(logM_rel, 28),
        M_rel_decimal=mp.nstr(mp.e**logM_rel, 28),
        logM_tail_bound=mp.nstr(tail_bd, 6),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[relative-zeta] wrote {jout}", flush=True)

    # Write TeX snippet
    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    q10 = ", ".join(str(x) for x in prim_q[:10])
    pM10 = ", ".join(str(x) for x in prim_M[:10])
    r10 = ", ".join(str(x) for x in traces_r[:10])

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_relative_zeta_sync_vs_real_input.py")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (p_n(M))_{n=1}^{10}=(" + pM10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (r_n)_{n=1}^{10}=(a_n(B)-a_n(M))_{n=1}^{10}=(" + r10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (q_n)_{n=1}^{10}=(p_n(B)-p_n(M))_{n=1}^{10}=(" + q10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("")
    lines.append("\\begin{equation*}")
    lines.append(
        "\\boxed{\\ C_{B/M}="
        + payload.C_rel_exact
        + "\\ \\approx\\ "
        + payload.C_rel_decimal
        + "\\ }"
    )
    lines.append("\\end{equation*}")
    lines.append("\\begin{equation*}")
    lines.append(
        "\\boxed{\\ \\log M_{B/M}\\approx "
        + payload.logM_rel_decimal
        + ",\\quad M_{B/M}\\approx "
        + payload.M_rel_decimal
        + "\\ }"
    )
    lines.append("\\end{equation*}")
    lines.append("")
    lines.append("\\noindent\\textbf{Audits.} ")
    lines.append(
        "\\(q_n\\) from Möbius on \\(r_n\\): "
        + ("OK" if payload.audit_q_from_r_ok else "FAIL")
        + ".\\quad "
        + "Sign audit on \\(q_n\\) up to n="
        + str(n_max)
        + ": "
        + ("OK" if payload.audit_q_sign_ok else "FAIL")
        + ".\\quad "
        + "\\(r_n\\) 10th-order recurrence: "
        + ("OK" if payload.audit_r_recurrence_ok else "FAIL")
        + ".\\quad "
        + "Tail bd (\\(\\log M_{B/M}\\), N="
        + str(mobius_N)
        + "): "
        + payload.logM_tail_bound
        + "."
    )
    lines.append("")

    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[relative-zeta] wrote {tout}", flush=True)

    if not payload.audit_q_from_r_ok:
        raise SystemExit("Audit failed: q_n != Mobius(r_n).")
    if not payload.audit_q_sign_ok:
        raise SystemExit("Audit failed: negative q_n not only at n=2.")
    if not payload.audit_r_recurrence_ok:
        raise SystemExit("Audit failed: r_n recurrence check failed.")


if __name__ == "__main__":
    main()

