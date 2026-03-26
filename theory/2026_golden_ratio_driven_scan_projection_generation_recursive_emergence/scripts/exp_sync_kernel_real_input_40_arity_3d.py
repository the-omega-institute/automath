#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute 3D Dirichlet–Mertens tensors for the real-input 40-state kernel.

Third axis can be chosen as:
- N_e mod m3  (output-bit count)
- N_2 mod m3  (collision/trigger count: 1_{d=2})

Outputs:
- artifacts/export/sync_kernel_real_input_40_arity_3d.json (default)
- sections/generated/tab_real_input_40_arity_dirichlet_mertens_333.tex (3x3x3 summary)
- sections/generated/tab_real_input_40_arity_dirichlet_mertens_555.tex (5x5x5 full tensor)
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir
from common_phi_fold import Progress

from common_paths import generated_dir

@dataclass(frozen=True)
class KernelEdge:
    src: str
    dst: str
    d: int
    e: int


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


def build_kernel_map(edges: List[KernelEdge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(edge.src, edge.d): (edge.dst, edge.e) for edge in edges}


def build_real_input_states() -> List[Tuple[str, int, int]]:
    states: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                states.append((s, px, py))
    return states


def parse_triple_values(text: str) -> List[Tuple[int, int, int]]:
    raw = [chunk.strip() for chunk in text.split(",")] if text else []
    triples: List[Tuple[int, int, int]] = []
    for chunk in raw:
        if not chunk:
            continue
        parts = [p.strip() for p in chunk.split("x")]
        if len(parts) != 3:
            raise SystemExit(f"[arity-3d] invalid triple (use axbxc): {chunk}")
        try:
            m1, m2, m3 = (int(parts[0]), int(parts[1]), int(parts[2]))
        except ValueError as exc:
            raise SystemExit(f"[arity-3d] invalid triple value: {chunk}") from exc
        if m1 < 2 or m2 < 2 or m3 < 2:
            raise SystemExit(f"[arity-3d] triple entries must be >=2, got {chunk}")
        triples.append((m1, m2, m3))
    if not triples:
        triples = [(3, 3, 3)]
    seen = set()
    out: List[Tuple[int, int, int]] = []
    for t in triples:
        if t in seen:
            continue
        seen.add(t)
        out.append(t)
    return out


def build_weighted_matrix_numeric(
    q: complex,
    r: complex,
    u: complex,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    *,
    third_axis: str,
) -> np.ndarray:
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    M = np.zeros((n, n), dtype=complex)
    for s, px, py in states:
        _src_neg = 1 if "-" in s else 0
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, e = kernel_map[(s, d)]
                chi = e - (1 if d == 2 else 0)
                # Negative-carry event: entering the negative-carry zone Q_- (state after the step).
                nu = 1 if "-" in dst_state else 0
                if third_axis == "Ne":
                    w3 = int(e)
                elif third_axis == "N2":
                    w3 = 1 if d == 2 else 0
                else:
                    raise ValueError(f"invalid third_axis: {third_axis}")
                i = idx[(s, px, py)]
                j = idx[(dst_state, x, y)]
                M[i, j] += (q**chi) * (r**nu) * (u**w3)
    return M


def _log_zeta_from_eigs(eigs: np.ndarray, z: float) -> complex:
    """Return log(zeta(z)) = -sum_j log(1 - z * lambda_j).

    We use eigenvalues directly to fix the analytic branch unambiguously for |z*lambda_j|<1,
    which holds for twisted characters at z=1/lambda (and higher powers z^k).
    """
    zz = z + 0.0j
    s = 0.0 + 0.0j
    for ev in eigs:
        s += cmath.log(1.0 - zz * ev)
    return -s


def _twist_constant_via_mobius_logzeta(
    *,
    q: complex,
    r: complex,
    u: complex,
    z: float,
    k_max: int,
    prog: Progress,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    label: str,
    third_axis: str,
) -> complex:
    """Compute C(q,r,u) = P(z) via P(z)=sum_{k>=1} mu(k)/k * log zeta(z^k).

    This converges rapidly for twisted characters where rho(M(q,r,u)) < 1/z.
    """
    M = build_weighted_matrix_numeric(q, r, u, states, kernel_map, third_axis=third_axis)
    eigs = np.linalg.eigvals(M)
    acc = 0.0 + 0.0j
    for k in range(1, k_max + 1):
        mu = mobius(k)
        if mu == 0:
            continue
        zk = z**k
        logz = _log_zeta_from_eigs(eigs, zk)
        acc += (float(mu) / float(k)) * logz
        if k % 50 == 0:
            prog.tick(f"{label} mobius-logzeta k={k}/{k_max}")
    return acc


def _twist_constant_decompose_k1_tail(
    *,
    q: complex,
    r: complex,
    u: complex,
    z: float,
    k_max: int,
    prog: Progress,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    label: str,
    third_axis: str,
) -> Tuple[complex, complex, complex]:
    """Return (C_total, C_k1, C_tail) where

    C_total := sum_{k>=1} mu(k)/k * log zeta(z^k)
    C_k1    := log zeta(z)  (the k=1 term)
    C_tail  := sum_{k>=2} mu(k)/k * log zeta(z^k)
    """
    M = build_weighted_matrix_numeric(q, r, u, states, kernel_map, third_axis=third_axis)
    eigs = np.linalg.eigvals(M)

    logz1 = _log_zeta_from_eigs(eigs, z)
    acc = 0.0 + 0.0j
    for k in range(2, k_max + 1):
        mu = mobius(k)
        if mu == 0:
            continue
        zk = z**k
        logz = _log_zeta_from_eigs(eigs, zk)
        acc += (float(mu) / float(k)) * logz
        if k % 50 == 0:
            prog.tick(f"{label} tail k={k}/{k_max}")
    return logz1 + acc, logz1, acc


def spectral_radius(B: np.ndarray) -> float:
    vals = np.linalg.eigvals(B)
    return float(np.max(np.abs(vals)))


def mobius(n: int) -> int:
    if n == 1:
        return 1
    mu = 1
    p = 2
    nn = n
    while p * p <= nn:
        if nn % p == 0:
            nn //= p
            if nn % p == 0:
                return 0
            mu = -mu
        p += 1
    if nn > 1:
        mu = -mu
    return mu


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

def _write_dirichlet_mertens_tensor_tex(
    *,
    m1: int,
    m2: int,
    m3: int,
    class_constants: Dict[str, float],
    rho_map: Dict[str, float],
    lam: float,
    mathsf_M: float,
    out_path: Path,
    third_axis: str,
    marginal_2d: Dict[str, float] | None = None,
) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)

    rho_max = max(rho_map.values()) if rho_map else 0.0
    rho_ratio = rho_max / lam if lam > 0 else 0.0
    if rho_map:
        mx = rho_max
        argmax = sorted([k for k, v in rho_map.items() if abs(v - mx) <= 1e-12])
    else:
        argmax = []

    def fmt(x: float) -> str:
        # Reviewer-friendly; keep fixed width sign.
        return f"{x:+.8f}".replace("+", "\\phantom{-}")

    def entry(a: int, b: int, c: int) -> str:
        return fmt(float(class_constants[f"{a},{b},{c}"]))

    # Marginalize over (b,c) to get chi mod m1 constants.
    marg: List[float] = []
    for a in range(m1):
        s = 0.0
        for b in range(m2):
            for c in range(m3):
                s += float(class_constants[f"{a},{b},{c}"])
        marg.append(s)

    total_sum = 0.0
    for a in range(m1):
        for b in range(m2):
            for c in range(m3):
                total_sum += float(class_constants[f"{a},{b},{c}"])

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_3d.py")
    axis_tex = "N_e" if third_axis == "Ne" else "N_2"
    lines.append(f"% ({m1},{m2},{m3}) Dirichlet--Mertens constants tensor for (chi mod {m1}, N_- mod {m2}, {axis_tex} mod {m3}).")
    lines.append(
        f"\\paragraph{{$(({m1},{m2},{m3}))$：Dirichlet--Mertens 常数张量（可复现输出）}}"
    )
    if m1 == 3 and m2 == 3 and m3 == 5:
        # Special presentation to "break permutation equivalence":
        # slice by c = N_e mod 5, and show each slice as a 3x3 (b rows, a cols).
        c_label = "N_e(\\gamma)\\bmod 5" if third_axis == "Ne" else "N_2(\\gamma)\\bmod 5"
        lines.append(
            f"按 $c={c_label}$ 分 5 张 $3\\times 3$ 切片（行 $b=N_-(\\gamma)\\bmod 3$，列 $a=\\chi(\\gamma)\\bmod 3$），常数项为："
        )
        for c in range(5):
            lines.append("$$")
            lines.append(f"c={c}:\\quad")
            lines.append("\\begin{pmatrix}")
            for b in range(3):
                row = " & ".join(entry(a, b, c) for a in range(3))
                if b < 2:
                    lines.append(f"{row}\\\\")
                else:
                    lines.append(f"{row}")
            lines.append("\\end{pmatrix}")
            lines.append("$$")
    else:
        lines.append(
            f"按 $a=\\chi(\\gamma)\\bmod {m1}$ 分 {m1} 张 ${m2}\\times {m3}$ 切片（行 $b=N_-(\\gamma)\\bmod {m2}$，列 $c={axis_tex}(\\gamma)\\bmod {m3}$），常数项为："
        )
        for a in range(m1):
            lines.append("$$")
            lines.append(f"a={a}:\\quad")
            lines.append("\\begin{pmatrix}")
            for b in range(m2):
                row = " & ".join(entry(a, b, c) for c in range(m3))
                if b < m2 - 1:
                    lines.append(f"{row}\\\\")
                else:
                    lines.append(f"{row}")
            lines.append("\\end{pmatrix}")
            lines.append("$$")

    lines.append("\\paragraph{指数级误差：最坏扭曲谱半径比（可复现输出）}")
    lines.append("数值上")
    lines.append("$$")
    lines.append(
        f"\\rho_{{{m1},{m2},{m3}}}\\approx {rho_max:.12f},\\qquad \\frac{{\\rho_{{{m1},{m2},{m3}}}}}{{\\lambda}}\\approx {rho_ratio:.12f}."
    )
    lines.append("$$")
    if argmax:
        joined = ",\\ ".join([f"({t})" for t in argmax])
        lines.append("达到最坏谱半径的非平凡角色索引（$j=(j_1,j_2,j_3)$）为：")
        lines.append("$$")
        lines.append(joined)
        lines.append("$$")

    lines.append(
        f"\\paragraph{{一维边际：只看 $\\chi\\bmod {m1}$ 的 Dirichlet--Mertens 常数}}"
    )
    lines.append(
        f"对 $b,c$ 求和得到 $C_a^{{({m1})}}:=\\sum_{{b,c}} C^{{({m1},{m2},{m3})}}_{{a,b,c}}$："
    )
    lines.append("$$")
    vec = ",".join([f"{x:+.8f}" for x in marg])
    lines.append(f"\\bigl({vec}\\bigr).")
    lines.append("$$")

    lines.append("\\paragraph{总和校验（可复现输出）}")
    lines.append("按定义应满足 $\\sum_{a,b,c}C^{(m_1,m_2,m_3)}_{a,b,c}=\\mathsf{M}$；数值上")
    lines.append("$$")
    lines.append(f"\\left|\\sum_{{a,b,c}} C^{{({m1},{m2},{m3})}}_{{a,b,c}}-\\mathsf{{M}}\\right|\\approx {abs(total_sum - mathsf_M):.3e}.")
    lines.append("$$")

    if marginal_2d is not None and m1 == 3 and m2 == 3 and m3 == 5:
        # Optional audit: compare 2D constants (computed independently) with the 3D marginal sum over c.
        max_abs = 0.0
        for a in range(3):
            for b in range(3):
                s3 = sum(float(class_constants[f"{a},{b},{c}"]) for c in range(5))
                s2 = float(marginal_2d[f"{a},{b}"])
                max_abs = max(max_abs, abs(s3 - s2))
        lines.append("\\paragraph{边际一致性校验（可复现输出）}")
        lines.append("对 $c$ 求和得到的二维边际应与独立计算的 $(3,3)$ 常数一致；数值上")
        lines.append("$$")
        lines.append(f"\\max_{{a,b}}\\left|\\sum_{{c=0}}^4 C^{{(3,3,5)}}_{{a,b,c}}-C^{{(3,3)}}_{{a,b}}\\right|\\approx {max_abs:.3e}.")
        lines.append("$$")

    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_dirichlet_mertens_335_n2_summary_tex(
    *,
    class_constants: Dict[str, float],
    rho_map: Dict[str, float],
    lam: float,
    out_path: Path,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> None:
    """Write derived consequences for the (3,3,5) tensor with third axis N2 mod 5.

    This file is meant to be \\input into the paper, and everything in it is computed
    from the reported 5 slices and the worst twisted spectral radius ratio.
    """
    out_path.parent.mkdir(parents=True, exist_ok=True)

    # Helper: access C_{a,b,c} with a=chi mod 3, b=N_- mod 3, c=N2 mod 5.
    def C(a: int, b: int, c: int) -> float:
        return float(class_constants[f"{a},{b},{c}"])

    # Worst ratio and argmax characters.
    rho_max = max(rho_map.values()) if rho_map else 0.0
    rho_ratio = rho_max / lam if lam > 0 else 0.0
    argmax: List[str] = []
    if rho_map:
        mx = rho_max
        argmax = sorted([k for k, v in rho_map.items() if abs(v - mx) <= 1e-12])

    # Slice sums S_c = sum_{a,b} C_{a,b,c}.
    S_c: List[float] = []
    for c in range(5):
        s = 0.0
        for a in range(3):
            for b in range(3):
                s += C(a, b, c)
        S_c.append(s)

    # Slice means over (a,b): \bar C_c = (1/9) sum_{a,b} C_{a,b,c}.
    mean_c: List[float] = []
    for c in range(5):
        mean_c.append(S_c[c] / 9.0)

    # Total variation energy across c (per-cell variance along c).
    # Define var_{a,b} := (1/5) sum_c (C_{a,b,c} - mean_{a,b})^2.
    var_ab = np.zeros((3, 3), dtype=float)  # rows b, cols a
    for a in range(3):
        for b in range(3):
            vals = [C(a, b, c) for c in range(5)]
            mu = sum(vals) / 5.0
            var_ab[b, a] = sum((x - mu) ** 2 for x in vals) / 5.0
    var_total = float(np.sum(var_ab))
    frac_row_b0 = float(np.sum(var_ab[0, :]) / var_total) if var_total > 0 else 0.0
    frac_col_a1 = float(np.sum(var_ab[:, 1]) / var_total) if var_total > 0 else 0.0
    frac_cell_a1b0 = float(var_ab[0, 1] / var_total) if var_total > 0 else 0.0

    # Within-slice standard deviation across (a,b) for each c.
    sd_c: List[float] = []
    for c in range(5):
        vals = [C(a, b, c) for b in range(3) for a in range(3)]
        mu = sum(vals) / 9.0
        var = sum((x - mu) ** 2 for x in vals) / 9.0
        sd_c.append(var**0.5)

    # Frobenius deviation from rank-0 (all-ones) slice:
    #   Delta_c = || C_{..c} - mean_c * 11^T ||_F
    # and max absolute entry deviation.
    delta_c: List[float] = []
    max_dev_c: List[float] = []
    for c in range(5):
        mu = mean_c[c]
        sq = 0.0
        md = 0.0
        for a in range(3):
            for b in range(3):
                d = C(a, b, c) - mu
                sq += d * d
                md = max(md, abs(d))
        delta_c.append(sq**0.5)
        max_dev_c.append(md)

    # Discrete Fourier coefficients along c for each (a,b).
    # For f(c) on Z/5: f(c) = sum_{j=0}^4 \hat f(j) * omega^{jc}, with
    # \hat f(j) = (1/5) sum_c f(c) omega^{-jc}.
    omega = cmath.exp(2j * math.pi / 5.0)
    mean = np.zeros((3, 3), dtype=float)
    A1 = np.zeros((3, 3), dtype=complex)
    A2 = np.zeros((3, 3), dtype=complex)
    for a in range(3):
        for b in range(3):
            f = [C(a, b, c) for c in range(5)]
            mean[b, a] = sum(f) / 5.0
            h1 = 0.0 + 0.0j
            h2 = 0.0 + 0.0j
            for c in range(5):
                h1 += f[c] * (omega ** (-1 * c))
                h2 += f[c] * (omega ** (-2 * c))
            A1[b, a] = h1 / 5.0
            A2[b, a] = h2 / 5.0

    max_abs_A1 = float(np.max(np.abs(A1)))
    max_abs_A2 = float(np.max(np.abs(A2)))
    ratio_A2_A1 = (max_abs_A2 / max_abs_A1) if max_abs_A1 > 0 else 0.0

    # Extra certificates derived from the exact two-harmonic representation.
    #
    # (a) Resonance-cell near extremality for the sharp Fourier-norm bound.
    # For each fixed (a,b), define the oscillatory lift:
    #   Delta_{b,a}(c) := f_{a,b}(c) - \hat f_{a,b}(0).
    # Then |Delta_{b,a}(c)| <= 2(|A1_{b,a}| + |A2_{b,a}|) for all (b,a,c),
    # hence also <= 2(max|A1| + max|A2|).
    delta_res = float(C(1, 0, 0) - mean[0, 1])  # resonance cell (a,b,c)=(1,0,0)
    bound_universal = 2.0 * (max_abs_A1 + max_abs_A2)
    ratio_extremal = (delta_res / bound_universal) if bound_universal > 0 else float("nan")
    # Verify that both harmonics attain their entrywise maxima at the same cell (b=0,a=1).
    iA1 = int(np.argmax(np.abs(A1)))
    iA2 = int(np.argmax(np.abs(A2)))
    locA1 = (int(iA1 // 3), int(iA1 % 3))  # (b,a)
    locA2 = (int(iA2 // 3), int(iA2 % 3))  # (b,a)
    phase_A1_res = float(cmath.phase(A1[0, 1]))
    phase_A2_res = float(cmath.phase(A2[0, 1]))
    phase_gap = float(abs(((phase_A2_res - phase_A1_res + math.pi) % (2.0 * math.pi)) - math.pi))

    # (b) 2D marginal matrix over c and the 1D marginal over b=N_- mod 3:
    #   sum_c C_{a,b,c} = 5 * mean[b,a],
    #   C^{(-)}_b := sum_{a,c} C_{a,b,c} = 5 * sum_a mean[b,a].
    marg_ab = 5.0 * mean
    marg_b = 5.0 * np.sum(mean, axis=1)

    # (c) Harmonic alignment certificate (Frobenius best collinearity): A2 ≈ eta* A1.
    def _frob_inner(X: np.ndarray, Y: np.ndarray) -> complex:
        return complex(np.vdot(X, Y))  # conj(X)*Y summed over entries

    denom_eta = _frob_inner(A1, A1)
    eta_star = (_frob_inner(A1, A2) / denom_eta) if denom_eta != 0 else complex("nan")
    eps_parallel = (
        float(np.linalg.norm(A2 - eta_star * A1) / np.linalg.norm(A2))
        if float(np.linalg.norm(A2)) > 0
        else float("nan")
    )
    # Harmonic energy ratio (new fingerprint):
    #   E1 := ||A^(1)||_F^2 / (||A^(1)||_F^2 + ||A^(2)||_F^2),
    # where A^(1), A^(2) are the j=1 and j=2 Fourier matrices on Z/5.
    eA1 = float(np.sum(np.abs(A1) ** 2))
    eA2 = float(np.sum(np.abs(A2) ** 2))
    E1 = (eA1 / (eA1 + eA2)) if (eA1 + eA2) > 0 else float("nan")

    # DFT of aggregated drift S_c on Z/5: \hat S(j) = (1/5) sum_c S_c omega^{-jc}.
    Shat = []
    for j in range(5):
        acc = 0.0 + 0.0j
        for c in range(5):
            acc += S_c[c] * (omega ** (-j * c))
        Shat.append(acc / 5.0)

    # Mixing-length proxies from rho_ratio.
    tau_mix = (1.0 / (-math.log(rho_ratio))) if (0.0 < rho_ratio < 1.0) else float("inf")
    t_half = (math.log(2.0) / (-math.log(rho_ratio))) if (0.0 < rho_ratio < 1.0) else float("inf")
    susceptibility = (1.0 / (1.0 - rho_ratio)) if (0.0 < rho_ratio < 1.0) else float("inf")
    log_susceptibility = math.log(susceptibility) if (susceptibility > 0 and math.isfinite(susceptibility)) else float("nan")

    # Low-rank compressibility diagnostic: SVD of the (5 x 9) matrix with rows indexed by c,
    # and columns indexed by flattened (a,b). We report both the raw tensor and the
    # c-centered tensor (subtract per-column mean across c).
    T = np.zeros((5, 9), dtype=float)
    for c in range(5):
        k = 0
        for b in range(3):
            for a in range(3):
                T[c, k] = C(a, b, c)
                k += 1
    # Raw SVD.
    _U, svals_raw, _Vt = np.linalg.svd(T, full_matrices=False)
    e_raw = (svals_raw**2).astype(float)
    e_raw_sum = float(np.sum(e_raw))
    e_raw_cum = (np.cumsum(e_raw) / e_raw_sum) if e_raw_sum > 0 else np.zeros_like(e_raw)
    # Center along c (per-column mean).
    T_center = T - np.mean(T, axis=0, keepdims=True)
    _Uc, svals_ctr, _Vtc = np.linalg.svd(T_center, full_matrices=False)
    e_ctr = (svals_ctr**2).astype(float)
    e_ctr_sum = float(np.sum(e_ctr))
    e_ctr_cum = (np.cumsum(e_ctr) / e_ctr_sum) if e_ctr_sum > 0 else np.zeros_like(e_ctr)
    s2_over_s1 = float(svals_ctr[1] / svals_ctr[0]) if (len(svals_ctr) >= 2 and svals_ctr[0] > 0) else float("nan")

    # Near-coboundary quadratic law (heuristic prediction) for modulus p.
    kappa_est = float("nan")
    pred_p: Dict[int, float] = {}
    if 0.0 < rho_ratio < 1.0:
        kappa_est = (1.0 - rho_ratio) / ((2.0 * math.pi / 5.0) ** 2)
        for p in (7, 11, 13):
            pred = 1.0 - kappa_est * ((2.0 * math.pi / float(p)) ** 2)
            pred_p[p] = float(pred)

    # Variance-density identification (spectral/pressure method).
    # For the collision cocycle xi = 1_{d=2} and real tilt u = exp(t),
    # define lambda(t)=rho(M(q=r=1,u=exp(t))) and P(t)=log lambda(t).
    # Then sigma_xi^2 = P''(0), and the small-angle twist gap satisfies
    #   1 - rho_p/lambda ~ (sigma_xi^2/2) * (2pi/p)^2.
    def _lambda_of_t(t: float) -> float:
        u_real = math.exp(t)
        M_t = build_weighted_matrix_numeric(
            1.0 + 0.0j,
            1.0 + 0.0j,
            u_real + 0.0j,
            states,
            kernel_map,
            third_axis="N2",
        )
        return spectral_radius(M_t)

    # Use a stable symmetric second-difference (avoid too small h due to eig rounding).
    h_var = 1e-3
    lam0 = _lambda_of_t(0.0)
    P0 = math.log(lam0)
    Pp = math.log(_lambda_of_t(h_var))
    Pm = math.log(_lambda_of_t(-h_var))
    sigma2_xi = (Pp - 2.0 * P0 + Pm) / (h_var * h_var)
    kappa_var = 0.5 * sigma2_xi
    g_infty = (4.0 * (math.pi**2)) * kappa_var

    # "Best 5-coloring" (near-coboundary certificate): find h:V->Z/5 that maximizes satisfied edges
    # for constraints h(v)-h(u) == xi(u->v) mod 5, where xi = 1_{d=2}.
    idx_state = {st: i for i, st in enumerate(states)}
    nV = len(states)
    out_edges: List[List[Tuple[int, int]]] = [[] for _ in range(nV)]  # (to, w)
    in_edges: List[List[Tuple[int, int]]] = [[] for _ in range(nV)]  # (from, w)
    edges_flat: List[Tuple[int, int, int]] = []
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, _e = kernel_map[(s, d)]
                w = 1 if d == 2 else 0
                u_idx = idx_state[(s, px, py)]
                v_idx = idx_state[(dst_state, x, y)]
                out_edges[u_idx].append((v_idx, w))
                in_edges[v_idx].append((u_idx, w))
                edges_flat.append((u_idx, v_idx, w))
    mE = len(edges_flat)

    def _score(h: List[int]) -> int:
        sat = 0
        for uu, vv, ww in edges_flat:
            if (h[vv] - h[uu]) % 5 == ww:
                sat += 1
        return sat

    def _improve(h: List[int], *, max_iter: int = 200) -> List[int]:
        for _ in range(max_iter):
            changed = 0
            for v in range(nV):
                best_l = h[v]
                best_sat_local = -1
                for l in range(5):
                    sat_local = 0
                    for to, w in out_edges[v]:
                        if (h[to] - l) % 5 == w:
                            sat_local += 1
                    for fr, w in in_edges[v]:
                        if (l - h[fr]) % 5 == w:
                            sat_local += 1
                    if sat_local > best_sat_local:
                        best_sat_local = sat_local
                        best_l = l
                if best_l != h[v]:
                    h[v] = best_l
                    changed += 1
            if changed == 0:
                break
        return h

    rng = np.random.default_rng(20260203)
    best_sat = -1
    best_h: List[int] = [0 for _ in range(nV)]
    for _ in range(200):
        h0 = [int(x) for x in rng.integers(0, 5, size=nV)]
        h1 = _improve(h0)
        sat = _score(h1)
        if sat > best_sat:
            best_sat = sat
            best_h = h1[:]
    eps_best = float("nan") if mE == 0 else float(1.0 - (best_sat / float(mE)))

    # Stationary-weighted defect (rigorous energy-style certificate):
    # compute the PF equilibrium edge measure for the untwisted adjacency (q=r=u=1),
    # then evaluate residual r(e) in the integer lift [-2,2] and report:
    #   eps_pi  := P_pi[e is violated],
    #   eps2_pi := E_pi[r(e)^2],
    # which yields the bound kappa <= eps2_pi/2 (for the variance-based kappa).
    eps_pi = float("nan")
    eps2_pi = float("nan")
    kappa_bound = float("nan")
    if mE > 0:
        M1 = build_weighted_matrix_numeric(
            1.0 + 0.0j,
            1.0 + 0.0j,
            1.0 + 0.0j,
            states,
            kernel_map,
            third_axis="N2",
        )
        A = np.real(M1).astype(float)
        vals, vecs = np.linalg.eig(A)
        i0 = int(np.argmax(np.real(vals)))
        lam_pf = float(np.real(vals[i0]))
        r_vec = np.real(vecs[:, i0]).astype(float)
        valsL, vecsL = np.linalg.eig(A.T)
        j0 = int(np.argmax(np.real(valsL)))
        l_vec = np.real(vecsL[:, j0]).astype(float)
        if float(np.sum(r_vec)) < 0:
            r_vec = -r_vec
        if float(np.sum(l_vec)) < 0:
            l_vec = -l_vec
        lr = float(l_vec @ r_vec)
        if lr != 0.0:
            l_vec = l_vec / lr  # normalize so that l^T r = 1

        lift = {0: 0, 1: 1, 2: 2, 3: -2, 4: -1}
        bad_mass = 0.0
        r2_mass = 0.0
        for uu, vv, ww in edges_flat:
            p_edge = float(l_vec[uu] * r_vec[vv] / lam_pf)
            diff = (best_h[vv] - best_h[uu] - ww) % 5
            res = int(lift[int(diff)])
            if res != 0:
                bad_mass += p_edge
            r2_mass += p_edge * float(res * res)
        eps_pi = float(bad_mass)
        eps2_pi = float(r2_mass)
        kappa_bound = 0.5 * eps2_pi

    # Cancellation fingerprint: sign imbalance and residual after cancellation.
    all_entries: List[float] = []
    for c in range(5):
        for b in range(3):
            for a in range(3):
                all_entries.append(C(a, b, c))
    sum_pos = float(sum(x for x in all_entries if x > 0))
    sum_neg = float(sum(x for x in all_entries if x < 0))
    cnt_pos = int(sum(1 for x in all_entries if x > 0))
    cnt_neg = int(sum(1 for x in all_entries if x < 0))
    total_sum = float(sum(all_entries))
    kappa_cancel = (sum_pos / total_sum) if abs(total_sum) > 0 else float("nan")

    def fmt(x: float) -> str:
        return f"{x:.12f}"

    def fmt_sd(x: float) -> str:
        return f"{x:.6g}"

    def fmt_complex(z: complex) -> str:
        # LaTeX-friendly complex: a + b\,\mathrm{i}.
        re = f"{z.real:+.8f}".replace("+", "\\phantom{-}")
        sgn = "+" if z.imag >= 0 else "-"
        im = f"{abs(z.imag):.8f}"
        return f"{re}{sgn}{im}\\,\\mathrm{{i}}"

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_3d.py")
    lines.append("% Derived consequences for the (3,3,5) tensor with third axis N2 mod 5.")
    lines.append("\\paragraph{从 $((3,3,5))$ 输出推导出的二级结论（可复现）}")
    lines.append("下述量全部由上表的 5 张 $3\\times 3$ 切片与最坏扭曲谱半径比直接计算得到。")

    lines.append("\\paragraph{慢模完全由碰撞 cocycle 主导}")
    lines.append("最坏谱半径比与达到最坏的角色索引为：")
    lines.append("$$")
    lines.append(f"\\frac{{\\rho_{{3,3,5}}}}{{\\lambda}}\\approx {fmt(rho_ratio)}.")
    lines.append("$$")
    if 0.0 < rho_ratio < 1.0:
        lines.append("并定义谱缺口（缺口越小，混合越慢）")
        lines.append("$$")
        lines.append(f"\\delta_{{\\mathrm{{spec}}}}:=1-\\frac{{\\rho_{{3,3,5}}}}{{\\lambda}}\\approx {fmt(1.0 - rho_ratio)}.")
        lines.append("$$")
    if argmax:
        joined = ",\\ ".join([f"({t})" for t in argmax])
        lines.append("$$")
        lines.append(joined)
        lines.append("$$")
    lines.append("由此定义主相关长度尺度（指数衰减的时间常数）与半衰期：")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append(
        f"\\tau_{{\\mathrm{{mix}}}}:=\\frac{{1}}{{-\\log(\\rho_{{3,3,5}}/\\lambda)}}&\\approx {fmt(tau_mix)},\\\\"
    )
    lines.append(
        f"t_{{1/2}}:=\\frac{{\\log 2}}{{-\\log(\\rho_{{3,3,5}}/\\lambda)}}&\\approx {fmt(t_half)}."
    )
    lines.append("\\end{aligned}")
    lines.append("$$")
    lines.append("并定义偏置易感度（Abel 累积的自然尺度）")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append(f"\\chi:=\\frac{{1}}{{1-\\rho_{{3,3,5}}/\\lambda}}&\\approx {fmt(susceptibility)},\\\\")
    lines.append(f"\\log\\chi&\\approx {fmt(log_susceptibility)}.")
    lines.append("\\end{aligned}")
    lines.append("$$")

    lines.append("\\paragraph{碰撞同余类 $c$ 的常数漂移（总偏置）}")
    lines.append("定义 $S_c:=\\sum_{a=0}^2\\sum_{b=0}^2 C^{(3,3,5)}_{a,b,c}$。数值上")
    lines.append("$$")
    vec = ",".join([f"{x:+.6f}" for x in S_c])
    lines.append(f"(S_0,S_1,S_2,S_3,S_4)\\approx({vec}).")
    lines.append("$$")

    lines.append("\\paragraph{三维耦合在 $c$ 轴上的局部化（切片方差）}")
    lines.append("定义每张切片在 $3\\times 3$ 网格上的标准差（按 $9$ 个条目平均）：")
    lines.append("$$")
    vec_sd = ",".join([fmt_sd(x) for x in sd_c])
    lines.append(f"\\bigl(\\mathrm{{sd}}(c=0),\\dots,\\mathrm{{sd}}(c=4)\\bigr)\\approx\\bigl({vec_sd}\\bigr).")
    lines.append("$$")

    lines.append("\\paragraph{$c$-方向变分能量的局域共振（胞元/行/列贡献）}")
    lines.append("对每个胞元 $(a,b)$ 定义 $c$-方向方差能量 $\\mathrm{var}_{a,b}:=\\frac15\\sum_{c=0}^4\\bigl(C_{a,b,c}-\\frac15\\sum_{c'}C_{a,b,c'}\\bigr)^2$，并令总能量 $\\mathrm{Var}:=\\sum_{a,b}\\mathrm{var}_{a,b}$。数值上")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append(f"\\frac{{\\sum_a\\mathrm{{var}}_{{a,0}}}}{{\\mathrm{{Var}}}}&\\approx {frac_row_b0:.6f},\\\\")
    lines.append(f"\\frac{{\\sum_b\\mathrm{{var}}_{{1,b}}}}{{\\mathrm{{Var}}}}&\\approx {frac_col_a1:.6f},\\\\")
    lines.append(f"\\frac{{\\mathrm{{var}}_{{1,0}}}}{{\\mathrm{{Var}}}}&\\approx {frac_cell_a1b0:.6f}.")
    lines.append("\\end{aligned}")
    lines.append("$$")

    lines.append("\\paragraph{近因子化诊断：切片到 rank-0 的偏离}")
    lines.append("定义切片均值 $\\overline C_c:=\\frac19\\sum_{a,b}C_{a,b,c}$，并以 Frobenius 范数度量偏离")
    lines.append("$$")
    lines.append("\\Delta_c:=\\left\\|\\bigl(C_{a,b,c}\\bigr)_{a,b}-\\overline C_c\\,\\mathbf{1}\\mathbf{1}^\\top\\right\\|_F,\\qquad")
    lines.append("\\max\\mathrm{dev}(c):=\\max_{a,b}\\left|C_{a,b,c}-\\overline C_c\\right|.")
    lines.append("$$")
    lines.append("数值上")
    lines.append("$$")
    vec_d = ",".join([fmt_sd(x) for x in delta_c])
    lines.append(f"(\\Delta_0,\\Delta_1,\\Delta_2,\\Delta_3,\\Delta_4)\\approx({vec_d}).")
    lines.append("$$")
    lines.append("并且")
    lines.append("$$")
    vec_md = ",".join([f"{x:.6g}" for x in max_dev_c])
    lines.append(f"(\\max\\mathrm{{dev}}(0),\\dots,\\max\\mathrm{{dev}}(4))\\approx({vec_md}).")
    lines.append("$$")
    # Tail scalarization index:
    #   eta_tail := max_{c in {2,3,4}} ||slice_c - mean_c 11^T||_F / |mean_c|.
    eta_tail = 0.0
    for c in (2, 3, 4):
        denom = abs(mean_c[c])
        if denom > 0:
            eta_tail = max(eta_tail, float(delta_c[c]) / denom)
    lines.append("并定义尾部近标量化指纹")
    lines.append("$$")
    lines.append(
        "\\eta_{\\mathrm{tail}}:=\\max_{c\\in\\{2,3,4\\}}\\frac{\\left\\|\\bigl(C_{a,b,c}\\bigr)_{a,b}-\\overline C_c\\,\\mathbf{1}\\mathbf{1}^\\top\\right\\|_F}{|\\overline C_c|}"
        f"\\approx {eta_tail:.6f}."
    )
    lines.append("$$")

    lines.append("\\paragraph{三相正常形：每张切片的均值漂移与最大偏差}")
    lines.append("记 $\\overline C_c:=\\frac19\\sum_{a,b}C_{a,b,c}$，以及 $\\Delta_c:=\\max_{a,b}|C_{a,b,c}-\\overline C_c|$。数值上")
    lines.append("$$")
    vec_mean = ",".join([f"{x:+.6f}" for x in mean_c])
    lines.append(f"(\\overline C_0,\\overline C_1,\\overline C_2,\\overline C_3,\\overline C_4)\\approx({vec_mean}).")
    lines.append("$$")
    lines.append("并且")
    lines.append("$$")
    vec_D = ",".join([f"{x:.6g}" for x in max_dev_c])
    lines.append(f"(\\Delta_0,\\Delta_1,\\Delta_2,\\Delta_3,\\Delta_4)\\approx({vec_D}).")
    lines.append("$$")

    lines.append("\\paragraph{$S_c$ 的 $\\ZZ/5$-傅里叶结构（聚合漂移）}")
    lines.append("令 $\\widehat S(j):=\\frac15\\sum_{c=0}^{4}S_c\\,\\omega_5^{-jc}$。则")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append(f"\\widehat S(0)&\\approx {Shat[0].real:.12f},\\\\")
    lines.append(f"|\\widehat S(1)|=|\\widehat S(4)|&\\approx {abs(Shat[1]):.12f},\\\\")
    lines.append(f"|\\widehat S(2)|=|\\widehat S(3)|&\\approx {abs(Shat[2]):.12f}.")
    lines.append("\\end{aligned}")
    lines.append("$$")

    lines.append("\\paragraph{$\\mathbb{{Z}}/5$ 轴的傅里叶压缩指纹（均值 + 两个复模）}")
    lines.append("对每个固定的 $(a,b)$，令 $f_{a,b}(c):=C^{(3,3,5)}_{a,b,c}$（$c\\in\\ZZ/5$）。其离散傅里叶系数为")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append("\\widehat f_{a,b}(j)&:=\\frac15\\sum_{c=0}^{4} f_{a,b}(c)\\,\\omega_5^{-jc},\\\\")
    lines.append("\\omega_5&:=e^{2\\pi i/5}.")
    lines.append("\\end{aligned}")
    lines.append("$$")
    lines.append("从而有恒等分解（对所有 $c$ 精确成立）")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append("f_{a,b}(c)=\\widehat f_{a,b}(0)")
    lines.append("&+2\\Re\\bigl(\\widehat f_{a,b}(1)\\,\\omega_5^{c}\\bigr)\\\\")
    lines.append("&+2\\Re\\bigl(\\widehat f_{a,b}(2)\\,\\omega_5^{2c}\\bigr).")
    lines.append("\\end{aligned}")
    lines.append("$$")
    lines.append("记 $\\overline C_{b,a}:=\\widehat f_{a,b}(0)$（行 $b$、列 $a$）与两张复矩阵 $A^{(1)}_{b,a}:=\\widehat f_{a,b}(1)$、$A^{(2)}_{b,a}:=\\widehat f_{a,b}(2)$。则：")
    lines.append("$$")
    lines.append("\\overline C=")
    lines.append("\\begin{pmatrix}")
    for b in range(3):
        row = " & ".join(f"{mean[b, a]:+.8f}".replace("+", "\\phantom{-}") for a in range(3))
        lines.append(row + ("\\\\" if b < 2 else ""))
    lines.append("\\end{pmatrix}")
    lines.append("$$")
    lines.append("并且两条谐波复矩阵为")
    lines.append("$$")
    lines.append("A^{(1)}=")
    lines.append("\\begin{pmatrix}")
    for b in range(3):
        row = " & ".join(fmt_complex(A1[b, a]) for a in range(3))
        lines.append(row + ("\\\\" if b < 2 else ""))
    lines.append("\\end{pmatrix}")
    lines.append("$$")
    lines.append("$$")
    lines.append("A^{(2)}=")
    lines.append("\\begin{pmatrix}")
    for b in range(3):
        row = " & ".join(fmt_complex(A2[b, a]) for a in range(3))
        lines.append(row + ("\\\\" if b < 2 else ""))
    lines.append("\\end{pmatrix}")
    lines.append("$$")
    lines.append("并且（以条目绝对值的最大值度量）")
    lines.append("$$")
    lines.append(
        f"\\max_{{a,b}}|A^{{(1)}}_{{a,b}}|\\approx {fmt(max_abs_A1)},\\qquad"
        f"\\max_{{a,b}}|A^{{(2)}}_{{a,b}}|\\approx {fmt(max_abs_A2)},\\qquad"
        f"\\frac{{\\max|A^{{(2)}}|}}{{\\max|A^{{(1)}}|}}\\approx {fmt(ratio_A2_A1)}."
    )
    lines.append("$$")
    lines.append("其中 $A^{(1)}$ 与 $A^{(2)}$ 的具体条目可由同一脚本在 JSON 输出中复核。")

    lines.append("\\paragraph{二维边际矩阵与 $N_-\\bmod 3$ 的新边际向量（精确）}")
    lines.append(
        "由 $\\sum_{c=0}^4\\omega_5^c=0$，对每个 $(a,b)$ 有严格恒等式 "
        "$\\sum_{c=0}^{4}C^{(3,3,5)}_{a,b,c}=5\\,\\overline C_{b,a}$。因此二维边际矩阵（行 $b$、列 $a$）为"
    )
    lines.append("$$")
    lines.append("C^{(3,3)}=")
    lines.append("\\begin{pmatrix}")
    for b in range(3):
        row = " & ".join(f"{marg_ab[b, a]:+.8f}".replace("+", "\\phantom{-}") for a in range(3))
        lines.append(row + ("\\\\" if b < 2 else ""))
    lines.append("\\end{pmatrix}")
    lines.append("$$")
    lines.append("进一步对 $a,c$ 求和得到 $N_-\\bmod 3$ 的一维边际常数向量（按 $b=0,1,2$ 排列）")
    lines.append("$$")
    lines.append(
        (
            "\\bigl(C^{(-)}_0,C^{(-)}_1,C^{(-)}_2\\bigr)"
            f"\\approx\\bigl({marg_b[0]:+.8f},{marg_b[1]:+.8f},{marg_b[2]:+.8f}\\bigr)."
        ).replace("+", "\\phantom{-}")
    )
    lines.append("$$")

    lines.append("\\paragraph{共振胞元的傅里叶范数近极值：相位构造性对齐}")
    lines.append(
        "在共振胞元 $(a,b,c)=(1,0,0)$ 处，定义振荡抬升 "
        "$\\Delta_{b,a}(0):=C^{(3,3,5)}_{a,b,0}-\\overline C_{b,a}$。"
        "由两谐波恒等分解对任意 $(a,b,c)$ 有"
    )
    lines.append("$$")
    lines.append(
        "\\left|\\Delta_{b,a}(c)\\right|\\le 2\\bigl(|A^{(1)}_{b,a}|+|A^{(2)}_{b,a}|\\bigr)"
        "\\le 2\\bigl(\\|A^{(1)}\\|_\\infty+\\|A^{(2)}\\|_\\infty\\bigr)."
    )
    lines.append("$$")
    lines.append("而在该共振胞元处")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append(f"\\Delta_{{(b,a)=(0,1)}}(0)&\\approx {delta_res:.8f},\\\\")
    lines.append(
        f"2\\bigl(\\|A^{{(1)}}\\|_\\infty+\\|A^{{(2)}}\\|_\\infty\\bigr)&\\approx {bound_universal:.9f},\\\\"
    )
    lines.append(
        f"\\frac{{\\Delta_{{(0,1)}}(0)}}{{2(\\|A^{{(1)}}\\|_\\infty+\\|A^{{(2)}}\\|_\\infty)}}&\\approx {ratio_extremal:.9f}."
    )
    lines.append("\\end{aligned}")
    lines.append("$$")
    lines.append("并且两条谐波的条目最大值同在该胞元（以 $(b,a)$ 坐标计）：")
    lines.append("$$")
    lines.append(
        f"\\operatorname*{{argmax}}|A^{{(1)}}|=({locA1[0]},{locA1[1]}),\\qquad "
        f"\\operatorname*{{argmax}}|A^{{(2)}}|=({locA2[0]},{locA2[1]})."
    )
    lines.append("$$")
    lines.append("对应相位在 $c=0$ 处近同相，绝对相位差为")
    lines.append("$$")
    lines.append(f"\\bigl|\\arg A^{{(2)}}_{{0,1}}-\\arg A^{{(1)}}_{{0,1}}\\bigr|\\approx {phase_gap:.6f}\\ \\text{{(radian)}}.")
    lines.append("$$")

    lines.append("\\paragraph{两谐波矩阵的对齐证书：Frobenius 最佳共线残差}")
    lines.append("以 Frobenius 内积定义最佳共线系数")
    lines.append("$$")
    lines.append(
        "\\eta^\\star:=\\frac{\\langle A^{(2)},A^{(1)}\\rangle_F}{\\|A^{(1)}\\|_F^2},\\qquad "
        "\\varepsilon_{\\parallel}:=\\frac{\\|A^{(2)}-\\eta^\\star A^{(1)}\\|_F}{\\|A^{(2)}\\|_F}."
    )
    lines.append("$$")
    lines.append("数值上")
    lines.append("$$")
    sgn = "+" if eta_star.imag >= 0 else "-"
    lines.append(
        f"\\eta^\\star\\approx {eta_star.real:+.8f}{sgn}{abs(eta_star.imag):.8f}\\,\\mathrm{{i}},\\qquad "
        f"\\varepsilon_\\parallel\\approx {eps_parallel:.6f}."
    )
    lines.append("$$")
    lines.append(
        "该证书表明：尽管尾部切片在 $(a,b)$ 上接近 rank-$0$ 标量矩阵（见 $\\Delta_3,\\Delta_4$ 的量级），"
        "两条谐波矩阵在整体 Frobenius 意义下并不近共线；尾部近标量化更精确地表现为“均值矩阵的各向异性”与"
        "两谐波在特定相位处的抵消。"
    )

    lines.append("\\paragraph{整体低秩可压缩：$c$-中心化后的 rank-2 诊断（SVD）}")
    lines.append("把张量 $C^{(3,3,5)}_{a,b,c}$ 展平成 $T\\in\\RR^{5\\times 9}$（行索引 $c$，列索引为扁平化的 $(a,b)$），并做 $c$-方向中心化：对每一列减去其在 $c$ 上的均值。令中心化后的奇异值为 $s_1\\ge\\cdots\\ge s_5$，则（Frobenius 能量）累计占比为")
    lines.append("$$")
    if e_ctr_sum > 0:
        lines.append(
            f"\\frac{{s_1^2}}{{\\sum s_i^2}}\\approx {e_ctr_cum[0]:.6f},\\qquad "
            f"\\frac{{s_1^2+s_2^2}}{{\\sum s_i^2}}\\approx {e_ctr_cum[1]:.6f},\\qquad "
            f"\\frac{{s_1^2+s_2^2+s_3^2}}{{\\sum s_i^2}}\\approx {e_ctr_cum[2]:.6f},\\qquad "
            f"\\frac{{s_2}}{{s_1}}\\approx {s2_over_s1:.6f}."
        )
    else:
        lines.append("\\text{(no data)}")
    lines.append("$$")
    lines.append("（对比：未中心化的原始 $T$ 之累计能量占比为）")
    lines.append("$$")
    if e_raw_sum > 0:
        lines.append(
            f"\\frac{{(s_1^{{\\mathrm{{raw}}}})^2}}{{\\sum (s_i^{{\\mathrm{{raw}}}})^2}}\\approx {e_raw_cum[0]:.6f},\\qquad "
            f"\\frac{{(s_1^{{\\mathrm{{raw}}}})^2+(s_2^{{\\mathrm{{raw}}}})^2}}{{\\sum (s_i^{{\\mathrm{{raw}}}})^2}}\\approx {e_raw_cum[1]:.6f},\\qquad "
            f"\\frac{{(s_1^{{\\mathrm{{raw}}}})^2+(s_2^{{\\mathrm{{raw}}}})^2+(s_3^{{\\mathrm{{raw}}}})^2}}{{\\sum (s_i^{{\\mathrm{{raw}}}})^2}}\\approx {e_raw_cum[2]:.6f}."
        )
    else:
        lines.append("\\text{(no data)}")
    lines.append("$$")

    lines.append("\\paragraph{强抵消残差与稳健标量指纹}")
    lines.append("统计全部 $45$ 个条目，记 $M:=\\sum_{a,b,c}C_{a,b,c}$，以及正项/负项之和 $\\sum_{C>0}C$ 与 $\\sum_{C<0}C$。数值上")
    lines.append("$$")
    lines.append("\\begin{aligned}")
    lines.append(f"\\#\\{{C>0\\}}&={cnt_pos},\\\\")
    lines.append(f"\\#\\{{C<0\\}}&={cnt_neg},\\\\")
    lines.append(f"\\sum_{{C>0}}C&\\approx {sum_pos:.6f},\\\\")
    lines.append(f"\\sum_{{C<0}}C&\\approx {sum_neg:.6f},\\\\")
    lines.append(f"M&\\approx {total_sum:.12f}.")
    lines.append("\\end{aligned}")
    lines.append("$$")
    lines.append("并定义抵消指纹")
    lines.append("$$")
    lines.append(f"\\kappa_{{\\mathrm{{cancel}}}}:=\\frac{{\\sum_{{C>0}}C}}{{\\sum C}}\\approx {kappa_cancel:.6f}.")
    lines.append("$$")

    lines.append("\\paragraph{near-coboundary 小角二次律（可检验预测）}")
    lines.append("用 $p=5$ 的观测缺口 $1-\\rho_{3,3,5}/\\lambda$ 估计")
    lines.append("$$")
    if 0.0 < rho_ratio < 1.0:
        lines.append(
            f"\\kappa:=\\frac{{1-\\rho_{{3,3,5}}/\\lambda}}{{(2\\pi/5)^2}}\\approx {kappa_est:.6f},"
        )
    else:
        lines.append("\\kappa\\ \\text{undefined},")
    lines.append("$$")
    if 0.0 < rho_ratio < 1.0:
        theta5 = (2.0 * math.pi) / 5.0
        sigma2_hat_lin = 2.0 * (1.0 - rho_ratio) / (theta5 * theta5)
        sigma2_hat_log = (-2.0 * math.log(rho_ratio)) / (theta5 * theta5)
        lines.append("等价地（把 $p=5$ 的有限角扭曲视为小角近似的反推），可定义两种“反推方差密度”估计：")
        lines.append("$$")
        lines.append(
            f"\\widehat\\sigma_\\xi^2\\,\\text{{(lin)}}:=\\frac{{2(1-\\rho_{{3,3,5}}/\\lambda)}}{{(2\\pi/5)^2}}\\approx {sigma2_hat_lin:.12f},\\qquad "
            f"\\widehat\\sigma_\\xi^2\\,\\text{{(log)}}:=-\\frac{{2\\log(\\rho_{{3,3,5}}/\\lambda)}}{{(2\\pi/5)^2}}\\approx {sigma2_hat_log:.12f}."
        )
        lines.append("$$")
        lines.append("其中 log 版本来自二次律的指数形式 $\\rho(it)/\\lambda\\approx\\exp(-\\sigma_\\xi^2 t^2/2)$。")
    lines.append("并给出预测（待计算 $((3,3,p))$ 数据验证）：")
    lines.append("$$")
    if pred_p:
        parts = []
        for p in (7, 11, 13):
            if p in pred_p:
                parts.append(f"\\rho_{{3,3,{p}}}/\\lambda\\approx {pred_p[p]:.6f}")
        lines.append(",\\qquad ".join(parts) + ".")
    else:
        lines.append("\\text{(no prediction)}")
    lines.append("$$")

    lines.append("\\paragraph{方差密度识别：$\\kappa$ 的可证明本体（collision cocycle）}")
    lines.append("对碰撞 cocycle $\\xi=\\mathbf{1}_{\\{d=2\\}}$，考虑实参倾斜 $u=\\exp(t)$ 的压力 $P(t)=\\log\\rho(M(1,1,\\exp(t)))$。数值差分给出")
    lines.append("$$")
    lines.append(
        f"\\sigma_\\xi^2:=P''(0)\\approx {fmt(sigma2_xi)},\\qquad \\kappa_\\mathrm{{var}}:=\\sigma_\\xi^2/2\\approx {fmt(kappa_var)}."
    )
    lines.append("$$")
    lines.append("从而对应的选择律极限常数（见 $g(p)$ 的定义）为")
    lines.append("$$")
    lines.append(f"g_\\infty:=4\\pi^2\\,\\kappa_\\mathrm{{var}}=2\\pi^2\\sigma_\\xi^2\\approx {fmt(g_infty)}.")
    lines.append("$$")

    lines.append("\\paragraph{谐波能量指纹：第一谐波占比}")
    lines.append("令 $A^{(1)},A^{(2)}$ 为 $\\ZZ/5$ 上的 $j=1,2$ 两个谐波复矩阵（见下文输出）。定义能量占比")
    lines.append("$$")
    lines.append("\\mathcal{E}_1:=\\frac{\\|A^{(1)}\\|_F^2}{\\|A^{(1)}\\|_F^2+\\|A^{(2)}\\|_F^2}.")
    lines.append("$$")
    lines.append("数值上")
    lines.append("$$")
    lines.append(f"\\mathcal{{E}}_1\\approx {E1:.6f}.")
    lines.append("$$")
    if 0.0 < E1 < 1.0:
        R_harm = E1 / (1.0 - E1)
        lines.append("并可等价给出谐波强度比指纹")
        lines.append("$$")
        lines.append(f"R_\\mathrm{{harm}}:=\\frac{{\\|A^{{(1)}}\\|_F^2}}{{\\|A^{{(2)}}\\|_F^2}}=\\frac{{\\mathcal{{E}}_1}}{{1-\\mathcal{{E}}_1}}\\approx {R_harm:.6f}.")
        lines.append("$$")

    lines.append("\\paragraph{碰撞 cocycle 的 near-coboundary 证书：best $\\ZZ/5$-着色缺陷}")
    lines.append("把 40 状态图的每条边赋 cocycle $\\xi=\\mathbf{1}_{\\{d=2\\}}\\in\\ZZ/5$，并用局部改进的启发式在 $\\ZZ/5$ 上寻找 $h:V\\to\\ZZ/5$ 使得约束 $h(v)-h(u)\\equiv \\xi(u\\to v)\\ (\\mathrm{mod}\\ 5)$ 尽量多地满足。以边不一致比例定义缺陷")
    lines.append("$$")
    if mE > 0 and best_sat >= 0:
        lines.append(f"\\varepsilon:=1-\\frac{{\\#\\text{{(satisfied edges)}}}}{{|E|}}\\ \\lesssim\\ {eps_best:.6f}\\quad(\\text{{best found; }}|E|={mE}).")
    else:
        lines.append("\\varepsilon\\ \\text{undefined}.")
    lines.append("$$")

    lines.append("并进一步给出与平衡态一致的加权缺陷（用无扭曲 PF 平衡边测度加权）：")
    lines.append("$$")
    if not (math.isnan(eps_pi) or math.isnan(eps2_pi) or math.isnan(kappa_bound)):
        lines.append("\\begin{aligned}")
        lines.append(f"\\varepsilon_\\pi&:=\\mathbb{{P}}_\\pi[\\text{{violated}}]\\approx {fmt(eps_pi)},\\\\")
        lines.append(f"\\varepsilon_\\pi^{{(2)}}&:=\\mathbb{{E}}_\\pi[r(e)^2]\\approx {fmt(eps2_pi)},\\\\")
        lines.append(f"\\kappa_\\mathrm{{var}}&\\le\\ \\varepsilon_\\pi^{{(2)}}/2\\approx {fmt(kappa_bound)}.")
        lines.append("\\end{aligned}")
    else:
        lines.append("\\varepsilon_\\pi,\\ \\varepsilon_\\pi^{(2)}\\ \\text{undefined}.")
    lines.append("$$")

    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_dirichlet_mertens_335_n2_fourier_top_tex(
    *,
    class_constants: Dict[str, float],
    out_path: Path,
    top_k: int = 12,
) -> None:
    r"""Write top 3D DFT modes of the (3,3,5) constant tensor (third axis N2 mod 5).

    We use the normalized Fourier transform on G = Z/3 x Z/3 x Z/5:
      \hat C(j1,j2,j3) := (1/|G|) sum_{a,b,c} C_{a,b,c} * exp(-2πi(j1 a/3 + j2 b/3 + j3 c/5)).
    """
    out_path.parent.mkdir(parents=True, exist_ok=True)
    omega3 = cmath.exp(2j * math.pi / 3.0)
    omega5 = cmath.exp(2j * math.pi / 5.0)
    denom = 45.0

    def C(a: int, b: int, c: int) -> float:
        return float(class_constants[f"{a},{b},{c}"])

    def hat(j1: int, j2: int, j3: int) -> complex:
        acc = 0.0 + 0.0j
        for a in range(3):
            for b in range(3):
                for c in range(5):
                    phase = (omega3 ** (-j1 * a)) * (omega3 ** (-j2 * b)) * (omega5 ** (-j3 * c))
                    acc += C(a, b, c) * phase
        return acc / denom

    modes: List[Tuple[float, int, int, int, complex]] = []
    for j1 in range(3):
        for j2 in range(3):
            for j3 in range(5):
                if j1 == 0 and j2 == 0 and j3 == 0:
                    continue
                z = hat(j1, j2, j3)
                modes.append((abs(z), j1, j2, j3, z))
    modes.sort(key=lambda t: (-t[0], t[1], t[2], t[3]))
    modes = modes[: max(1, int(top_k))]

    def fmt_complex(z: complex) -> str:
        re = f"{z.real:+.8f}".replace("+", "\\phantom{-}")
        sgn = "+" if z.imag >= 0 else "-"
        im = f"{abs(z.imag):.8f}"
        return f"{re}{sgn}{im}\\,\\mathrm{{i}}"

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_sync_kernel_real_input_40_arity_3d.py")
    lines.append("% Top 3D DFT modes of C^{(3,3,5)} for third axis N2 mod 5.")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Three-dimensional DFT of the $((3,3,5))$ Dirichlet--Mertens constant tensor "
        "(third axis $N_2\\bmod 5$). We list the largest nontrivial Fourier modes "
        "$\\widehat C(j_1,j_2,j_3)$ on $\\ZZ/3\\times\\ZZ/3\\times\\ZZ/5$.}"
    )
    lines.append("\\label{tab:real_input_40_arity_335_n2_fourier_top}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$j_1$ & $j_2$ & $j_3$ & $\\widehat C(j)$ & $|\\widehat C(j)|$ & $45\\,\\widehat C(j)$\\\\")
    lines.append("\\midrule")
    for mag, j1, j2, j3, z in modes:
        lines.append(
            f"{j1} & {j2} & {j3} & ${fmt_complex(z)}$ & {mag:.8f} & ${fmt_complex(45.0 * z)}$\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="3D arity/negative/output Dirichlet–Mertens constants")
    parser.add_argument("--mertens-n", type=int, default=200, help="Max n for the untwisted Mertens constant estimate")
    parser.add_argument("--k-max", type=int, default=200, help="Max k for Möbius/log-zeta evaluation of twisted constants")
    parser.add_argument(
        "--third-axis",
        type=str,
        default="Ne",
        choices=["Ne", "N2"],
        help="Third axis choice: Ne (output-bit count) or N2 (collision count 1_{d=2})",
    )
    parser.add_argument(
        "--triple-values",
        type=str,
        default="2x2x2,3x2x2,3x3x3,3x3x5,5x5x5",
        help="Comma-separated m1xm2xm3 triples for Dirichlet–Mertens constants",
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON output")
    parser.add_argument(
        "--output",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/sync_kernel_real_input_40_arity_3d.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="sync-kernel-real-input-arity-3d", every_seconds=20.0)
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    phi = (1.0 + 5.0**0.5) / 2.0
    lam = phi * phi
    gamma = 0.5772156649015329
    mertens_n = args.mertens_n
    k_max = int(args.k_max)
    z = 1.0 / lam
    third_axis = str(args.third_axis)

    # Untwisted Mertens constant estimate (needs partial sums; stable at moderate mertens_n).
    # We intentionally keep this path separate from twisted constants (computed via log-zeta).
    def _traces_untwisted(max_n: int) -> List[complex]:
        M1 = build_weighted_matrix_numeric(1.0 + 0.0j, 1.0 + 0.0j, 1.0 + 0.0j, states, kernel_map, third_axis=third_axis)
        A = M1.copy()
        out: List[complex] = []
        for n in range(1, max_n + 1):
            if n > 1:
                A = A @ M1
            out.append(np.trace(A))
            prog.tick(f"q=r=u=1 trace n={n}/{max_n}")
        return out

    def _pvals_from_traces(traces: List[complex]) -> List[complex]:
        max_n = len(traces)
        pvals: List[complex] = []
        for n in range(1, max_n + 1):
            s = 0.0 + 0.0j
            for d in range(1, n + 1):
                if n % d == 0:
                    s += mobius(d) * traces[n // d - 1]
            pvals.append(s / float(n))
        return pvals

    p_one = _pvals_from_traces(_traces_untwisted(mertens_n))
    logM = 0.0
    for n, pn in enumerate(p_one, start=1):
        logM += (pn.real / (lam**n)) - 1.0 / n
    mathsf_M = logM + gamma

    triples = parse_triple_values(args.triple_values)
    triple_keys = [f"{m1}x{m2}x{m3}" for m1, m2, m3 in triples]
    triple_twist_C: Dict[str, Dict[str, Dict[str, float]]] = {}
    triple_class_C: Dict[str, Dict[str, float]] = {}
    triple_rho: Dict[str, Dict[str, float]] = {}
    triple_rho_max: Dict[str, float] = {}

    for m1, m2, m3 in triples:
        omega1 = np.exp(2j * math.pi / m1)
        omega2 = np.exp(2j * math.pi / m2)
        omega3 = np.exp(2j * math.pi / m3)
        twist_constants: Dict[str, Dict[str, float]] = {}
        rho_vals: Dict[str, float] = {}
        for j1 in range(m1):
            q = omega1**j1
            for j2 in range(m2):
                r = omega2**j2
                for j3 in range(m3):
                    if j1 == 0 and j2 == 0 and j3 == 0:
                        continue
                    u = omega3**j3
                    label = f"m={m1}x{m2}x{m3} j={j1},{j2},{j3}"
                    # Twisted constants are computed via the convergent log-zeta identity:
                    #   P(z)=sum_{k>=1} mu(k)/k * log zeta(z^k)
                    # evaluated at z=1/lambda (inside the disk for twisted characters).
                    C = _twist_constant_via_mobius_logzeta(
                        q=q,
                        r=r,
                        u=u,
                        z=z,
                        k_max=k_max,
                        prog=prog,
                        states=states,
                        kernel_map=kernel_map,
                        label=label,
                        third_axis=third_axis,
                    )
                    key = f"{j1},{j2},{j3}"
                    twist_constants[key] = {"re": float(C.real), "im": float(C.imag)}
                    rho = spectral_radius(build_weighted_matrix_numeric(q, r, u, states, kernel_map, third_axis=third_axis))
                    rho_vals[key] = rho

        denom = float(m1 * m2 * m3)
        class_constants: Dict[str, float] = {}
        for r1 in range(m1):
            for r2 in range(m2):
                for r3 in range(m3):
                    acc = mathsf_M / denom
                    for j1 in range(m1):
                        q = omega1**j1
                        for j2 in range(m2):
                            r = omega2**j2
                            for j3 in range(m3):
                                if j1 == 0 and j2 == 0 and j3 == 0:
                                    continue
                                u = omega3**j3
                                key = f"{j1},{j2},{j3}"
                                phase = (q ** (-r1)) * (r ** (-r2)) * (u ** (-r3))
                                acc += (phase * complex(twist_constants[key]["re"], twist_constants[key]["im"])) / denom
                    class_constants[f"{r1},{r2},{r3}"] = float(acc.real)

        # Optional: for (3,3,5), compute an independent 2D (3,3) constant grid to audit marginal consistency.
        marginal_2d: Dict[str, float] | None = None
        if m1 == 3 and m2 == 3 and m3 == 5:
            omega1 = np.exp(2j * math.pi / m1)
            omega2 = np.exp(2j * math.pi / m2)
            denom2 = float(m1 * m2)
            # Twisted constants C(j1,j2) with u fixed to 1 (ignoring the 3rd axis).
            twist2: Dict[str, complex] = {}
            for j1 in range(m1):
                q = omega1**j1
                for j2 in range(m2):
                    r = omega2**j2
                    if j1 == 0 and j2 == 0:
                        continue
                    label2 = f"m=3x3 (marginal) j={j1},{j2}"
                    twist2[f"{j1},{j2}"] = _twist_constant_via_mobius_logzeta(
                        q=q,
                        r=r,
                        u=1.0 + 0.0j,
                        z=z,
                        k_max=k_max,
                        prog=prog,
                        states=states,
                        kernel_map=kernel_map,
                        label=label2,
                        third_axis=third_axis,
                    )
            marginal_2d = {}
            for a in range(m1):
                for b in range(m2):
                    acc2 = mathsf_M / denom2
                    for j1 in range(m1):
                        q = omega1**j1
                        for j2 in range(m2):
                            r = omega2**j2
                            if j1 == 0 and j2 == 0:
                                continue
                            phase = (q ** (-a)) * (r ** (-b))
                            acc2 += (phase * twist2[f"{j1},{j2}"]) / denom2
                    marginal_2d[f"{a},{b}"] = float(acc2.real)

        key_triple = f"{m1}x{m2}x{m3}"
        triple_twist_C[key_triple] = twist_constants
        triple_class_C[key_triple] = class_constants
        triple_rho[key_triple] = rho_vals
        triple_rho_max[key_triple] = max(rho_vals.values()) if rho_vals else 0.0

    payload: Dict[str, object] = {
        "chi_def": "chi = e - 1_{d=2}",
        "nu_def": "nu = 1_{s' in Q_-}",
        "e_def": "e in {0,1} is output bit",
        "third_axis": ("N_e (output-bit count)" if third_axis == "Ne" else "N_2 (collision count 1_{d=2})"),
        "mertens_n": mertens_n,
        "k_max": k_max,
        "mathsf_M": mathsf_M,
        "triple_values": triple_keys,
        "triple_twist_C": triple_twist_C,
        "triple_class_C": triple_class_C,
        "triple_rho": triple_rho,
        "triple_rho_max": triple_rho_max,
        "triple_rho_max_ratio": {k: v / lam for k, v in triple_rho_max.items()},
    }

    if not args.no_output:
        out_path = (
            Path(args.output)
            if args.output
            else export_dir() / "sync_kernel_real_input_40_arity_3d.json"
        )
        write_json(out_path, payload)
        print(f"[sync-kernel-real-input-arity-3d] wrote {out_path}", flush=True)

        # Write LaTeX snippets for each requested tensor.
        for m1, m2, m3 in triples:
            key = f"{m1}x{m2}x{m3}"
            if key not in triple_class_C or key not in triple_rho:
                continue
            suffix = "" if third_axis == "Ne" else "_N2"
            out_tex = generated_dir() / f"tab_real_input_40_arity_dirichlet_mertens_{m1}{m2}{m3}{suffix}.tex"
            _write_dirichlet_mertens_tensor_tex(
                m1=m1,
                m2=m2,
                m3=m3,
                class_constants=triple_class_C[key],
                rho_map=triple_rho[key],
                lam=lam,
                mathsf_M=mathsf_M,
                out_path=out_tex,
                third_axis=third_axis,
                marginal_2d=(marginal_2d if (m1 == 3 and m2 == 3 and m3 == 5) else None),
            )
            print(f"[sync-kernel-real-input-arity-3d] wrote {out_tex}", flush=True)
            if m1 == 3 and m2 == 3 and m3 == 5 and third_axis == "N2":
                out_summary = generated_dir() / "tab_real_input_40_arity_dirichlet_mertens_335_N2_summary.tex"
                _write_dirichlet_mertens_335_n2_summary_tex(
                    class_constants=triple_class_C[key],
                    rho_map=triple_rho[key],
                    lam=lam,
                    out_path=out_summary,
                    states=states,
                    kernel_map=kernel_map,
                )
                print(f"[sync-kernel-real-input-arity-3d] wrote {out_summary}", flush=True)
                out_fourier_top = generated_dir() / "tab_real_input_40_arity_dirichlet_mertens_335_N2_fourier_top.tex"
                _write_dirichlet_mertens_335_n2_fourier_top_tex(
                    class_constants=triple_class_C[key],
                    out_path=out_fourier_top,
                    top_k=12,
                )
                print(f"[sync-kernel-real-input-arity-3d] wrote {out_fourier_top}", flush=True)

    print("[sync-kernel-real-input-arity-3d] done", flush=True)


if __name__ == "__main__":
    main()
