#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Minimal closed-loop validation for the ((3,3,p)) N2 (collision) axis.

Goal
  Reproduce (and validate at larger primes) the diffusion-law interface used in the paper:

    1 - rho_{3,3,p}/lambda = kappa_inf * (2π/p)^2 + c4 * (2π/p)^4 + O(p^{-6}),
    kappa_inf = sigma_xi^2 / 2,

where xi is the collision cocycle xi(e)=1_{d=2} on the real-input 40-state kernel.

This script is self-contained (no imports from other paper scripts) and builds:
  - the kernel graph (10 internal states),
  - the 40 lifted states (internal x carry bits),
  - the weighted twist matrix M(q,r,u) for ((3,3,p)) with third axis = N2 mod p,
  - the Parry Markov chain and the Poisson solver for sigma_xi^2,
  - the (p,q)-Richardson extrapolator for kappa_inf.

Outputs (defaults):
  - artifacts/export/arity_335_n2_poisson_richardson_validate.json
  - sections/generated/tab_real_input_40_arity_335_n2_poisson_richardson_validate.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import numpy as np

def _paper_root() -> Path:
    # scripts/.. = paper root
    return Path(__file__).resolve().parents[1]


def _export_dir() -> Path:
    return _paper_root() / "artifacts" / "export"


def _generated_dir() -> Path:
    return _paper_root() / "sections" / "generated"


def _phi() -> float:
    return (1.0 + 5.0**0.5) / 2.0


def _lam_target() -> float:
    p = _phi()
    return p * p


@dataclass(frozen=True)
class KernelEdge:
    src: str
    dst: str
    d: int
    e: int


KERNEL_STATES: List[str] = [
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


def build_kernel_map(edges: Sequence[KernelEdge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(edge.src, edge.d): (edge.dst, edge.e) for edge in edges}


def build_real_input_states() -> List[Tuple[str, int, int]]:
    # 10 internal states x 4 carry-bit states = 40
    states: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                states.append((s, px, py))
    return states


def build_weighted_matrix_numeric(
    q: complex,
    r: complex,
    u: complex,
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> np.ndarray:
    """Twisted 40x40 matrix for the 3D family with third axis = N2.

    - q^{chi}: output-bit/collision-adjusted cocycle
    - r^{nu}:  negative-carry indicator (entering Q_-)
    - u^{xi}:  collision cocycle xi = 1_{d=2}  (N2 axis)
    """
    idx = {state: i for i, state in enumerate(states)}
    n = len(idx)
    M = np.zeros((n, n), dtype=complex)
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, e = kernel_map[(s, d)]
                chi = e - (1 if d == 2 else 0)
                nu = 1 if "-" in dst_state else 0
                xi = 1 if d == 2 else 0
                i = idx[(s, px, py)]
                j = idx[(dst_state, x, y)]
                M[i, j] += (q**chi) * (r**nu) * (u**xi)
    return M


def spectral_radius(B: np.ndarray) -> float:
    vals = np.linalg.eigvals(B)
    return float(np.max(np.abs(vals)))


@dataclass(frozen=True)
class LiftEdge:
    src: int
    dst: int
    xi: int  # collision cocycle 1_{d=2}


def _build_lift_edges(
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> List[LiftEdge]:
    idx = {st: i for i, st in enumerate(states)}
    edges: List[LiftEdge] = []
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, _e = kernel_map[(s, d)]
                src_i = idx[(s, px, py)]
                dst_i = idx[(dst_state, x, y)]
                xi = 1 if d == 2 else 0
                edges.append(LiftEdge(src=src_i, dst=dst_i, xi=xi))
    return edges


def _adjacency_from_edges(n: int, edges: Sequence[LiftEdge]) -> np.ndarray:
    A = np.zeros((n, n), dtype=float)
    for e in edges:
        A[e.src, e.dst] += 1.0
    return A


def _pf_eigenvectors(A: np.ndarray) -> Tuple[float, np.ndarray, np.ndarray]:
    # Right eigenvector (PF)
    vals, vecs = np.linalg.eig(A)
    i0 = int(np.argmax(np.real(vals)))
    lam = float(np.real(vals[i0]))
    r = np.real(vecs[:, i0]).astype(float)
    # Left eigenvector
    valsL, vecsL = np.linalg.eig(A.T)
    j0 = int(np.argmax(np.real(valsL)))
    l = np.real(vecsL[:, j0]).astype(float)

    # Fix signs
    if float(np.sum(r)) < 0.0:
        r = -r
    if float(np.sum(l)) < 0.0:
        l = -l

    lr = float(l @ r)
    if lr == 0.0:
        raise RuntimeError("PF normalization failed: l^T r = 0")
    l = l / lr
    return lam, l, r


def _parry_chain(A: np.ndarray, lam: float, l: np.ndarray, r: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    n = A.shape[0]
    P = np.zeros((n, n), dtype=float)
    for i in range(n):
        if r[i] <= 0.0:
            continue
        for j in range(n):
            aij = A[i, j]
            if aij == 0.0:
                continue
            P[i, j] = aij * r[j] / (lam * r[i])
    pi = (l * r).astype(float)
    s = float(np.sum(pi))
    if s <= 0.0:
        raise RuntimeError("Invalid stationary mass")
    pi = pi / s
    return P, pi


def _edge_weight(l: np.ndarray, r: np.ndarray, lam: float, src: int, dst: int) -> float:
    # Parry edge measure per parallel edge: m(e)=l_src*r_dst/lam with l^T r=1.
    return float(l[src] * r[dst] / lam)


def _mu_edge_mean(edges: Sequence[LiftEdge], l: np.ndarray, r: np.ndarray, lam: float) -> float:
    mu = 0.0
    for e in edges:
        mu += _edge_weight(l, r, lam, e.src, e.dst) * float(e.xi)
    return float(mu)


def _solve_poisson(P: np.ndarray, pi: np.ndarray, b: np.ndarray) -> np.ndarray:
    # Solve (I-P)f=b with gauge pi^T f=0 via augmented linear system.
    n = P.shape[0]
    I = np.eye(n, dtype=float)
    A = I - P
    M = np.zeros((n + 1, n + 1), dtype=float)
    M[:n, :n] = A
    M[:n, n] = pi
    M[n, :n] = pi
    rhs = np.zeros((n + 1,), dtype=float)
    rhs[:n] = b
    sol = np.linalg.solve(M, rhs)
    f = sol[:n]
    # enforce gauge exactly (project out mean)
    f = f - float(pi @ f)
    return f


def _sigma2_from_f(edges: Sequence[LiftEdge], l: np.ndarray, r: np.ndarray, lam: float, mu: float, f: np.ndarray) -> float:
    s = 0.0
    for e in edges:
        w = _edge_weight(l, r, lam, e.src, e.dst)
        d = float(e.xi) - mu + float(f[e.dst] - f[e.src])
        s += w * d * d
    return float(s)


def kappa_inf_poisson(*, states: Sequence[Tuple[str, int, int]], kernel_map: Dict[Tuple[str, int], Tuple[str, int]]) -> Dict[str, float]:
    edges = _build_lift_edges(states, kernel_map)
    n = len(states)
    A = _adjacency_from_edges(n, edges)
    lam_pf, lvec, rvec = _pf_eigenvectors(A)

    P, pi = _parry_chain(A, lam_pf, lvec, rvec)
    mu = _mu_edge_mean(edges, lvec, rvec, lam_pf)

    # b_i = E[xi - mu | state i] under Parry chain (uniform over parallel edges).
    b = np.zeros((n,), dtype=float)
    for e in edges:
        b[e.src] += (rvec[e.dst] / (lam_pf * rvec[e.src])) * (float(e.xi) - mu)

    f = _solve_poisson(P, pi, b)
    sigma2 = _sigma2_from_f(edges, lvec, rvec, lam_pf, mu, f)
    kappa = 0.5 * sigma2
    return {
        "n_states": int(n),
        "n_edges": int(len(edges)),
        "lambda_pf": float(lam_pf),
        "lambda_target": float(_lam_target()),
        "lambda_abs_err": float(abs(lam_pf - _lam_target())),
        "mu_edge_mean": float(mu),
        "sigma2": float(sigma2),
        "kappa_inf": float(kappa),
    }


@dataclass(frozen=True)
class ScanRow:
    p: int
    rho: float
    rho_ratio: float
    gap: float
    g: float
    kappa_p: float
    s_re: float
    argmax: List[Tuple[int, int, int]]

    # predictions (optional, can be nan)
    rho_ratio_pred2: float
    rho_ratio_pred4: float
    s_re_pred2: float
    s_re_pred4: float
    abs_err_pred2: float
    abs_err_pred4: float


def _parse_int_list_csv(s: str) -> List[int]:
    out: List[int] = []
    for chunk in (x.strip() for x in s.split(",")):
        if not chunk:
            continue
        out.append(int(chunk))
    return out


def _omega(m: int) -> complex:
    return np.exp(2j * math.pi / float(m))


def _scan_rho_max_for_p(
    p: int,
    *,
    states: Sequence[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
    scan_full: bool,
    kappa_inf: float,
    c4: float | None,
    lam: float,
) -> ScanRow:
    m1, m2, m3 = 3, 3, p
    omega1 = _omega(m1)
    omega2 = _omega(m2)
    omega3 = _omega(m3)

    rho_max = -1.0
    argmax: List[Tuple[int, int, int]] = []
    tol = 1e-12

    j1_iter: Iterable[int] = range(m1) if scan_full else (0,)
    j2_iter: Iterable[int] = range(m2) if scan_full else (0,)
    j3_iter: Iterable[int] = range(m3) if scan_full else range(1, m3)  # omit trivial when scan_full=False

    for j1 in j1_iter:
        q = omega1**j1
        for j2 in j2_iter:
            r = omega2**j2
            for j3 in j3_iter:
                if scan_full and j1 == 0 and j2 == 0 and j3 == 0:
                    continue
                u = omega3**j3
                M = build_weighted_matrix_numeric(q, r, u, states, kernel_map)
                rho = spectral_radius(M)
                if rho > rho_max + tol:
                    rho_max = rho
                    argmax = [(j1, j2, j3)]
                elif abs(rho - rho_max) <= tol:
                    argmax.append((j1, j2, j3))

    rho_ratio = rho_max / lam
    gap = 1.0 - rho_ratio
    g = gap * float(p * p)
    theta = (2.0 * math.pi) / float(p)
    kappa_p = gap / (theta * theta)
    s_re = 1.0 + math.log(rho_ratio) / math.log(lam)

    # Predictions: quadratic gap only, and optional quartic gap using c4.
    rho_ratio_pred2 = 1.0 - (kappa_inf * theta * theta)
    rho_ratio_pred4 = float("nan")
    if c4 is not None:
        rho_ratio_pred4 = 1.0 - (kappa_inf * theta * theta) - (c4 * (theta**4))

    s_re_pred2 = 1.0 + math.log(rho_ratio_pred2) / math.log(lam) if 0.0 < rho_ratio_pred2 < 1.0 else float("nan")
    s_re_pred4 = (
        1.0 + math.log(rho_ratio_pred4) / math.log(lam) if (c4 is not None and 0.0 < rho_ratio_pred4 < 1.0) else float("nan")
    )
    abs_err_pred2 = abs(rho_ratio - rho_ratio_pred2)
    abs_err_pred4 = abs(rho_ratio - rho_ratio_pred4) if c4 is not None else float("nan")

    return ScanRow(
        p=int(p),
        rho=float(rho_max),
        rho_ratio=float(rho_ratio),
        gap=float(gap),
        g=float(g),
        kappa_p=float(kappa_p),
        s_re=float(s_re),
        argmax=sorted(argmax),
        rho_ratio_pred2=float(rho_ratio_pred2),
        rho_ratio_pred4=float(rho_ratio_pred4),
        s_re_pred2=float(s_re_pred2),
        s_re_pred4=float(s_re_pred4),
        abs_err_pred2=float(abs_err_pred2),
        abs_err_pred4=float(abs_err_pred4),
    )


def _estimate_c4_from_calib(ps: Sequence[int], rows_by_p: Dict[int, ScanRow], kappa_inf: float) -> Dict[str, object]:
    # From A(p)=kappa_inf + c4(2π)^2/p^2 + O(p^{-4}), where A(p)=kappa_p.
    c4s: List[Dict[str, float]] = []
    two_pi_sq = (2.0 * math.pi) ** 2
    for p in ps:
        row = rows_by_p.get(int(p))
        if row is None:
            raise RuntimeError(f"calibration p={p} missing from scan rows")
        c4 = (row.kappa_p - kappa_inf) * float(p * p) / two_pi_sq
        c4s.append({"p": float(p), "c4": float(c4)})
    c4_vals = [d["c4"] for d in c4s]
    c4_mean = float(sum(c4_vals) / float(len(c4_vals))) if c4_vals else float("nan")
    c4_span = float(max(c4_vals) - min(c4_vals)) if len(c4_vals) >= 2 else float("nan")
    return {
        "calib_p_list": [int(p) for p in ps],
        "c4_by_p": c4s,
        "c4_mean": c4_mean,
        "c4_span": c4_span,
    }


def _richardson_kappa_hat(p: int, q: int, A_p: float, A_q: float) -> float:
    # kappa_hat(p,q) = (A(p)p^2 - A(q)q^2)/(p^2-q^2)
    pp = float(p * p)
    qq = float(q * q)
    return float((A_p * pp - A_q * qq) / (pp - qq))


def _write_validation_tex(
    path: Path,
    *,
    rows: Sequence[ScanRow],
    poisson: Dict[str, float],
    c4_payload: Dict[str, object],
    rich_pairs: Sequence[Dict[str, float]],
) -> None:
    kappa_inf = float(poisson["kappa_inf"])
    sigma2 = float(poisson["sigma2"])
    c4_mean = float(c4_payload["c4_mean"])
    calib = ", ".join(str(int(p)) for p in (c4_payload.get("calib_p_list") or []))

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_arity_335_n2_poisson_richardson_validate.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Closed-loop validation for the $((3,3,p))$ pure-collision slow mode (third axis $N_2\\bmod p$). "
        "We use the Poisson-extracted variance limit $\\kappa_\\infty=\\sigma_\\xi^2/2$ and estimate the quartic "
        "gap coefficient $c_4$ from $A(p)=\\kappa_p$ at calibration moduli $p\\in\\{"
        + calib
        + "\\}$. "
        "We compare the true $\\rho_{3,3,p}/\\lambda$ to the quadratic and quartic gap predictions "
        "$\\rho/\\lambda\\approx 1-\\kappa_\\infty\\theta_p^2-c_4\\theta_p^4$ with $\\theta_p=2\\pi/p$. "
        f"Here $\\sigma_\\xi^2\\approx {sigma2:.12f}$, $\\kappa_\\infty\\approx {kappa_inf:.12f}$, "
        f"$c_4\\approx {c4_mean:.12f}$.}}"
    )
    lines.append("\\label{tab:real_input_40_arity_335_n2_poisson_richardson_validate}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$p$ & $\\rho/\\lambda$ & quad pred & quartic pred & $|\\Delta|$ (quartic) & $A(p)=\\kappa_p$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.p} & {r.rho_ratio:.12f} & {r.rho_ratio_pred2:.12f} & {r.rho_ratio_pred4:.12f} & "
            f"{r.abs_err_pred4:.3e} & {r.kappa_p:.12f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")

    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Richardson extrapolation for $\\kappa_\\infty$ using "
        "$\\widehat\\kappa(p,q)=(A(p)p^2-A(q)q^2)/(p^2-q^2)$ with $A(p)=\\kappa_p$. "
        "We list consecutive pairs from the scan list and compare to the Poisson value.}"
    )
    lines.append("\\label{tab:real_input_40_arity_335_n2_richardson_pairs}")
    lines.append("\\begin{tabular}{r r r r}")
    lines.append("\\toprule")
    lines.append("$p$ & $q$ & $\\widehat\\kappa(p,q)$ & $|\\widehat\\kappa-\\kappa_\\infty|$\\\\")
    lines.append("\\midrule")
    for rr in rich_pairs:
        p = int(rr["p"])
        q = int(rr["q"])
        khat = float(rr["kappa_hat"])
        err = float(rr["abs_err_vs_poisson"])
        lines.append(f"{p} & {q} & {khat:.12f} & {err:.3e}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Poisson + Richardson closed-loop validation for ((3,3,p)) on the N2 axis.")
    parser.add_argument(
        "--p-list",
        type=str,
        default="5,7,11,13,17,19,23,29,31",
        help="Comma-separated list of moduli p to scan (typically primes).",
    )
    parser.add_argument(
        "--scan-full",
        action="store_true",
        help="Scan the full (j1,j2,j3)!=(0,0,0) set; default scans only pure collision axis (j1=j2=0, j3!=0).",
    )
    parser.add_argument(
        "--calib-p-list",
        type=str,
        default="7,13",
        help="Comma-separated calibration moduli used to estimate c4 from A(p)=kappa_p.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(_export_dir() / "arity_335_n2_poisson_richardson_validate.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(_generated_dir() / "tab_real_input_40_arity_335_n2_poisson_richardson_validate.tex"),
    )
    args = parser.parse_args()

    p_list = _parse_int_list_csv(str(args.p_list))
    if not p_list:
        raise SystemExit("empty p-list")
    for p in p_list:
        if p < 3 or p % 2 == 0:
            raise SystemExit(f"require odd p>=3, got {p}")

    calib_p_list = _parse_int_list_csv(str(args.calib_p_list))
    if not calib_p_list:
        raise SystemExit("empty calib-p-list")

    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()

    lam = _lam_target()
    poisson = kappa_inf_poisson(states=states, kernel_map=kernel_map)
    kappa_inf = float(poisson["kappa_inf"])

    # First pass scan (no c4-based predictions yet).
    rows0: List[ScanRow] = []
    for p in p_list:
        rows0.append(
            _scan_rho_max_for_p(
                int(p),
                states=states,
                kernel_map=kernel_map,
                scan_full=bool(args.scan_full),
                kappa_inf=kappa_inf,
                c4=None,
                lam=lam,
            )
        )
    rows_by_p0 = {r.p: r for r in rows0}

    c4_payload = _estimate_c4_from_calib(calib_p_list, rows_by_p0, kappa_inf)
    c4_mean = float(c4_payload["c4_mean"])

    # Second pass scan, now with quartic predictions enabled.
    rows: List[ScanRow] = []
    for p in p_list:
        rows.append(
            _scan_rho_max_for_p(
                int(p),
                states=states,
                kernel_map=kernel_map,
                scan_full=bool(args.scan_full),
                kappa_inf=kappa_inf,
                c4=c4_mean,
                lam=lam,
            )
        )

    # Richardson extrapolation on kappa_p=A(p)
    rich_rows: List[Dict[str, float]] = []
    for i in range(len(rows) - 1):
        p = rows[i].p
        q = rows[i + 1].p
        khat = _richardson_kappa_hat(p, q, rows[i].kappa_p, rows[i + 1].kappa_p)
        rich_rows.append(
            {
                "p": float(p),
                "q": float(q),
                "kappa_hat": float(khat),
                "abs_err_vs_poisson": float(abs(khat - kappa_inf)),
            }
        )

    payload: Dict[str, object] = {
        "third_axis": "N2",
        "m1": 3,
        "m2": 3,
        "scan_full": bool(args.scan_full),
        "lambda": float(lam),
        "poisson": poisson,
        "c4_estimate": c4_payload,
        "rows": [asdict(r) for r in rows],
        "richardson_pairs": rich_rows,
    }

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[poisson-richardson-validate] wrote {jout}", flush=True)

    tout = Path(str(args.tex_out))
    _write_validation_tex(tout, rows=rows, poisson=poisson, c4_payload=c4_payload, rich_pairs=rich_rows)
    print(f"[poisson-richardson-validate] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

