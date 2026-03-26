#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Approximate traces and primitive spectra at intermediate u via matrix-free Monte Carlo.

Goal (paper-facing):
For each parallel-addition kernel K in {K9,K13,K21} (single-flow compiled BFS graph),
estimate:
  a_n(u) := Tr(M_K(u)^n)
and then reconstruct a primitive layered spectrum estimate
  B_{K,n}(u) = (1/n) * sum_{d|n} mu(d) * Tr(M_K(u^d)^{n/d})
by plugging-in the stochastic trace estimates.

We use Hutchinson's estimator (Rademacher vectors):
  Tr(A) = E[r^T A r],  r_i in {±1} iid.
In our usage A = M(u)^n is only accessed through repeated sparse matvecs.

Outputs:
- artifacts/export/parallel_addition_kernels_trace_hutchinson.json
- sections/generated/tab_parallel_addition_kernels_fingerprint_u_samples.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
import exp_parallel_addition_kernels_bfs as bfs


def _write_text(p: Path, s: str) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(s, encoding="utf-8")


def _mobius(n: int) -> int:
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
        p += 1 if p == 2 else 2
    if x > 1:
        mu = -mu
    return mu


def _divisors(n: int) -> List[int]:
    ds: List[int] = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            ds.append(d)
            if d * d != n:
                ds.append(n // d)
        d += 1
    return sorted(ds)


@dataclass(frozen=True)
class MatOp:
    n: int
    src: np.ndarray  # shape (E,)
    dst: np.ndarray  # shape (E,)
    kappa: np.ndarray  # shape (E,)

    def weights(self, u: float) -> np.ndarray:
        """Return edge weights w_e = u^{kappa_e} as float64 (no allocation on repeated u)."""
        # kappa is small (0/1 for K9, up to 2 for K21 in our compilation).
        if u == 0.0:
            return (self.kappa == 0).astype(np.float64, copy=False)
        if u == 1.0:
            return np.ones(self.kappa.shape[0], dtype=np.float64)
        kmax = int(np.max(self.kappa)) if self.kappa.size else 0
        pow_u = np.empty(kmax + 1, dtype=np.float64)
        pow_u[0] = 1.0
        for k in range(1, kmax + 1):
            pow_u[k] = pow_u[k - 1] * float(u)
        return pow_u[self.kappa.astype(np.int64, copy=False)]

    def matvec_inplace(self, x: np.ndarray, w_edge: np.ndarray, y: np.ndarray, tmp: np.ndarray) -> None:
        """Compute y := M(u) x using precomputed w_edge, without allocating."""
        # tmp[e] = x[src[e]] * w_edge[e]
        np.take(x, self.src, out=tmp)
        tmp *= w_edge
        y.fill(0.0)
        np.add.at(y, self.dst, tmp)


def _build_op(spec: bfs.KernelSpec, *, prog: bfs.Progress) -> Tuple[MatOp, int]:
    idx, edges = bfs._bfs_states(spec, prog)
    n = len(idx)
    b = len(spec.alphabet)
    src = np.fromiter((e[0] for e in edges), dtype=np.int32, count=len(edges))
    dst = np.fromiter((e[1] for e in edges), dtype=np.int32, count=len(edges))
    kappa = np.fromiter((int(e[3]) + int(e[4]) for e in edges), dtype=np.int8, count=len(edges))
    return MatOp(n=n, src=src, dst=dst, kappa=kappa), b


def _power_method(op: MatOp, u: float, *, itmax: int, tol: float, prog: bfs.Progress, label: str) -> float:
    x = np.full(op.n, 1.0 / op.n, dtype=np.float64)
    y = np.empty_like(x)
    tmp = np.empty(op.src.shape[0], dtype=np.float64)
    w_edge = op.weights(u)
    lam = 0.0
    t0 = time.time()
    for it in range(1, itmax + 1):
        op.matvec_inplace(x, w_edge, y, tmp)
        s = float(np.sum(y))
        if s <= 0.0:
            return 0.0
        y *= 1.0 / s
        lam_new = s
        if it > 50 and abs(lam_new - lam) / max(1.0, abs(lam_new)) < tol:
            prog.tick(f"{label} power it={it} u={u} lam~{lam_new:.12g}")
            return lam_new
        lam = lam_new
        x, y = y, x
        if (time.time() - t0) > 20.0:
            prog.tick(f"{label} power it={it} u={u} lam~{lam_new:.12g}")
            t0 = time.time()
    return lam


def _hutchinson_trace_power(
    op: MatOp,
    u: float,
    n_power: int,
    *,
    samples: int,
    rng: np.random.Generator,
    prog: bfs.Progress,
    label: str,
) -> Tuple[float, float]:
    # Returns (mean, standard_error) for Tr(M(u)^n_power).
    vals = np.empty(samples, dtype=np.float64)
    t0 = time.time()
    w_edge = op.weights(u)
    tmp = np.empty(op.src.shape[0], dtype=np.float64)
    buf_a = np.empty(op.n, dtype=np.float64)
    buf_b = np.empty(op.n, dtype=np.float64)
    for s in range(samples):
        r = rng.integers(0, 2, size=op.n, dtype=np.int8)
        r = (2 * r - 1).astype(np.float64, copy=False)
        v: np.ndarray = r
        out = buf_a
        for _ in range(n_power):
            op.matvec_inplace(v, w_edge, out, tmp)
            v, out = out, (buf_b if out is buf_a else buf_a)
        vals[s] = float(r @ v)
        if (time.time() - t0) > 20.0:
            prog.tick(f"{label} Hutch n={n_power} u={u} sample={s+1}/{samples}")
            t0 = time.time()
    mean = float(vals.mean())
    # Unbiased sample variance, then SE.
    if samples >= 2:
        se = float(vals.std(ddof=1) / math.sqrt(samples))
    else:
        se = float("nan")
    return mean, se


def _latex_float(x: float, digits: int = 6) -> str:
    if not math.isfinite(x):
        return r"\texttt{nan}"
    return f"{x:.{digits}g}"


def _make_table(rows: List[Dict[str, str]], *, u_grid: List[float], n_list: List[int], samples: int) -> str:
    u_cols = ",".join(_latex_float(u, 3) for u in u_grid)
    n_cols = ",".join(str(n) for n in n_list)
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\setlength{\tabcolsep}{6pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.15}")
    caption = (
        r"中间权重 $u$ 的核指纹近似：对 $u\in\{"
        + u_cols
        + r"\}$，用 Hutchinson 随机迹估计近似 $a_n(u)=\Tr(M_K(u)^n)$ 并经 Möbius 反演得到 $\widehat B_{K,n}(u)$（单流；样本数 $S="
        + str(samples)
        + r"$；脚本 \texttt{scripts/exp\_parallel\_addition\_kernels\_trace\_hutchinson.py} 生成）。这里列出 $n\in\{"
        + n_cols
        + r"\}$ 的 $\widehat B_{K,n}(u)$（数值为估计均值，$\pm$ 后为标准误差 $\mathrm{se}=O(S^{-1/2})$；primitive 层对迹误差的线性传播与 $1/n$ 滤波增益见命题 \ref{prop:mobius-error-propagation}）。"
    )
    lines.append(r"\caption{" + caption + r"}")
    lines.append(r"\label{tab:parallel-addition-kernels-fingerprint-u-samples}")
    lines.append(r"\begin{tabular}{@{}lccc p{0.55\textwidth}@{}}")
    lines.append(r"\toprule")
    lines.append(r"核 & $\zeta_K(z,0)$ & $\lambda_K(u)$ 采样 & $p_n(0)$（$n\le 8$） & $\widehat B_{K,n}(u)$（中间 $u$） \\")
    lines.append(r"\midrule")
    for r in rows:
        lines.append(" & ".join([r["kernel"], r["zeta0"], r["lambda_samples"], r["p0_8"], r["Bhat"]]) + r" \\")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def _estimate_bhat_correlated(
    op: MatOp,
    u_grid: List[float],
    n_list: List[int],
    *,
    samples: int,
    rng: np.random.Generator,
    prog: bfs.Progress,
    label: str,
) -> Tuple[Dict[str, Dict[str, float]], Dict[str, Dict[str, float]]]:
    """
    Correlated Hutchinson estimator for B_n(u) to reduce cancellation noise:
    for each sample r_s, compute all needed r_s^T M(u)^k r_s, then combine per-sample
    using the Möbius inversion formula, and only then average across samples.
    """

    # Precompute which (u_val, power) pairs we need.
    need: Dict[float, List[int]] = {}
    for u in u_grid:
        for n in n_list:
            for d in _divisors(n):
                mu = _mobius(d)
                if mu == 0:
                    continue
                u_val = u ** d
                p = n // d
                need.setdefault(u_val, [])
                if p not in need[u_val]:
                    need[u_val].append(p)
    for u_val in need:
        need[u_val].sort()

    # Use the SAME Rademacher probes for all u-values (common random numbers),
    # so Möbius combinations (which subtract large traces) have much lower variance.
    R = rng.integers(0, 2, size=(samples, op.n), dtype=np.int8)
    R = (2 * R - 1).astype(np.float64, copy=False)

    # For each u_val, compute per-sample quadratic forms for required powers.
    # Store as: q[u_val][p][s] = r_s^T M(u_val)^p r_s
    q: Dict[float, Dict[int, np.ndarray]] = {}
    t0 = time.time()
    for u_val, powers in need.items():
        w_edge = op.weights(float(u_val))
        tmp = np.empty(op.src.shape[0], dtype=np.float64)
        buf_a = np.empty(op.n, dtype=np.float64)
        buf_b = np.empty(op.n, dtype=np.float64)
        q_u: Dict[int, np.ndarray] = {p: np.empty(samples, dtype=np.float64) for p in powers}
        for s in range(samples):
            r = R[s]
            v: np.ndarray = r
            out = buf_a
            pmax = powers[-1]
            j = 0
            target = powers[j]
            for p in range(1, pmax + 1):
                op.matvec_inplace(v, w_edge, out, tmp)
                v, out = out, (buf_b if out is buf_a else buf_a)
                if p == target:
                    q_u[p][s] = float(r @ v)
                    j += 1
                    if j >= len(powers):
                        break
                    target = powers[j]
            if (time.time() - t0) > 20.0:
                prog.tick(f"{label} correlated traces u={u_val:.6g} sample={s+1}/{samples}")
                t0 = time.time()
        q[u_val] = q_u

    # Combine per sample into Bhat values.
    Bhat: Dict[str, Dict[str, float]] = {}
    Bhat_se: Dict[str, Dict[str, float]] = {}
    for u in u_grid:
        Bu: Dict[str, float] = {}
        Bu_se: Dict[str, float] = {}
        for n in n_list:
            b_samples = np.zeros(samples, dtype=np.float64)
            for d in _divisors(n):
                mu = _mobius(d)
                if mu == 0:
                    continue
                u_val = u ** d
                p = n // d
                b_samples += (mu / n) * q[u_val][p]
            Bu[str(n)] = float(b_samples.mean())
            Bu_se[str(n)] = float(b_samples.std(ddof=1) / math.sqrt(samples)) if samples >= 2 else float("nan")
        Bhat[str(u)] = Bu
        Bhat_se[str(u)] = Bu_se
    return Bhat, Bhat_se


def main() -> None:
    parser = argparse.ArgumentParser(description="Hutchinson trace estimator for intermediate-u kernel fingerprints")
    parser.add_argument("--u-grid", type=str, default="0.25,0.5,0.75", help="Comma-separated u values in (0,1)")
    parser.add_argument("--nmax", type=int, default=7, help="Max n for Bhat_n(u) estimates")
    parser.add_argument("--n-list", type=str, default="3,5,7", help="Comma-separated n to show in LaTeX table")
    parser.add_argument("--samples", type=int, default=200, help="Number of Hutchinson samples S")
    parser.add_argument("--seed", type=int, default=12345)
    parser.add_argument("--no-output", action="store_true")
    args = parser.parse_args()

    u_grid = [float(x.strip()) for x in args.u_grid.split(",") if x.strip()]
    n_list = [int(x.strip()) for x in args.n_list.split(",") if x.strip()]
    if any(u <= 0.0 or u >= 1.0 for u in u_grid):
        raise SystemExit("All u in --u-grid must lie in (0,1). Endpoints u=0,1 are closed-form and not estimated here.")
    if args.nmax < 1:
        raise SystemExit("--nmax must be >= 1")
    if any(n < 1 or n > args.nmax for n in n_list):
        raise SystemExit("All n in --n-list must satisfy 1 <= n <= nmax.")

    prog = bfs.Progress(label="par-add-trace-hutch", every_seconds=20.0)
    print("[par-add-trace-hutch] start", flush=True)

    rng = np.random.default_rng(args.seed)
    specs = bfs._make_specs(n_max_primitive=20)

    payload: Dict[str, object] = {
        "u_grid": u_grid,
        "nmax": args.nmax,
        "samples": args.samples,
        "seed": args.seed,
        "kernels": [],
    }
    table_rows: List[Dict[str, str]] = []

    for spec in specs:
        name_tex = r"$K_{9}$" if "9-local" in spec.name else (r"$K_{13}$" if "13-local" in spec.name else r"$K_{21}$")
        zeta0 = r"$\frac{1}{1-7z}$" if "9-local" in spec.name else (r"$\frac{1}{1-3z}$" if "13-local" in spec.name else r"$\frac{1}{1-z-z^2}$")
        prog.tick(f"{spec.name} BFS build begin")
        op, b = _build_op(spec, prog=prog)
        prog.tick(f"{spec.name} BFS build done states={op.n} edges={len(op.src)}")

        # closed-form carry-free primitive p_n(0) from spec (single-flow skeleton)
        p0 = bfs._primitive_from_traces(spec.carry_free_traces)
        p0_8 = "(" + ",".join(str(x) for x in p0[:8]) + ")"

        # lambda(u) samples via power method
        lam_samples: Dict[float, float] = {}
        for u in u_grid:
            lam_samples[u] = _power_method(op, u, itmax=6000, tol=1e-12, prog=prog, label=spec.name)

        # Estimate Bhat_n(u) only for n in n_list (correlated to reduce cancellation noise).
        Bhat, Bhat_se = _estimate_bhat_correlated(
            op,
            u_grid,
            n_list,
            samples=args.samples,
            rng=rng,
            prog=prog,
            label=spec.name,
        )

        payload["kernels"].append(
            {
                "name": spec.name,
                "states": op.n,
                "alphabet_size": b,
                "u_grid": u_grid,
                "lambda_u": {str(u): lam_samples[u] for u in u_grid},
                "p0_n_le_20": p0,
                "Bhat": Bhat,
                "Bhat_se": Bhat_se,
            }
        )

        # Make LaTeX row content.
        lam_cell = ", ".join([f"$u={_latex_float(u,3)}:\\ { _latex_float(lam_samples[u], 6)}$" for u in u_grid])
        # show Bhat for selected n_list and all u_grid
        bh_lines: List[str] = []
        for n in n_list:
            parts = []
            for u in u_grid:
                est = Bhat[str(u)][str(n)]
                se = Bhat_se[str(u)][str(n)]
                parts.append(rf"$u={_latex_float(u,3)}:\ { _latex_float(est, 6)} \pm { _latex_float(se, 3)}$")
            bh_lines.append(rf"$n={n}$: " + "; ".join(parts))
        bh_cell = r"\par ".join(bh_lines)

        table_rows.append(
            {
                "kernel": name_tex,
                "zeta0": zeta0,
                "lambda_samples": lam_cell,
                "p0_8": f"${p0_8}$",
                "Bhat": bh_cell,
            }
        )

        prog.tick(f"{spec.name} done")

    if not args.no_output:
        out_json = export_dir() / "parallel_addition_kernels_trace_hutchinson.json"
        _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"[par-add-trace-hutch] wrote {out_json}", flush=True)

        out_tex = generated_dir() / "tab_parallel_addition_kernels_fingerprint_u_samples.tex"
        _write_text(out_tex, _make_table(table_rows, u_grid=u_grid, n_list=n_list, samples=args.samples))
        print(f"[par-add-trace-hutch] wrote {out_tex}", flush=True)

    print("[par-add-trace-hutch] done", flush=True)


if __name__ == "__main__":
    main()

