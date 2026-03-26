#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Pressure + multifractal (Legendre) spectrum for Fold_m collision moments (q up to 60).

We work with Fold_m fiber multiplicities d_m(x)=|Fold_m^{-1}(x)| and collision moments:
  S_q(m) = sum_x d_m(x)^q = sum_{r mod F_{m+2}} c_m(r)^q,
where c_m(r) is the residue DP count modulo F_{m+2}.

For large q, S_q(m) is huge. We therefore compute log S_q(m) stably from the
histogram of residue counts:
  log S_q(m) = q log D_m + log sum_r (c_m(r)/D_m)^q,   D_m := max_r c_m(r).

We estimate log r_q as the slope in a linear regression of log S_q(m) vs m on a
fixed window m in [m_min, m_max]. (This matches the endpoint-convergence script,
but here we compute all q up to q_max in one run.)

We then form the pressure:
  P(q) = log r_q - q log 2,
and compute:
  - a discrete lower convex envelope (convex hull) of P(q) on integer q,
  - a discrete Legendre spectrum f(gamma) via:
      I(gamma) = sup_q (q gamma - log r_q),    f(gamma) = log(phi) - I(gamma).

Outputs (default):
  - artifacts/export/fold_collision_pressure_multifractal_q60.json
  - artifacts/export/fold_collision_pressure_multifractal_q60_rq.png
  - artifacts/export/fold_collision_pressure_multifractal_q60_pressure.png
  - artifacts/export/fold_collision_pressure_multifractal_q60_falpha.png
  - sections/generated/fig_fold_collision_pressure_multifractal_q60_{rq,pressure,falpha}.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import matplotlib.pyplot as plt
import numpy as np

from common_mod_fib_dp import counts_mod_fib_hist
from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, Progress


def log_moments_from_hist(vals: np.ndarray, freq: np.ndarray, q_max: int) -> Dict[int, float]:
    """Compute log S_q for q=2..q_max from histogram (vals,freq) in float64."""
    if q_max < 2:
        raise ValueError("q_max must be >= 2")
    if vals.size == 0:
        raise ValueError("empty histogram")
    D = int(np.max(vals))
    if D <= 0:
        raise ValueError("max count must be positive")

    v = vals.astype(np.float64)
    f = freq.astype(np.float64)
    r = v / float(D)  # in [0,1]

    out: Dict[int, float] = {}
    for q in range(2, q_max + 1):
        # sum_r (c/D)^q = sum_vals freq * (val/D)^q
        # Note: no overflow (<=mod), underflow is acceptable.
        s = float(np.sum(f * (r**float(q))))
        if not (s > 0.0):
            # Should never happen because r=1 occurs at least once.
            raise RuntimeError(f"nonpositive scaled moment sum for q={q}: {s}")
        out[q] = float(q) * math.log(float(D)) + math.log(s)
    return out


def lower_convex_hull(points: List[Tuple[int, float]]) -> List[Tuple[int, float]]:
    """Return the lower convex hull chain for points with increasing x (monotone chain)."""
    if not points:
        return []
    pts = sorted(points, key=lambda t: (t[0], t[1]))

    def cross(o: Tuple[int, float], a: Tuple[int, float], b: Tuple[int, float]) -> float:
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    hull: List[Tuple[int, float]] = []
    for p in pts:
        while len(hull) >= 2 and cross(hull[-2], hull[-1], p) <= 0.0:
            hull.pop()
        hull.append(p)
    return hull


def eval_piecewise_linear(hull: List[Tuple[int, float]], xs: List[int]) -> List[float]:
    """Evaluate the piecewise-linear function defined by hull vertices on given integer xs."""
    if not hull:
        return [float("nan")] * len(xs)
    if len(hull) == 1:
        return [hull[0][1]] * len(xs)

    out: List[float] = []
    j = 0
    for x in xs:
        while j + 1 < len(hull) and x > hull[j + 1][0]:
            j += 1
        if x <= hull[0][0]:
            out.append(hull[0][1])
            continue
        if x >= hull[-1][0]:
            out.append(hull[-1][1])
            continue
        x0, y0 = hull[j]
        x1, y1 = hull[j + 1]
        if x1 == x0:
            out.append(y1)
            continue
        t = (x - x0) / float(x1 - x0)
        out.append((1.0 - t) * y0 + t * y1)
    return out


@dataclass(frozen=True)
class Row:
    q: int
    log_rq: float
    r_q: float
    pressure_Pq: float
    h_q: float
    rq_pow_1_over_q: float
    note: str


def _write_fig_tex(fig_name: str, png_rel: str, caption: str, label: str) -> None:
    p = generated_dir() / f"{fig_name}.tex"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(
        "\\begin{figure}[H]\n"
        "\\centering\n"
        f"\\includegraphics[width=0.92\\linewidth]{{{png_rel}}}\n"
        f"\\caption{{{caption}}}\n"
        f"\\label{{{label}}}\n"
        "\\end{figure}\n",
        encoding="utf-8",
    )


def main() -> None:
    ap = argparse.ArgumentParser(description="Pressure + multifractal (Legendre) spectrum for Fold collision moments.")
    ap.add_argument("--m-min", type=int, default=24, help="Minimum m in regression window.")
    ap.add_argument("--m-max", type=int, default=30, help="Maximum m in regression window.")
    ap.add_argument("--q-max", type=int, default=60, help="Maximum Renyi order q to compute (>=2).")
    ap.add_argument("--use-exact-up-to", type=int, default=17, help="Override regression by exact r_q for q<=this.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_pressure_multifractal_q60.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--png-rq",
        type=str,
        default=str(export_dir() / "fold_collision_pressure_multifractal_q60_rq.png"),
        help="Output PNG path (r_q^{1/q}).",
    )
    ap.add_argument(
        "--png-pressure",
        type=str,
        default=str(export_dir() / "fold_collision_pressure_multifractal_q60_pressure.png"),
        help="Output PNG path (pressure).",
    )
    ap.add_argument(
        "--png-falpha",
        type=str,
        default=str(export_dir() / "fold_collision_pressure_multifractal_q60_falpha.png"),
        help="Output PNG path (f(gamma)).",
    )
    args = ap.parse_args()

    m_min = int(args.m_min)
    m_max = int(args.m_max)
    q_max = int(args.q_max)
    if m_min < 2 or m_max < m_min:
        raise SystemExit("Require m_max >= m_min >= 2")
    if q_max < 2:
        raise SystemExit("Require q_max >= 2")

    prog = Progress("fold-pressure-mf", every_seconds=20.0)

    ms = list(range(m_min, m_max + 1))
    qs = list(range(2, q_max + 1))

    # Compute log S_q(m) for all q on the m window.
    logS: Dict[int, Dict[int, float]] = {q: {} for q in qs}
    for m in ms:
        vals, freq = counts_mod_fib_hist(m, prog=prog)
        log_mom = log_moments_from_hist(vals, freq, q_max=q_max)
        for q in qs:
            logS[q][m] = log_mom[q]
        prog.tick(f"m={m} done (hist size={len(vals)})")
        print(f"[fold-pressure-mf] m={m} done (mod=F_{{m+2}}={int(np.sum(freq))})", flush=True)

    # Regression slope -> log r_q estimate.
    xs = np.array(ms, dtype=np.float64)
    log_rq_est: Dict[int, float] = {}
    for q in qs:
        ys = np.array([logS[q][m] for m in ms], dtype=np.float64)
        slope, _intercept = np.polyfit(xs, ys, deg=1)
        log_rq_est[q] = float(slope)

    # Optional exact overrides (q<=17 are paper-canonical).
    use_exact_up_to = int(args.use_exact_up_to)
    exact_log_rq: Dict[int, float] = {}
    if use_exact_up_to >= 2:
        import exp_fold_collision_renyi_spectrum as rs

        for q in range(2, min(use_exact_up_to, q_max) + 1):
            rq: float | None = None
            if q == 2:
                rq = float(rs.perron_root_r2())
            elif q == 3:
                rq = float(rs.perron_root_r3())
            elif q == 4:
                rq = float(rs.perron_root_r4())
            elif q in rs.PRECOMPUTED_RQ:
                rq = float(rs.PRECOMPUTED_RQ[q])
            if rq is not None and rq > 0:
                exact_log_rq[q] = math.log(rq)

    log2 = math.log(2.0)

    rows: List[Row] = []
    for q in qs:
        log_rq = exact_log_rq.get(q, log_rq_est[q])
        rq = math.exp(log_rq)
        Pq = log_rq - float(q) * log2
        hq = float(q) * log2 - log_rq
        rows.append(
            Row(
                q=int(q),
                log_rq=float(log_rq),
                r_q=float(rq),
                pressure_Pq=float(Pq),
                h_q=float(hq),
                rq_pow_1_over_q=float(rq ** (1.0 / float(q))),
                note=("exact" if q in exact_log_rq else f"regress m∈[{m_min},{m_max}]"),
            )
        )

    # Lower convex envelope of (q, P(q)).
    pts = [(r.q, float(r.pressure_Pq)) for r in rows]
    hull = lower_convex_hull(pts)
    hull_qs = [x for (x, _y) in hull]
    hull_P = [y for (_x, y) in hull]
    P_env = eval_piecewise_linear(hull, [r.q for r in rows])

    # Discrete Legendre spectrum from log r_q.
    phi_q = np.array([r.log_rq for r in rows], dtype=np.float64)
    q_arr = np.array([r.q for r in rows], dtype=np.float64)
    # alpha-range from finite differences of phi(q).
    if len(rows) >= 2:
        slopes = np.diff(phi_q) / np.diff(q_arr)
        a_min = float(np.min(slopes))
        a_max = float(np.max(slopes))
    else:
        a_min, a_max = 0.0, 1.0
    # Guard against degeneracy.
    if not (a_max > a_min + 1e-15):
        a_min -= 1e-3
        a_max += 1e-3
    alpha_grid = np.linspace(a_min, a_max, num=600, dtype=np.float64)
    # I(alpha) = max_q (q*alpha - phi(q))
    # Vectorize: for each alpha, compute max over q.
    # shape: (len(alpha), len(q))
    vals = alpha_grid[:, None] * q_arr[None, :] - phi_q[None, :]
    I_alpha = np.max(vals, axis=1)
    f_alpha = math.log(float(PHI)) - I_alpha

    # --- Plots ---
    # 1) r_q^(1/q)
    fig1 = plt.figure(figsize=(7.8, 4.6))
    ax1 = fig1.add_subplot(1, 1, 1)
    qs_i = [r.q for r in rows]
    rq_1q = [r.rq_pow_1_over_q for r in rows]
    ax1.plot(qs_i, rq_1q, marker="o", linewidth=1.5, markersize=3.0, label=r"$r_q^{1/q}$")
    ax1.axhline(y=float(math.sqrt(float(PHI))), color="#444444", linestyle="--", linewidth=1.0, label=r"$\sqrt{\varphi}$")
    ax1.set_xlabel("q")
    ax1.set_ylabel(r"$r_q^{1/q}$")
    ax1.set_title(r"Fold collision: $r_q^{1/q}$ (regression window in m)")
    ax1.grid(True, alpha=0.25)
    ax1.legend(loc="best", fontsize=9)
    out_rq = Path(str(args.png_rq))
    out_rq.parent.mkdir(parents=True, exist_ok=True)
    fig1.tight_layout()
    fig1.savefig(out_rq, dpi=160)
    plt.close(fig1)

    # 2) pressure + convex envelope + linear bounds
    fig2 = plt.figure(figsize=(7.8, 4.6))
    ax2 = fig2.add_subplot(1, 1, 1)
    Pq = [r.pressure_Pq for r in rows]
    ax2.plot(qs_i, Pq, marker="o", linewidth=1.2, markersize=3.0, label="P(q) raw")
    ax2.plot(qs_i, P_env, linewidth=2.0, color="#E53935", label="lower convex envelope")
    # hull vertices
    ax2.scatter(hull_qs, hull_P, s=18, color="#E53935", zorder=3, label="hull vertices")

    logphi = math.log(float(PHI))
    # Lower bound: P(q) >= (1-q) log phi
    lb = [(1.0 - float(q)) * logphi for q in qs_i]
    # Upper bound: P(q) <= (1 + q/2) log phi - q log 2
    ub = [(1.0 + 0.5 * float(q)) * logphi - float(q) * log2 for q in qs_i]
    ax2.plot(qs_i, lb, linestyle="--", linewidth=1.0, color="#1E88E5", label=r"LB: $(1-q)\log\varphi$")
    ax2.plot(qs_i, ub, linestyle="--", linewidth=1.0, color="#43A047", label=r"UB: $(1+q/2)\log\varphi-q\log2$")

    ax2.set_xlabel("q")
    ax2.set_ylabel(r"$P(q)=\log r_q - q\log 2$")
    ax2.set_title("Fold collision pressure (discrete q)")
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="best", fontsize=8)
    out_P = Path(str(args.png_pressure))
    out_P.parent.mkdir(parents=True, exist_ok=True)
    fig2.tight_layout()
    fig2.savefig(out_P, dpi=160)
    plt.close(fig2)

    # 3) f(alpha)
    fig3 = plt.figure(figsize=(7.8, 4.6))
    ax3 = fig3.add_subplot(1, 1, 1)
    ax3.plot(alpha_grid, f_alpha, linewidth=1.6)
    ax3.set_xlabel(r"$\gamma$")
    ax3.set_ylabel(r"$f(\gamma)$")
    ax3.set_title(r"Discrete Legendre spectrum: $f(\gamma)=\log\varphi-\sup_q(q\gamma-\log r_q)$")
    ax3.grid(True, alpha=0.25)
    out_f = Path(str(args.png_falpha))
    out_f.parent.mkdir(parents=True, exist_ok=True)
    fig3.tight_layout()
    fig3.savefig(out_f, dpi=160)
    plt.close(fig3)

    # --- TeX wrappers ---
    # Use paths relative to the paper root in the includegraphics.
    # Convention in this paper: figures are included as artifacts/export/... .
    rel_rq = f"artifacts/export/{out_rq.name}"
    rel_P = f"artifacts/export/{out_P.name}"
    rel_f = f"artifacts/export/{out_f.name}"
    _write_fig_tex(
        "fig_fold_collision_pressure_multifractal_q60_rq",
        rel_rq,
        caption=r"Fold collision spectrum: $r_q^{1/q}$ estimated from a regression of $\log S_q(m)$ on $m$.",
        label="fig:fold-collision-rq-1q",
    )
    _write_fig_tex(
        "fig_fold_collision_pressure_multifractal_q60_pressure",
        rel_P,
        caption=r"Fold collision pressure $P(q)=\log r_q-q\log2$ with a discrete lower convex envelope and two linear bounds.",
        label="fig:fold-collision-pressure",
    )
    _write_fig_tex(
        "fig_fold_collision_pressure_multifractal_q60_falpha",
        rel_f,
        caption=r"Discrete Legendre spectrum $f(\gamma)=\log\varphi-\sup_q(q\gamma-\log r_q)$ built from the estimated $\log r_q$.",
        label="fig:fold-collision-falpha",
    )

    payload = {
        "m_min": m_min,
        "m_max": m_max,
        "q_max": q_max,
        "rows": [asdict(r) for r in rows],
        "pressure_hull_vertices": [{"q": int(q), "P": float(P)} for q, P in hull],
        "pressure_envelope": [{"q": int(r.q), "P_env": float(pe)} for r, pe in zip(rows, P_env, strict=True)],
        "alpha_grid": alpha_grid.tolist(),
        "I_alpha": I_alpha.tolist(),
        "f_alpha": f_alpha.tolist(),
        "notes": {
            "pressure_definition": "P(q)=log r_q - q log 2",
            "legendre_definition": "I(alpha)=sup_q(q alpha - log r_q), f(alpha)=log(phi)-I(alpha)",
            "exact_overrides_q_le": sorted(exact_log_rq.keys()),
        },
        "outputs": {
            "png_rq": str(out_rq),
            "png_pressure": str(out_P),
            "png_falpha": str(out_f),
            "fig_tex_rq": str(generated_dir() / "fig_fold_collision_pressure_multifractal_q60_rq.tex"),
            "fig_tex_pressure": str(generated_dir() / "fig_fold_collision_pressure_multifractal_q60_pressure.tex"),
            "fig_tex_falpha": str(generated_dir() / "fig_fold_collision_pressure_multifractal_q60_falpha.tex"),
        },
    }
    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[fold-pressure-mf] wrote {jout}", flush=True)
    print(f"[fold-pressure-mf] wrote {out_rq}", flush=True)
    print(f"[fold-pressure-mf] wrote {out_P}", flush=True)
    print(f"[fold-pressure-mf] wrote {out_f}", flush=True)


if __name__ == "__main__":
    main()

