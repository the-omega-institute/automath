#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Horizon spectral measure: endpoint window mass asymptotic (audit script).

Outputs:
- artifacts/export/horizon_mu_endpoint_window_asymptotic.json
- sections/generated/tab_horizon_mu_endpoint_window_asymptotic.tex

This script performs a small numerical audit of the endpoint-window mass law for the
horizon spectral measure μ_ζ on the unit circle, as described in
Theorem (endpoint-window asymptotic) in the appendix.

Under RH, the spectral measure admits an atomic representation supported on Cayley
images of critical-line zeros, with weights (1+γ^2)^{-1}. For an endpoint angular
window I_ε around ξ=-1, this yields

  μ_ζ(I_ε) = 2 * Σ_{γ >= cot(ε/2)} (1+γ^2)^{-1},

and the first-order asymptotic prediction is

  μ_ζ(I_ε) ~ (ε/(2π)) * (log(1/(π ε)) + 1),  ε↓0.

We approximate the sum using mpmath.zetazero(k) up to a cutoff γ_cut, and add a
small tail correction based on the Riemann–von Mangoldt main term.

Performance:
- Cache computed Im(ρ_k) values under artifacts/cache/zetazeros/ to avoid repeated
  zetazero() calls on reruns.
- Disable caching with OMEGA_ZETAZERO_NO_CACHE=1.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
import os
import json
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence

import mpmath as mp
import numpy as np

from common_paths import artifacts_dir, export_dir, generated_dir


@dataclass(frozen=True)
class Row:
    eps: mp.mpf
    T_eps: mp.mpf
    k_tail: int
    mu_trunc: mp.mpf
    mu_tail_est: mp.mpf
    mu_est: mp.mpf
    mu_asymp: mp.mpf


def _asymp_mu_eps(eps: mp.mpf) -> mp.mpf:
    # μ_ζ(I_ε) ~ (ε/(2π)) * (log(1/(π ε)) + 1)
    return (eps / (2 * mp.pi)) * (mp.log(1 / (mp.pi * eps)) + 1)


def _tail_estimate(gamma_cut: mp.mpf) -> mp.mpf:
    # Tail from γ_cut to ∞ using the first-order RVM-based approximation:
    # 2 ∫_{γ_cut}^∞ (1/(1+t^2)) dN(t) ~ (1/π) (log(γ_cut/(2π)) + 1)/γ_cut.
    return (1 / mp.pi) * (mp.log(gamma_cut / (2 * mp.pi)) + 1) / gamma_cut


def _zetazero_cache_paths() -> tuple[Path, Path]:
    d = artifacts_dir() / "cache" / "zetazeros"
    return d / "zetazero_gammas.npy", d / "zetazero_gammas_meta.json"


def _load_zetazero_cache() -> tuple[np.ndarray, Dict[str, object]] | None:
    cache_path, meta_path = _zetazero_cache_paths()
    if (not cache_path.is_file()) or (not meta_path.is_file()):
        return None
    try:
        arr = np.load(cache_path)
        if getattr(arr, "ndim", 0) != 1:
            return None
        meta_raw = json.loads(meta_path.read_text(encoding="utf-8"))
        meta: Dict[str, object] = meta_raw if isinstance(meta_raw, dict) else {}
        return arr.astype(np.float64, copy=False), meta
    except Exception:
        return None


def _write_zetazero_cache(gammas: np.ndarray, meta: Dict[str, object]) -> None:
    cache_path, meta_path = _zetazero_cache_paths()
    cache_path.parent.mkdir(parents=True, exist_ok=True)

    tmp_path = cache_path.with_suffix(".tmp.npy")
    tmp_meta = meta_path.with_suffix(".tmp.json")
    try:
        np.save(tmp_path, gammas.astype(np.float64, copy=False))
        tmp_path.replace(cache_path)
    finally:
        try:
            if tmp_path.exists():
                tmp_path.unlink()
        except Exception:
            pass

    try:
        tmp_meta.write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        tmp_meta.replace(meta_path)
    finally:
        try:
            if tmp_meta.exists():
                tmp_meta.unlink()
        except Exception:
            pass


def _compute_zeros_upto(gamma_max: mp.mpf, *, max_zeros: int) -> List[mp.mpf]:
    # Computing zeta zeros is expensive; cache the imaginary parts on disk.
    no_cache = os.environ.get("OMEGA_ZETAZERO_NO_CACHE", "").strip() in {
        "1",
        "true",
        "TRUE",
        "yes",
        "YES",
    }

    gamma_max_f = float(gamma_max)
    cache_hit = False

    gammas_all: List[float] = []
    if not no_cache:
        loaded = _load_zetazero_cache()
        if loaded is not None:
            arr, _meta = loaded
            if int(arr.size) > 0 and float(arr[0]) > 0:
                # Assume cache stores consecutive zeros starting from k=1.
                gammas_all = arr.tolist()
                cache_hit = True

    # Extend cache if needed.
    t0 = time.time()
    last_print = t0
    if gammas_all and (gammas_all[-1] < gamma_max_f):
        k0 = len(gammas_all) + 1
        print(
            f"[exp_horizon_mu_endpoint_window_asymptotic] cache_extend start_k={k0} cached_gamma_max~{gammas_all[-1]:.6g} target_gamma_max~{gamma_max_f:.6g}",
            flush=True,
        )
        for k in range(k0, max_zeros + 1):
            z = mp.zetazero(k)
            gamma = abs(mp.im(z))
            gf = float(gamma)
            gammas_all.append(gf)
            if gamma > gamma_max:
                # Cache one extra sentinel zero beyond gamma_max so that future runs
                # with the same cutoff do not need an additional zetazero() call.
                break
            now = time.time()
            if now - last_print >= 20.0:
                last_print = now
                dt = now - t0
                print(
                    f"[exp_horizon_mu_endpoint_window_asymptotic] zeros={k} gamma~{gf:.3f} elapsed_s={dt:.2f}",
                    flush=True,
                )
        else:
            # Reached max_zeros without crossing gamma_max.
            if gammas_all and (gammas_all[-1] <= gamma_max_f):
                raise RuntimeError(
                    "max_zeros reached before exceeding gamma_max; increase --max-zeros or lower --gamma-max"
                )

        if not no_cache:
            meta_out: Dict[str, object] = {
                "mp_dps": int(mp.mp.dps),
                "n_zeros": int(len(gammas_all)),
                "gamma_max_cached": float(gammas_all[-1]) if gammas_all else 0.0,
                "updated_at_unix": float(time.time()),
            }
            _write_zetazero_cache(np.asarray(gammas_all, dtype=np.float64), meta_out)

    # Compute from scratch if cache was empty/unavailable.
    if not gammas_all:
        gammas_all = []
        for k in range(1, max_zeros + 1):
            z = mp.zetazero(k)
            gamma = abs(mp.im(z))
            gf = float(gamma)
            gammas_all.append(gf)
            if gamma > gamma_max:
                # Cache one extra sentinel zero beyond gamma_max so that future runs
                # with the same cutoff do not need an additional zetazero() call.
                break
            now = time.time()
            if now - last_print >= 20.0:
                last_print = now
                dt = now - t0
                print(
                    f"[exp_horizon_mu_endpoint_window_asymptotic] zeros={k} gamma~{gf:.3f} elapsed_s={dt:.2f}",
                    flush=True,
                )
        else:
            if gammas_all and (gammas_all[-1] <= gamma_max_f):
                raise RuntimeError(
                    "max_zeros reached before exceeding gamma_max; increase --max-zeros or lower --gamma-max"
                )

        if not no_cache:
            meta_out = {
                "mp_dps": int(mp.mp.dps),
                "n_zeros": int(len(gammas_all)),
                "gamma_max_cached": float(gammas_all[-1]) if gammas_all else 0.0,
                "updated_at_unix": float(time.time()),
            }
            _write_zetazero_cache(np.asarray(gammas_all, dtype=np.float64), meta_out)

    if cache_hit and gammas_all and (gammas_all[-1] >= gamma_max_f):
        # Silent fast path: cache hit, no extension needed.
        pass

    # Return only the zeros up to the requested cutoff.
    # Use Python float cutoff for speed; convert to mp for downstream computations.
    j = bisect_right(gammas_all, gamma_max_f)
    out_f = gammas_all[:j]
    if not out_f:
        raise RuntimeError("no zeros collected (gamma_max too small?)")
    return [mp.mpf(str(g)) for g in out_f]


def _suffix_sums(weights: Sequence[mp.mpf]) -> List[mp.mpf]:
    out: List[mp.mpf] = [mp.mpf("0")] * (len(weights) + 1)
    s = mp.mpf("0")
    for i in range(len(weights) - 1, -1, -1):
        s += weights[i]
        out[i] = s
    out[len(weights)] = mp.mpf("0")
    return out


def _bisect_left_mpf(xs: Sequence[mp.mpf], x: mp.mpf) -> int:
    lo, hi = 0, len(xs)
    while lo < hi:
        mid = (lo + hi) // 2
        if xs[mid] < x:
            lo = mid + 1
        else:
            hi = mid
    return lo


def _write_table(rows: List[Row], gamma_cut: mp.mpf, n_zeros: int) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]\n")
    lines.append("\\centering\n")
    lines.append("\\small\n")
    lines.append("\\begin{tabular}{rrrrrr}\n")
    lines.append("\\toprule\n")
    lines.append(
        "$\\varepsilon$ & $T_{\\varepsilon}$ & $K$ & $\\widehat\\mu_{\\zeta}(I_{\\varepsilon})$ & asymp & ratio\\\\\n"
    )
    lines.append("\\midrule\n")
    for r in rows:
        eps = float(r.eps)
        T = float(r.T_eps)
        K = int(r.k_tail)
        mu_est = float(r.mu_est)
        mu_asymp = float(r.mu_asymp)
        ratio = float(r.mu_est / r.mu_asymp) if r.mu_asymp != 0 else float("nan")
        lines.append(
            f"{eps:.4g} & {T:.4g} & {K:d} & {mu_est:.6g} & {mu_asymp:.6g} & {ratio:.4g}\\\\\n"
        )
    lines.append("\\bottomrule\n")
    lines.append("\\end{tabular}\n")
    lines.append(
        "\\caption{端点角窗质量的数值审计：以临界线零点的 Cayley 原子化近似 $\\mu_{\\zeta}(I_{\\varepsilon})$，并与一阶渐近 $\\frac{\\varepsilon}{2\\pi}(\\log\\frac{1}{\\pi\\varepsilon}+1)$ 比较。表中 $K$ 为纳入求和的零点个数（满足 $\\gamma\\ge T_{\\varepsilon}$ 且 $\\gamma\\le \\gamma_{\\mathrm{cut}}$）。本表使用零点至截止 $\\gamma_{\\mathrm{cut}}\\approx "
        f"{float(gamma_cut):.6g}"
        "$（共 "
        f"{n_zeros}"
        " 个），并对 $\\gamma>\\gamma_{\\mathrm{cut}}$ 的尾项加入基于 Riemann--von Mangoldt 主项的一阶估计。}\n"
    )
    lines.append("\\label{tab:horizon-mu-endpoint-window-asymptotic}\n")
    lines.append("\\end{table}\n")

    p = generated_dir() / "tab_horizon_mu_endpoint_window_asymptotic.tex"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("".join(lines), encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Audit endpoint window mass asymptotic for horizon spectral measure."
    )
    ap.add_argument("--dps", type=int, default=80, help="mpmath decimal precision.")
    ap.add_argument(
        "--gamma-max",
        type=float,
        default=1500.0,
        help="Collect zeros up to this gamma cutoff (positive imaginary part).",
    )
    ap.add_argument(
        "--max-zeros",
        type=int,
        default=4000,
        help="Safety cap on number of zeros to query.",
    )
    ap.add_argument(
        "--eps",
        type=float,
        nargs="*",
        default=[0.25, 0.2, 0.15, 0.12, 0.1, 0.08, 0.06, 0.05],
        help="List of endpoint window half-widths ε (radians).",
    )
    args = ap.parse_args()

    mp.mp.dps = int(args.dps)
    gamma_max = mp.mpf(str(args.gamma_max))

    t0 = time.time()
    gammas = _compute_zeros_upto(gamma_max, max_zeros=int(args.max_zeros))
    gamma_cut = gammas[-1]
    n_zeros = len(gammas)
    weights = [mp.mpf("1") / (mp.mpf("1") + g * g) for g in gammas]
    suff = _suffix_sums(weights)
    tail = _tail_estimate(gamma_cut)

    rows: List[Row] = []
    for eps_f in list(args.eps):
        eps = mp.mpf(str(eps_f))
        if eps <= 0 or eps >= mp.pi:
            raise ValueError("eps must satisfy 0 < eps < pi")
        T_eps = mp.mpf("1") / mp.tan(eps / 2)
        i0 = _bisect_left_mpf(gammas, T_eps)
        k_tail = max(0, n_zeros - i0)
        mu_trunc = mp.mpf("2") * suff[i0]
        mu_est = mu_trunc + tail
        mu_asymp = _asymp_mu_eps(eps)
        rows.append(
            Row(
                eps=eps,
                T_eps=T_eps,
                k_tail=k_tail,
                mu_trunc=mu_trunc,
                mu_tail_est=tail,
                mu_est=mu_est,
                mu_asymp=mu_asymp,
            )
        )

    # Write JSON audit.
    out_json = export_dir() / "horizon_mu_endpoint_window_asymptotic.json"
    out_json.parent.mkdir(parents=True, exist_ok=True)
    payload: Dict[str, object] = {
        "mp_dps": int(args.dps),
        "gamma_max_requested": float(args.gamma_max),
        "gamma_cut": float(gamma_cut),
        "n_zeros": int(n_zeros),
        "tail_estimate": float(tail),
        "rows": [
            {
                "eps": float(r.eps),
                "T_eps": float(r.T_eps),
                "K": int(r.k_tail),
                "mu_trunc": float(r.mu_trunc),
                "mu_tail_est": float(r.mu_tail_est),
                "mu_est": float(r.mu_est),
                "mu_asymp": float(r.mu_asymp),
                "ratio": float(r.mu_est / r.mu_asymp) if r.mu_asymp != 0 else None,
            }
            for r in rows
        ],
        "elapsed_s": float(time.time() - t0),
    }
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Write TeX table.
    _write_table(rows, gamma_cut=gamma_cut, n_zeros=n_zeros)

    dt = time.time() - t0
    print(
        f"[exp_horizon_mu_endpoint_window_asymptotic] done zeros={n_zeros} gamma_cut={float(gamma_cut):.6g} elapsed_s={dt:.2f}",
        flush=True,
    )


if __name__ == "__main__":
    main()

