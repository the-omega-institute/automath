#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: offline-zero Neumann trace formulas.

This script numerically checks (on a finite grid):
- Explicit shift formula for N^{(a)} (depth translation).
- L^2 interaction formula for N.
- Band-limited backward estimate (noise-free truncation term behaviour).

The checks are numerical sanity tests; the paper statements are exact.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

import numpy as np


def _paper_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _export_path() -> Path:
    return _paper_root() / "artifacts" / "export" / "xi_offline_neumann_trace_cauchy_semigroup_audit.json"


def P(a: float, x: np.ndarray) -> np.ndarray:
    return (1.0 / np.pi) * (a / (x * x + a * a))


@dataclass(frozen=True)
class Zero:
    gamma: float
    delta: float
    m: int


def N_of_x(xs: np.ndarray, zeros: list[Zero]) -> np.ndarray:
    out = np.zeros_like(xs, dtype=float)
    for z in zeros:
        out += 2.0 * z.m * (z.delta / ((xs - z.gamma) ** 2 + z.delta**2))
    return out


def N_shift(xs: np.ndarray, zeros: list[Zero], a: float) -> np.ndarray:
    out = np.zeros_like(xs, dtype=float)
    for z in zeros:
        out += 2.0 * z.m * ((z.delta + a) / ((xs - z.gamma) ** 2 + (z.delta + a) ** 2))
    return out


def conv_fft(f: np.ndarray, g: np.ndarray, dx: float) -> np.ndarray:
    """
    Circular convolution using FFT on a centered grid.

    Input f,g are sampled on a symmetric grid xs in [-L, L) (i.e. x=0 is near the middle index).
    FFT assumes x=0 at index 0, hence we ifftshift before FFT and fftshift after iFFT.
    """
    f0 = np.fft.ifftshift(f)
    g0 = np.fft.ifftshift(g)
    F = np.fft.rfft(f0)
    G = np.fft.rfft(g0)
    h0 = np.fft.irfft(F * G, n=f.size) * dx
    return np.fft.fftshift(h0)


def rfft_centered(f: np.ndarray, dx: float) -> np.ndarray:
    """rFFT of centered-grid samples with continuous FT scaling."""
    f0 = np.fft.ifftshift(f)
    return np.fft.rfft(f0) * dx


def l2_sq(xs: np.ndarray, f: np.ndarray) -> float:
    dx = xs[1] - xs[0]
    return float(np.sum(f * f) * dx)


def main() -> None:
    # Synthetic finite configuration (moderate separation).
    zeros = [
        Zero(gamma=-4.0, delta=0.35, m=1),
        Zero(gamma=1.5, delta=0.8, m=2),
        Zero(gamma=7.0, delta=0.5, m=1),
    ]

    # Grid.
    L = 200.0
    n = 2**15
    xs = np.linspace(-L, L, n, endpoint=False)
    dx = xs[1] - xs[0]

    N = N_of_x(xs, zeros)

    # Check shift formula via convolution.
    a = 1.25
    kernel = P(a, xs)  # centered at 0 on circular grid
    N_conv = conv_fft(N, kernel, dx=dx)
    N_explicit = N_shift(xs, zeros, a=a)

    # L2 interaction closed form.
    l2_num = l2_sq(xs, N)
    l2_formula = 0.0
    for zj in zeros:
        for zk in zeros:
            a_jk = zj.delta + zk.delta
            b_jk = zj.gamma - zk.gamma
            l2_formula += (zj.m * zk.m) * (a_jk / (b_jk * b_jk + a_jk * a_jk))
    l2_formula *= 4.0 * np.pi

    # Band-limited tail bound (noise-free): compare numeric tail L2 against exp(-delta_min*Lambda).
    delta_min = min(z.delta for z in zeros)
    M = float(np.sum([2.0 * np.pi * z.m for z in zeros]))  # L1 mass

    # Angular frequencies for rFFT bins.
    freqs = np.fft.rfftfreq(n, d=dx) * 2.0 * np.pi
    dxi = 2.0 * np.pi / (n * dx)
    Nhat = rfft_centered(N, dx=dx)

    def tail_l2(Lambda: float) -> float:
        mask = np.abs(freqs) > Lambda
        # Approximate Plancherel: ||f||_2^2 = (1/2π) ∫ |f̂(ξ)|^2 dξ
        return float(np.sqrt((1.0 / (2.0 * np.pi)) * np.sum(np.abs(Nhat[mask]) ** 2) * dxi))

    Lambdas = [0.5, 1.0, 2.0, 3.0, 4.0]
    tail_checks = []
    for Lam in Lambdas:
        tail = tail_l2(Lam)
        bound = (M / np.sqrt(np.pi * delta_min)) * np.exp(-delta_min * Lam)
        tail_checks.append({"Lambda": Lam, "tail_l2": tail, "bound": bound, "ratio": tail / bound})

    out = {
        "grid": {"L": L, "n": n, "dx": dx},
        "zeros": [{"gamma": z.gamma, "delta": z.delta, "m": z.m} for z in zeros],
        "shift_check": {
            "a": a,
            "rel_l2_error": float(np.sqrt(l2_sq(xs, N_conv - N_explicit)) / np.sqrt(l2_sq(xs, N_explicit))),
        },
        "l2_interaction": {
            "l2_sq_numeric": l2_num,
            "l2_sq_formula": float(l2_formula),
            "rel_error": float(abs(l2_num - l2_formula) / max(1.0, abs(l2_formula))),
        },
        "tail_bounds": tail_checks,
    }

    p = _export_path()
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()

