#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: DtN identity and Fourier–Laplace tomography fingerprint.

Outputs:
- artifacts/export/xi_horizon_dtn_fourier_laplace_audit.json
- sections/generated/tab_xi_horizon_dtn_fourier_laplace_audit.tex

This script provides a small, deterministic numerical audit for:
(i) Proposition `con:discussion-dtn-generator` (Dirichlet–to–Neumann map = -|D|).
(ii) Proposition `con:discussion-defect-measure-fourier-laplace` (Fourier–Laplace factorization).
"""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from typing import Dict, List, Sequence, Tuple

import numpy as np

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class DtnAudit:
    L: float
    N: int
    eps_y: float
    rel_l2_error: float
    rel_linf_error: float


@dataclass(frozen=True)
class FourierLaplaceAudit:
    t: float
    L: float
    N: int
    xi_targets: List[float]
    xi_used: List[float]
    max_rel_error: float
    max_abs_error: float


def _fmt_float(x: float, sig: int = 6) -> str:
    return f"{x:.{sig}g}"


def _centered_grid(L: float, N: int) -> Tuple[np.ndarray, float]:
    """Grid x in [-L, L) with N points (N even)."""
    if N % 2 != 0:
        raise ValueError("require N even")
    dx = (2.0 * float(L)) / float(N)
    x = (np.arange(N, dtype=np.float64) - (N // 2)) * dx
    return x, dx


def _fft_xi(N: int, dx: float) -> np.ndarray:
    """Angular frequencies xi_k compatible with numpy FFT conventions."""
    return 2.0 * math.pi * np.fft.fftfreq(N, d=dx)


def _apply_multiplier_centered(f: np.ndarray, mult: np.ndarray) -> np.ndarray:
    """Apply Fourier multiplier on a centered grid (periodic FFT model)."""
    f0 = np.fft.ifftshift(f)
    F = np.fft.fft(f0)
    out0 = np.fft.ifft(F * mult).real
    return np.fft.fftshift(out0)


def _l2_norm(f: np.ndarray, dx: float) -> float:
    return float(math.sqrt(float(np.sum(np.abs(f) ** 2)) * float(dx)))


def _dtn_audit() -> DtnAudit:
    # Large periodic box to suppress wrap-around for a rapidly decaying test function.
    L = 40.0
    N = 2**15
    eps_y = 1e-3

    x, dx = _centered_grid(L=L, N=N)
    f = np.exp(-(x**2))

    xi = _fft_xi(N=N, dx=dx)
    abs_xi = np.abs(xi)

    u_eps = _apply_multiplier_centered(f, np.exp(-eps_y * abs_xi))
    d_approx = (u_eps - f) / eps_y

    minus_absD_f = _apply_multiplier_centered(f, -abs_xi)

    err = d_approx - minus_absD_f
    rel_l2 = _l2_norm(err, dx=dx) / max(_l2_norm(minus_absD_f, dx=dx), 1e-300)
    rel_linf = float(np.max(np.abs(err))) / max(float(np.max(np.abs(minus_absD_f))), 1e-300)

    return DtnAudit(
        L=float(L),
        N=int(N),
        eps_y=float(eps_y),
        rel_l2_error=float(rel_l2),
        rel_linf_error=float(rel_linf),
    )


def _poisson_kernel(x: np.ndarray, t: float) -> np.ndarray:
    return (1.0 / math.pi) * (t / (x**2 + t**2))


def _lorentz_peak(x: np.ndarray, gamma: float, delta: float) -> np.ndarray:
    """4*delta / ((x-gamma)^2 + (1+delta)^2)."""
    a = 1.0 + float(delta)
    return (4.0 * float(delta)) / ((x - float(gamma)) ** 2 + a * a)


def _fourier_laplace_audit() -> FourierLaplaceAudit:
    # Periodic box for circular-convolution approximation (tails ~1/x^2).
    L = 4096.0
    N = 2**15
    t = 0.7

    # Deterministic discrete measure nu = sum w_j delta_{(gamma_j,delta_j)}.
    # These numbers are fixed to keep the audit stable across runs.
    atoms: Sequence[Tuple[float, float, float]] = [
        (-1.2, 0.15, 0.70),
        (0.5, 0.40, 1.10),
        (2.0, 0.05, 0.90),
    ]
    gammas = np.array([a[0] for a in atoms], dtype=np.float64)
    deltas = np.array([a[1] for a in atoms], dtype=np.float64)
    weights = np.array([a[2] for a in atoms], dtype=np.float64)

    x, dx = _centered_grid(L=L, N=N)

    H_nu = np.zeros_like(x)
    for (gamma, delta, w) in atoms:
        H_nu += float(w) * _lorentz_peak(x, gamma=gamma, delta=delta)

    P_t = _poisson_kernel(x, t=t)

    # Discrete circular convolution (Riemann-sum scaled).
    H0 = np.fft.ifftshift(H_nu)
    P0 = np.fft.ifftshift(P_t)
    conv0 = np.fft.ifft(np.fft.fft(H0) * np.fft.fft(P0)).real * dx
    H_nu_t = np.fft.fftshift(conv0)

    # Evaluate Fourier transform by discrete Riemann sums at a few target xi.
    xi_targets = [0.0, 0.5, 1.5, 3.0, 5.0]
    xi_used: List[float] = []
    abs_errs: List[float] = []
    rel_errs: List[float] = []

    for xi in xi_targets:
        xi = float(xi)
        # Numerical transform over [-L,L).
        Hhat_num = dx * np.sum(H_nu_t * np.exp(-1j * xi * x))
        # Analytic formula from Proposition `con:discussion-defect-measure-fourier-laplace`.
        s = abs(xi)
        coeff = weights * (deltas / (1.0 + deltas))
        Hhat_an = 4.0 * math.pi * math.exp(-t * s) * np.sum(
            coeff * np.exp(-(1.0 + deltas) * s) * np.exp(-1j * gammas * xi)
        )
        abs_err = float(abs(Hhat_num - Hhat_an))
        rel_err = abs_err / max(float(abs(Hhat_an)), 1e-300)
        xi_used.append(xi)
        abs_errs.append(abs_err)
        rel_errs.append(rel_err)

    return FourierLaplaceAudit(
        t=float(t),
        L=float(L),
        N=int(N),
        xi_targets=[float(v) for v in xi_targets],
        xi_used=xi_used,
        max_rel_error=float(max(rel_errs) if rel_errs else 0.0),
        max_abs_error=float(max(abs_errs) if abs_errs else 0.0),
    )


def _write_json(dtn: DtnAudit, fl: FourierLaplaceAudit) -> str:
    out: Dict[str, object] = {
        "dtn_audit": asdict(dtn),
        "fourier_laplace_audit": asdict(fl),
    }
    p = export_dir() / "xi_horizon_dtn_fourier_laplace_audit.json"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return str(p)


def _write_table(dtn: DtnAudit, fl: FourierLaplaceAudit) -> str:
    lines: List[str] = []
    lines.append("\\begin{table}[H]\n")
    lines.append("\\centering\n")
    lines.append("\\small\n")
    lines.append("\\begin{tabular}{l l r}\n")
    lines.append("\\toprule\n")
    lines.append("audit & metric & value\\\\\n")
    lines.append("\\midrule\n")

    lines.append(
        "DtN ($\\partial_y u(x,0)=-|D|f$)"
        " & $\\|\\mathrm{FD}_\\varepsilon+|D|\\|_{L^2}/\\||D|\\|_{L^2}$"
        f" & {_fmt_float(dtn.rel_l2_error, sig=6)}\\\\\n"
    )
    lines.append(
        "DtN ($\\partial_y u(x,0)=-|D|f$)"
        " & $\\|\\mathrm{FD}_\\varepsilon+|D|\\|_{L^\\infty}/\\||D|\\|_{L^\\infty}$"
        f" & {_fmt_float(dtn.rel_linf_error, sig=6)}\\\\\n"
    )
    lines.append(
        "Fourier--Laplace ($\\widehat{H_{\\nu,t}}$)"
        " & $\\max_{\\xi\\in\\Xi}|\\widehat{H}_{\\mathrm{num}}-\\widehat{H}_{\\mathrm{an}}|/|\\widehat{H}_{\\mathrm{an}}|$"
        f" & {_fmt_float(fl.max_rel_error, sig=6)}\\\\\n"
    )

    lines.append("\\bottomrule\n")
    lines.append("\\end{tabular}\n")
    lines.append(
        "\\caption{视界 Poisson 粗粒化的数值审计："
        "Dirichlet--to--Neumann 恒等式（命题~\\ref{con:discussion-dtn-generator}）与 "
        "二维缺陷测度的 Fourier--Laplace 指纹分解（命题~\\ref{con:discussion-defect-measure-fourier-laplace}）。}\n"
    )
    lines.append("\\label{tab:xi-horizon-dtn-fourier-laplace-audit}\n")
    lines.append("\\end{table}\n")

    p = generated_dir() / "tab_xi_horizon_dtn_fourier_laplace_audit.tex"
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text("".join(lines), encoding="utf-8")
    return str(p)


def main() -> None:
    dtn = _dtn_audit()
    fl = _fourier_laplace_audit()
    _write_json(dtn, fl)
    _write_table(dtn, fl)


if __name__ == "__main__":
    main()

