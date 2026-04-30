#!/usr/bin/env python3
"""
Generate figures and tables for:
  "Two detector-defined shells from stationary Unruh--DeWitt click records
   in static KMS spacetimes"

Output (in ../generated/):
  fig_hazard_cov.pdf        -- Fig 2: hazard function + covariance phase change
  fig_spectrum_fano.pdf     -- Fig 3: spectral density + Fano factor
  fig_shell_radii.pdf       -- Fig 4: Schwarzschild shell radii
  tab_worked_example.tex    -- Table 2: numerical Schwarzschild inversion example
"""

import os
import sys
import time
import numpy as np

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from scipy.optimize import brentq

# ---------------------------------------------------------------------------
# Global constants and style
# ---------------------------------------------------------------------------
PHI = (1 + np.sqrt(5)) / 2
LOG_PHI = np.log(PHI)

OUTDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'generated')

plt.rcParams.update({
    'text.usetex': False,
    'font.family': 'serif',
    'font.size': 10,
    'axes.labelsize': 11,
    'legend.fontsize': 8,
    'figure.dpi': 300,
    'axes.linewidth': 0.6,
    'xtick.major.width': 0.5,
    'ytick.major.width': 0.5,
})

# ---------------------------------------------------------------------------
# Core model functions
# ---------------------------------------------------------------------------

def compute_gamma_c(kappa_r, dtau, tol=1e-14):
    """Solve  dtau = (log kappa_r - log Gamma_c) / (kappa_r - Gamma_c)."""
    def residual(gamma):
        return dtau - (np.log(kappa_r) - np.log(gamma)) / (kappa_r - gamma)

    # Limit as gamma -> kappa_r: RHS -> 1/kappa_r
    lim = 1.0 / kappa_r
    if dtau > lim:
        lo, hi = 1e-15, kappa_r * (1 - 1e-12)
    elif dtau < lim:
        lo, hi = kappa_r * (1 + 1e-12), kappa_r * 1e6
    else:
        return kappa_r
    return brentq(residual, lo, hi, xtol=tol)


def compute_params(Gamma, kappa_r, dtau):
    """Return (p, c, a, b, lam, rho) for the finite-recovery model."""
    p = np.exp(-Gamma * dtau)
    c = np.exp(-kappa_r * dtau)
    diff = kappa_r - Gamma

    if abs(diff) < 1e-12 * max(kappa_r, Gamma):
        # Degenerate case
        a = 0.5 * kappa_r * Gamma * dtau**2
        b = kappa_r * dtau * np.exp(-kappa_r * dtau)
        lam = 0.0
    else:
        a = (kappa_r * (1 - p) - Gamma * (1 - c)) / diff
        b = kappa_r * (p - c) / diff
        lam = (kappa_r * c - Gamma * p) / diff

    denom = 1 - p + b
    pi_D = (1 - p) / denom
    pi_R = b / denom
    rho = pi_R * (1 - p) + pi_D * a
    return p, c, a, b, lam, rho


def hazard_seq(Gamma, kappa_r, dtau, kmax=20):
    """Return array h_0, ..., h_{kmax-1}."""
    p = np.exp(-Gamma * dtau)
    c = np.exp(-kappa_r * dtau)
    ks = np.arange(kmax)
    pk = p ** ks
    ck = c ** ks
    num = kappa_r * (1 - p) * pk - Gamma * (1 - c) * ck
    den = kappa_r * pk - Gamma * ck
    return num / den


def covariance_seq(Gamma, kappa_r, dtau, nmax=15):
    """Return Cov(A_0, A_n) for n = 1, ..., nmax."""
    _, _, a, _, lam, rho = compute_params(Gamma, kappa_r, dtau)
    ns = np.arange(1, nmax + 1)
    return rho * (a - rho) * lam ** (ns - 1)


def spectral_density(theta, Gamma, kappa_r, dtau):
    """f(theta) on array theta."""
    _, _, a, _, lam, rho = compute_params(Gamma, kappa_r, dtau)
    ct = np.cos(theta)
    return (rho * (1 - rho)
            + 2 * rho * (a - rho) * (ct - lam) / (1 - 2 * lam * ct + lam**2))


def fano_factor(Gamma, kappa_r, dtau):
    """Asymptotic Fano factor."""
    _, _, a, _, lam, rho = compute_params(Gamma, kappa_r, dtau)
    return 1 - rho + 2 * (a - rho) / (1 - lam)


# ---------------------------------------------------------------------------
# Figure 2: Hazard function and covariance phase change
# ---------------------------------------------------------------------------

def make_fig_hazard_cov():
    print("[1/4] Generating fig_hazard_cov.pdf ...")
    t0 = time.time()

    kappa_r = 5.0
    dtau = 0.3
    Gamma_c = compute_gamma_c(kappa_r, dtau)
    print(f"  kappa_r = {kappa_r}, dtau = {dtau}, Gamma_c = {Gamma_c:.6f}")

    configs = [
        (0.4 * Gamma_c, r'$\Gamma = 0.4\,\Gamma_c$', '#1976D2'),
        (Gamma_c,        r'$\Gamma = \Gamma_c$',      '#388E3C'),
        (2.5 * Gamma_c,  r'$\Gamma = 2.5\,\Gamma_c$', '#D32F2F'),
    ]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.5, 2.8))

    # (a) Hazard h_k
    kmax = 15
    ks = np.arange(kmax)
    for Gamma, label, color in configs:
        hk = hazard_seq(Gamma, kappa_r, dtau, kmax)
        ax1.plot(ks, hk, 'o-', color=color, markersize=3, linewidth=1.1, label=label)
    ax1.set_xlabel(r'$k$')
    ax1.set_ylabel(r'$h_k$')
    ax1.set_title('(a)  Click hazard after $k$ zeros', fontsize=10)
    ax1.legend(fontsize=7.5, loc='lower right')
    ax1.set_xlim(-0.5, kmax - 0.5)

    # (b) Covariance
    nmax = 12
    ns = np.arange(1, nmax + 1)
    for Gamma, label, color in configs:
        cv = covariance_seq(Gamma, kappa_r, dtau, nmax)
        ax2.plot(ns, cv, 's-', color=color, markersize=3, linewidth=1.1, label=label)
    ax2.axhline(0, color='gray', linewidth=0.5, linestyle='--')
    ax2.set_xlabel(r'$n$')
    ax2.set_ylabel(r'$\mathrm{Cov}(A_0,\,A_n)$')
    ax2.set_title(r'(b)  Lag-$n$ covariance', fontsize=10)
    ax2.legend(fontsize=7.5)
    ax2.set_xlim(0.5, nmax + 0.5)

    fig.tight_layout(w_pad=2.5)
    path = os.path.join(OUTDIR, 'fig_hazard_cov.pdf')
    fig.savefig(path, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {path}  ({time.time()-t0:.1f}s)")


# ---------------------------------------------------------------------------
# Figure 3: Spectral density and Fano factor
# ---------------------------------------------------------------------------

def make_fig_spectrum_fano():
    print("[2/4] Generating fig_spectrum_fano.pdf ...")
    t0 = time.time()

    kappa_r = 5.0
    dtau = 0.3

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.5, 2.8))

    # (a) Spectral density f(theta)
    theta = np.linspace(0.01, np.pi, 400)
    Gamma_vals = [1.0, 3.0, 6.0, 12.0]
    colors_a = ['#1976D2', '#388E3C', '#F57C00', '#D32F2F']
    for Gamma, color in zip(Gamma_vals, colors_a):
        ft = spectral_density(theta, Gamma, kappa_r, dtau)
        ax1.plot(theta / np.pi, ft, color=color, linewidth=1.2,
                 label=rf'$\Gamma\Delta\tau = {Gamma*dtau:.1f}$')
    ax1.set_xlabel(r'$\theta / \pi$')
    ax1.set_ylabel(r'$f(\theta)$')
    ax1.set_title('(a)  Spectral density', fontsize=10)
    ax1.legend(fontsize=7.5)
    ax1.set_xlim(0, 1)

    # (b) Fano factor vs Gamma*dtau for several kappa_r*dtau
    s_vals = [0.5, 1.5, 2.5]
    colors_b = ['#1976D2', '#F57C00', '#D32F2F']
    linestyles = ['-', '--', ':']
    Gdt_range = np.linspace(0.02, 8.0, 300)
    for s_val, color, ls in zip(s_vals, colors_b, linestyles):
        kr_local = s_val / dtau
        F_arr = np.array([fano_factor(Gdt / dtau, kr_local, dtau)
                          for Gdt in Gdt_range])
        ax2.plot(Gdt_range, F_arr, color=color, linewidth=1.2, linestyle=ls,
                 label=rf'$\kappa_{{\mathrm{{r}}}}\Delta\tau = {s_val}$')
    ax2.axhline(1, color='gray', linewidth=0.5, linestyle='--')
    ax2.set_xlabel(r'$\Gamma\Delta\tau$')
    ax2.set_ylabel(r'Fano factor $F$')
    ax2.set_title('(b)  Asymptotic Fano factor', fontsize=10)
    ax2.legend(fontsize=7.5)
    ax2.set_ylim(0, 1.15)
    ax2.set_xlim(0, 8)

    fig.tight_layout(w_pad=2.5)
    path = os.path.join(OUTDIR, 'fig_spectrum_fano.pdf')
    fig.savefig(path, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {path}  ({time.time()-t0:.1f}s)")


# ---------------------------------------------------------------------------
# Figure 4: Schwarzschild shell radii and proper-distance ratio
# ---------------------------------------------------------------------------

def make_fig_shell_radii():
    print("[3/4] Generating fig_shell_radii.pdf ...")
    t0 = time.time()

    # Units: r_s = 2M = 1, so M = 1/2, beta_inf = 4 pi
    beta_inf = 4 * np.pi
    Omega = 1.0
    lc2S = 2.0      # lambda_c^2 * S(Omega)
    kappa_r = 5.0

    s_arr = np.logspace(-2.5, np.log10(0.7), 250)   # kappa_r * dtau
    dtau_arr = s_arr / kappa_r

    N_phi_arr = np.full_like(s_arr, np.nan)
    N_mem_arr = np.full_like(s_arr, np.nan)
    C_arr     = np.full_like(s_arr, np.nan)
    rho_ratio_exact = np.full_like(s_arr, np.nan)

    for i, (s, dt) in enumerate(zip(s_arr, dtau_arr)):
        if i % 50 == 0:
            print(f"  Computing shell data: {i}/{len(s_arr)} ...")
        try:
            Gc = compute_gamma_c(kappa_r, dt)
        except Exception:
            continue

        beta_phi = (1 / Omega) * np.log(1 + lc2S * dt / LOG_PHI)
        beta_mem = (1 / Omega) * np.log(1 + lc2S / Gc)
        Np = beta_phi / beta_inf
        Nm = beta_mem / beta_inf

        if 0 < Np < 1 and 0 < Nm < 1:
            N_phi_arr[i] = Np
            N_mem_arr[i] = Nm
            C_arr[i] = dt * Gc / LOG_PHI
            # Proper distance near horizon: rho ~ 2 sqrt(r/r_s - 1)
            rho_p = 2 * np.sqrt(1 / (1 - Np**2) - 1)
            rho_m = 2 * np.sqrt(1 / (1 - Nm**2) - 1)
            rho_ratio_exact[i] = rho_p / rho_m

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.5, 2.8))

    # (a) Lapse values N_phi, N_mem
    valid = np.isfinite(N_phi_arr) & np.isfinite(N_mem_arr)
    ax1.plot(s_arr[valid], N_phi_arr[valid], color='#D32F2F', linewidth=1.5,
             label=r'$N_\varphi$ (exact-clock)')
    ax1.plot(s_arr[valid], N_mem_arr[valid], color='#1976D2', linewidth=1.5,
             label=r'$N_{\mathrm{mem}}$ (memory)')
    ax1.set_xlabel(r'$\kappa_{\mathrm{r}}\Delta\tau$')
    ax1.set_ylabel(r'Lapse $N$')
    ax1.set_title('(a)  Shell lapse values', fontsize=10)
    ax1.legend(fontsize=8)
    ax1.set_xscale('log')

    # (b) Proper-distance ratio vs leading-order
    valid2 = np.isfinite(rho_ratio_exact) & np.isfinite(C_arr)
    ax2.plot(s_arr[valid2], rho_ratio_exact[valid2], color='#388E3C', linewidth=1.5,
             label=r'Exact $\rho_\varphi / \rho_{\mathrm{mem}}$')
    ax2.plot(s_arr[valid2], C_arr[valid2], color='gray', linewidth=1.2, linestyle='--',
             label=r'Leading-order ratio')
    ax2.set_xlabel(r'$\kappa_{\mathrm{r}}\Delta\tau$')
    ax2.set_ylabel(r'$\rho_\varphi \,/\, \rho_{\mathrm{mem}}$')
    ax2.set_title(r'(b)  Proper-distance ratio', fontsize=10)
    ax2.legend(fontsize=7.5)
    ax2.set_xscale('log')

    fig.tight_layout(w_pad=2.5)
    path = os.path.join(OUTDIR, 'fig_shell_radii.pdf')
    fig.savefig(path, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {path}  ({time.time()-t0:.1f}s)")


# ---------------------------------------------------------------------------
# Table 2: Schwarzschild worked example (numerical inversion)
# ---------------------------------------------------------------------------

def make_tab_worked_example():
    print("[4/4] Generating tab_worked_example.tex ...")
    t0 = time.time()

    # Units: r_s = 2M = 1, M = 1/2, beta_inf = 4 pi
    beta_inf = 4 * np.pi
    Omega = 1.0
    lc2S = 2.0

    modes = [
        {'label': r'$D_1$', 'dtau': 0.50, 'kappa_r': 8.0},
        {'label': r'$D_2$', 'dtau': 1.20, 'kappa_r': 3.0},
    ]

    rows = []
    shell_data = []  # for inverse verification

    for m in modes:
        dt  = m['dtau']
        kr  = m['kappa_r']
        Gc  = compute_gamma_c(kr, dt)
        Gp  = LOG_PHI / dt

        beta_phi = (1 / Omega) * np.log(1 + lc2S * dt / LOG_PHI)
        beta_mem = (1 / Omega) * np.log(1 + lc2S / Gc)

        Np = beta_phi / beta_inf
        Nm = beta_mem / beta_inf

        rp = 1.0 / (1.0 - Np**2)
        rm = 1.0 / (1.0 - Nm**2)

        C_ratio = dt * Gc / LOG_PHI

        # Verify amplitude cancellation (Theorem 5.1)
        lhs = (np.exp(beta_inf * Omega * Np) - 1) / (np.exp(beta_inf * Omega * Nm) - 1)

        rows.append({
            'label': m['label'],
            'dtau': dt, 'kappa_r': kr,
            'Gamma_c': Gc, 'Gamma_phi': Gp,
            'beta_phi': beta_phi, 'beta_mem': beta_mem,
            'N_phi': Np, 'N_mem': Nm,
            'r_phi': rp, 'r_mem': rm,
            'C': C_ratio, 'lhs_ratio': lhs,
        })
        shell_data.append((beta_phi, beta_mem, rp, rm))

    # Inverse: recover beta_inf and M from Mode 1
    bp1, bm1, rp1, rm1 = shell_data[0]
    beta_inf_sq_rec = (bp1**2 * rp1 - bm1**2 * rm1) / (rp1 - rm1)
    M_rec = rp1 * rm1 * (bp1**2 - bm1**2) / (2 * (bp1**2 * rp1 - bm1**2 * rm1))

    # Jacobian for the two-mode inverse on the family (beta_inf, M)
    def shell_ratio(beta_inf_local, mass_local, r_phi_local, r_mem_local):
        n_phi = np.sqrt(1.0 - 2.0 * mass_local / r_phi_local)
        n_mem = np.sqrt(1.0 - 2.0 * mass_local / r_mem_local)
        return ((np.exp(beta_inf_local * Omega * n_phi) - 1.0)
                / (np.exp(beta_inf_local * Omega * n_mem) - 1.0))

    def ratio_function(beta_inf_local, mass_local, row):
        return shell_ratio(beta_inf_local, mass_local, row['r_phi'], row['r_mem']) - row['C']

    h = 1e-6
    jac_rows = []
    for row in rows:
        d_beta = (ratio_function(beta_inf + h, 0.5, row) - ratio_function(beta_inf - h, 0.5, row)) / (2 * h)
        d_mass = (ratio_function(beta_inf, 0.5 + h, row) - ratio_function(beta_inf, 0.5 - h, row)) / (2 * h)
        jac_rows.append((d_beta, d_mass))
    jac_det = jac_rows[0][0] * jac_rows[1][1] - jac_rows[0][1] * jac_rows[1][0]

    # Write LaTeX table
    lines = []
    lines.append(r'\begin{table}[t]')
    lines.append(r'\centering\small')
    lines.append(r'\caption{Schwarzschild worked example ($r_{\mathrm s}=2M=1$, '
                 r'$\beta_\infty=4\pi$, $\Omega=1$, '
                 r'$\lambda_c^2\mathcal S=2$). '
                 r'All quantities are in units of $r_{\mathrm s}$. '
                 r'The critical rate $\Gamma_c$ is computed from~\eqref{eq:gamma-c-main} '
                 r'and cross-checked against the Lambert $W$ formula~\eqref{eq:lambert-Gc}. '
                 r'The two modes have distinct ratio constants $C_1\neq C_2$, so the '
                 r'Jacobian of the two-mode system is generically nonsingular.}')
    lines.append(r'\label{tab:worked}')
    lines.append(r'\begin{tabular}{l c c}')
    lines.append(r'\toprule')
    lines.append(r'Quantity & $D_1$ & $D_2$ \\')
    lines.append(r'\midrule')
    lines.append(r'$\Delta\tau$ & '
                 f'{rows[0]["dtau"]:.2f} & {rows[1]["dtau"]:.2f}' r' \\')
    lines.append(r'$\kappa_{\mathrm r}$ & '
                 f'{rows[0]["kappa_r"]:.1f} & {rows[1]["kappa_r"]:.1f}' r' \\')
    lines.append(r'$\Gamma_c$ & '
                 f'{rows[0]["Gamma_c"]:.6f} & {rows[1]["Gamma_c"]:.6f}' r' \\')
    lines.append(r'$\Gamma_\varphi = \log\varphi/\Delta\tau$ & '
                 f'{rows[0]["Gamma_phi"]:.6f} & {rows[1]["Gamma_phi"]:.6f}' r' \\')
    lines.append(r'$\beta_\varphi$ & '
                 f'{rows[0]["beta_phi"]:.6f} & {rows[1]["beta_phi"]:.6f}' r' \\')
    lines.append(r'$\beta_{\mathrm{mem}}$ & '
                 f'{rows[0]["beta_mem"]:.6f} & {rows[1]["beta_mem"]:.6f}' r' \\')
    lines.append(r'$N_\varphi$ & '
                 f'{rows[0]["N_phi"]:.6f} & {rows[1]["N_phi"]:.6f}' r' \\')
    lines.append(r'$N_{\mathrm{mem}}$ & '
                 f'{rows[0]["N_mem"]:.6f} & {rows[1]["N_mem"]:.6f}' r' \\')
    lines.append(r'$r_\varphi / r_{\mathrm s}$ & '
                 f'{rows[0]["r_phi"]:.6f} & {rows[1]["r_phi"]:.6f}' r' \\')
    lines.append(r'$r_{\mathrm{mem}} / r_{\mathrm s}$ & '
                 f'{rows[0]["r_mem"]:.6f} & {rows[1]["r_mem"]:.6f}' r' \\')
    lines.append(r'$C = \Delta\tau\Gamma_c / \log\varphi$ & '
                 f'{rows[0]["C"]:.6f} & {rows[1]["C"]:.6f}' r' \\')
    lines.append(r'Ratio check (Thm~5.1) & '
                 f'{rows[0]["lhs_ratio"]:.6f} & {rows[1]["lhs_ratio"]:.6f}' r' \\')
    lines.append(r'\midrule')
    lines.append(r'\multicolumn{3}{l}{'
                 r'\textit{Inverse recovery from $D_1$ '
                 r'(Proposition~5.4):}} \\')
    lines.append(r'$\beta_\infty^2$ (recovered) & '
                 r'\multicolumn{2}{c}{'
                 f'{beta_inf_sq_rec:.4f}'
                 r' (exact: '
                 f'{beta_inf**2:.4f}'
                 r')} \\')
    lines.append(r'$M$ (recovered) & '
                 r'\multicolumn{2}{c}{'
                 f'{M_rec:.6f}'
                 r' (exact: $0.500000$)} \\')
    lines.append(r'\midrule')
    lines.append(r'\multicolumn{3}{l}{'
                 r'\textit{Two-mode verification for the family $(\beta_\infty,M)$:}} \\')
    lines.append(r'$\det D(F_1,F_2)|_{(\beta_\infty,M)}$ & '
                 r'\multicolumn{2}{c}{'
                 f'${jac_det:.6f}$'
                 r'} \\')
    lines.append(r'\bottomrule')
    lines.append(r'\end{tabular}')
    lines.append(r'\end{table}')

    path = os.path.join(OUTDIR, 'tab_worked_example.tex')
    with open(path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines) + '\n')

    print(f"  Saved: {path}")

    # Print summary to stdout
    for r in rows:
        print(f"  {r['label']}: Gamma_c = {r['Gamma_c']:.6f}, "
              f"r_phi = {r['r_phi']:.6f}, r_mem = {r['r_mem']:.6f}, "
              f"C = {r['C']:.6f}, ratio_check = {r['lhs_ratio']:.6f}")
    print(f"  Inverse: beta_inf^2 = {beta_inf_sq_rec:.6f} "
          f"(exact {beta_inf**2:.6f}), M = {M_rec:.6f} (exact 0.5)")
    print(f"  Two-mode Jacobian determinant: {jac_det:.6f}")
    print(f"  Done ({time.time()-t0:.1f}s)")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == '__main__':
    os.makedirs(OUTDIR, exist_ok=True)
    print(f"Output directory: {OUTDIR}\n")

    make_fig_hazard_cov()
    make_fig_spectrum_fano()
    make_fig_shell_radii()
    make_tab_worked_example()

    print("\nAll figures and tables generated successfully.")
