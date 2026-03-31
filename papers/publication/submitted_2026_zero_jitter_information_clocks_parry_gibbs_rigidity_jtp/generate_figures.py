"""Generate figures for the paper:
Tilt Dynamics of Cylinder Information and the Parry Measure
on the Golden-Mean Shift.

Outputs:
  fig_jitter_tilt.pdf  -- two-panel figure (sigma^2 and tilt trajectories)
"""

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MultipleLocator
import os

print("Starting figure generation...")

# --- constants ---
phi = (1 + np.sqrt(5)) / 2
p_phi = 1.0 / phi  # Parry point

# --- panel (a): asymptotic jitter sigma^2(p) ---
p = np.linspace(0.01, 0.99, 800)
L = np.log((1 - p) / p**2)
sigma2 = p * (1 - p) / (2 - p)**3 * L**2

# entropy deficit Delta h(p) = log(phi) - h(p)
H2 = -p * np.log(p) - (1 - p) * np.log(1 - p)
h = H2 / (2 - p)
Delta_h = np.log(phi) - h

print("  Panel (a): sigma^2(p) computed")

# --- panel (b): tilt trajectories T_t^n(p) for fixed t ---
t_fixed = 0.5
p_initials = [0.05, 0.15, 0.30, 0.50, 0.70, 0.85, 0.95]
n_iters = 15


def L_coord(p_val):
    return np.log((1 - p_val) / p_val**2)


def L_inv(u):
    """Solve L(p) = u for p in (0,1), i.e., (1-p)/p^2 = e^u."""
    eu = np.exp(u)
    # p^2 * eu + p - 1 = 0  =>  p = (-1 + sqrt(1 + 4*eu)) / (2*eu)
    return (-1 + np.sqrt(1 + 4 * eu)) / (2 * eu)


print("  Panel (b): computing tilt trajectories...")

trajectories = {}
for p0 in p_initials:
    traj = [p0]
    p_cur = p0
    for _ in range(n_iters):
        u = (1 - t_fixed) * L_coord(p_cur)
        p_cur = L_inv(u)
        traj.append(p_cur)
    trajectories[p0] = traj

print("  Panel (b): tilt trajectories computed")

# --- plotting ---
fig, axes = plt.subplots(1, 2, figsize=(11, 4.2))

# Panel (a)
ax = axes[0]
ax.plot(p, sigma2, color="#1565C0", linewidth=1.8, label=r"$\sigma^2(p)$")
ax.plot(p, 2 * Delta_h, color="#E65100", linewidth=1.4, linestyle="--",
        label=r"$2\,\Delta h(p)$")
ax.axvline(p_phi, color="gray", linewidth=0.8, linestyle=":")
ax.annotate(r"$p=\phi^{-1}$", xy=(p_phi, 0), xytext=(p_phi + 0.06, 0.08),
            fontsize=10, color="gray",
            arrowprops=dict(arrowstyle="->", color="gray", lw=0.8))
ax.set_xlabel(r"$p$", fontsize=12)
ax.set_ylabel("value", fontsize=12)
ax.set_title(r"(a) Asymptotic jitter $\sigma^2(p)$ and $2\,\Delta h(p)$",
             fontsize=11)
ax.legend(fontsize=10, loc="upper right")
ax.set_xlim(0, 1)
ax.set_ylim(-0.01, 0.55)
ax.xaxis.set_major_locator(MultipleLocator(0.2))

# Panel (b)
ax = axes[1]
colors = plt.cm.viridis(np.linspace(0.1, 0.9, len(p_initials)))
ns = np.arange(n_iters + 1)
for idx, p0 in enumerate(p_initials):
    ax.plot(ns, trajectories[p0], "o-", markersize=3.5,
            linewidth=1.2, color=colors[idx],
            label=rf"$p_0={p0:.2f}$")
ax.axhline(p_phi, color="gray", linewidth=0.8, linestyle=":")
ax.annotate(r"$\phi^{-1}$", xy=(n_iters, p_phi),
            xytext=(n_iters - 2.5, p_phi + 0.06),
            fontsize=10, color="gray")
ax.set_xlabel(r"iteration $n$", fontsize=12)
ax.set_ylabel(r"$T_t^{\,n}(p_0)$", fontsize=12)
ax.set_title(rf"(b) Tilt orbits, $t={t_fixed}$", fontsize=11)
ax.legend(fontsize=8, loc="upper right", ncol=2)
ax.set_xlim(-0.3, n_iters + 0.3)
ax.set_ylim(0, 1)

plt.tight_layout()

outdir = os.path.dirname(os.path.abspath(__file__))
outpath = os.path.join(outdir, "fig_jitter_tilt.pdf")
fig.savefig(outpath, bbox_inches="tight", dpi=300)
plt.close(fig)

print(f"Figure saved to {outpath}")
print("Done.")
