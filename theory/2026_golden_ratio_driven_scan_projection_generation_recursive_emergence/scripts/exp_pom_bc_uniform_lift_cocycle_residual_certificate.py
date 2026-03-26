#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate: Beck--Chevalley defect 2-cocycle and residual increments.

Certifies identities in subsec__pom-beck-chevalley-gauge-anomaly-pressure:
  - multiplicative defect: L_f L_g = rho_{f,g} ⊙ L_{g∘f},
  - 2-cocycle identity for rho under triple composition,
  - residual increment identity (KL telescoping step),
  - telescoping decomposition on a projection tower.

Outputs:
  artifacts/export/pom_bc_uniform_lift_cocycle_residual_certificate.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir


def _rng(seed: int) -> np.random.Generator:
    return np.random.default_rng(seed)


def _random_strictly_positive_simplex(g: np.random.Generator, n: int) -> np.ndarray:
    x = g.random(n) + 0.05
    return x / float(np.sum(x))


def _random_surjection(g: np.random.Generator, n: int, m: int) -> np.ndarray:
    """Return array h of length n with values in {0,..,m-1}, surjective."""
    if not (1 <= m <= n):
        raise ValueError("require 1<=m<=n")
    h = np.empty(n, dtype=int)
    # Ensure surjectivity by planting all images once.
    perm = g.permutation(n)
    h[perm[:m]] = np.arange(m, dtype=int)
    h[perm[m:]] = g.integers(0, m, size=n - m, dtype=int)
    return h


def _fiber_sizes(h: np.ndarray, m: int) -> np.ndarray:
    d = np.zeros(m, dtype=int)
    for v in h:
        d[int(v)] += 1
    return d


def _pushforward(h: np.ndarray, m: int, mu: np.ndarray) -> np.ndarray:
    pi = np.zeros(m, dtype=float)
    for u, v in enumerate(h):
        pi[int(v)] += float(mu[u])
    return pi


def _lift_uniform(h: np.ndarray, m: int, pi: np.ndarray) -> np.ndarray:
    d = _fiber_sizes(h, m)
    out = np.empty(h.shape[0], dtype=float)
    for u, v in enumerate(h):
        vv = int(v)
        out[u] = float(pi[vv]) / float(d[vv])
    return out


def _kl(p: np.ndarray, q: np.ndarray) -> float:
    # p, q strictly positive and sum to 1
    return float(np.sum(p * (np.log(p) - np.log(q))))


def _relative_error(a: float, b: float, eps: float = 1e-15) -> float:
    num = abs(a - b)
    den = max(abs(a), abs(b), eps)
    return float(num / den)


def _defect_rho(f: np.ndarray, g: np.ndarray, nY: int, nZ: int) -> np.ndarray:
    """rho_{f,g} on X: length |X|."""
    d_f = _fiber_sizes(f, nY)
    d_g = _fiber_sizes(g, nZ)
    gf = g[f]
    d_gf = _fiber_sizes(gf, nZ)
    rho = np.empty(f.shape[0], dtype=float)
    for x in range(f.shape[0]):
        y = int(f[x])
        z = int(g[y])
        rho[x] = float(d_gf[z]) / (float(d_g[z]) * float(d_f[y]))
    return rho


@dataclass(frozen=True)
class Trial:
    nx: int
    ny: int
    nz: int
    nw: int
    err_defect_identity: float
    err_cocycle: float
    err_residual_increment: float
    err_telescope: float


def _max_abs_rel_vec(a: np.ndarray, b: np.ndarray) -> float:
    denom = np.maximum(np.maximum(np.abs(a), np.abs(b)), 1e-15)
    return float(np.max(np.abs(a - b) / denom))


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit certificate: BC 2-cocycle and residual increments.")
    ap.add_argument("--seed", type=int, default=20260228)
    ap.add_argument("--trials", type=int, default=8)
    ap.add_argument("--tower-layers", type=int, default=4)
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "pom_bc_uniform_lift_cocycle_residual_certificate.json"),
    )
    args = ap.parse_args()

    g = _rng(int(args.seed))
    trials: List[Trial] = []

    for _ in range(int(args.trials)):
        nz = int(g.integers(2, 5))
        ny = int(g.integers(nz, nz + 4))
        nx = int(g.integers(ny, ny + 5))
        nw = int(g.integers(nx, nx + 6))

        f = _random_surjection(g, nx, ny)  # X -> Y
        gg = _random_surjection(g, ny, nz)  # Y -> Z
        h = _random_surjection(g, nw, nx)  # W -> X

        nu = _random_strictly_positive_simplex(g, nz)

        # Defect identity on X
        Lg_nu = _lift_uniform(gg, nz, nu)  # on Y
        Lf_Lg_nu = _lift_uniform(f, ny, Lg_nu)  # on X, note: L_f acts on Δ(Y)
        gf = gg[f]
        Lgf_nu = _lift_uniform(gf, nz, nu)  # on X
        rho_fg = _defect_rho(f, gg, ny, nz)
        err_defect = _max_abs_rel_vec(Lf_Lg_nu, rho_fg * Lgf_nu)

        # Cocycle identity on W
        rho_hf = _defect_rho(h, f, nx, ny)  # W via h:W->X and f:X->Y
        fh = f[h]  # W -> Y
        rho_fh_g = _defect_rho(fh, gg, ny, nz)  # W via fh and g
        rho_fg_pull = rho_fg[h]  # rho_{f,g} ∘ h
        gfh = gg[fh]  # W -> Z
        rho_h_gf = _defect_rho(h, gg[f], nx, nz)  # W via h and g∘f
        err_cocycle = _max_abs_rel_vec(rho_hf * rho_fh_g, rho_fg_pull * rho_h_gf)

        # Residual increment identity
        # Build Omega -> X -> Y with Omega = W, f0:W->X is h, g0:X->Y is f then Y->? but need X->Y
        # Use f0 = h: Omega->X and g0 = f: X->Y, so h0 = f∘h.
        omega_to_x = h  # Ω -> X
        x_to_y = f  # X -> Y
        omega_to_y = x_to_y[omega_to_x]

        mu = _random_strictly_positive_simplex(g, nw)  # on Ω
        pi_x = _pushforward(omega_to_x, nx, mu)
        tau_y = _pushforward(x_to_y, ny, pi_x)

        mu_e_f = _lift_uniform(omega_to_x, nx, pi_x)  # L_f in theorem: lift along Ω->X
        mu_e_h = _lift_uniform(omega_to_y, ny, tau_y)  # lift along Ω->Y

        R_f = _kl(mu, mu_e_f)
        R_h = _kl(mu, mu_e_h)

        # Expected KL of π(·|y) vs σ_y
        d_f_x = _fiber_sizes(omega_to_x, nx)  # |Ω_x|
        d_h_y = _fiber_sizes(omega_to_y, ny)  # |Ω_y|

        exp_kl = 0.0
        for y in range(ny):
            if tau_y[y] <= 0:
                continue
            xs = np.where(x_to_y == y)[0]
            pi_cond = pi_x[xs] / float(tau_y[y])
            sigma = d_f_x[xs].astype(float) / float(d_h_y[y])
            exp_kl += float(tau_y[y]) * _kl(pi_cond, sigma)

        err_residual = _relative_error(R_h, R_f + exp_kl)

        # Telescoping on a random tower Ω=X0 -> X1 -> ... -> Xn
        layers = int(args.tower_layers)
        sizes = [int(g.integers(8, 14))]
        for _k in range(layers):
            sizes.append(int(g.integers(2, min(7, sizes[-1]) + 1)))
        maps: List[np.ndarray] = []
        for k in range(1, layers + 1):
            maps.append(_random_surjection(g, sizes[k - 1], sizes[k]))

        mu0 = _random_strictly_positive_simplex(g, sizes[0])

        def composed_to(k: int) -> np.ndarray:
            hcomp = np.arange(sizes[0], dtype=int)
            for j in range(k):
                hcomp = maps[j][hcomp]
            return hcomp

        R = []
        for k in range(layers + 1):
            if k == 0:
                R.append(0.0)
                continue
            Fk = composed_to(k)
            pik = _pushforward(Fk, sizes[k], mu0)
            mu_e = _lift_uniform(Fk, sizes[k], pik)
            R.append(_kl(mu0, mu_e))

        increments = []
        for k in range(layers):
            Fk = composed_to(k)
            Fk1 = composed_to(k + 1)
            pi_k = _pushforward(Fk, sizes[k], mu0)
            tau_k1 = _pushforward(maps[k], sizes[k + 1], pi_k)

            d_Fk_x = _fiber_sizes(Fk, sizes[k])
            d_Fk1_y = _fiber_sizes(Fk1, sizes[k + 1])

            step = 0.0
            for y in range(sizes[k + 1]):
                if tau_k1[y] <= 0:
                    continue
                xs = np.where(maps[k] == y)[0]
                pi_cond = pi_k[xs] / float(tau_k1[y])
                sigma = d_Fk_x[xs].astype(float) / float(d_Fk1_y[y])
                step += float(tau_k1[y]) * _kl(pi_cond, sigma)
            increments.append(step)

        telescope_rhs = float(np.sum(increments))
        err_telescope = _relative_error(R[-1], telescope_rhs)

        trials.append(
            Trial(
                nx=nx,
                ny=ny,
                nz=nz,
                nw=nw,
                err_defect_identity=float(err_defect),
                err_cocycle=float(err_cocycle),
                err_residual_increment=float(err_residual),
                err_telescope=float(err_telescope),
            )
        )

    payload: Dict[str, object] = {
        "meta": {"script": Path(__file__).name, "seed": int(args.seed), "trials": int(args.trials), "tower_layers": int(args.tower_layers)},
        "results": [asdict(t) for t in trials],
        "max_errors": {
            "defect_identity": max(t.err_defect_identity for t in trials),
            "cocycle": max(t.err_cocycle for t in trials),
            "residual_increment": max(t.err_residual_increment for t in trials),
            "telescope": max(t.err_telescope for t in trials),
        },
    }

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[pom-bc-uniform-lift-cocycle-residual] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

