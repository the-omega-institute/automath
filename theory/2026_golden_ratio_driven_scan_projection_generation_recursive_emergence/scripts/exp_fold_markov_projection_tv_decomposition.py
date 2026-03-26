#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Audit: TV decomposition induced by Fold Markov projection K_m = Q_m \circ P_m.

All code is English-only by repository convention.

Outputs:
- artifacts/export/fold_markov_projection_tv_decomposition.json
- sections/generated/tab_fold_markov_projection_tv_decomposition.tex
"""

from __future__ import annotations

import json
import math
import random
import time
from dataclasses import dataclass
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m, is_golden_legal, parry_pi_m


def int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def bits_to_key(bits: Sequence[int]) -> str:
    return "".join("1" if b else "0" for b in bits)


def tv(mu: Sequence[float], nu: Sequence[float]) -> float:
    return 0.5 * sum(abs(a - b) for a, b in zip(mu, nu))


def tv_dict(p: Dict[str, float], q: Dict[str, float]) -> float:
    keys = set(p.keys()) | set(q.keys())
    return 0.5 * sum(abs(p.get(k, 0.0) - q.get(k, 0.0)) for k in keys)


@dataclass(frozen=True)
class FiberInfo:
    x: str
    idxs: List[int]


def build_fibers(m: int, prog: Progress) -> Tuple[List[str], Dict[str, FiberInfo]]:
    micro_to_x: List[str] = [""] * (1 << m)
    fibers: Dict[str, List[int]] = {}
    for idx in range(1 << m):
        if idx % (1 << 15) == 0:
            prog.tick(f"m={m} fibers idx={idx}/{1 << m}")
        micro = int_to_bits(idx, m)
        x_bits = fold_m(micro)
        if not is_golden_legal(x_bits):
            raise RuntimeError("Fold_m produced an illegal golden word")
        x = bits_to_key(x_bits)
        micro_to_x[idx] = x
        fibers.setdefault(x, []).append(idx)

    finfo: Dict[str, FiberInfo] = {
        x: FiberInfo(x=x, idxs=idxs) for x, idxs in fibers.items()
    }
    return micro_to_x, finfo


def pushforward_P(mu: Sequence[float], micro_to_x: Sequence[str]) -> Dict[str, float]:
    out: Dict[str, float] = {}
    for idx, p in enumerate(mu):
        if p == 0.0:
            continue
        x = micro_to_x[idx]
        out[x] = out.get(x, 0.0) + p
    return out


def uniform_lift_Q(
    pi: Dict[str, float], fibers: Dict[str, FiberInfo], n_omega: int
) -> List[float]:
    out = [0.0] * n_omega
    for x, fx in fibers.items():
        px = pi.get(x, 0.0)
        if px == 0.0:
            continue
        d = float(len(fx.idxs))
        val = px / d
        for idx in fx.idxs:
            out[idx] = val
    return out


def normalize(mu: List[float]) -> List[float]:
    s = sum(mu)
    if s <= 0.0 or not math.isfinite(s):
        raise RuntimeError("Invalid mass")
    return [x / s for x in mu]


def random_prob_vector(rng: random.Random, n: int) -> List[float]:
    # Simple deterministic Dirichlet(1) via exponential.
    xs = [rng.random() for _ in range(n)]
    # Avoid extremely tiny mass degeneracy: square to bias toward sparsity (still >0).
    xs = [x * x for x in xs]
    return normalize(xs)


def parry_pi_Xm(fibers: Dict[str, FiberInfo]) -> Dict[str, float]:
    pi: Dict[str, float] = {}
    s = 0.0
    for x in fibers.keys():
        bits = [1 if c == "1" else 0 for c in x]
        px = parry_pi_m(bits)
        pi[x] = px
        s += px
    if abs(s - 1.0) > 1e-10:
        raise RuntimeError(f"Parry cylinder mass mismatch: sum={s}")
    return pi


def main() -> None:
    t0 = time.time()
    prog = Progress("fold_tvproj")

    m = 12
    n_omega = 1 << m
    micro_to_x, fibers = build_fibers(m, prog)
    n_X = len(fibers)

    # Fixed baseline: pi = Parry on X_m, mu0 = Q pi.
    pi_parry = parry_pi_Xm(fibers)
    mu0 = uniform_lift_Q(pi_parry, fibers, n_omega)

    rng = random.Random(20260204)
    mus: List[List[float]] = [mu0]
    for _ in range(7):
        mus.append(random_prob_vector(rng, n_omega))

    # Precompute K(mu) = Q(P(mu)).
    Pis: List[Dict[str, float]] = []
    Kmus: List[List[float]] = []
    Res: List[float] = []
    for i, mu in enumerate(mus):
        prog.tick(f"precompute i={i}/{len(mus)}")
        pi = pushforward_P(mu, micro_to_x)
        kmu = uniform_lift_Q(pi, fibers, n_omega)
        Pis.append(pi)
        Kmus.append(kmu)
        Res.append(tv(mu, kmu))

    # Check identities on random pairs.
    pairs: List[Tuple[int, int]] = []
    for _ in range(12):
        i = rng.randrange(0, len(mus))
        j = rng.randrange(0, len(mus))
        if i == j:
            j = (j + 1) % len(mus)
        pairs.append((i, j))

    rows = []
    max_eq_err = 0.0
    min_gap = 1e9
    for i, j in pairs:
        mu, nu = mus[i], mus[j]
        pi, qi = Pis[i], Pis[j]
        kmu, knu = Kmus[i], Kmus[j]

        tv_mn = tv(mu, nu)
        tv_vis = tv_dict(pi, qi)
        tv_k = tv(kmu, knu)
        eq_err = abs(tv_k - tv_vis)
        max_eq_err = max(max_eq_err, eq_err)

        upper = tv_vis + Res[i] + Res[j]
        gap = upper - tv_mn
        min_gap = min(min_gap, gap)

        rows.append(
            {
                "i": i,
                "j": j,
                "tv(mu,nu)": tv_mn,
                "tv(Pmu,Pnu)": tv_vis,
                "tv(Kmu,Knu)": tv_k,
                "tv(mu,Kmu)": Res[i],
                "tv(nu,Knu)": Res[j],
                "upper": upper,
                "upper_minus_tv": gap,
            }
        )

    # Export JSON audit.
    export_dir().mkdir(parents=True, exist_ok=True)
    payload = {
        "m": m,
        "omega": n_omega,
        "X": n_X,
        "num_mus": len(mus),
        "pairs": pairs,
        "rows": rows,
        "max_abs_err_tvK_minus_tvP": max_eq_err,
        "min_upper_minus_tv": min_gap,
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "fold_markov_projection_tv_decomposition.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    # Write TeX table.
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{3pt}")
    lines.append(
        "\\caption{折叠诱导的 Markov 投影 $K_m:=Q_m\\circ P_m$ 的 TV 分解核对（$m=12$）。对若干确定性生成的微观分布 $\\mu,\\nu$，计算 $D_{\\mathrm{TV}}(K_m\\mu,K_m\\nu)$ 并与可见推前距离 $D_{\\mathrm{TV}}(P_m\\mu,P_m\\nu)$ 比较（应相等）；同时用三角不等式给出上界 $D_{\\mathrm{TV}}(\\mu,\\nu)\\le D_{\\mathrm{TV}}(P_m\\mu,P_m\\nu)+D_{\\mathrm{TV}}(\\mu,K_m\\mu)+D_{\\mathrm{TV}}(\\nu,K_m\\nu)$，并报告余量。}"
    )
    lines.append("\\label{tab:fold_markov_projection_tv_decomposition}")
    lines.append("\\begin{tabular}{rrrrrrrr}")
    lines.append("\\toprule")
    lines.append(
        "pair & $D_{\\mathrm{TV}}(\\mu,\\nu)$ & $D_{\\mathrm{TV}}(P\\mu,P\\nu)$ & $D_{\\mathrm{TV}}(K\\mu,K\\nu)$ & $D_{\\mathrm{TV}}(\\mu,K\\mu)$ & $D_{\\mathrm{TV}}(\\nu,K\\nu)$ & upper & upper$-D_{\\mathrm{TV}}$\\\\"
    )
    lines.append("\\midrule")
    for k, r in enumerate(rows):
        lines.append(
            f"{k} & {r['tv(mu,nu)']:.6g} & {r['tv(Pmu,Pnu)']:.6g} & {r['tv(Kmu,Knu)']:.6g} & {r['tv(mu,Kmu)']:.6g} & {r['tv(nu,Knu)']:.6g} & {r['upper']:.6g} & {r['upper_minus_tv']:.3g}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    out = generated_dir() / "tab_fold_markov_projection_tv_decomposition.tex"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(
        f"[fold_tvproj] OK m={m} omega={n_omega} X={n_X} max_eq_err={max_eq_err:.3g} min_gap={min_gap:.3g} wall={time.time() - t0:.2f}s",
        flush=True,
    )


if __name__ == "__main__":
    main()
