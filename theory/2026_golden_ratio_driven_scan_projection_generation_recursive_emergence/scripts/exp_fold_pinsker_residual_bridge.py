#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Audit: Pinsker-type bridge between residual TV and residual KL for Fold.

We compute for random micro measures mu on Omega_m:
- mu^e := K_m mu = Q_m P_m mu (fiber-uniform lift)
- TV_res := D_TV(mu, mu^e)
- KL_res := D_KL(mu || mu^e)
and check Pinsker: TV_res <= sqrt(KL_res/2).

Outputs:
- artifacts/export/fold_pinsker_residual_bridge.json
- sections/generated/tab_fold_pinsker_residual_bridge.tex
"""

from __future__ import annotations

import json
import math
import random
import time
from dataclasses import dataclass
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m, is_golden_legal


def int_to_bits(x: int, m: int) -> List[int]:
    return [(x >> (m - 1 - i)) & 1 for i in range(m)]


def bits_to_key(bits: Sequence[int]) -> str:
    return "".join("1" if b else "0" for b in bits)


def latex_escape_text(s: str) -> str:
    return s.replace("_", "\\_")


def normalize(mu: List[float]) -> List[float]:
    s = sum(mu)
    if s <= 0.0 or not math.isfinite(s):
        raise RuntimeError("Invalid mass")
    return [x / s for x in mu]


def random_prob_vector(rng: random.Random, n: int, power: float = 2.0) -> List[float]:
    xs = [rng.random() ** power for _ in range(n)]
    return normalize(xs)


def tv(mu: Sequence[float], nu: Sequence[float]) -> float:
    return 0.5 * sum(abs(a - b) for a, b in zip(mu, nu))


def kl(mu: Sequence[float], nu: Sequence[float], eps: float = 1e-300) -> float:
    s = 0.0
    for p, q in zip(mu, nu):
        if p <= 0.0:
            continue
        qq = q if q > 0.0 else eps
        s += p * math.log(p / qq)
    return s


def build_fibers(m: int, prog: Progress) -> Tuple[List[str], Dict[str, List[int]]]:
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
    return micro_to_x, fibers


def pushforward_P(mu: Sequence[float], micro_to_x: Sequence[str]) -> Dict[str, float]:
    out: Dict[str, float] = {}
    for idx, p in enumerate(mu):
        if p == 0.0:
            continue
        x = micro_to_x[idx]
        out[x] = out.get(x, 0.0) + p
    return out


def uniform_lift_Q(
    pi: Dict[str, float], fibers: Dict[str, List[int]], n_omega: int
) -> List[float]:
    out = [0.0] * n_omega
    for x, idxs in fibers.items():
        px = pi.get(x, 0.0)
        if px == 0.0:
            continue
        d = float(len(idxs))
        val = px / d
        for idx in idxs:
            out[idx] = val
    return out


@dataclass(frozen=True)
class Row:
    name: str
    tv_res: float
    kl_res: float
    pinsker_rhs: float
    ratio: float


def main() -> None:
    t0 = time.time()
    prog = Progress("fold_pinsker")

    m = 12
    n = 1 << m
    micro_to_x, fibers = build_fibers(m, prog)

    rng = random.Random(20260204)
    mus: List[Tuple[str, List[float]]] = []
    mus.append(("uniform", [1.0 / n] * n))
    mus.append(("dirichlet_p2", random_prob_vector(rng, n, power=2.0)))
    mus.append(("dirichlet_p5", random_prob_vector(rng, n, power=5.0)))
    mus.append(("dirichlet_p12", random_prob_vector(rng, n, power=12.0)))

    rows: List[Row] = []
    for name, mu in mus:
        pi = pushforward_P(mu, micro_to_x)
        mue = uniform_lift_Q(pi, fibers, n)
        tv_res = tv(mu, mue)
        kl_res = kl(mu, mue)
        rhs = math.sqrt(max(kl_res, 0.0) / 2.0)
        ratio = (tv_res / rhs) if rhs > 0.0 else 0.0
        rows.append(
            Row(name=name, tv_res=tv_res, kl_res=kl_res, pinsker_rhs=rhs, ratio=ratio)
        )

    export_dir().mkdir(parents=True, exist_ok=True)
    payload = {
        "m": m,
        "omega": n,
        "rows": [
            {
                "name": r.name,
                "tv_res": r.tv_res,
                "kl_res": r.kl_res,
                "pinsker_rhs": r.pinsker_rhs,
                "ratio": r.ratio,
            }
            for r in rows
        ],
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "fold_pinsker_residual_bridge.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        "\\caption{折叠残差的 Pinsker 桥接核对（$m=12$）：对若干确定性生成的 $\\mu$，令 $\\mu^e=K_m\\mu$，报告 $D_{\\mathrm{TV}}(\\mu,\\mu^e)$、$D_{\\mathrm{KL}}(\\mu\\|\\\\mu^e)$ 及上界 $\\sqrt{D_{\\mathrm{KL}}/2}$ 与比值。}"
    )
    lines.append("\\label{tab:fold_pinsker_residual_bridge}")
    lines.append("\\begin{tabular}{lrrrr}")
    lines.append("\\toprule")
    lines.append(
        "$\\mu$ & $D_{\\mathrm{TV}}(\\mu,\\mu^e)$ & $D_{\\mathrm{KL}}(\\mu\\|\\mu^e)$ & $\\sqrt{D_{\\mathrm{KL}}/2}$ & ratio\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{latex_escape_text(r.name)} & {r.tv_res:.6g} & {r.kl_res:.6g} & {r.pinsker_rhs:.6g} & {r.ratio:.6g}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out = generated_dir() / "tab_fold_pinsker_residual_bridge.tex"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")

    mx = max(r.ratio for r in rows)
    print(
        f"[fold_pinsker] OK m={m} rows={len(rows)} max_ratio={mx:.6g} wall={time.time() - t0:.2f}s",
        flush=True,
    )


if __name__ == "__main__":
    main()
