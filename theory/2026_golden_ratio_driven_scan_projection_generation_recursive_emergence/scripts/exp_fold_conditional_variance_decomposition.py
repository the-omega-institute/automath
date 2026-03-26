#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit: conditional expectation (w.r.t. an arbitrary micro measure) and variance decomposition.

All code is English-only by repository convention.

Outputs:
- artifacts/export/fold_conditional_variance_decomposition.json
- sections/generated/tab_fold_conditional_variance_decomposition.tex
"""

from __future__ import annotations

import json
import math
import random
import time
from dataclasses import dataclass
from typing import Dict, List, Sequence, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fib_upto, fold_m, is_golden_legal


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


def random_prob_vector(
    rng: random.Random, n: int, sparsity: float = 1.0
) -> List[float]:
    xs = [rng.random() for _ in range(n)]
    if sparsity != 1.0:
        xs = [x**sparsity for x in xs]
    return normalize(xs)


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


def fib_weights_for_value(m: int) -> List[int]:
    fib = fib_upto(m + 2)
    return [fib[k] for k in range(1, m + 1)]


def micro_value(micro: Sequence[int], w: Sequence[int]) -> int:
    return sum(int(b) * int(wi) for b, wi in zip(micro, w))


def compute_f_vals(m: int, prog: Progress) -> List[float]:
    w = fib_weights_for_value(m)
    fib = fib_upto(m + 3)
    scale = float(fib[m + 2])  # F_{m+3}
    f_vals = [0.0] * (1 << m)
    for idx in range(1 << m):
        if idx % (1 << 15) == 0:
            prog.tick(f"m={m} f idx={idx}/{1 << m}")
        micro = int_to_bits(idx, m)
        N = micro_value(micro, w)
        f_vals[idx] = float(N) / scale
    return f_vals


@dataclass(frozen=True)
class Row:
    name: str
    mean_f: float
    l2_f: float
    l2_E: float
    l2_res: float
    cond_var: float
    pyth_err: float
    var_err: float


def conditional_expectation(
    f: Sequence[float], mu: Sequence[float], fibers: Dict[str, List[int]]
) -> List[float]:
    Ef = [0.0] * len(mu)
    for _, idxs in fibers.items():
        mass = sum(mu[i] for i in idxs)
        if mass <= 0.0:
            # If fiber has zero mass, the value is irrelevant under mu; keep zeros.
            continue
        avg = sum(mu[i] * f[i] for i in idxs) / mass
        for i in idxs:
            Ef[i] = avg
    return Ef


def conditional_variance_average(
    f: Sequence[float], mu: Sequence[float], fibers: Dict[str, List[int]]
) -> float:
    out = 0.0
    for _, idxs in fibers.items():
        mass = sum(mu[i] for i in idxs)
        if mass <= 0.0:
            continue
        avg = sum(mu[i] * f[i] for i in idxs) / mass
        var = sum(mu[i] * ((f[i] - avg) ** 2) for i in idxs) / mass
        out += mass * var
    return out


def main() -> None:
    t0 = time.time()
    prog = Progress("fold_condvar")

    m = 12
    n = 1 << m
    _, fibers = build_fibers(m, prog)
    f = compute_f_vals(m, prog)

    rng = random.Random(20260204)
    mus: List[Tuple[str, List[float]]] = []
    mus.append(("uniform", [1.0 / n] * n))
    mus.append(("dirichlet_s1", random_prob_vector(rng, n, sparsity=1.0)))
    mus.append(("dirichlet_s3", random_prob_vector(rng, n, sparsity=3.0)))
    mus.append(("dirichlet_s8", random_prob_vector(rng, n, sparsity=8.0)))

    rows: List[Row] = []
    for name, mu in mus:
        Ef = conditional_expectation(f, mu, fibers)
        mean_f = sum(mu[i] * f[i] for i in range(n))
        mean_E = sum(mu[i] * Ef[i] for i in range(n))
        if abs(mean_f - mean_E) > 1e-10:
            raise RuntimeError("E_mu should preserve expectation")

        l2_f2 = sum(mu[i] * (f[i] ** 2) for i in range(n))
        l2_E2 = sum(mu[i] * (Ef[i] ** 2) for i in range(n))
        l2_res2 = sum(mu[i] * ((f[i] - Ef[i]) ** 2) for i in range(n))
        pyth_err = abs(l2_f2 - (l2_E2 + l2_res2))

        cond_var = conditional_variance_average(f, mu, fibers)
        var_err = abs(cond_var - l2_res2)

        rows.append(
            Row(
                name=name,
                mean_f=mean_f,
                l2_f=math.sqrt(l2_f2),
                l2_E=math.sqrt(l2_E2),
                l2_res=math.sqrt(l2_res2),
                cond_var=cond_var,
                pyth_err=pyth_err,
                var_err=var_err,
            )
        )

    export_dir().mkdir(parents=True, exist_ok=True)
    payload = {
        "m": m,
        "omega": n,
        "rows": [
            {
                "name": r.name,
                "mean_f": r.mean_f,
                "l2_f": r.l2_f,
                "l2_E": r.l2_E,
                "l2_res": r.l2_res,
                "cond_var": r.cond_var,
                "pyth_err": r.pyth_err,
                "var_err": r.var_err,
            }
            for r in rows
        ],
        "wall_time_seconds": time.time() - t0,
    }
    (export_dir() / "fold_conditional_variance_decomposition.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        "\\caption{任意微观分布 $\\mu$ 下的条件期望 $E_{\\mu}[\\cdot\\mid \\Fold_m]$ 与方差分解数值核对（$m=12$）。取 $f$ 为归一化窗口值（与前表一致），对若干确定性生成的 $\\mu$ 检查 $\\|f\\|_2^2=\\|E_{\\mu}f\\|_2^2+\\|f-E_{\\mu}f\\|_2^2$ 及 $\\mathbb E_{\\mu}[\\mathrm{Var}(f\\mid\\Fold_m)]=\\|f-E_{\\mu}f\\|_2^2$。}"
    )
    lines.append("\\label{tab:fold_conditional_variance_decomposition}")
    lines.append("\\begin{tabular}{lrrrrrr}")
    lines.append("\\toprule")
    lines.append(
        "$\\mu$ & $\\mathbb E[f]$ & $\\|f\\|_2$ & $\\|E_{\\mu}f\\|_2$ & $\\|f-E_{\\mu}f\\|_2$ & var avg & err\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        err = max(r.pyth_err, r.var_err)
        lines.append(
            f"{latex_escape_text(r.name)} & {r.mean_f:.6g} & {r.l2_f:.6g} & {r.l2_E:.6g} & {r.l2_res:.6g} & {r.cond_var:.6g} & {err:.3g}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out = generated_dir() / "tab_fold_conditional_variance_decomposition.tex"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(
        f"[fold_condvar] OK m={m} rows={len(rows)} wall={time.time() - t0:.2f}s",
        flush=True,
    )


if __name__ == "__main__":
    main()
