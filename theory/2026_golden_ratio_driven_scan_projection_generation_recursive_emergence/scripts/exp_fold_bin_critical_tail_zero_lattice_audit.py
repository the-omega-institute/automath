#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit certificate for bin-fold critical tails, capacity profile, and zero lattice.

This script uses the exact digit-DP backend for Fold^{bin}_m to audit three claims:

1. The critical tail staircase at T_m(s) = (2/phi)^m * exp(s).
2. The corresponding continuous-capacity broken-line limit.
3. The complex-temperature zero lattice near Re q = -1 for k = 0.

Outputs:
  - artifacts/export/fold_bin_critical_tail_zero_lattice_audit.json
  - sections/generated/eq_fold_bin_critical_tail_zero_lattice_audit.tex

All code is English-only by repository convention.
"""

from __future__ import annotations

import json
import math
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

import mpmath as mp

from common_paths import export_dir, generated_dir
from common_phi_fold import PHI, fib_upto
from exp_fold_bin_gauge_m6_invariants import _K_of_m, _V_m, _count_tail_leq, _golden_words


TAIL_M = 24
TAIL_S_VALUES = (-0.75, -0.25, 0.20)
ZERO_MS = (20, 24)
ZERO_K = 0


@dataclass(frozen=True)
class TailRow:
    s: float
    m: int
    x_size: int
    threshold: float
    tail_ratio: float
    tail_limit: float
    capacity_ratio: float
    capacity_limit: float


@dataclass(frozen=True)
class ZeroRow:
    m: int
    k: int
    q0_re: float
    q0_im: float
    q_re: float
    q_im: float
    abs_error: float
    residual: float


def _compute_histogram(m: int) -> Dict[int, int]:
    target = (1 << m) - 1
    k_max = _K_of_m(target)
    fib = fib_upto(k_max + 2)
    hist: Dict[int, int] = {}
    for w in _golden_words(m):
        value = _V_m(w, fib)
        d = int(_count_tail_leq(limit=target - value, m=m, K=k_max, w_m=w[-1]))
        hist[d] = hist.get(d, 0) + 1
    return dict(sorted(hist.items()))


def _tail_limit(s: float) -> float:
    if s < -math.log(PHI):
        return 1.0
    if s < 0.0:
        return 1.0 / PHI
    return 0.0


def _capacity_limit(s: float) -> float:
    if s < -math.log(PHI):
        return (PHI * PHI / math.sqrt(5.0)) * math.exp(s)
    if s < 0.0:
        return (PHI / math.sqrt(5.0)) * math.exp(s) + 1.0 / (PHI * math.sqrt(5.0))
    return 1.0


def _audit_tail_and_capacity(hist: Dict[int, int], *, m: int) -> List[TailRow]:
    x_size = int(sum(hist.values()))
    total_micro = float(1 << m)
    rows: List[TailRow] = []
    critical_scale = (2.0 / PHI) ** m
    for s in TAIL_S_VALUES:
        threshold = critical_scale * math.exp(float(s))
        tail_count = sum(count for d, count in hist.items() if float(d) >= threshold)
        capacity = sum(float(count) * min(float(d), threshold) for d, count in hist.items())
        rows.append(
            TailRow(
                s=float(s),
                m=int(m),
                x_size=x_size,
                threshold=float(threshold),
                tail_ratio=float(tail_count / x_size),
                tail_limit=float(_tail_limit(float(s))),
                capacity_ratio=float(capacity / total_micro),
                capacity_limit=float(_capacity_limit(float(s))),
            )
        )
    return rows


def _power_sum(hist: Dict[int, int], q: mp.mpc, logd: Dict[int, mp.mpf]) -> mp.mpc:
    return mp.fsum(mp.mpf(count) * mp.e ** (q * logd[d]) for d, count in hist.items())


def _power_sum_derivative(hist: Dict[int, int], q: mp.mpc, logd: Dict[int, mp.mpf]) -> mp.mpc:
    return mp.fsum(mp.mpf(count) * logd[d] * mp.e ** (q * logd[d]) for d, count in hist.items())


def _predicted_zero(m: int, k: int) -> mp.mpc:
    fib = fib_upto(m + 1)
    f_m = mp.mpf(fib[m - 1])
    f_m1 = mp.mpf(fib[m])
    return -mp.log(f_m1 / f_m) / mp.log(mp.mpf(PHI)) + mp.mpf(2 * k + 1) * mp.pi * mp.j / mp.log(mp.mpf(PHI))


def _find_zero(hist: Dict[int, int], *, m: int, k: int) -> ZeroRow:
    mp.mp.dps = 90
    q0 = _predicted_zero(m, k)
    logd = {d: mp.log(mp.mpf(d)) for d in hist}
    q = mp.mpc(q0)
    tol = mp.mpf("1e-40")
    for _ in range(40):
        value = _power_sum(hist, q, logd)
        deriv = _power_sum_derivative(hist, q, logd)
        step = value / deriv
        q -= step
        if abs(step) <= tol:
            break
    residual = abs(_power_sum(hist, q, logd))
    return ZeroRow(
        m=int(m),
        k=int(k),
        q0_re=float(mp.re(q0)),
        q0_im=float(mp.im(q0)),
        q_re=float(mp.re(q)),
        q_im=float(mp.im(q)),
        abs_error=float(abs(q - q0)),
        residual=float(residual),
    )


def _tex_float(x: float, digits: int = 6) -> str:
    ax = abs(float(x))
    if ax == 0.0:
        return "0"
    if 1.0e-4 <= ax < 1.0e4:
        s = f"{float(x):.{digits}f}"
        s = s.rstrip("0").rstrip(".")
        return s if s else "0"
    mantissa, exponent = f"{float(x):.{digits-1}e}".split("e")
    mantissa = mantissa.rstrip("0").rstrip(".")
    return f"{mantissa}\\times 10^{{{int(exponent)}}}"


def _tex_complex(re_part: float, im_part: float) -> str:
    sign = "+" if im_part >= 0.0 else "-"
    return f"{_tex_float(re_part)}{sign}{_tex_float(abs(im_part))}\\,\\mathrm{{i}}"


def _write_tex(tail_rows: List[TailRow], zero_rows: List[ZeroRow], out_path: Path) -> None:
    if not tail_rows:
        raise ValueError("tail_rows must be non-empty")
    tail_m = tail_rows[0].m
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_fold_bin_critical_tail_zero_lattice_audit.py")
    lines.append("\\begin{equation}\\label{eq_fold_bin_critical_tail_zero_lattice_audit}")
    lines.append("\\begin{aligned}")
    for row in tail_rows:
        lines.append(
            f"&s={_tex_float(row.s, digits=2)}:\\ "
            f"\\frac{{N_{{{tail_m}}}^{{\\mathrm{{bin}}}}(T_{{{tail_m}}}({_tex_float(row.s, digits=2)}))}}{{|X_{{{tail_m}}}|}}"
            f"={_tex_float(row.tail_ratio)}\\to {_tex_float(row.tail_limit)},\\quad "
            f"2^{{-{tail_m}}}\\mathcal C_{{{tail_m}}}^{{\\mathrm{{bin,cont}}}}(T_{{{tail_m}}}({_tex_float(row.s, digits=2)}))"
            f"={_tex_float(row.capacity_ratio)}\\to {_tex_float(row.capacity_limit)}\\\\"
        )
    err_line = ",\\ ".join(
        [
            f"|q_{{{row.m},0}}-q_{{{row.m},0}}^{{(0)}}|={_tex_float(row.abs_error)}"
            for row in zero_rows
        ]
    )
    last = zero_rows[-1]
    lines.append(f"&{err_line}\\\\")
    lines.append(
        "&q_{"
        + f"{last.m},0"
        + "}^{{(0)}}="
        + _tex_complex(last.q0_re, last.q0_im)
        + ",\\qquad q_{"
        + f"{last.m},0"
        + "}="
        + _tex_complex(last.q_re, last.q_im)
        + ",\\qquad |S_{q_{"
        + f"{last.m},0"
        + "}}^{\\mathrm{bin}}("
        + f"{last.m}"
        + ")|="
        + _tex_float(last.residual)
    )
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def _write_json(tail_rows: List[TailRow], zero_rows: List[ZeroRow], out_path: Path, *, wall_s: float) -> None:
    payload = {
        "version": 1,
        "tail_m": int(TAIL_M),
        "tail_s_values": [float(s) for s in TAIL_S_VALUES],
        "zero_ms": [int(m) for m in ZERO_MS],
        "zero_k": int(ZERO_K),
        "wall_time_seconds": float(wall_s),
        "tail_rows": [
            {
                "s": float(row.s),
                "m": int(row.m),
                "x_size": int(row.x_size),
                "threshold": float(row.threshold),
                "tail_ratio": float(row.tail_ratio),
                "tail_limit": float(row.tail_limit),
                "capacity_ratio": float(row.capacity_ratio),
                "capacity_limit": float(row.capacity_limit),
            }
            for row in tail_rows
        ],
        "zero_rows": [
            {
                "m": int(row.m),
                "k": int(row.k),
                "q0_re": float(row.q0_re),
                "q0_im": float(row.q0_im),
                "q_re": float(row.q_re),
                "q_im": float(row.q_im),
                "abs_error": float(row.abs_error),
                "residual": float(row.residual),
            }
            for row in zero_rows
        ],
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> None:
    t0 = time.time()
    hist_cache: Dict[int, Dict[int, int]] = {}
    for m in sorted(set([int(TAIL_M), *[int(v) for v in ZERO_MS]])):
        hist_cache[m] = _compute_histogram(m)
        print(f"[fold-bin-critical-audit] computed histogram m={m}", flush=True)

    tail_rows = _audit_tail_and_capacity(hist_cache[TAIL_M], m=TAIL_M)
    zero_rows = [_find_zero(hist_cache[m], m=m, k=ZERO_K) for m in ZERO_MS]

    wall_s = float(time.time() - t0)

    json_out = export_dir() / "fold_bin_critical_tail_zero_lattice_audit.json"
    _write_json(tail_rows, zero_rows, json_out, wall_s=wall_s)
    print(f"[fold-bin-critical-audit] wrote {json_out}", flush=True)

    tex_out = generated_dir() / "eq_fold_bin_critical_tail_zero_lattice_audit.tex"
    _write_tex(tail_rows, zero_rows, tex_out)
    print(f"[fold-bin-critical-audit] wrote {tex_out}", flush=True)
    print(f"[fold-bin-critical-audit] done wall_s={wall_s:.3f}", flush=True)


if __name__ == "__main__":
    main()
