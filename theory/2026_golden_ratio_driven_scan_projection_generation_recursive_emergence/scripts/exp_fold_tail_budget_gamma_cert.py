#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tail-budget optimization demo: gamma_cert_m(eps) with automatic q selection.

We implement the optimized certificate:

  gamma_cert_m(eps) = inf_{q>=2} ( log r_q - log 2 + (1/m) log(1/eps) )/(q-1),

and (optionally) a finite-m exact variant using log S_q(m) computed from the
residue DP histogram.

We also compute the *actual* tail mass under pi_m(x)=d_m(x)/2^m at the chosen
gamma, using the same histogram:

  P_{pi_m}( (1/m) log d_m(X) >= gamma ) = (1/2^m) * sum_{d >= exp(m gamma)} d.

Outputs (default):
  - artifacts/export/fold_tail_budget_gamma_cert.json

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Mapping, Tuple

import numpy as np

from common_paths import export_dir
from common_tail_budget import (
    B_from_logB,
    GammaCert,
    gamma_cert_from_logSq,
    gamma_cert_from_rq,
    logB_from_gamma,
    prime_list_for_log_target,
)


def _parse_float_list(s: str) -> List[float]:
    out: List[float] = []
    for p in str(s).split(","):
        p = p.strip()
        if not p:
            continue
        out.append(float(p))
    return out


def _rq_from_exact_table(q_max: int) -> Dict[int, float]:
    """Return r_q for q<=17 from the audited exact table."""
    import exp_fold_collision_renyi_spectrum as rs

    if q_max > 17:
        raise ValueError("Exact r_q table only available for q<=17 in this script.")
    rq: Dict[int, float] = {2: float(rs.perron_root_r2()), 3: float(rs.perron_root_r3()), 4: float(rs.perron_root_r4())}
    for q, v in rs.PRECOMPUTED_RQ.items():
        if int(q) <= int(q_max):
            rq[int(q)] = float(v)
    return rq


def _rq_from_pressure_json(path: Path, q_max: int) -> Dict[int, float]:
    """Load r_q from fold_collision_pressure_multifractal_q60.json."""
    if not path.is_file():
        raise FileNotFoundError(str(path))
    payload = json.loads(path.read_text(encoding="utf-8"))
    rows = payload.get("rows", [])
    rq: Dict[int, float] = {}
    for r in rows:
        q = int(r["q"])
        if q < 2 or q > int(q_max):
            continue
        rq[q] = float(r["r_q"])
    if len(rq) < 2:
        raise ValueError("Not enough r_q entries in JSON payload")
    return rq


def _fold_counts_hist(m: int) -> Tuple[np.ndarray, np.ndarray]:
    """Return histogram (vals,freq) for Fold residue counts c_m(r) mod F_{m+2}."""
    import exp_fold_collision_pressure_multifractal_q60 as mf
    from common_phi_fold import Progress

    # Keep progress quiet here; this script is an audit helper, not a full pipeline step.
    prog = Progress("fold-tail-budget", every_seconds=30.0)
    vals, freq = mf.counts_mod_fib_hist(int(m), prog=prog)
    return vals, freq


def _logS_from_hist(vals: np.ndarray, freq: np.ndarray, q_max: int) -> Dict[int, float]:
    import exp_fold_collision_pressure_multifractal_q60 as mf

    return mf.log_moments_from_hist(vals, freq, int(q_max))


def _tail_mass_from_hist(vals: np.ndarray, freq: np.ndarray, *, m: int, logB: float) -> float:
    """Compute tail probability under pi_m at threshold exp(logB)."""
    if not math.isfinite(logB):
        return float("nan")
    # event: log d >= logB  <=>  d >= exp(logB)
    v = vals.astype(np.float64)
    f = freq.astype(np.float64)
    logv = np.log(v)
    mask = logv >= float(logB)
    tail = float(np.sum(f[mask] * v[mask]) / float(2**int(m)))
    return tail


@dataclass(frozen=True)
class Row:
    eps: float
    rq: GammaCert | None
    logS: GammaCert | None
    tail_prob_at_rq: float | None
    tail_prob_at_logS: float | None
    primes_for_rq: List[int] | None
    primes_for_logS: List[int] | None


def main() -> None:
    ap = argparse.ArgumentParser(description="Optimize gamma_cert_m(eps) over q and audit tail mass for Fold_m.")
    ap.add_argument("--m", type=int, default=24)
    ap.add_argument("--eps-list", type=str, default="1e-3,1e-6,1e-9")
    ap.add_argument("--q-max", type=int, default=17)
    ap.add_argument(
        "--rq-json",
        type=str,
        default="",
        help="Optional JSON with r_q rows (e.g. artifacts/export/fold_collision_pressure_multifractal_q60.json).",
    )
    ap.add_argument("--no-rq", action="store_true", help="Skip r_q-based gamma_cert.")
    ap.add_argument("--no-logS", action="store_true", help="Skip logS-based (finite-m exact) gamma_cert.")
    ap.add_argument("--no-tail", action="store_true", help="Skip tail-mass computation under pi_m.")
    ap.add_argument("--no-primes", action="store_true", help="Skip prime-register budget suggestion.")
    ap.add_argument(
        "--output",
        type=str,
        default=str(export_dir() / "fold_tail_budget_gamma_cert.json"),
        help="Output JSON path.",
    )
    args = ap.parse_args()

    m = int(args.m)
    q_max = int(args.q_max)
    eps_list = _parse_float_list(args.eps_list)
    if m < 2:
        raise SystemExit("Require --m >= 2")
    if q_max < 2:
        raise SystemExit("Require --q-max >= 2")
    if not eps_list:
        raise SystemExit("Empty --eps-list")

    # Precompute histogram once (enables exact logS and tail mass).
    vals: np.ndarray | None = None
    freq: np.ndarray | None = None
    logS_by_q: Dict[int, float] | None = None
    if (not args.no_logS) or (not args.no_tail):
        vals, freq = _fold_counts_hist(m)
        if not args.no_logS:
            logS_by_q = _logS_from_hist(vals, freq, q_max=q_max)

    # Prepare r_q table if requested.
    rq_by_q: Dict[int, float] | None = None
    if not args.no_rq:
        if args.rq_json:
            rq_by_q = _rq_from_pressure_json(Path(args.rq_json), q_max=q_max)
        else:
            if q_max <= 17:
                rq_by_q = _rq_from_exact_table(q_max=q_max)
            else:
                default_json = export_dir() / "fold_collision_pressure_multifractal_q60.json"
                rq_by_q = _rq_from_pressure_json(default_json, q_max=q_max)

    rows: List[Row] = []
    for eps in eps_list:
        rq_cert = gamma_cert_from_rq(m=m, eps=eps, rq_by_q=rq_by_q) if rq_by_q is not None else None
        logS_cert = (
            gamma_cert_from_logSq(m=m, eps=eps, logSq_by_q=logS_by_q) if logS_by_q is not None else None
        )

        tail_rq = None
        tail_logS = None
        if (not args.no_tail) and (vals is not None) and (freq is not None):
            if rq_cert is not None:
                tail_rq = _tail_mass_from_hist(vals, freq, m=m, logB=logB_from_gamma(m=m, gamma=rq_cert.gamma))
            if logS_cert is not None:
                tail_logS = _tail_mass_from_hist(vals, freq, m=m, logB=logB_from_gamma(m=m, gamma=logS_cert.gamma))

        primes_rq = None
        primes_logS = None
        if not args.no_primes:
            if rq_cert is not None:
                logB = logB_from_gamma(m=m, gamma=rq_cert.gamma)
                primes_rq, _logP = prime_list_for_log_target(math.log(2.0) + float(logB))
            if logS_cert is not None:
                logB = logB_from_gamma(m=m, gamma=logS_cert.gamma)
                primes_logS, _logP = prime_list_for_log_target(math.log(2.0) + float(logB))

        rows.append(
            Row(
                eps=float(eps),
                rq=rq_cert,
                logS=logS_cert,
                tail_prob_at_rq=tail_rq,
                tail_prob_at_logS=tail_logS,
                primes_for_rq=primes_rq,
                primes_for_logS=primes_logS,
            )
        )

    # Build JSON payload.
    def cert_to_dict(c: GammaCert | None) -> dict | None:
        if c is None:
            return None
        logB = logB_from_gamma(m=m, gamma=c.gamma)
        return {
            "gamma": float(c.gamma),
            "q_star": int(c.q_star),
            "logB": float(logB),
            "B": B_from_logB(float(logB)),
            "gamma_by_q": {str(k): float(v) for k, v in sorted(c.gamma_by_q.items())},
        }

    payload = {
        "params": {
            "m": m,
            "q_max": q_max,
            "eps_list": [float(e) for e in eps_list],
            "rq_source": (args.rq_json if args.rq_json else ("exact<=17 or default-q60-json")),
        },
        "rows": [
            {
                "eps": float(r.eps),
                "rq_cert": cert_to_dict(r.rq),
                "logS_cert": cert_to_dict(r.logS),
                "tail_prob_at_rq": float(r.tail_prob_at_rq) if r.tail_prob_at_rq is not None else None,
                "tail_prob_at_logS": float(r.tail_prob_at_logS) if r.tail_prob_at_logS is not None else None,
                "primes_for_rq": r.primes_for_rq,
                "primes_for_logS": r.primes_for_logS,
            }
            for r in rows
        ],
    }

    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Console summary.
    for r in rows:
        msg = f"[fold-tail-budget] m={m} eps={r.eps:g}"
        if r.rq is not None:
            logB = logB_from_gamma(m=m, gamma=r.rq.gamma)
            msg += f"  rq: q*={r.rq.q_star} gamma={r.rq.gamma:.6g} logB={logB:.6g}"
            if r.tail_prob_at_rq is not None:
                msg += f" tail~{r.tail_prob_at_rq:.3g}"
        if r.logS is not None:
            logB = logB_from_gamma(m=m, gamma=r.logS.gamma)
            msg += f"  logS: q*={r.logS.q_star} gamma={r.logS.gamma:.6g} logB={logB:.6g}"
            if r.tail_prob_at_logS is not None:
                msg += f" tail~{r.tail_prob_at_logS:.3g}"
        print(msg, flush=True)

    print(f"[fold-tail-budget] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

