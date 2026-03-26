#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the two-orbit (one-heavy, many-light) closed-form stationarity condition for R_w(delta).

We consider w=(p,q,...,q) on n symbols (n>=3), with q=(1-p)/(n-1), and verify:
  - The symmetric 4-orbit optimizer reduces to a 1D variable a=P(0,0) with
      c=(p-a)/(n-1), b=(1-delta-a)/(n-1), d=(delta+2a-2p)/((n-1)(n-2)).
  - The unique interior optimum a* satisfies the stationarity equation
      a* d*^2 = b* c*^2,
    equivalently the cubic certificate
      a(n-1)(delta+2a-2p)^2 = (n-2)^2(1-delta-a)(p-a)^2.
  - The achieved value matches the general scalar-collapse solution for R_w(delta).

Outputs:
  - artifacts/export/pom_diagonal_rate_two_orbit_cubic_audit.json
  - sections/generated/eq_pom_diagonal_rate_two_orbit_cubic_audit.tex
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict

import mpmath as mp

from common_diagonal_rate import solve_scalar_collapse
from common_paths import export_dir, generated_dir


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class Payload:
    n: int
    p: str
    q: str
    delta: str
    delta0: str
    a_star: str
    b_star: str
    c_star: str
    d_star: str
    stationarity_residual: str
    cubic_residual: str
    R_two_orbit: str
    R_general: str
    R_abs_diff: str
    general_A: str
    general_kappa: str


def _bisect_root(f, lo, hi, *, tol, max_iter=200):
    flo = f(lo)
    fhi = f(hi)
    if flo * fhi > 0:
        raise ValueError("Root not bracketed.")
    for _ in range(max_iter):
        mid = (lo + hi) / 2
        fmid = f(mid)
        if abs(fmid) <= tol:
            return mid
        if flo * fmid < 0:
            hi, fhi = mid, fmid
        else:
            lo, flo = mid, fmid
    return (lo + hi) / 2


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit two-orbit cubic stationarity for diagonal-coupling R_w(delta).")
    parser.add_argument("--dps", type=int, default=90, help="Decimal precision (default: 90).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TeX outputs.")
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 60:
        raise SystemExit("Require --dps >= 60 for stable outputs.")
    mp.mp.dps = dps

    t0 = time.time()
    print("[pom-diagonal-rate-two-orbit] start", flush=True)

    # Example parameters.
    n = 7
    p = mp.mpf("0.40")
    q = (1 - p) / (n - 1)
    delta0 = mp.mpf(1) - (p * p + (n - 1) * q * q)
    delta = mp.mpf("0.20")
    if not (0 < delta < delta0):
        raise RuntimeError("Chosen delta is not in (0,delta0).")

    # Feasible interior interval for a=P(0,0).
    eps = mp.mpf(10) ** (-(mp.mp.dps // 3))
    lo = p - delta / 2 + eps  # d>0
    hi = min(p, 1 - delta) - eps  # c>0 and b>0
    if not (lo < hi):
        raise RuntimeError("Empty feasible interval for a.")

    def cubic_f(a):
        left = a * (n - 1) * (delta + 2 * a - 2 * p) ** 2
        right = (n - 2) ** 2 * (1 - delta - a) * (p - a) ** 2
        return left - right

    a_star = _bisect_root(cubic_f, lo, hi, tol=mp.mpf(10) ** (-(mp.mp.dps // 2)))

    c_star = (p - a_star) / (n - 1)
    b_star = (1 - delta - a_star) / (n - 1)
    d_star = (delta + 2 * a_star - 2 * p) / ((n - 1) * (n - 2))

    stat_res = abs(a_star * d_star * d_star - b_star * c_star * c_star)
    cubic_res = abs(cubic_f(a_star))

    # Closed-form value.
    R_two = (
        a_star * mp.log(a_star / (p * p))
        + (n - 1) * b_star * mp.log(b_star / (q * q))
        + 2 * (n - 1) * c_star * mp.log(c_star / (p * q))
        + (n - 1) * (n - 2) * d_star * mp.log(d_star / (q * q))
    )

    # Compare to general scalar-collapse solver.
    w = [p] + [q] * (n - 1)
    sol = solve_scalar_collapse(w, delta, dps=dps)
    R_gen = sol.R
    diff = abs(R_two - R_gen)

    payload = Payload(
        n=int(n),
        p=mp.nstr(p, 25),
        q=mp.nstr(q, 25),
        delta=mp.nstr(delta, 25),
        delta0=mp.nstr(delta0, 25),
        a_star=mp.nstr(a_star, 25),
        b_star=mp.nstr(b_star, 25),
        c_star=mp.nstr(c_star, 25),
        d_star=mp.nstr(d_star, 25),
        stationarity_residual=mp.nstr(stat_res, 10),
        cubic_residual=mp.nstr(cubic_res, 10),
        R_two_orbit=mp.nstr(R_two, 25),
        R_general=mp.nstr(R_gen, 25),
        R_abs_diff=mp.nstr(diff, 10),
        general_A=mp.nstr(sol.A, 25),
        general_kappa=mp.nstr(sol.kappa, 25),
    )

    if not args.no_output:
        out_json = export_dir() / "pom_diagonal_rate_two_orbit_cubic_audit.json"
        _write_json(out_json, asdict(payload))

        tex = "\n".join(
            [
                "% Auto-generated by scripts/exp_pom_diagonal_rate_two_orbit_cubic_audit.py",
                "\\[",
                "w=(p,q,\\dots,q),\\quad q=\\frac{1-p}{n-1},\\quad"
                "c=\\frac{p-a}{n-1},\\ b=\\frac{1-\\delta-a}{n-1},\\ d=\\frac{\\delta+2a-2p}{(n-1)(n-2)}.",
                "\\]",
                "\\[",
                "a(n-1)(\\delta+2a-2p)^{2}=(n-2)^{2}(1-\\delta-a)(p-a)^{2},\\qquad a d^{2}=b c^{2}.",
                "\\]",
                "\\[",
                f"\\text{{Example: }}n={n},\\ p={mp.nstr(p,10)},\\ \\delta={mp.nstr(delta,10)},\\ a^\\star\\approx {mp.nstr(a_star,15)},\\ R\\approx {mp.nstr(R_gen,15)}.",
                "\\]",
                "",
            ]
        )
        out_tex = generated_dir() / "eq_pom_diagonal_rate_two_orbit_cubic_audit.tex"
        _write_text(out_tex, tex)

        print(f"[pom-diagonal-rate-two-orbit] wrote {out_json}", flush=True)
        print(f"[pom-diagonal-rate-two-orbit] wrote {out_tex}", flush=True)

    # Hard checks.
    if stat_res > mp.mpf("1e-20"):
        raise RuntimeError("Stationarity residual too large.")
    if diff > mp.mpf("1e-20"):
        raise RuntimeError("Two-orbit value does not match general solver.")

    dt = time.time() - t0
    print(
        "[pom-diagonal-rate-two-orbit] checks:"
        f" stat_res={mp.nstr(stat_res,5)} diff={mp.nstr(diff,5)} seconds={dt:.3f}",
        flush=True,
    )
    print("[pom-diagonal-rate-two-orbit] done", flush=True)


if __name__ == "__main__":
    main()

