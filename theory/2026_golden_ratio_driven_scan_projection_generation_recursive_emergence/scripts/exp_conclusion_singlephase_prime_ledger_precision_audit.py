#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit certificates for single-phase prime-ledger embeddings and precision budgets.

What this script audits:
1) Finite-box injectivity checks for the phase map built from sqrt(prime) weights.
2) Numerical checks of the multiquadratic norm lower bound:
      |sum a_j sqrt(p_j) - k| >= M^{-(2^r-1)}.
3) Precision-window bounds on finite boxes [-A,A]^r:
      r log2(2A+1) <= B_{r,A} <= 1 + (2^r-1) log2(3 A r sqrt(p_r)),
   where B_{r,A} = ceil(log2(2/delta_{r,A})).
4) Density heuristics via maximal circular gap shrinkage as box radius grows.

Outputs:
- artifacts/export/conclusion_singlephase_prime_ledger_precision_audit.json
- sections/generated/tab_conclusion_singlephase_prime_ledger_precision_audit.tex
"""

from __future__ import annotations

import itertools
import json
import math
import random
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import mpmath as mp

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class PrecisionCase:
    r: int
    A: int
    count: int
    delta_true: float
    delta_cert: float
    B_lower: int
    B_true: int
    B_upper: int
    injective_finite_box: bool
    bound_ok: bool


def _first_primes(n: int) -> List[int]:
    out: List[int] = []
    x = 2
    while len(out) < n:
        is_prime = True
        lim = int(math.isqrt(x))
        for p in out:
            if p > lim:
                break
            if x % p == 0:
                is_prime = False
                break
        if is_prime:
            out.append(x)
        x += 1
    return out


def _phase_value(vec: Sequence[int], primes: Sequence[int]) -> mp.mpf:
    s = mp.mpf("0")
    for a, p in zip(vec, primes):
        s += mp.mpf(a) * mp.sqrt(p)
    return mp.frac(s)


def _all_vectors(r: int, A: int) -> Iterable[Tuple[int, ...]]:
    return itertools.product(range(-A, A + 1), repeat=r)


def _min_circle_distance(values: List[mp.mpf]) -> mp.mpf:
    vals = sorted(values)
    n = len(vals)
    if n < 2:
        return mp.mpf("1")
    gaps = [vals[i + 1] - vals[i] for i in range(n - 1)]
    gaps.append(vals[0] + 1 - vals[-1])
    return min(gaps)


def _finite_box_injective(values: List[mp.mpf], digits: int = 80) -> bool:
    # Numerical injectivity witness on a finite box.
    keys = [mp.nstr(v, digits) for v in values]
    return len(keys) == len(set(keys))


def _norm_bound_random_checks(
    *,
    rng: random.Random,
    trials_per_r: int = 120,
    A: int = 5,
) -> Dict[str, object]:
    results: Dict[str, object] = {}
    for r in (2, 3, 4, 5):
        primes = _first_primes(r)
        passed = 0
        tested = 0
        max_gap_ratio = mp.mpf("0")
        for _ in range(trials_per_r):
            coeffs = [rng.randint(-A, A) for _ in range(r)]
            if all(c == 0 for c in coeffs):
                continue
            s = mp.mpf("0")
            for c, p in zip(coeffs, primes):
                s += mp.mpf(c) * mp.sqrt(p)
            # Sample k near s to stress near-integer cases.
            k0 = int(mp.nint(s))
            k = k0 + rng.randint(-2, 2)
            alpha = s - mp.mpf(k)
            if mp.almosteq(alpha, 0):
                # Degenerate rare numerical corner; skip.
                continue
            M = abs(k) + sum(abs(c) * mp.sqrt(p) for c, p in zip(coeffs, primes))
            bound = mp.power(M, -(2**r - 1))
            tested += 1
            if abs(alpha) + mp.mpf("1e-70") >= bound:
                passed += 1
            ratio = bound / abs(alpha)
            if ratio > max_gap_ratio:
                max_gap_ratio = ratio
        results[str(r)] = {
            "tested": tested,
            "passed": passed,
            "pass_ratio": float(passed / tested) if tested else 1.0,
            "max(bound/|alpha|)": float(max_gap_ratio),
        }
        print(
            f"[singlephase-audit] norm-bound r={r} tested={tested} passed={passed}",
            flush=True,
        )
    return results


def _density_gap_scan(primes: Sequence[int]) -> List[Dict[str, object]]:
    rows: List[Dict[str, object]] = []
    r = len(primes)
    for L in (4, 8, 12):
        values = [_phase_value(v, primes) for v in _all_vectors(r, L)]
        values_sorted = sorted(values)
        max_gap = mp.mpf("0")
        for i in range(len(values_sorted) - 1):
            gap = values_sorted[i + 1] - values_sorted[i]
            if gap > max_gap:
                max_gap = gap
        tail_gap = values_sorted[0] + 1 - values_sorted[-1]
        if tail_gap > max_gap:
            max_gap = tail_gap
        rows.append(
            {
                "r": r,
                "L": L,
                "count": len(values),
                "max_gap": float(max_gap),
            }
        )
        print(
            f"[singlephase-audit] density-scan r={r} L={L} count={len(values)} max_gap={float(max_gap):.6e}",
            flush=True,
        )
    return rows


def _precision_cases() -> List[PrecisionCase]:
    cases: List[PrecisionCase] = []
    for (r, A) in ((2, 2), (3, 2), (4, 2), (5, 1)):
        primes = _first_primes(r)
        vals = [_phase_value(v, primes) for v in _all_vectors(r, A)]
        count = len(vals)
        delta_true = _min_circle_distance(vals)
        injective = _finite_box_injective(vals, digits=90)

        # Certified lower separation from the multiquadratic norm bound.
        C = mp.mpf("3")
        delta_cert = mp.power(C * A * r * mp.sqrt(primes[-1]), -(2**r - 1))
        bound_ok = bool(delta_true + mp.mpf("1e-70") >= delta_cert)

        B_true = int(math.ceil(math.log2(float(2 / delta_true))))
        B_lower = int(math.floor(r * math.log2(2 * A + 1)))
        B_upper = int(math.ceil(1 + (2**r - 1) * math.log2(3 * A * r * math.sqrt(primes[-1]))))

        cases.append(
            PrecisionCase(
                r=r,
                A=A,
                count=count,
                delta_true=float(delta_true),
                delta_cert=float(delta_cert),
                B_lower=B_lower,
                B_true=B_true,
                B_upper=B_upper,
                injective_finite_box=injective,
                bound_ok=bound_ok and (B_lower <= B_true <= B_upper),
            )
        )
        print(
            f"[singlephase-audit] precision-case r={r} A={A} N={count} "
            f"B=[{B_lower},{B_true},{B_upper}] injective={injective}",
            flush=True,
        )
    return cases


def _tex_table(cases: List[PrecisionCase], density_rows: List[Dict[str, object]]) -> str:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        "\\caption{单相位素数账本在有限盒上的精度审计。"
        "$\\delta_{r,A}$ 表示 $[-A,A]^r$ 上观测到的最小圆弧分离度，"
        "$\\delta_{\\mathrm{cert}}=(3Ar\\sqrt{p_r})^{-(2^r-1)}$ "
        "表示由多平方根范数界给出的证书化下界。}"
    )
    lines.append("\\label{tab:conclusion_singlephase_prime_ledger_precision_audit}")
    lines.append("\\begin{tabular}{c c c c c c c c}")
    lines.append("\\toprule")
    lines.append("$r$ & $A$ & $|\\mathcal E_{r,A}|$ & $\\delta_{r,A}$ & $\\delta_{\\mathrm{cert}}$ & $B_{\\mathrm{lb}}$ & $B_{r,A}$ & $B_{\\mathrm{ub}}$\\\\")
    lines.append("\\midrule")
    for row in cases:
        lines.append(
            f"{row.r} & {row.A} & {row.count} & "
            f"{row.delta_true:.3e} & {row.delta_cert:.3e} & "
            f"{row.B_lower} & {row.B_true} & {row.B_upper}\\\\"
        )
    lines.append("\\midrule")
    lines.append("\\multicolumn{8}{c}{\\textit{稠密性启发式（固定 $r=3$，统计 $[-L,L]^3$ 上最大圆弧间隙）：}}\\\\")
    for d in density_rows:
        lines.append(
            f"\\multicolumn{{2}}{{c}}{{L={d['L']}}} & "
            f"\\multicolumn{{2}}{{c}}{{N={d['count']}}} & "
            f"\\multicolumn{{4}}{{c}}{{$\\max\\,\\mathrm{{gap}}={d['max_gap']:.3e}$}}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    return "\n".join(lines) + "\n"


def main() -> None:
    t0 = time.time()
    mp.mp.dps = 120
    rng = random.Random(20260228)
    print("[singlephase-audit] start", flush=True)

    cases = _precision_cases()
    norm_checks = _norm_bound_random_checks(rng=rng, trials_per_r=140, A=6)
    density_rows = _density_gap_scan(_first_primes(3))

    payload = {
        "meta": {
            "script": Path(__file__).name,
            "seconds": float(time.time() - t0),
            "mp_dps": mp.mp.dps,
            "seed": 20260228,
        },
        "precision_cases": [asdict(c) for c in cases],
        "norm_bound_random_checks": norm_checks,
        "density_gap_scan": density_rows,
        "all_precision_case_bounds_ok": all(c.bound_ok for c in cases),
    }

    out_json = export_dir() / "conclusion_singlephase_prime_ledger_precision_audit.json"
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    out_tex = generated_dir() / "tab_conclusion_singlephase_prime_ledger_precision_audit.tex"
    out_tex.parent.mkdir(parents=True, exist_ok=True)
    out_tex.write_text(_tex_table(cases, density_rows), encoding="utf-8")

    print(f"[singlephase-audit] wrote {out_json}", flush=True)
    print(f"[singlephase-audit] wrote {out_tex}", flush=True)
    print(f"[singlephase-audit] done seconds={time.time() - t0:.3f}", flush=True)


if __name__ == "__main__":
    main()
