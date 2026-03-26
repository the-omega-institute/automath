#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compute a small Renyi-q projection entropy spectrum for Fold_m (q=2..17).

We enumerate Fold_m fibers for moderate m and compute:
  S_q(m) = sum_x d_m(x)^q,  q=2..7
  pi_m(x) = d_m(x)/2^m
  H_q(m) = -log sum_x pi_m(x)^q = -log( S_q(m) / 2^(q m) )

For q=2,3,4, the paper gives exact finite-state collision kernels (A2, A3, A4), hence exact Perron roots:
  r2: x^3 - 2x^2 - 2x + 2 = 0
  r3: x^3 - 2x^2 - 4x + 2 = 0
  r4: x^5 - 2x^4 - 7x^3 - 2x + 2 = 0
and entropy rates:
  h_q = log(2^q / r_q).

For q=5..8, we output a numerical "fingerprint" by estimating the exponential growth base
from ratios S_q(m)/S_q(m-1), with Aitken Δ^2 acceleration on the last three ratios.

For q=5..16, we use exact Perron roots recovered from verified integer recurrences
(small-order recurrences for q=5..8; higher-order for q>=9).

Outputs (default):
  - artifacts/export/fold_collision_renyi_spectrum.json
  - sections/generated/tab_fold_collision_renyi_spectrum.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from itertools import product
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress, fold_m, word_to_str


PRECOMPUTED_RQ = {
    # q=5..8: exact Perron roots from verified recurrences
    5: 4.800521005045,
    6: 5.999420196605,
    7: 7.505689291928,
    8: 9.398674561950,
    9: 11.778421934989,
    10: 14.771098354824,
    11: 18.535847481911,
    12: 23.273459728285,
    13: 29.237338790942,
    14: 36.747376282795,
    15: 46.207510260773,
    16: 58.127951897329,
    17: 73.153329263205,
}


def collision_counts(m: int, progress: Progress | None = None) -> Dict[str, int]:
    counts: Dict[str, int] = {}
    total = 1 << m
    for i, bits in enumerate(product([0, 1], repeat=m), start=1):
        x = word_to_str(fold_m(bits))
        counts[x] = counts.get(x, 0) + 1
        if progress is not None:
            progress.tick(f"m={m} i={i}/{total} distinct={len(counts)}")
    return counts


def s_q_from_counts(counts: Dict[str, int], q: int) -> int:
    if q <= 0:
        raise ValueError("q must be positive")
    if q == 1:
        return sum(counts.values())
    if q == 2:
        return sum(v * v for v in counts.values())
    if q == 3:
        return sum(v * v * v for v in counts.values())
    # generic power
    return sum(int(v**q) for v in counts.values())


def perron_root_r2() -> float:
    # Largest real root of x^3 - 2x^2 - 2x + 2 = 0 via Newton.
    def f(x: float) -> float:
        return x**3 - 2.0 * x**2 - 2.0 * x + 2.0

    def df(x: float) -> float:
        return 3.0 * x**2 - 4.0 * x - 2.0

    x = 2.5
    for _ in range(50):
        x = x - f(x) / df(x)
    return x


def perron_root_r3() -> float:
    # Largest real root of x^3 - 2x^2 - 4x + 2 = 0 via Newton.
    def f(x: float) -> float:
        return x**3 - 2.0 * x**2 - 4.0 * x + 2.0

    def df(x: float) -> float:
        return 3.0 * x**2 - 4.0 * x - 4.0

    x = 3.1
    for _ in range(50):
        x = x - f(x) / df(x)
    return x


def perron_root_r4() -> float:
    # Largest real root of x^5 - 2x^4 - 7x^3 - 2x + 2 = 0 via Newton.
    def f(x: float) -> float:
        return x**5 - 2.0 * x**4 - 7.0 * x**3 - 2.0 * x + 2.0

    def df(x: float) -> float:
        return 5.0 * x**4 - 8.0 * x**3 - 21.0 * x**2 - 2.0

    x = 3.85
    for _ in range(80):
        x = x - f(x) / df(x)
    return x


def aitken_limit(x0: float, x1: float, x2: float) -> float | None:
    """Aitken Δ^2 acceleration for a scalar sequence."""
    d1 = x1 - x0
    d2 = x2 - x1
    denom = d2 - d1
    if abs(denom) < 1e-18:
        return None
    return x0 - (d1 * d1) / denom


def write_table_tex(path: Path, rows: List[Dict[str, object]]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{A small R\\'enyi projection-entropy fingerprint for the Fold$_m$ output distribution "
        "$\\pi_m(x)=d_m(x)/2^m$. For $q=2,3,4$, $r_q$ is exact (from the finite-state collision kernels); "
        "for $q\\ge 5$, $r_q$ is exact from verified integer recurrences.}"
    )
    lines.append("\\label{tab:fold_collision_renyi_spectrum}")
    lines.append("\\begin{tabular}{r r r l}")
    lines.append("\\toprule")
    lines.append("$q$ & $r_q$ & $h_q=\\log(2^q/r_q)$ & note\\\\")
    lines.append("\\midrule")
    for r in rows:
        q = int(r["q"])  # type: ignore[arg-type]
        rq = float(r["r_q"])  # type: ignore[arg-type]
        hq = float(r["h_q"])  # type: ignore[arg-type]
        note = str(r["note"])
        lines.append(f"{q} & {rq:.12f} & {hq:.12f} & {note}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute Renyi-q collision spectrum for Fold_m by enumeration.")
    parser.add_argument("--m-min", type=int, default=8, help="Minimum m for enumeration table.")
    parser.add_argument("--m-max", type=int, default=18, help="Maximum m for enumeration table.")
    parser.add_argument("--q-max", type=int, default=17, help="Maximum q (>=2) for spectrum.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_renyi_spectrum.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_renyi_spectrum.tex"),
        help="Output LaTeX table path.",
    )
    args = parser.parse_args()

    if args.m_min < 2 or args.m_max < args.m_min:
        raise SystemExit("Require m_max >= m_min >= 2")
    if args.q_max < 2:
        raise SystemExit("Require q_max >= 2")

    prog = Progress("renyi-spectrum", every_seconds=20.0)

    qs = list(range(2, args.q_max + 1))
    # Enumerate only for q needing ratio estimates (q=5..8 by default).
    qs_enum = [q for q in qs if (q >= 5 and q not in PRECOMPUTED_RQ)]
    S: Dict[int, Dict[int, int]] = {q: {} for q in qs_enum}
    if qs_enum:
        for m in range(args.m_min, args.m_max + 1):
            counts = collision_counts(m, progress=prog)
            for q in qs_enum:
                S[q][m] = s_q_from_counts(counts, q)
            print(f"[renyi-spectrum] m={m} |X_m|={len(counts)}", flush=True)

    r2 = perron_root_r2()
    r3 = perron_root_r3()
    r4 = perron_root_r4()

    rows: List[Dict[str, object]] = []
    for q in qs:
        if q == 2:
            rq = r2
            note = "exact (A2)"
        elif q == 3:
            rq = r3
            note = "exact (A3)"
        elif q == 4:
            rq = r4
            note = "exact (A4)"
        elif q in PRECOMPUTED_RQ:
            rq = PRECOMPUTED_RQ[q]
            note = "exact (recurrence)"
        else:
            # estimate from last three ratios S(m)/S(m-1)
            ms = sorted(S[q].keys())
            if len(ms) < 4:
                raise SystemExit("Need at least 4 m values to estimate r_q")
            m2, m1, m0 = ms[-1], ms[-2], ms[-3]
            r0 = S[q][m0] / float(S[q][m0 - 1]) if (m0 - 1) in S[q] else S[q][m0] / float(S[q][ms[-4]])
            r1 = S[q][m1] / float(S[q][m0])
            r2r = S[q][m2] / float(S[q][m1])
            rq_hat = aitken_limit(r0, r1, r2r)
            rq = rq_hat if rq_hat is not None else r2r
            note = f"enum+ratio (m={m0},{m1},{m2})"

        hq = math.log((2.0**q) / rq)
        rows.append({"q": q, "r_q": rq, "h_q": hq, "note": note})

    payload: Dict[str, object] = {
        "m_min": args.m_min,
        "m_max": args.m_max,
        "q_max": args.q_max,
        "S_q": {str(q): {str(m): int(S[q][m]) for m in sorted(S[q].keys())} for q in qs_enum},
        "r2_exact": r2,
        "r3_exact": r3,
        "r4_exact": r4,
        "r_q_precomputed": PRECOMPUTED_RQ,
        "rows": rows,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"[renyi-spectrum] wrote {jout}", flush=True)

    write_table_tex(Path(args.tex_out), rows)
    print(f"[renyi-spectrum] wrote {args.tex_out}", flush=True)


if __name__ == "__main__":
    main()

