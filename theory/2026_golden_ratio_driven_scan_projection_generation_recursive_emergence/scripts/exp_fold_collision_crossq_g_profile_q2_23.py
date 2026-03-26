#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Cross-q inequality diagnostic for Fold collision Perron roots.

For each moment order q we have an exponential base r_q defined by:
  S_q(m) := sum_x d_m(x)^q = Theta(r_q^m).

Using the finite-dimensional norm inequality for a length-n vector v:
  ||v||_p <= n^(1/p - 1/q) ||v||_q,     2 <= p < q,
and applying it to v = (d_m(x))_{x in X_m} with n=|X_m|~phi^m gives:
  log r_q >= (q/p) log r_p + (1 - q/p) log phi.

Equivalently, the profile
  g(q) := (log r_q - log phi)/q
is monotone nondecreasing in q.

This script reads audited r_q from the generated moment-spectrum tables (q=2..23)
and emits:
  - a small g(q) table,
  - a monotonicity check (as a regression guardrail for future extensions).

Outputs (default):
  - artifacts/export/fold_collision_crossq_g_profile_q2_23.json
  - sections/generated/tab_fold_collision_crossq_g_profile_q2_23.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir, paper_root


_RQ_TABLES_REL = [
    "sections/generated/tab_fold_collision_moment_spectrum_k2_8.tex",
    "sections/generated/tab_fold_collision_moment_spectrum_k9_17.tex",
    "sections/generated/tab_fold_collision_moment_spectrum_k18_23.tex",
]


def _tex_float(x: str) -> float:
    x = x.strip().strip("$").rstrip("\\")
    x = x.replace("\\,", "").replace("\\;", "").replace("\\!", "")
    return float(x)


def _load_rq_from_generated_tables() -> Dict[int, float]:
    out: Dict[int, float] = {}
    for rel in _RQ_TABLES_REL:
        p = paper_root() / rel
        if not p.is_file():
            raise FileNotFoundError(f"Missing required generated table: {p}")
        txt = p.read_text(encoding="utf-8")
        for line in txt.splitlines():
            line = line.strip()
            if not line:
                continue
            if not re.match(r"^\d+\s*&", line):
                continue
            parts = [s.strip() for s in line.split("&")]
            if len(parts) < 4:
                continue
            q = int(parts[0])
            rq = _tex_float(parts[3])
            out[q] = float(rq)
    return out


@dataclass(frozen=True)
class Row:
    q: int
    r_q: float
    g_q: float
    delta_prev: float | None


def _write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Cross-$q$ profile $g(q)=(\\log r_q-\\log\\varphi)/q$ from audited Perron roots $r_q$ "
        "(Tables~\\ref{tab:fold_collision_moment_spectrum_k2_8}, \\ref{tab:fold_collision_moment_spectrum_k9_17}, "
        "\\ref{tab:fold_collision_moment_spectrum_k18_23}). "
        "By the norm inequality on $d_m$ with $|X_m|\\sim\\varphi^m$, $g(q)$ must be nondecreasing in $q$.}"
    )
    lines.append("\\label{tab:fold_collision_crossq_g_profile_q2_23}")
    lines.append("\\begin{tabular}{r r r}")
    lines.append("\\toprule")
    lines.append("$q$ & $g(q)$ & $g(q)-g(q-1)$\\\\")
    lines.append("\\midrule")
    for r in rows:
        if r.delta_prev is None:
            lines.append(f"{r.q} & {r.g_q:.12f} & ---\\\\")
        else:
            lines.append(f"{r.q} & {r.g_q:.12f} & {r.delta_prev:.2e}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Cross-q g-profile monotonicity check for Fold collision spectrum.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_crossq_g_profile_q2_23.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_crossq_g_profile_q2_23.tex"),
        help="Output LaTeX table path.",
    )
    ap.add_argument("--tol", type=float, default=1e-12, help="Tolerance for monotonicity violations.")
    args = ap.parse_args()

    rq = _load_rq_from_generated_tables()
    qs = sorted(rq.keys())
    if qs != list(range(2, 24)):
        # We can still run, but the audit expectation is q=2..23 contiguous.
        print(f"[crossq-g] WARNING: expected q=2..23 contiguous, got q={qs}", flush=True)

    phi = (1.0 + 5.0**0.5) / 2.0
    logphi = math.log(phi)

    rows: List[Row] = []
    violations: List[Tuple[int, float, int, float]] = []
    prev_g = None
    prev_q = None
    for q in qs:
        gq = (math.log(float(rq[q])) - logphi) / float(q)
        delta = None
        if prev_g is not None:
            delta = float(gq - prev_g)
            if gq < prev_g - float(args.tol):
                violations.append((int(prev_q), float(prev_g), int(q), float(gq)))  # type: ignore[arg-type]
        rows.append(Row(q=int(q), r_q=float(rq[q]), g_q=float(gq), delta_prev=delta))
        prev_g = float(gq)
        prev_q = int(q)

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "source_tables": list(_RQ_TABLES_REL),
        "phi": phi,
        "tol": float(args.tol),
        "rows": [asdict(r) for r in rows],
        "violations": [{"q_prev": a, "g_prev": b, "q": c, "g": d} for (a, b, c, d) in violations],
        "ok_monotone_nondecreasing": (len(violations) == 0),
    }
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[crossq-g] wrote {jout}", flush=True)

    tout = Path(str(args.tex_out))
    _write_table_tex(tout, rows)
    print(f"[crossq-g] wrote {tout}", flush=True)

    if violations:
        raise SystemExit(f"Monotonicity violated in {len(violations)} adjacent steps (see JSON).")


if __name__ == "__main__":
    main()

