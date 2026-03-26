#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Reconstruct phi from the Fold collision Renyi spectrum (audited r_q table).

We read audited Perron roots r_q from the generated moment-spectrum tables:
  - sections/generated/tab_fold_collision_moment_spectrum_k2_8.tex
  - sections/generated/tab_fold_collision_moment_spectrum_k9_17.tex
  - sections/generated/tab_fold_collision_moment_spectrum_k18_23.tex

Define
  h_q := log(2^q / r_q),
  s_q := h_q / q = log 2 - (log r_q)/q,
so that s_q -> log(2/sqrt(phi)) and hence
  phi = 4 * exp(-2 * lim_{q->infty} s_q).

To accelerate the (often slow) q-direction convergence, we apply Aitken Δ^2:
  s_inf(q) ≈ s_{q+2} - (s_{q+2}-s_{q+1})^2 / (s_{q+2}-2 s_{q+1}+s_q),
and define the internal estimator:
  phi_hat_q := 4 * exp(-2*s_inf(q)).

Outputs (default):
  - artifacts/export/fold_collision_phi_reconstruction_from_renyi.json
  - sections/generated/tab_fold_collision_phi_reconstruction_from_renyi.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir, paper_root


_RQ_TABLES_REL = [
    "sections/generated/tab_fold_collision_moment_spectrum_k2_8.tex",
    "sections/generated/tab_fold_collision_moment_spectrum_k9_17.tex",
    "sections/generated/tab_fold_collision_moment_spectrum_k18_23.tex",
]


def _tex_float(x: str) -> float:
    x = x.strip()
    x = x.strip("$")
    x = x.rstrip("\\")
    # Remove common TeX spacing tokens.
    x = x.replace("\\,", "")
    x = x.replace("\\;", "")
    x = x.replace("\\!", "")
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
            # Rows are of the form:
            #   12 & 13 & 15 & 23.273... & ...
            # so we match a leading integer followed by '&'.
            if not re.match(r"^\d+\s*&", line):
                continue
            parts = [s.strip() for s in line.split("&")]
            if len(parts) < 4:
                continue
            q = int(parts[0])
            rq = _tex_float(parts[3])
            out[q] = float(rq)
    return out


def _aitken_limit(x0: float, x1: float, x2: float) -> float | None:
    denom = x2 - 2.0 * x1 + x0
    if abs(denom) < 1e-18:
        return None
    return x2 - ((x2 - x1) ** 2) / denom


@dataclass(frozen=True)
class Row:
    q: int
    r_q: float
    s_q: float
    phi_hat_raw: float
    s_inf_aitken: float | None
    phi_hat_aitken: float | None
    abs_err_aitken: float | None


def _write_table_tex(path: Path, rows: List[Row], *, phi_true: float) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Internal reconstruction of $\\varphi$ from the collision spectrum. "
        "We read audited Perron roots $r_q$ (Tables~\\ref{tab:fold_collision_moment_spectrum_k2_8}, "
        "\\ref{tab:fold_collision_moment_spectrum_k9_17}, \\ref{tab:fold_collision_moment_spectrum_k18_23}) "
        "and form $s_q=h_q/q=\\log 2-(\\log r_q)/q$. "
        "Applying Aitken $\\Delta^2$ acceleration in the $q$-direction gives $s_q^{(\\infty)}$ and "
        "$\\widehat\\varphi_q:=4e^{-2s_q^{(\\infty)}}$ (no Fibonacci input).}"
    )
    lines.append("\\label{tab:fold_collision_phi_reconstruction_from_renyi}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$q$ & $s_q$ & $s_q^{(\\infty)}$ (Aitken) & $\\widehat\\varphi_q$ & $|\\widehat\\varphi_q-\\varphi|$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        if r.s_inf_aitken is None or r.phi_hat_aitken is None or r.abs_err_aitken is None:
            continue
        lines.append(
            f"{r.q} & {r.s_q:.12f} & {r.s_inf_aitken:.12f} & {r.phi_hat_aitken:.12f} & {r.abs_err_aitken:.2e}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Reconstruct phi from audited Fold collision Renyi spectrum.")
    ap.add_argument("--q-min-table", type=int, default=8, help="Minimum q to include in the TeX table.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_phi_reconstruction_from_renyi.json"),
        help="Output JSON path.",
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_phi_reconstruction_from_renyi.tex"),
        help="Output LaTeX table path.",
    )
    args = ap.parse_args()

    rq = _load_rq_from_generated_tables()
    qs = sorted(rq.keys())
    if not qs:
        raise SystemExit("No r_q values found in generated tables.")

    phi_true = (1.0 + 5.0**0.5) / 2.0
    log2 = math.log(2.0)

    # s_q values (from r_q).
    s: Dict[int, float] = {q: (log2 - math.log(float(rq[q])) / float(q)) for q in qs}

    rows: List[Row] = []
    for q in qs:
        sq = float(s[q])
        phi_hat_raw = 4.0 * math.exp(-2.0 * sq)
        s_inf = None
        phi_hat_aitken = None
        abs_err = None
        if (q + 1) in s and (q + 2) in s:
            s_inf = _aitken_limit(s[q], s[q + 1], s[q + 2])
            if s_inf is not None:
                phi_hat_aitken = 4.0 * math.exp(-2.0 * float(s_inf))
                abs_err = abs(float(phi_hat_aitken) - float(phi_true))
        rows.append(
            Row(
                q=int(q),
                r_q=float(rq[q]),
                s_q=sq,
                phi_hat_raw=float(phi_hat_raw),
                s_inf_aitken=(float(s_inf) if s_inf is not None else None),
                phi_hat_aitken=(float(phi_hat_aitken) if phi_hat_aitken is not None else None),
                abs_err_aitken=(float(abs_err) if abs_err is not None else None),
            )
        )

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "source_tables": list(_RQ_TABLES_REL),
        "phi_true": phi_true,
        "rows": [asdict(r) for r in rows],
    }
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[phi-reconstruct] wrote {jout}", flush=True)

    # Write TeX table (only rows with Aitken available and q>=q_min_table).
    q_min_table = int(args.q_min_table)
    table_rows = [r for r in rows if r.q >= q_min_table]
    tout = Path(str(args.tex_out))
    _write_table_tex(tout, table_rows, phi_true=phi_true)
    print(f"[phi-reconstruct] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

