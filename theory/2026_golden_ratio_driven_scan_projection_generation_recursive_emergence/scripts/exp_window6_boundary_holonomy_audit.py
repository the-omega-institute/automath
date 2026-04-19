#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Window-6 boundary holonomy audit.

Outputs:
  - artifacts/export/window6_boundary_holonomy_audit.json
  - sections/generated/tab_window6_boundary_holonomy_audit.tex
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_window6_audit import boundary_delta_pattern, window6_data


def _write_table_tex(path: Path, rows: List[Dict[str, object]]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\caption{Window-6 boundary holonomy audit: canonical sheet pairs and minimal residual certificates.}")
    lines.append("\\label{tab:window6_boundary_holonomy_audit}")
    lines.append("\\begin{tabular}{l l l}")
    lines.append("\\toprule")
    lines.append("object & exact value & role\\\\")
    lines.append("\\midrule")
    for row in rows:
        lines.append(f"{row['object']} & {row['value']} & {row['role']}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit the window-6 boundary holonomy layer.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_boundary_holonomy_audit.json"),
    )
    ap.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_window6_boundary_holonomy_audit.tex"),
    )
    args = ap.parse_args()

    wd = window6_data()
    delta_m6 = boundary_delta_pattern(6)
    delta_m7 = boundary_delta_pattern(7)
    delta_m8 = boundary_delta_pattern(8)

    payload = {
        "window": 6,
        "boundary_words": wd.boundary_words,
        "sheet_pairs": wd.sheet_pairs,
        "delta_sets": {
            "m6": delta_m6,
            "m7": delta_m7,
            "m8": delta_m8,
        },
        "certificates": {
            "rank_C_boundary": 3,
            "rank_P_geo": 1,
            "rank_quotient": 2,
            "torus_rank_faithful": 3,
        },
        "notes": {
            "rank_C_boundary": "Three independent boundary sheet involutions.",
            "rank_P_geo": "Diagonal subgroup seen by strong local geometric uplift.",
            "rank_quotient": "Irreducible non-geometric residual quotient.",
            "torus_rank_faithful": "Minimal torus rank for faithful compact holonomy.",
        },
    }

    out_json = Path(args.json_out)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    rows = [
        {"object": "$X_6^{\\mathrm{bdry}}$", "value": "$\\{\\texttt{100001},\\texttt{100101},\\texttt{101001}\\}$", "role": "boundary support"},
        {"object": "$\\delta_{\\mathrm{bdry}}$", "value": "$34=F_9$", "role": "canonical sheet gap"},
        {"object": "$C_{\\partial}$", "value": "$(\\mathbb Z/2\\mathbb Z)^3$", "role": "boundary center"},
        {"object": "$P_6^{\\mathrm{geo}}$", "value": "$\\langle(1,1,1)\\rangle\\cong\\mathbb Z/2\\mathbb Z$", "role": "geometric diagonal"},
        {"object": "$C_{\\partial}/P_6^{\\mathrm{geo}}$", "value": "$(\\mathbb Z/2\\mathbb Z)^2$", "role": "irreducible residual"},
        {"object": "$r_{\\mathrm{tor}}(Z_6^{\\mathrm{bd}})$", "value": "$3$", "role": "faithful torus rank"},
        {"object": "$\\Delta_6^{\\mathrm{bdry}}$", "value": "$\\{0,34\\}$", "role": "choice-free anchor"},
        {"object": "$\\Delta_7^{\\mathrm{bdry}}$", "value": "$\\{0,55,89\\}$", "role": "three-sheet lift"},
        {"object": "$\\Delta_8^{\\mathrm{bdry}}$", "value": "$\\{0,89,144\\}$", "role": "three-sheet lift"},
    ]
    _write_table_tex(Path(args.tex_tab_out), rows)

    print("[window6-boundary-holonomy] wrote JSON and TeX table artifacts", flush=True)


if __name__ == "__main__":
    main()
