#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Character-energy decomposition for the (3,3,5) Dirichlet–Mertens constant tensor.

We use the full tensor C^{(3,3,5)}_{a,b,c} exported by:
  artifacts/export/sync_kernel_real_input_40_arity_3d_N2_335.json
and form the centered tensor:
  C~_{a,b,c} = C_{a,b,c} - M/45,
where M = sum_{a,b,c} C_{a,b,c}.

Define the unnormalized 3D Fourier transform on G=(Z/3)^2 x (Z/5):
  C_hat(j1,j2,j3) = sum_{a,b,c} C~_{a,b,c} * w3^{j1 a + j2 b} * w5^{j3 c},
with w3=exp(2πi/3), w5=exp(2πi/5).

Then Parseval gives:
  sum_{a,b,c} |C~_{a,b,c}|^2 = (1/45) * sum_{j in G} |C_hat(j)|^2,
and the inverse transform yields a rank-1 outer-product decomposition after flattening.

Outputs:
  - artifacts/export/arity_335_character_energy.json
  - sections/generated/tab_arity_335_character_energy_head.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir, paper_root


def _load_json(rel: str) -> dict:
    return json.loads((paper_root() / rel).read_text(encoding="utf-8"))


def _w(n: int, k: int) -> complex:
    return complex(math.cos(2.0 * math.pi * k / n), math.sin(2.0 * math.pi * k / n))


@dataclass(frozen=True)
class ModeRow:
    j1: int
    j2: int
    j3: int
    is_pure_collision: bool
    energy: float
    energy_frac: float
    energy_cum: float


def write_table_tex(path: Path, rows: List[ModeRow], parseval_rel_err: float) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Character-energy head for the centered $((3,3,5))$ tensor "
        "$\\widetilde C=C-\\mathsf{M}/45$ under the full group "
        "$G=(\\mathbb{Z}/3)^2\\times(\\mathbb{Z}/5)$. "
        "We list the largest Fourier modes $|\\widehat{\\widetilde C}(j)|^2$ "
        "(unnormalized DFT), their energy fractions, and cumulative energy. "
        f"Parseval relative error: {parseval_rel_err:.2e}.}}"
    )
    lines.append("\\label{tab:arity_335_character_energy_head}")
    lines.append("\\begin{tabular}{r r r r r r}")
    lines.append("\\toprule")
    lines.append("$j_1$ & $j_2$ & $j_3$ & pure $N_2$ & $|\\widehat{\\widetilde C}(j)|^2$ & cum\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.j1} & {r.j2} & {r.j3} & "
            f"{'yes' if r.is_pure_collision else 'no'} & "
            f"{r.energy:.6e} & {r.energy_cum:.6f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute character-energy head for the (3,3,5) constant tensor.")
    parser.add_argument(
        "--in-json",
        type=str,
        default="artifacts/export/sync_kernel_real_input_40_arity_3d_N2_335.json",
        help="Input JSON (relative to paper root).",
    )
    parser.add_argument("--head", type=int, default=12, help="Number of top modes to report.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "arity_335_character_energy.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_arity_335_character_energy_head.tex"),
    )
    args = parser.parse_args()

    payload = _load_json(str(args.in_json))
    d = payload["triple_class_C"]["3x3x5"]
    M = float(payload["mathsf_M"])

    # Build tensor C[a,b,c].
    C = np.zeros((3, 3, 5), dtype=np.float64)
    for key, v in d.items():
        a, b, c = (int(x) for x in key.split(","))
        C[a, b, c] = float(v)

    Cc = C - (M / 45.0)

    w3 = _w(3, 1)
    w5 = _w(5, 1)

    # Unnormalized DFT over G.
    modes: List[Tuple[Tuple[int, int, int], complex]] = []
    for j1 in range(3):
        for j2 in range(3):
            for j3 in range(5):
                s = 0.0 + 0.0j
                for a in range(3):
                    for b in range(3):
                        for c in range(5):
                            s += complex(Cc[a, b, c]) * (w3 ** (j1 * a + j2 * b)) * (w5 ** (j3 * c))
                modes.append(((j1, j2, j3), s))

    energies = [abs(z) ** 2 for _, z in modes]
    E_total = float(sum(energies))

    # Parseval audit.
    lhs = float(np.sum(Cc * Cc))
    rhs = E_total / 45.0
    parseval_rel_err = abs(lhs - rhs) / max(1e-300, lhs)

    # Sort by energy descending, excluding the trivial mode (0,0,0) which is ~0 by centering.
    items = []
    for (j1, j2, j3), z in modes:
        e = float(abs(z) ** 2)
        items.append((e, j1, j2, j3, z))
    items.sort(reverse=True, key=lambda t: t[0])

    head = int(args.head)
    rows: List[ModeRow] = []
    cum = 0.0
    for e, j1, j2, j3, _ in items:
        if j1 == 0 and j2 == 0 and j3 == 0:
            continue
        frac = e / E_total if E_total > 0 else 0.0
        cum += frac
        rows.append(
            ModeRow(
                j1=int(j1),
                j2=int(j2),
                j3=int(j3),
                is_pure_collision=(int(j1) == 0 and int(j2) == 0 and int(j3) != 0),
                energy=e,
                energy_frac=frac,
                energy_cum=cum,
            )
        )
        if len(rows) >= head:
            break

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(
        json.dumps(
            {
                "M": M,
                "parseval": {"lhs_sum_sq": lhs, "rhs_sum_sq": rhs, "rel_err": parseval_rel_err},
                "E_total_hat": E_total,
                "head": [asdict(r) for r in rows],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(f"[arity-335-char-energy] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows, parseval_rel_err=parseval_rel_err)
    print(f"[arity-335-char-energy] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

