#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Verify functoriality (projection/marginal invariance) of Dirichlet–Mertens constant tensors.

We compare:
  - 1D constants: artifacts/export/sync_kernel_real_input_40_arity.json
      arity_class_C[m][a]   for chi mod m
  - 2D constants: artifacts/export/sync_kernel_real_input_40_arity_2d.json
      pair_class_C["mxn"]["a,b"]  for (chi mod m, nu mod n)
  - 3D constants: artifacts/export/sync_kernel_real_input_40_arity_3d.json
      triple_class_C["axbxc"]["a,b,c"] for (chi mod a, nu mod b, third axis mod c)

Functoriality claim (paper-level):
  Marginalizing a refined tensor over a forgotten label equals the coarser tensor.
In particular, for (m1,m2,m3)=(3,3,5) in our default 3D output:
  sum_{c mod 5} C_{a,b,c}^{(3,3,5)} = C_{a,b}^{(3,3)}  (from 2D output)
  sum_{b mod 3, c mod 5} C_{a,b,c}^{(3,3,5)} = C_a^{(3)} (from 1D output)
and total sum matches the global Mertens constant.

Outputs (default):
  - artifacts/export/real_input_40_dirichlet_mertens_functoriality.json
  - sections/generated/tab_real_input_40_dirichlet_mertens_functoriality.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir, paper_root


def _load_json(rel: str) -> dict:
    p = paper_root() / rel
    return json.loads(p.read_text(encoding="utf-8"))


def _parse_key_abc(key: str) -> Tuple[int, int, int]:
    a, b, c = (int(x) for x in key.split(","))
    return a, b, c


def _parse_key_ab(key: str) -> Tuple[int, int]:
    a, b = (int(x) for x in key.split(","))
    return a, b


@dataclass(frozen=True)
class CheckRow:
    triple: str
    max_abs_diff_3d_to_2d: float
    max_abs_diff_3d_to_1d: float
    abs_diff_total_sum: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify functoriality of Dirichlet–Mertens tensors (real-input 40).")
    parser.add_argument("--triple", type=str, default="3x3x5", help="Triple key present in 3D JSON (default: 3x3x5)")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "real_input_40_dirichlet_mertens_functoriality.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_real_input_40_dirichlet_mertens_functoriality.tex"),
    )
    args = parser.parse_args()

    j1 = _load_json("artifacts/export/sync_kernel_real_input_40_arity.json")
    j2 = _load_json("artifacts/export/sync_kernel_real_input_40_arity_2d.json")
    j3 = _load_json("artifacts/export/sync_kernel_real_input_40_arity_3d.json")

    triple_key = str(args.triple)
    if "triple_class_C" not in j3 or triple_key not in j3["triple_class_C"]:
        raise SystemExit(f"Missing triple_class_C[{triple_key}] in 3D JSON.")

    m1, m2, m3 = (int(x) for x in triple_key.split("x"))
    # In our construction: axis1 is chi mod m1, axis2 is nu mod m2, axis3 is third axis mod m3.
    pair_key = f"{m1}x{m2}"
    if "pair_class_C" not in j2 or pair_key not in j2["pair_class_C"]:
        raise SystemExit(f"Missing pair_class_C[{pair_key}] in 2D JSON.")

    if "arity_class_C" not in j1 or str(m1) not in j1["arity_class_C"]:
        raise SystemExit(f"Missing arity_class_C[{m1}] in 1D JSON.")

    C3: Dict[str, float] = j3["triple_class_C"][triple_key]
    C2: Dict[str, float] = j2["pair_class_C"][pair_key]
    C1: Dict[str, float] = j1["arity_class_C"][str(m1)]
    M_total = float(j3.get("mathsf_M", float("nan")))

    # Build marginal sums from 3D.
    marg_ab = {(a, b): 0.0 for a in range(m1) for b in range(m2)}
    marg_a = {a: 0.0 for a in range(m1)}
    total = 0.0
    for k, v in C3.items():
        a, b, c = _parse_key_abc(k)
        marg_ab[(a, b)] += float(v)
        marg_a[a] += float(v)
        total += float(v)

    # Compare to 2D.
    diffs_ab: List[float] = []
    for a in range(m1):
        for b in range(m2):
            v3 = marg_ab[(a, b)]
            v2 = float(C2[f"{a},{b}"])
            diffs_ab.append(abs(v3 - v2))

    # Compare to 1D (chi mod m1).
    diffs_a: List[float] = []
    for a in range(m1):
        v3 = marg_a[a]
        v1 = float(C1[str(a)])
        diffs_a.append(abs(v3 - v1))

    row = CheckRow(
        triple=triple_key,
        max_abs_diff_3d_to_2d=max(diffs_ab) if diffs_ab else 0.0,
        max_abs_diff_3d_to_1d=max(diffs_a) if diffs_a else 0.0,
        abs_diff_total_sum=abs(total - M_total),
    )

    payload = {
        "triple": row.triple,
        "m1": m1,
        "m2": m2,
        "m3": m3,
        "pair_key": pair_key,
        "mathsf_M_total": M_total,
        "total_sum_from_tensor": total,
        "max_abs_diff_3d_to_2d": row.max_abs_diff_3d_to_2d,
        "max_abs_diff_3d_to_1d": row.max_abs_diff_3d_to_1d,
        "abs_diff_total_sum": row.abs_diff_total_sum,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[functoriality] wrote {jout}", flush=True)

    # Write LaTeX summary table.
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Functoriality (projection invariance) check for Dirichlet--Mertens constant tensors. "
        "We compare (i) the 3D tensor marginalized to 2D, (ii) the 3D tensor marginalized to 1D, and (iii) the total-sum constraint "
        "$\\sum C=\\mathsf{M}$. Values are max absolute discrepancies (should be near floating error).}"
    )
    lines.append("\\label{tab:real_input_40_dirichlet_mertens_functoriality}")
    lines.append("\\begin{tabular}{l r r r}")
    lines.append("\\toprule")
    lines.append("triple & max $|\\sum_c C_{a,b,c}-C_{a,b}|$ & max $|\\sum_{b,c} C_{a,b,c}-C_a|$ & $|\\sum C-\\mathsf{M}|$\\\\")
    lines.append("\\midrule")
    lines.append(
        f"{row.triple} & {row.max_abs_diff_3d_to_2d:.3e} & {row.max_abs_diff_3d_to_1d:.3e} & {row.abs_diff_total_sum:.3e}\\\\"
    )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    tex = Path(args.tex_out)
    tex.parent.mkdir(parents=True, exist_ok=True)
    tex.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[functoriality] wrote {tex}", flush=True)


if __name__ == "__main__":
    main()

