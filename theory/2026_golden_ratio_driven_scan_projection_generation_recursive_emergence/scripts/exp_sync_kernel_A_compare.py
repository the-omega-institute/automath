#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Generate the A-compare table for sync-kernel variants (single entrypoint).

This script is intended to be the *only* command needed by the user:

  python3 scripts/exp_sync_kernel_A_compare.py

It will run prerequisite scripts if their JSON artifacts are missing, then
write a LaTeX table fragment into sections/generated/.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List

from common_paths import export_dir, generated_dir, paper_root, scripts_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class Prereq:
    name: str
    script: str
    out_rel: str


PREREQS: List[Prereq] = [
    Prereq(
        name="sync_kernel_primitive_spectrum",
        script="exp_sync_kernel_primitive_spectrum.py",
        out_rel="artifacts/export/sync_kernel_primitive_spectrum.json",
    ),
    Prereq(
        name="sync_kernel_real_input_40",
        script="exp_sync_kernel_real_input_40.py",
        out_rel="artifacts/export/sync_kernel_real_input_40.json",
    ),
    Prereq(
        name="collision_kernel_A2_primitive",
        script="exp_collision_kernel_A2_primitive.py",
        out_rel="artifacts/export/collision_kernel_A2_primitive.json",
    ),
    Prereq(
        name="collision_kernel_A2_finite_part",
        script="exp_collision_kernel_A2_finite_part.py",
        out_rel="artifacts/export/collision_kernel_A2_finite_part.json",
    ),
]


def _read_json(path: Path) -> Dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _ensure_prereqs(no_run: bool, prog: Progress) -> None:
    for pr in PREREQS:
        out_path = paper_root() / pr.out_rel
        if out_path.is_file() and out_path.stat().st_size > 0:
            continue
        if no_run:
            raise SystemExit(f"Missing prerequisite output (run disabled): {out_path}")
        script_path = scripts_dir() / pr.script
        if not script_path.is_file():
            raise SystemExit(f"Missing prerequisite script: {script_path}")
        cmd = [sys.executable, str(script_path)]
        print(f"[A-compare] RUN {pr.name}: {' '.join(cmd)}", flush=True)
        subprocess.check_call(cmd, cwd=str(paper_root()))
        prog.tick(f"ran {pr.name}")
        if not (out_path.is_file() and out_path.stat().st_size > 0):
            raise SystemExit(f"Expected output missing/empty: {out_path}")


def _fmt_float(x: float, digits: int = 10) -> str:
    return f"{x:.{digits}g}"


def _tex_escape(s: str) -> str:
    return s.replace("_", r"\_")


def _make_table(sync10: Dict[str, Any], real40: Dict[str, Any], coll_prim: Dict[str, Any], coll_fp: Dict[str, Any]) -> str:
    # 10-state sync kernel (unconstrained input)
    B0 = float(sync10.get("pf_eigenvalue", 3.0))
    h0 = float(sync10.get("pf_eigenvalue", 3.0))
    logM0 = float(sync10["log_M_B"])
    C0 = float(sync10["C_B"])
    det0 = "(z-1)(z+1)(3z-1)(z^3-z^2+z+1)"
    p0 = sync10.get("primitive_p_n", [])
    a0 = sync10.get("traces_a_n", [])

    # 40-state real-input kernel
    lam1 = float(real40["lambda_pf"])
    h1 = float(real40["entropy_log"])
    logM1 = float(real40["log_mathfrak_M"])
    C1 = float(real40["zeta_residue_C"])
    det1 = str(real40["det_factorization"])
    p1 = real40.get("p_n", [])
    a1 = real40.get("a_n", [])

    # Collision kernel A2 (3-state SFT)
    r2 = float(coll_fp["r2"])
    det2 = "1-2z-2z^2+2z^3"
    # JSON is 1-indexed lists with a_n[0]=0, p_n[0]=0
    p2 = coll_prim.get("p_n", [0])

    def first_terms(xs: List[Any], n: int = 10) -> str:
        vals = [str(int(v)) for v in xs[:n]]
        return "(" + ",".join(vals) + ")" if vals else "()"

    rows = [
        {
            "name": r"$K_{\mathrm{sync}}$（10 状态）",
            "A": r"$\{0,1\}$",
            "B": r"$\{0,1,2\}$",
            "states": "10",
            "lambda": _fmt_float(B0, 12),
            "h": r"$\log 3$",
            "det": f"${det0}$",
            "a10": first_terms(a0, 10),
            "p10": f"${first_terms(p0, 10)}$",
            "logM": _fmt_float(logM0, 16),
            "C": _fmt_float(C0, 12),
        },
        {
            "name": r"$K_{\mathrm{real}}$（40 状态）",
            "A": r"$\{0,1\}$（真实输入约束）",
            "B": r"$\{0,1,2\}$（受约束）",
            "states": "40",
            "lambda": _fmt_float(lam1, 12),
            "h": _tex_escape(_fmt_float(h1, 12)),
            "det": f"${_tex_escape(det1)}$",
            "a10": first_terms(a1, 10),
            "p10": f"${first_terms(p1, 10)}$",
            "logM": _fmt_float(logM1, 16),
            "C": _fmt_float(C1, 12),
        },
        {
            "name": r"$A_2$（折叠碰撞核）",
            "A": r"---",
            "B": r"---",
            "states": "3",
            "lambda": _fmt_float(r2, 12),
            "h": r"$\log r_2$",
            "det": f"${det2}$",
            "a10": "---",
            "p10": f"${first_terms(p2[1:], 10)}$",
            "logM": _fmt_float(float(coll_fp["log_mathfrak_M"]), 16),
            "C": _fmt_float(float(coll_fp["C"]), 12),
        },
    ]

    # Note: keep it as a fragment (input-able).
    # Use \log\mathfrak{M} naming consistent with appendix.
    lines = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\small")
    lines.append(r"\setlength{\tabcolsep}{6pt}")
    lines.append(r"\renewcommand{\arraystretch}{1.15}")
    lines.append(
        r"\caption{核对比：同步核与折叠碰撞核的不变量对照（由脚本 \texttt{scripts/exp\_sync\_kernel\_A\_compare.py} 生成）。}"
    )
    lines.append(r"\label{tab:sync-kernel-A-compare}")
    lines.append(r"\begin{tabular}{@{}lccccccc@{}}")
    lines.append(r"\toprule")
    lines.append(
        r"核 & $A$ & $B=A{+}A$ & $|Q|$ & $\lambda_{\max}$ & $\det(I-zM_K)$ & $(p_n)_{n\le 10}$ & $\log\mathfrak{M}$ \\"
    )
    lines.append(r"\midrule")
    for r in rows:
        lines.append(
            " & ".join(
                [
                    r["name"],
                    r["A"],
                    r["B"],
                    r["states"],
                    r["lambda"],
                    r["det"],
                    r["p10"],
                    r["logM"],
                ]
            )
            + r" \\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate A-compare LaTeX table for sync kernels")
    parser.add_argument("--no-run", action="store_true", help="Do not run prerequisite scripts")
    parser.add_argument(
        "--output-tex",
        type=str,
        default="",
        help="Output .tex path (default: sections/generated/tab_sync_kernel_A_compare.tex)",
    )
    parser.add_argument(
        "--output-json",
        type=str,
        default="",
        help="Optional JSON summary output path (default: artifacts/export/sync_kernel_A_compare.json)",
    )
    args = parser.parse_args()

    prog = Progress(label="A-compare", every_seconds=20.0)
    print("[A-compare] start", flush=True)

    _ensure_prereqs(no_run=args.no_run, prog=prog)

    sync10_path = export_dir() / "sync_kernel_primitive_spectrum.json"
    real40_path = export_dir() / "sync_kernel_real_input_40.json"
    coll_prim_path = export_dir() / "collision_kernel_A2_primitive.json"
    coll_fp_path = export_dir() / "collision_kernel_A2_finite_part.json"
    sync10 = _read_json(sync10_path)
    real40 = _read_json(real40_path)
    coll_prim = _read_json(coll_prim_path)
    coll_fp = _read_json(coll_fp_path)
    prog.tick("loaded prerequisite JSON")

    tex = _make_table(sync10, real40, coll_prim, coll_fp)
    out_tex = Path(args.output_tex) if args.output_tex else (generated_dir() / "tab_sync_kernel_A_compare.tex")
    _write_text(out_tex, tex)
    print(f"[A-compare] wrote {out_tex}", flush=True)

    if args.output_json or True:
        out_json = Path(args.output_json) if args.output_json else (export_dir() / "sync_kernel_A_compare.json")
        payload = {
            "sources": {
                "sync10": str(sync10_path),
                "real40": str(real40_path),
            },
            "table_tex": str(out_tex),
            "sync10": {
                "states": 10,
                "pf_eigenvalue": sync10.get("pf_eigenvalue", 3.0),
                "det_factorization": sync10.get("det_factorization", {}),
                "primitive_p_n": sync10.get("primitive_p_n", []),
                "log_M": sync10.get("log_M_B", None),
                "C": sync10.get("C_B", None),
            },
            "real40": {
                "states": 40,
                "lambda_pf": real40.get("lambda_pf", None),
                "entropy_log": real40.get("entropy_log", None),
                "det_factorization": real40.get("det_factorization", None),
                "p_n": real40.get("p_n", []),
                "log_mathfrak_M": real40.get("log_mathfrak_M", None),
                "zeta_residue_C": real40.get("zeta_residue_C", None),
            },
        }
        _write_text(out_json, json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"[A-compare] wrote {out_json}", flush=True)

    print("[A-compare] done", flush=True)


if __name__ == "__main__":
    main()

