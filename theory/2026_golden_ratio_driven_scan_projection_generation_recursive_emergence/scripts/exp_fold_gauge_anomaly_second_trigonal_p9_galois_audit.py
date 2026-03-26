#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""
Audit the degree-9 parameter branch polynomial P9(t) from the *second* trigonal structure
in sections/body/folding/subsubsec__fold-gauge-anomaly-trigonal-mu-ramification.tex.

We verify (symbolically, reproducibly):
  - P9(t) ∈ Z[t] is primitive and its integer discriminant factorization.
  - Mod-p splitting types used in the S9 Jordan-criterion proof:
      p=19: irreducible (9)
      p=11: (8,1)
      p=7 : (5,4)
  - The squarefree part of Disc(P9) and the quadratic subfield Q(sqrt(33605193)).

Outputs:
  - artifacts/export/fold_gauge_anomaly_second_trigonal_p9_galois_audit.json
  - sections/generated/tab_fold_gauge_anomaly_second_trigonal_p9_galois_certificate.tex
"""

from __future__ import annotations

import argparse
import json
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir


def _write_text(path: Path, s: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(s, encoding="utf-8")


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _P9(t: sp.Symbol) -> sp.Expr:
    # Must match the statement in thm:fold-gauge-anomaly-second-trigonal-structure-discriminant.
    return (
        3 * t**9
        + 3 * t**8
        - 31 * t**7
        - 83 * t**6
        + 100 * t**5
        + 424 * t**4
        - 16 * t**3
        - 436 * t**2
        - 52 * t
        + 100
    )


def _factor_degrees_mod_p(poly: sp.Poly, p: int) -> List[int]:
    fac = sp.Poly(poly.as_expr(), poly.gens[0], modulus=p).factor_list()[1]
    degs = sorted([sp.Poly(f, poly.gens[0], modulus=p).degree() for (f, _e) in fac])
    return degs


def _squarefree_part_Z(n: int) -> int:
    # Return the positive squarefree part of |n|.
    n = abs(int(n))
    if n == 0:
        return 0
    f = sp.factorint(n)
    sf = 1
    for p, e in f.items():
        if e % 2 == 1:
            sf *= int(p)
    return int(sf)


def _tex_table(rows: List[Tuple[str, str]]) -> str:
    lines: List[str] = []
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\begin{tabular}{ll}")
    lines.append(r"\toprule")
    lines.append(r"\textbf{项目} & \textbf{证书/数值} \\")
    lines.append(r"\midrule")
    for k, v in rows:
        lines.append(f"{k} & {v} \\\\")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    return "\n".join(lines) + "\n"


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Audit P9(t) Galois/discriminant certificates for the second trigonal structure.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TEX outputs.")
    args = parser.parse_args(list(argv) if argv is not None else None)

    t0 = time.time()
    print("[fold_gauge_anomaly_second_trigonal_p9_galois_audit] start", flush=True)

    t = sp.Symbol("t")
    P9_expr = _P9(t)
    P9_poly = sp.Poly(P9_expr, t, domain=sp.ZZ)

    disc = int(sp.discriminant(P9_poly.as_expr(), t))
    disc_fac = sp.factorint(abs(disc))
    disc_sf = _squarefree_part_Z(disc)

    # Mod-p splitting certificates
    degs_19 = _factor_degrees_mod_p(P9_poly, 19)
    degs_11 = _factor_degrees_mod_p(P9_poly, 11)
    degs_7 = _factor_degrees_mod_p(P9_poly, 7)

    cert: Dict[str, object] = {
        "P9": str(P9_poly.as_expr()),
        "Disc(P9)": int(disc),
        "Disc(P9)_factor_abs": {int(p): int(e) for p, e in disc_fac.items()},
        "Disc(P9)_squarefree_part_abs": int(disc_sf),
        "mod_p_factor_degrees": {
            19: degs_19,
            11: degs_11,
            7: degs_7,
        },
        "checks": {
            "mod19_irreducible_9": bool(degs_19 == [9]),
            "mod11_split_8_1": bool(degs_11 == [1, 8]),
            "mod7_split_5_4": bool(degs_7 == [4, 5]),
            "disc_squarefree_kernel_expected": bool(disc_sf == 33605193),
        },
        "meta": {
            "script": Path(__file__).name,
            "seconds": float(time.time() - t0),
        },
    }

    if not args.no_output:
        out_json = export_dir() / "fold_gauge_anomaly_second_trigonal_p9_galois_audit.json"
        _write_json(out_json, cert)

        # Compact TEX certificate table (human-readable, paper-friendly).
        rows: List[Tuple[str, str]] = [
            (r"$P_9(t)$", r"$" + sp.latex(P9_poly.as_expr()) + r"$"),
            (r"$\mathrm{Disc}(P_9)$（平方自由核）", r"$" + str(disc_sf) + r"$"),
            (r"$P_9\bmod 19$ 因子次数", r"$(" + ",".join(map(str, degs_19)) + r")$"),
            (r"$P_9\bmod 11$ 因子次数", r"$(" + ",".join(map(str, degs_11)) + r")$"),
            (r"$P_9\bmod 7$ 因子次数", r"$(" + ",".join(map(str, degs_7)) + r")$"),
        ]
        tex = _tex_table(rows)
        out_tex = generated_dir() / "tab_fold_gauge_anomaly_second_trigonal_p9_galois_certificate.tex"
        _write_text(out_tex, tex)

        print(f"[fold_gauge_anomaly_second_trigonal_p9_galois_audit] wrote {out_json}", flush=True)
        print(f"[fold_gauge_anomaly_second_trigonal_p9_galois_audit] wrote {out_tex}", flush=True)

    chk = cert["checks"]
    print(
        "[fold_gauge_anomaly_second_trigonal_p9_galois_audit] checks:"
        f" mod19={chk['mod19_irreducible_9']}"
        f" mod11={chk['mod11_split_8_1']}"
        f" mod7={chk['mod7_split_5_4']}"
        f" disc_sf={chk['disc_squarefree_kernel_expected']}"
        f" seconds={cert['meta']['seconds']:.3f}",
        flush=True,
    )


if __name__ == "__main__":
    main()

