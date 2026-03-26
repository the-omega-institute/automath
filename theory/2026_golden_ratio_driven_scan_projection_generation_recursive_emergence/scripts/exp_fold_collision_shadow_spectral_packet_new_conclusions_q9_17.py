#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
New audit-layer conclusions built on the *audited* resonance objects (q=9..17):
  - Shadow spectral packet roots (r_q, lambda_q^-, mu_q) reconstructed from audited integer recurrences.
  - The two reference ratios in Table "shadow spectral packet":
      |mu_q|/r_{q-2},   |lambda_q^-|/r_{q-2},
    and the observed near-locking of arg(mu_q) around -1.83 rad.

This script adds four *directly checkable* derived outputs on the same audited set:

(A) Algebraic phase-lock residual certificate:
      zeta_q := mu_q / |mu_q|  (unit phase),
      rho_q  := |2 zeta_q^2 + zeta_q + 2|.
    The quadratic 2 z^2 + z + 2 = 0 has unit-circle roots
      z_* = (-1 ± i*sqrt(15))/4.
    We test proximity of zeta_q to the lower root (Im < 0) via rho_q and angle mismatch.

(B) Two independent inversions of r_{q-2} from the printed Table-33-style columns:
      r_{q-2}^{(mu)} := |mu_q| / (|mu_q|/r_{q-2}),
      r_{q-2}^{(-)}  := |lambda_q^-| / (|lambda_q^-|/r_{q-2}).
    We intentionally apply the same rounding used in the published table (6/4 decimals),
    so the mismatch is a pure "rounding-consistency" audit check.

(C) Two-step renormalization ratio:
      R_q := r_q / r_{q-2},
    computed from the inverted r_{q-2} values above.
    We also detect the "channel switch" crossing where |lambda_q^-|/r_{q-2} crosses 1.

Outputs:
  - artifacts/export/fold_collision_shadow_spectral_packet_new_conclusions_q9_17.json
  - sections/generated/tab_fold_collision_shadow_spectral_packet_algebraic_phase_residual_q9_17.tex
  - sections/generated/tab_fold_collision_shadow_spectral_packet_two_step_renormalization_q9_17.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

from common_paths import export_dir, generated_dir
from exp_fold_collision_shadow_spectral_packet_q9_17 import (
    RECS_2_8,
    RECS_9_17,
    _max_mod_nonreal_root,
    _outermost_negative_real_root,
    _perron_root,
    _poly_from_coeffs,
    _roots,
)


@dataclass(frozen=True)
class PhaseResidualRow:
    q: int
    mu_arg: float
    theta_alg: float
    delta_arg: float
    rho_poly: float
    chord_dist: float


@dataclass(frozen=True)
class TwoStepRenormRow:
    q: int
    r_q_print: float
    r_qm2_from_mu: float
    r_qm2_from_lambda: float
    r_qm2_abs_diff: float
    R_q_from_mu: float
    R_q_from_lambda: float
    abs_lambda_over_r_qm2_print: float
    channel_side: str


def _principal_arg(z: complex) -> float:
    return float(math.atan2(z.imag, z.real))


def _round_table_style(
    *,
    r_q: float,
    lambda_minus: float,
    mu_mod: float,
    mu_arg: float,
    r_qm2: float,
) -> Dict[str, float]:
    # Match the formatting in tab_fold_collision_shadow_spectral_packet_q9_17.tex.
    r_q_p = round(float(r_q), 6)
    lam_p = round(float(lambda_minus), 6)
    mu_mod_p = round(float(mu_mod), 6)
    mu_arg_p = round(float(mu_arg), 4)
    mu_over_p = round(float(mu_mod / r_qm2), 4)
    abs_lam_over_p = round(float(abs(lambda_minus) / r_qm2), 4)
    abs_lam_p = round(float(abs(lam_p)), 6)
    return {
        "r_q_print": r_q_p,
        "lambda_minus_print": lam_p,
        "abs_lambda_minus_print": abs_lam_p,
        "mu_mod_print": mu_mod_p,
        "mu_arg_print": mu_arg_p,
        "mu_over_r_qm2_print": mu_over_p,
        "abs_lambda_over_r_qm2_print": abs_lam_over_p,
    }


def _write_phase_residual_table_tex(path: Path, rows: List[PhaseResidualRow]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Algebraic phase-lock residual certificate for the resonance-region shadow packet "
        "($q=9,\\dots,17$). For each $q$, we take the unit phase "
        "$\\zeta_q:=\\mu_q/|\\mu_q|$ and test proximity to the unit-circle quadratic root "
        "$z_\\ast=(-1-\\mathrm{i}\\sqrt{15})/4$ of $2z^2+z+2=0$. We report "
        "$\\delta\\theta_q:=\\arg(\\zeta_q/z_\\ast)$ and the residual "
        "$\\rho_q:=|2\\zeta_q^2+\\zeta_q+2|$.}"
    )
    lines.append("\\label{tab:fold_collision_shadow_spectral_packet_algebraic_phase_residual_q9_17}")
    lines.append("\\begin{tabular}{r r r r r}")
    lines.append("\\toprule")
    lines.append("$q$ & $\\arg(\\mu_q)$ & $\\delta\\theta_q$ & $\\rho_q$ & $|\\zeta_q-z_\\ast|$\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"{r.q} & {r.mu_arg:.4f} & {r.delta_arg:.4f} & {r.rho_poly:.4f} & {r.chord_dist:.4f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_two_step_renorm_table_tex(path: Path, rows: List[TwoStepRenormRow]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.15}")
    lines.append(
        "\\caption{Two-step inversion of $r_{q-2}$ and a derived two-step renormalization ratio "
        "$R_q:=r_q/r_{q-2}$ for the resonance-region shadow packet ($q=9,\\dots,17$). "
        "We reconstruct $r_{q-2}$ in two independent ways from the table columns "
        "$|\\mu_q|/r_{q-2}$ and $|\\lambda_q^-|/r_{q-2}$, using the same rounding as the published "
        "shadow-packet table (6 decimals for $r_q,\\lambda_q^-,|\\mu_q|$ and 4 decimals for the ratios). "
        "The mismatch $|r_{q-2}^{(\\mu)}-r_{q-2}^{(-)}|$ is therefore a pure rounding-consistency check. "
        "We also record the sign of $|\\lambda_q^-|/r_{q-2}-1$ (the channel switch crosses at $q=12$).}"
    )
    lines.append("\\label{tab:fold_collision_shadow_spectral_packet_two_step_renormalization_q9_17}")
    lines.append("\\begin{tabular}{r r r r r r r}")
    lines.append("\\toprule")
    lines.append(
        "$q$ & $r_q$ & $r_{q-2}^{(\\mu)}$ & $r_{q-2}^{(-)}$ & $|\\Delta r|$ & $R_q$ & "
        "$|\\lambda_q^-|/r_{q-2}$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        # For R_q we print the average of the two reconstructions to reduce rounding noise.
        rqm2_avg = 0.5 * (r.r_qm2_from_mu + r.r_qm2_from_lambda)
        R_avg = r.r_q_print / rqm2_avg if rqm2_avg != 0 else float("nan")
        lines.append(
            f"{r.q} & {r.r_q_print:.6f} & {r.r_qm2_from_mu:.6f} & {r.r_qm2_from_lambda:.6f} & "
            f"{r.r_qm2_abs_diff:.6f} & {R_avg:.4f} & {r.abs_lambda_over_r_qm2_print:.4f}{r.channel_side}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _compute_shadow_packet_maps(*, dps: int) -> Tuple[Dict[int, float], Dict[int, List[complex]]]:
    # Recompute the same audited packet roots (same source as the base table script),
    # so this script is standalone and does not depend on any generated artifacts.
    recs_all = sorted([*RECS_2_8, *RECS_9_17], key=lambda r: r.q)
    r_map: Dict[int, float] = {}
    roots_map: Dict[int, List[complex]] = {}
    for rec in recs_all:
        poly = _poly_from_coeffs(rec.coeffs)
        roots = _roots(poly, dps=int(dps))
        r_map[rec.q] = _perron_root(roots)
        roots_map[rec.q] = roots
        print(f"[new-concl] precompute q={rec.q:2d} r_q={r_map[rec.q]:.12f}", flush=True)
    return r_map, roots_map


def main() -> None:
    parser = argparse.ArgumentParser(
        description="New audit-layer conclusions on top of the resonance shadow spectral packet (q=9..17)."
    )
    parser.add_argument("--dps", type=int, default=140, help="Decimal digits for sympy nroots (same as base scan).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_shadow_spectral_packet_new_conclusions_q9_17.json"),
    )
    parser.add_argument(
        "--tex-phase-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_shadow_spectral_packet_algebraic_phase_residual_q9_17.tex"),
    )
    parser.add_argument(
        "--tex-renorm-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_shadow_spectral_packet_two_step_renormalization_q9_17.tex"),
    )
    args = parser.parse_args()

    r_map, roots_map = _compute_shadow_packet_maps(dps=int(args.dps))

    # Algebraic target root (Im < 0) of 2 z^2 + z + 2 = 0.
    z_alg = complex(-0.25, -math.sqrt(15.0) / 4.0)
    theta_alg = _principal_arg(z_alg)

    phase_rows: List[PhaseResidualRow] = []
    renorm_rows: List[TwoStepRenormRow] = []

    switch_q: int | None = None
    for q in range(9, 18):
        roots = roots_map[q]
        rq = r_map[q]
        rqm2 = r_map[q - 2]

        lam_minus = _outermost_negative_real_root(roots)
        mu = _max_mod_nonreal_root(roots)
        mu_mod = float(abs(mu))
        mu_arg = _principal_arg(mu)

        # (A) algebraic residuals
        zeta = mu / abs(mu)
        zeta = zeta / abs(zeta)
        delta_arg = _principal_arg(zeta / z_alg)
        rho_poly = float(abs(2.0 * zeta * zeta + zeta + 2.0))
        chord = float(abs(zeta - z_alg))
        phase_rows.append(
            PhaseResidualRow(
                q=int(q),
                mu_arg=float(mu_arg),
                theta_alg=float(theta_alg),
                delta_arg=float(delta_arg),
                rho_poly=float(rho_poly),
                chord_dist=float(chord),
            )
        )

        # (B)(C) invert r_{q-2} from table-style rounded columns
        tbl = _round_table_style(r_q=rq, lambda_minus=lam_minus, mu_mod=mu_mod, mu_arg=mu_arg, r_qm2=rqm2)
        r_q_print = float(tbl["r_q_print"])
        mu_mod_print = float(tbl["mu_mod_print"])
        mu_over_print = float(tbl["mu_over_r_qm2_print"])
        abs_lam_print = float(tbl["abs_lambda_minus_print"])
        abs_lam_over_print = float(tbl["abs_lambda_over_r_qm2_print"])

        rqm2_from_mu = float(mu_mod_print / mu_over_print)
        rqm2_from_lam = float(abs_lam_print / abs_lam_over_print)
        dr = float(abs(rqm2_from_mu - rqm2_from_lam))

        R_mu = float(r_q_print / rqm2_from_mu)
        R_lam = float(r_q_print / rqm2_from_lam)

        side = "<" if abs_lam_over_print < 1.0 else ">"
        if switch_q is None and abs_lam_over_print > 1.0:
            switch_q = int(q)

        renorm_rows.append(
            TwoStepRenormRow(
                q=int(q),
                r_q_print=float(r_q_print),
                r_qm2_from_mu=float(rqm2_from_mu),
                r_qm2_from_lambda=float(rqm2_from_lam),
                r_qm2_abs_diff=float(dr),
                R_q_from_mu=float(R_mu),
                R_q_from_lambda=float(R_lam),
                abs_lambda_over_r_qm2_print=float(abs_lam_over_print),
                channel_side=str(side),
            )
        )

        print(
            f"[new-concl] q={q:2d} arg(mu)={mu_arg:.4f} delta_arg={delta_arg:.4f} "
            f"rho={rho_poly:.4f} |zeta-z*|={chord:.4f} "
            f"rqm2(mu)={rqm2_from_mu:.6f} rqm2(-)={rqm2_from_lam:.6f} R~={r_q_print/((rqm2_from_mu+rqm2_from_lam)/2):.4f} "
            f"|lambda|/rqm2={abs_lam_over_print:.4f}{side}",
            flush=True,
        )

    payload = {
        "target_quadratic": {"poly": "2 z^2 + z + 2", "z_alg_re": z_alg.real, "z_alg_im": z_alg.imag, "theta_alg": theta_alg},
        "phase_rows": [asdict(r) for r in phase_rows],
        "two_step_rows": [asdict(r) for r in renorm_rows],
        "channel_switch_q": switch_q,
    }
    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[new-concl] wrote {jout}", flush=True)

    _write_phase_residual_table_tex(Path(args.tex_phase_out), phase_rows)
    print(f"[new-concl] wrote {args.tex_phase_out}", flush=True)
    _write_two_step_renorm_table_tex(Path(args.tex_renorm_out), renorm_rows)
    print(f"[new-concl] wrote {args.tex_renorm_out}", flush=True)


if __name__ == "__main__":
    main()

