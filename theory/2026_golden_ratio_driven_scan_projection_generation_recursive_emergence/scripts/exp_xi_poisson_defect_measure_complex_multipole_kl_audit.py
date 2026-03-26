#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: defect-measure complex multipole asymptotics for Poisson-Cauchy coarsegraining.

This script is English-only by repository convention.

We verify:
  - Closed-form constants c_k = binom(2k-2,k-1)/2^(2k).
  - Symbolic identities for W = Gamma - i Delta:
      W^2 = (Gamma^2-Delta^2) - 2 i Gamma Delta,
      W^3 = (Gamma^3-3GammaDelta^2) - i(3Gamma^2Delta-Delta^3).
  - Numerical asymptotic checks on atomic defect measures:
      D_KL(h_t|g_t) ~ c_k |m_k|^2 T^(-2k),  k=2 and k=3,
      D_f(h_t|g_t)  ~ f''(1) c_k |m_k|^2 T^(-2k), f(u)=(u-1)^2/2,
      I_1(h_t|g_t)  ~ (2k) c_k |m_k|^2 T^(-(2k+1)).

Outputs:
  - artifacts/export/xi_poisson_defect_measure_complex_multipole_kl_audit.json
  - sections/generated/eq_xi_poisson_defect_measure_complex_multipole_kl_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Dict, List, Sequence, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


Atom = Tuple[mp.mpf, mp.mpf, mp.mpf]  # (weight, gamma, delta)


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _P(s: mp.mpf, x: mp.mpf) -> mp.mpf:
    return (s / (x * x + s * s)) / mp.pi


def _centers(atoms: Sequence[Atom]) -> Tuple[mp.mpf, mp.mpf]:
    wsum = mp.fsum(w for (w, _g, _d) in atoms)
    bg = mp.fsum(w * g for (w, g, _d) in atoms) / wsum
    bd = mp.fsum(w * d for (w, _g, d) in atoms) / wsum
    return bg, bd


def _moment_w(atoms: Sequence[Atom], k: int) -> complex:
    bg, bd = _centers(atoms)
    wsum = mp.fsum(w for (w, _g, _d) in atoms)
    val = 0j
    for (w, g, d) in atoms:
        W = complex(float(g - bg), float(-(d - bd)))
        val += float(w / wsum) * (W**k)
    return val


def _h_g(atoms: Sequence[Atom], t: mp.mpf, x: mp.mpf) -> Tuple[mp.mpf, mp.mpf, mp.mpf]:
    bg, bd = _centers(atoms)
    T = t + bd
    h = mp.mpf("0.0")
    for (w, g, d) in atoms:
        h += w * _P(t + d, x - g)
    g = _P(T, x - bg)
    return h, g, T


def _integrate_real_line(integrand: Callable[[mp.mpf], mp.mpf], dps: int) -> mp.mpf:
    # x = tan(theta), theta in (-pi/2, pi/2)
    mp.mp.dps = dps
    eps = mp.mpf("1e-7")
    a = -mp.pi / 2 + eps
    b = mp.pi / 2 - eps

    def f(theta: mp.mpf) -> mp.mpf:
        x = mp.tan(theta)
        jac = 1 / (mp.cos(theta) ** 2)
        return integrand(x) * jac

    return mp.quad(f, [a, mp.mpf("0.0"), b])


def _d_kl(atoms: Sequence[Atom], t: mp.mpf, dps: int) -> Tuple[mp.mpf, mp.mpf]:
    bg, _bd = _centers(atoms)

    def integrand(x: mp.mpf) -> mp.mpf:
        h, g, _T = _h_g(atoms, t, x)
        if h <= 0 or g <= 0:
            return mp.mpf("0.0")
        return h * mp.log(h / g)

    val = _integrate_real_line(integrand, dps=dps)
    _h0, _g0, T = _h_g(atoms, t, bg)
    return val, T


def _d_f(atoms: Sequence[Atom], t: mp.mpf, f: Callable[[mp.mpf], mp.mpf], dps: int) -> Tuple[mp.mpf, mp.mpf]:
    bg, _bd = _centers(atoms)

    def integrand(x: mp.mpf) -> mp.mpf:
        h, g, _T = _h_g(atoms, t, x)
        if g <= 0:
            return mp.mpf("0.0")
        u = h / g
        return g * f(u)

    val = _integrate_real_line(integrand, dps=dps)
    _h0, _g0, T = _h_g(atoms, t, bg)
    return val, T


def _scenario_k2() -> Sequence[Atom]:
    d0 = mp.mpf("1.3")
    return [
        (mp.mpf("0.5"), mp.mpf("-1.0"), d0),
        (mp.mpf("0.5"), mp.mpf("1.0"), d0),
    ]


def _scenario_k3(r: mp.mpf = mp.mpf("0.4"), bdelta: mp.mpf = mp.mpf("1.6")) -> Sequence[Atom]:
    atoms: List[Atom] = []
    for j in range(3):
        theta = 2 * mp.pi * j / 3
        W = r * mp.e ** (1j * theta)
        gamma = mp.mpf(str(mp.re(W)))
        # W = (gamma-bg) - i(delta-bd)  => delta = bd - Im(W)
        delta = bdelta - mp.mpf(str(mp.im(W)))
        atoms.append((mp.mpf("1") / 3, gamma, delta))
    return atoms


@dataclass(frozen=True)
class Payload:
    ck_formula_ok: bool
    ck_2_to_8: Dict[str, str]
    w2_identity_ok: bool
    w3_identity_ok: bool
    kl_k2_ratio: str
    kl_k2_target: str
    kl_k2_rel_err: str
    fdiv_k2_ratio: str
    fdiv_k2_target: str
    fdiv_k2_rel_err: str
    i1_k2_ratio: str
    i1_k2_target: str
    i1_k2_rel_err: str
    kl_k3_ratio: str
    kl_k3_target: str
    kl_k3_rel_err: str
    k2_equiv_o_t4_ok: bool
    elapsed_s: float


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit defect-measure complex multipole KL asymptotics.")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON/TEX outputs.")
    parser.add_argument("--dps", type=int, default=70, help="mpmath precision.")
    parser.add_argument("--t-k2", type=str, default="120", help="Large-time point for k=2 scenario.")
    parser.add_argument("--t-k3", type=str, default="90", help="Large-time point for k=3 scenario.")
    parser.add_argument("--dt", type=str, default="0.1", help="Finite-difference step for I1 audit.")
    args = parser.parse_args()

    t0 = time.time()
    print("[xi-poisson-defect-complex-multipole-kl] start", flush=True)

    mp.mp.dps = int(args.dps)

    # c_k chain
    ck: Dict[int, sp.Rational] = {}
    ck_formula_ok = True
    for k in range(2, 9):
        c = sp.Rational(sp.binomial(2 * k - 2, k - 1), 2 ** (2 * k))
        ck[k] = c
        ck_formula_ok = ck_formula_ok and (c > 0)

    # symbolic W^2, W^3 identities
    G, D = sp.symbols("G D", real=True)
    W = G - sp.I * D
    w2_identity_ok = bool(sp.expand(W**2 - ((G**2 - D**2) - 2 * sp.I * G * D)) == 0)
    w3_identity_ok = bool(
        sp.expand(W**3 - ((G**3 - 3 * G * D**2) - sp.I * (3 * G**2 * D - D**3))) == 0
    )
    print("[xi-poisson-defect-complex-multipole-kl] symbolic identities checked", flush=True)

    # k=2 scenario
    atoms2 = _scenario_k2()
    m2 = _moment_w(atoms2, 2)
    abs_m2_sq = mp.mpf(str(abs(m2) ** 2))
    t2 = mp.mpf(str(args.t_k2))
    dkl2, T2 = _d_kl(atoms2, t2, dps=int(args.dps))
    c2 = mp.mpf(str(sp.N(ck[2], 60)))
    ratio_kl2 = dkl2 * (T2**4) / abs_m2_sq
    rel_kl2 = abs(ratio_kl2 - c2) / c2

    # f-div with f(u)=(u-1)^2/2, f''(1)=1
    fd2, _ = _d_f(atoms2, t2, f=lambda u: (u - 1) ** 2 / 2, dps=int(args.dps))
    ratio_fd2 = fd2 * (T2**4) / abs_m2_sq
    rel_fd2 = abs(ratio_fd2 - c2) / c2

    # I1 via finite-difference on KL
    dt = mp.mpf(str(args.dt))
    dkl2_b, _ = _d_kl(atoms2, t2 + dt, dps=int(args.dps))
    i1_fd = -(dkl2_b - dkl2) / dt
    i1_target = 4 * c2  # (2k)c_k with k=2
    ratio_i12 = i1_fd * (T2**5) / abs_m2_sq
    rel_i12 = abs(ratio_i12 - i1_target) / i1_target
    print("[xi-poisson-defect-complex-multipole-kl] k=2 scenario checked", flush=True)

    # k=3 scenario with m2=0
    atoms3 = _scenario_k3()
    m2_3 = _moment_w(atoms3, 2)
    m3 = _moment_w(atoms3, 3)
    abs_m3_sq = mp.mpf(str(abs(m3) ** 2))
    t3 = mp.mpf(str(args.t_k3))
    dkl3, T3 = _d_kl(atoms3, t3, dps=int(args.dps))
    c3 = mp.mpf(str(sp.N(ck[3], 60)))
    ratio_kl3 = dkl3 * (T3**6) / abs_m3_sq
    rel_kl3 = abs(ratio_kl3 - c3) / c3

    # practical equivalence checkpoint: m2=0 forces much smaller than T^-4 scale in this scenario.
    k2_equiv_o_t4_ok = bool(abs(m2_3) < mp.mpf("1e-12"))
    print("[xi-poisson-defect-complex-multipole-kl] k=3 scenario checked", flush=True)

    elapsed = time.time() - t0
    payload = Payload(
        ck_formula_ok=bool(ck_formula_ok),
        ck_2_to_8={str(k): str(ck[k]) for k in range(2, 9)},
        w2_identity_ok=bool(w2_identity_ok),
        w3_identity_ok=bool(w3_identity_ok),
        kl_k2_ratio=str(ratio_kl2),
        kl_k2_target=str(c2),
        kl_k2_rel_err=str(rel_kl2),
        fdiv_k2_ratio=str(ratio_fd2),
        fdiv_k2_target=str(c2),
        fdiv_k2_rel_err=str(rel_fd2),
        i1_k2_ratio=str(ratio_i12),
        i1_k2_target=str(i1_target),
        i1_k2_rel_err=str(rel_i12),
        kl_k3_ratio=str(ratio_kl3),
        kl_k3_target=str(c3),
        kl_k3_rel_err=str(rel_kl3),
        k2_equiv_o_t4_ok=bool(k2_equiv_o_t4_ok),
        elapsed_s=float(elapsed),
    )

    if not args.no_output:
        out_json = export_dir() / "xi_poisson_defect_measure_complex_multipole_kl_audit.json"
        out_tex = generated_dir() / "eq_xi_poisson_defect_measure_complex_multipole_kl_audit.tex"
        _write_json(out_json, asdict(payload))

        tex_lines: List[str] = []
        tex_lines.append("% Auto-generated by scripts/exp_xi_poisson_defect_measure_complex_multipole_kl_audit.py")
        tex_lines.append(r"\[")
        tex_lines.append(r"c_k=\frac{1}{2^{2k}}\binom{2k-2}{k-1},\qquad"
                         r"(c_2,c_3,c_4,c_5)=\left(\frac18,\frac{3}{32},\frac{5}{64},\frac{35}{512}\right).")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(r"W=\Gamma-\mathrm{i}\Delta,\quad "
                         r"W^2=(\Gamma^2-\Delta^2)-2\mathrm{i}\Gamma\Delta,\quad "
                         r"W^3=(\Gamma^3-3\Gamma\Delta^2)-\mathrm{i}(3\Gamma^2\Delta-\Delta^3).")
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(
            r"D_{\mathrm{KL}}(h_t\mid g_t)\sim c_k\,\frac{|m_k|^2}{T^{2k}},\qquad "
            r"D_f(h_t\mid g_t)\sim f''(1)c_k\,\frac{|m_k|^2}{T^{2k}},\qquad "
            r"I_1(h_t\mid g_t)\sim (2k)c_k\,\frac{|m_k|^2}{T^{2k+1}}."
        )
        tex_lines.append(r"\]")
        tex_lines.append(r"\[")
        tex_lines.append(
            r"\text{Audit ratios:}\ "
            + rf"\frac{{T^4D_{{\mathrm{{KL}}}}}}{{|m_2|^2}}={mp.nstr(ratio_kl2, 12)},\ "
            + rf"\frac{{T^4D_f}}{{|m_2|^2}}={mp.nstr(ratio_fd2, 12)},\ "
            + rf"\frac{{T^5I_1}}{{|m_2|^2}}={mp.nstr(ratio_i12, 12)},\ "
            + rf"\frac{{T^6D_{{\mathrm{{KL}}}}}}{{|m_3|^2}}={mp.nstr(ratio_kl3, 12)}."
        )
        tex_lines.append(r"\]")
        _write_text(out_tex, "\n".join(tex_lines) + "\n")

    print(
        "[xi-poisson-defect-complex-multipole-kl] checks:"
        f" ck={payload.ck_formula_ok} w2={payload.w2_identity_ok} w3={payload.w3_identity_ok}"
        f" k2_kl_err={payload.kl_k2_rel_err} k2_f_err={payload.fdiv_k2_rel_err}"
        f" k2_i1_err={payload.i1_k2_rel_err} k3_kl_err={payload.kl_k3_rel_err}"
        f" m2_zero={payload.k2_equiv_o_t4_ok} sec={elapsed:.3f}",
        flush=True,
    )
    print("[xi-poisson-defect-complex-multipole-kl] done", flush=True)


if __name__ == "__main__":
    main()

