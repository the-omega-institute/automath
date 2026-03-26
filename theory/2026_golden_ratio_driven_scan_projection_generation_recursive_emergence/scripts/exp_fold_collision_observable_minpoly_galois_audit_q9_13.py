#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Observable minimal annihilators P_q for S_q(m) (q in {9,10,11,13}):
  - discriminant factorizations and squarefree parts Δ_q,
  - ramified prime sets B_q = {p : p | Disc(Π_q)},
  - mod-p factorization patterns used to certify Gal(Π_q/Q) = S_d via Jordan + discriminant,
  - negative-real dominant subleading root and the effective Ramanujan ratio R_q.

Context (paper-local):
  The minimal integer recurrences for S_q(m) in the resonance window are audited in
  parts/rem__pom-collision-kernel-rh-phase.tex (Theorem thm:pom-moment-resonance).
  Here P_q denotes the observable minimal annihilator (same polynomial as the
  minimal recurrence characteristic polynomial).

Outputs:
  - artifacts/export/fold_collision_observable_minpoly_galois_audit_q9_13.json
  - sections/generated/eq_fold_collision_observable_minpoly_discriminants_q9_13.tex
  - sections/generated/tab_fold_collision_observable_minpoly_galois_certificate_q9_13.tex
  - sections/generated/eq_fold_collision_observable_minpoly_negative_real_dominance_q9_13.tex
"""

from __future__ import annotations

import argparse
import json
import math
import warnings
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir

try:
    from sympy.utilities.exceptions import SymPyDeprecationWarning

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
except Exception:
    # Fallback if SymPy changes internals; warnings are non-fatal.
    pass

def _poly_Pi(q: int) -> sp.Poly:
    lam = sp.Symbol("lam")
    if q == 9:
        expr = lam**7 - 2 * lam**6 - 62 * lam**5 - 386 * lam**4 - 2819 * lam**3 - 62 * lam**2 - 900 * lam + 450
    elif q == 10:
        expr = (
            lam**9
            - 2 * lam**8
            - 96 * lam**7
            - 830 * lam**6
            - 7945 * lam**5
            - 2 * lam**4
            - 1852 * lam**3
            + 830 * lam**2
            - 4 * lam
            + 4
        )
    elif q == 11:
        expr = (
            lam**9
            - 2 * lam**8
            - 153 * lam**7
            - 1740 * lam**6
            - 21249 * lam**5
            + 9432 * lam**4
            + 86213 * lam**3
            + 1484 * lam**2
            + 18348 * lam
            - 9174
        )
    elif q == 13:
        expr = (
            lam**11
            - 2 * lam**10
            - 388 * lam**9
            - 7414 * lam**8
            - 148038 * lam**7
            + 317916 * lam**6
            + 4165856 * lam**5
            - 136252 * lam**4
            - 1565891 * lam**3
            - 318938 * lam**2
            - 289380 * lam
            + 144690
        )
    else:
        raise ValueError("q must be one of {9,10,11,13}")
    return sp.Poly(sp.expand(expr), lam)


def _squarefree_part_from_factorint(fac: Dict[int, int]) -> int:
    out = 1
    for p, e in fac.items():
        if e % 2 == 1:
            out *= int(p)
    return int(out)


def _factorint_to_tex(fac: Dict[int, int]) -> str:
    """
    Render a signed integer factorization dict {p: e} to a compact TeX string
    with primes sorted increasingly. A negative sign is rendered as a leading
    "-" (instead of an explicit "-1" factor).
    """
    neg = int(fac.get(-1, 0)) % 2 == 1
    fac_ = {int(p): int(e) for p, e in fac.items() if int(p) != -1}
    items = list(fac_.items())
    items.sort(key=lambda pe: abs(int(pe[0])))
    parts: List[str] = []
    for p, e in items:
        p = int(p)
        e = int(e)
        if e == 1:
            parts.append(str(p))
        else:
            parts.append(f"{p}^{{{e}}}")
    body = r"\cdot ".join(parts) if parts else "1"
    if neg:
        return "-" + body if body != "1" else "-1"
    return body


def _ramified_primes_sorted(fac: Dict[int, int]) -> List[int]:
    ps = [int(p) for p in fac.keys() if int(p) not in {-1, 1}]
    ps = sorted(set(abs(p) for p in ps))
    return ps


def _squarefree_factor_dict_from_disc_factor(disc_fac: Dict[int, int]) -> Dict[int, int]:
    """
    Given a full discriminant factorization dict {p: e}, return the squarefree-part
    factor dict (odd exponents only), including -1 if the sign is negative.
    """
    out: Dict[int, int] = {}
    if int(disc_fac.get(-1, 0)) % 2 == 1:
        out[-1] = 1
    for p, e in disc_fac.items():
        p = int(p)
        e = int(e)
        if p == -1:
            continue
        if e % 2 == 1:
            out[p] = 1
    return out


def _factor_degrees_mod_p(poly: sp.Poly, p: int) -> Tuple[bool, List[int]]:
    """
    Factor poly modulo p and return (squarefree?, sorted degrees list).
    """
    lam = poly.gens[0]
    f = sp.Poly(poly.as_expr(), lam, modulus=p)
    # squarefree check via gcd with derivative
    g = sp.gcd(f, f.diff())
    squarefree = (g.degree() == 0)
    _, facs = sp.factor_list(f, modulus=p)
    degs: List[int] = []
    for ff, ee in facs:
        degs.extend([sp.Poly(ff, lam, modulus=p).degree()] * int(ee))
    degs.sort(reverse=True)
    return bool(squarefree), degs


def _find_prime_with_degrees(poly: sp.Poly, disc_primes: set[int], want: List[int], p_max: int) -> int:
    want_sorted = sorted(want, reverse=True)
    for p in sp.primerange(2, p_max + 1):
        if p in disc_primes:
            continue
        squarefree, degs = _factor_degrees_mod_p(poly, p)
        if not squarefree:
            continue
        if degs == want_sorted:
            return int(p)
    raise RuntimeError(f"Failed to find prime with factor degrees {want_sorted} up to p_max={p_max}.")


def _find_prime_with_cycle_length(poly: sp.Poly, disc_primes: set[int], cycle_len: int, p_max: int) -> Tuple[int, List[int]]:
    for p in sp.primerange(2, p_max + 1):
        if p in disc_primes:
            continue
        squarefree, degs = _factor_degrees_mod_p(poly, p)
        if not squarefree:
            continue
        if cycle_len in degs:
            return int(p), degs
    raise RuntimeError(f"Failed to find prime whose factor degrees include {cycle_len} up to p_max={p_max}.")


def _mp_roots(poly: sp.Poly, dps: int = 80) -> List[mp.mpc]:
    mp.mp.dps = dps
    lam = poly.gens[0]
    coeffs = [mp.mpf(int(c)) for c in sp.Poly(poly.as_expr(), lam).all_coeffs()]
    # mpmath expects descending coefficients
    return list(mp.polyroots(coeffs, maxsteps=200))


def _dominant_roots(poly: sp.Poly) -> Dict[str, str]:
    """
    Return numerical data:
      - r: dominant Perron root (max |root|)
      - mu_minus: negative real root with max |root| among non-Perron roots
      - R: |mu_minus|/sqrt(r)
    """
    roots = _mp_roots(poly, dps=100)
    # pick dominant by modulus
    dom = max(roots, key=lambda z: abs(z))
    r = mp.re(dom)
    if abs(mp.im(dom)) > mp.mpf("1e-40"):
        raise RuntimeError("Dominant root was not (numerically) real.")
    if r <= 0:
        raise RuntimeError("Dominant real root was not positive.")

    # identify negative real root with largest modulus among non-dominant
    # (use a tolerance to classify roots)
    tol = mp.mpf("1e-40")
    mu_minus = None
    mu_minus_abs = mp.mpf("0")
    for z in roots:
        if abs(z - dom) <= mp.mpf("1e-30"):
            continue
        if abs(mp.im(z)) <= tol and mp.re(z) < 0:
            a = abs(mp.re(z))
            if a > mu_minus_abs:
                mu_minus_abs = a
                mu_minus = mp.re(z)
    if mu_minus is None:
        raise RuntimeError("No negative real subleading root detected.")
    R = abs(mu_minus) / mp.sqrt(r)
    return {
        "r": mp.nstr(r, 20),
        "mu_minus": mp.nstr(mu_minus, 20),
        "R": mp.nstr(R, 12),
    }


@dataclass(frozen=True)
class Item:
    q: int
    degree: int
    naive_mode_upper: int
    deficit: int
    disc: str
    disc_factor: Dict[str, int]
    disc_squarefree_part: int
    disc_squarefree_is_prime: bool
    ramified_primes: List[int]
    # galois certificate primes
    p_irreducible: int
    p_nminus1_1: int
    p_jordan: int
    p_jordan_degrees: List[int]
    # negative real dominance
    perron_r: str
    mu_minus: str
    R: str


@dataclass(frozen=True)
class Payload:
    items: List[Item]


def _write_tex_discriminants(path: Path, items: List[Item]) -> None:
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_fold_collision_observable_minpoly_galois_audit_q9_13.py")
    lines.append(r"\begin{equation}\label{eq:fold_collision_observable_minpoly_discriminants_q9_13}")
    lines.append(r"\begin{aligned}")
    for it in items:
        fac_int = {int(k): int(v) for k, v in it.disc_factor.items()}
        tex_fac = _factorint_to_tex(fac_int)
        lines.append(rf"\mathrm{{Disc}}(P_{{{it.q}}})&={tex_fac},\\")
    if lines[-1].endswith(r",\\"):
        lines[-1] = lines[-1][:-3] + "."
    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_tex_galois_certificate_table(path: Path, items: List[Item]) -> None:
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_fold_collision_observable_minpoly_galois_audit_q9_13.py")
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\caption{Mod-$p$ factorization certificates for $\mathrm{Gal}(P_q/\QQ)\cong S_d$ (unramified primes). "
                 r"Degrees list the factor degrees of $P_q\bmod p$.}")
    lines.append(r"\label{tab:fold_collision_observable_minpoly_galois_certificate_q9_13}")
    lines.append(r"\begin{tabular}{r r r l r l r l}")
    lines.append(r"\toprule")
    lines.append(r"$q$ & $d$ & $p_{\mathrm{irr}}$ & degs & $p_{(d-1,1)}$ & degs & $p_{\mathrm{J}}$ & degs\\")
    lines.append(r"\midrule")
    for it in items:
        poly = _poly_Pi(it.q)
        disc_primes = set(it.ramified_primes)
        _, degs_irr = _factor_degrees_mod_p(poly, it.p_irreducible)
        _, degs_nm = _factor_degrees_mod_p(poly, it.p_nminus1_1)
        degs_j = it.p_jordan_degrees

        def fmt_degs(ds: List[int]) -> str:
            return "(" + ",".join(str(x) for x in ds) + ")"

        lines.append(
            f"{it.q} & {it.degree} & {it.p_irreducible} & {fmt_degs(degs_irr)} & "
            f"{it.p_nminus1_1} & {fmt_degs(degs_nm)} & {it.p_jordan} & {fmt_degs(degs_j)}\\\\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _write_tex_negative_real(path: Path, items: List[Item]) -> None:
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_fold_collision_observable_minpoly_galois_audit_q9_13.py")
    lines.append(r"\begin{equation}\label{eq:fold_collision_observable_minpoly_negative_real_dominance_q9_13}")
    lines.append(r"\begin{aligned}")
    for it in items:
        lines.append(
            rf"R_{{{it.q}}}:=\frac{{|\mu^-_{{{it.q}}}|}}{{\sqrt{{r_{{{it.q}}}}}}}"
            rf"&\approx {it.R}\qquad"
            rf"(r_{{{it.q}}}\approx {it.perron_r},\ \mu^-_{{{it.q}}}\approx {it.mu_minus}),\\"
        )
    if lines[-1].endswith(r",\\"):
        lines[-1] = lines[-1][:-3] + "."
    lines.append(r"\end{aligned}")
    lines.append(r"\end{equation}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _fmt_prime_set_tex(primes: List[int]) -> str:
    """
    Format a list of primes as a TeX math set with allowbreak after commas.
    """
    if not primes:
        return r"\{\}"
    body = r",\allowbreak ".join(str(int(p)) for p in primes)
    return r"\{" + body + r"\}"


def _write_tex_ramified_primes_table(path: Path, items: List[Item]) -> None:
    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_fold_collision_observable_minpoly_galois_audit_q9_13.py")
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(r"\caption{Squarefree discriminant parts $\Delta_q^{\mathrm{disc}}$ and ramified prime sets "
                 r"$\mathcal{B}_q=\{p:\ p\mid \mathrm{Disc}(P_q)\}$ for $q\in\{9,10,11,13\}$.}")
    lines.append(r"\label{tab:fold_collision_observable_minpoly_ramified_primes_q9_13}")
    lines.append(r"\begin{tabular}{r l p{0.62\linewidth}}")
    lines.append(r"\toprule")
    lines.append(r"$q$ & $\Delta_q^{\mathrm{disc}}$ & $\mathcal{B}_q$\\")
    lines.append(r"\midrule")
    for it in items:
        disc_fac_int = {int(k): int(v) for k, v in it.disc_factor.items()}
        sqf_fac = _squarefree_factor_dict_from_disc_factor(disc_fac_int)
        sqf_tex = _factorint_to_tex(sqf_fac)
        B_tex = _fmt_prime_set_tex(it.ramified_primes)
        lines.append(f"{it.q} & ${sqf_tex}$ & ${B_tex}$\\\\")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit discriminants, ramification, Galois certificates, and negative-real dominance for Π_q (q=9,10,11,13).")
    parser.add_argument("--p-max", type=int, default=5000, help="Prime search upper bound for mod-p certificates.")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_collision_observable_minpoly_galois_audit_q9_13.json"),
        help="Output JSON path.",
    )
    parser.add_argument(
        "--tex-disc-out",
        type=str,
        default=str(generated_dir() / "eq_fold_collision_observable_minpoly_discriminants_q9_13.tex"),
        help="Output TeX path for discriminant factorizations.",
    )
    parser.add_argument(
        "--tex-gal-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_observable_minpoly_galois_certificate_q9_13.tex"),
        help="Output TeX path for mod-p Galois certificates table.",
    )
    parser.add_argument(
        "--tex-neg-out",
        type=str,
        default=str(generated_dir() / "eq_fold_collision_observable_minpoly_negative_real_dominance_q9_13.tex"),
        help="Output TeX path for negative-real dominance ratios.",
    )
    parser.add_argument(
        "--tex-ram-out",
        type=str,
        default=str(generated_dir() / "tab_fold_collision_observable_minpoly_ramified_primes_q9_13.tex"),
        help="Output TeX path for ramified prime sets table.",
    )
    args = parser.parse_args()

    qs = [9, 10, 11, 13]
    items: List[Item] = []

    for q in qs:
        poly = _poly_Pi(q)
        d = int(poly.degree())
        naive = int(2 * (q // 2) + 1)
        deficit = int(naive - d)

        lam = poly.gens[0]
        disc = sp.discriminant(poly, lam)
        disc_int = int(disc)
        disc_fac = sp.factorint(disc_int)
        sqfree = _squarefree_part_from_factorint(disc_fac)
        sqfree_is_prime = bool(sp.isprime(abs(int(sqfree))) is True)
        ramified = _ramified_primes_sorted(disc_fac)
        disc_primes = set(ramified)

        # Galois certificates via mod-p factor degrees.
        p_irred = _find_prime_with_degrees(poly, disc_primes, want=[d], p_max=args.p_max)
        p_nm1 = _find_prime_with_degrees(poly, disc_primes, want=[d - 1, 1], p_max=args.p_max)

        # Jordan prime cycle length choice
        if d == 7:
            cycle_len = 3
        elif d == 9:
            cycle_len = 5
        elif d == 11:
            cycle_len = 7
        else:
            raise RuntimeError("Unexpected degree.")
        p_j, degs_j = _find_prime_with_cycle_length(poly, disc_primes, cycle_len=cycle_len, p_max=args.p_max)

        # Negative-real dominance ratios.
        dom = _dominant_roots(poly)

        items.append(
            Item(
                q=int(q),
                degree=int(d),
                naive_mode_upper=int(naive),
                deficit=int(deficit),
                disc=str(disc_int),
                disc_factor={str(int(p)): int(e) for p, e in disc_fac.items()},
                disc_squarefree_part=int(sqfree),
                disc_squarefree_is_prime=bool(sqfree_is_prime),
                ramified_primes=[int(p) for p in ramified],
                p_irreducible=int(p_irred),
                p_nminus1_1=int(p_nm1),
                p_jordan=int(p_j),
                p_jordan_degrees=[int(x) for x in degs_j],
                perron_r=str(dom["r"]),
                mu_minus=str(dom["mu_minus"]),
                R=str(dom["R"]),
            )
        )

    payload = Payload(items=items)

    out = Path(args.json_out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[observable-minpoly-galois-audit] wrote {out}", flush=True)

    _write_tex_discriminants(Path(args.tex_disc_out), items)
    _write_tex_galois_certificate_table(Path(args.tex_gal_out), items)
    _write_tex_negative_real(Path(args.tex_neg_out), items)
    _write_tex_ramified_primes_table(Path(args.tex_ram_out), items)


if __name__ == "__main__":
    main()

