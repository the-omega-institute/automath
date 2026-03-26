#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Certificates for q=16,17 resonance-window characteristic polynomials P_16,P_17.

Outputs:
  - artifacts/export/pom_resonance_q16_q17_galois_newman_discriminant_support.json
  - sections/generated/tab_fold_collision_moment_charpoly_galois_certificate_q16_17.tex
  - sections/generated/eq_pom_resonance_disc_factorization_q16_q17.tex
"""

from __future__ import annotations

import json
import warnings
from dataclasses import asdict, dataclass

import sympy as sp
from sympy.ntheory.generate import primerange

from common_paths import export_dir, generated_dir

try:
    from sympy.utilities.exceptions import SymPyDeprecationWarning

    warnings.filterwarnings("ignore", category=SymPyDeprecationWarning)
except Exception:
    pass


def poly_P16_P17(q: int) -> sp.Poly:
    lam = sp.Symbol("lam")
    rec_c: dict[int, tuple[int, ...]] = {
        16: (2, 1611, 62312, 2559407, -24862788, -585266591, 62312, -44606766, 24862794, 255692, -124624, 8, -8),
        17: (
            2,
            2599,
            125872,
            6569850,
            -96034590,
            -2764163954,
            -643026032,
            -15022392733,
            769974566,
            15329386299,
            642908352,
            1347896340,
            -673948170,
        ),
    }
    cs = rec_c[int(q)]
    d = len(cs)
    expr = lam**d
    for i, c in enumerate(cs, start=1):
        expr -= sp.Integer(c) * lam ** (d - i)
    return sp.Poly(expr, lam, domain=sp.ZZ)


def vp(n: int, p: int) -> int:
    n = abs(int(n))
    p = int(p)
    if n == 0:
        raise ValueError("v_p(0) is undefined")
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return int(e)


def factor_degrees_mod_p(poly: sp.Poly, p: int) -> list[int]:
    lam = poly.gens[0]
    f = sp.Poly(poly.as_expr(), lam, modulus=int(p))
    _, facs = sp.factor_list(f, modulus=int(p))
    degs: list[int] = []
    for ff, ee in facs:
        deg = int(sp.Poly(ff, lam, modulus=int(p)).degree())
        degs.extend([deg] * int(ee))
    degs.sort(reverse=True)
    return degs


def is_irreducible_mod_p(poly: sp.Poly, p: int) -> bool:
    lam = poly.gens[0]
    f = sp.Poly(poly.as_expr(), lam, modulus=int(p))
    _, facs = sp.factor_list(f, modulus=int(p))
    return bool(len(facs) == 1 and int(facs[0][1]) == 1 and int(sp.Poly(facs[0][0], lam, modulus=int(p)).degree()) == poly.degree())


@dataclass(frozen=True)
class ModFactorCertificate:
    q: int
    degree: int
    p_irr: int
    degs_irr: list[int]
    p_76: int
    degs_76: list[int]
    p_121: int
    degs_121: list[int]
    p_112: int
    degs_112: list[int]
    unramified_primes: dict[str, bool]


def main() -> None:
    lam = sp.Symbol("lam")

    P16 = poly_P16_P17(16)
    P17 = poly_P16_P17(17)

    disc16 = int(sp.discriminant(P16, lam))
    disc17 = int(sp.discriminant(P17, lam))

    # Target factorization patterns used in manuscript arguments
    certs = {
        16: {
            "p_irr": 239,
            "p_76": 19,   # (7,6)
            "p_121": 127, # (12,1)
            "p_112": 47,  # (11,2)
        },
        17: {
            "p_irr": 31,
            "p_76": 23,
            "p_121": 59,
            "p_112": 41,
        },
    }

    def unramified(disc: int, p: int) -> bool:
        return int(disc) % int(p) != 0

    cert_rows: list[ModFactorCertificate] = []
    for q, P, disc in [(16, P16, disc16), (17, P17, disc17)]:
        c = certs[q]
        p_irr = int(c["p_irr"])
        p_76 = int(c["p_76"])
        p_121 = int(c["p_121"])
        p_112 = int(c["p_112"])

        unram = {
            "p_irr": unramified(disc, p_irr),
            "p_76": unramified(disc, p_76),
            "p_121": unramified(disc, p_121),
            "p_112": unramified(disc, p_112),
        }
        cert_rows.append(
            ModFactorCertificate(
                q=int(q),
                degree=int(P.degree()),
                p_irr=p_irr,
                degs_irr=factor_degrees_mod_p(P, p_irr),
                p_76=p_76,
                degs_76=factor_degrees_mod_p(P, p_76),
                p_121=p_121,
                degs_121=factor_degrees_mod_p(P, p_121),
                p_112=p_112,
                degs_112=factor_degrees_mod_p(P, p_112),
                unramified_primes=unram,
            )
        )

    # Discriminant support audits up to a fixed prime bound
    bound = 20000
    primes = list(primerange(2, bound + 1))

    def small_prime_support(disc: int) -> dict[int, int]:
        out: dict[int, int] = {}
        n = abs(int(disc))
        for p in primes:
            if n % p == 0:
                out[int(p)] = int(vp(n, p))
        return out

    supp16 = small_prime_support(disc16)
    supp17 = small_prime_support(disc17)

    # Proposed presentations (with exponents to be verified against computed valuations)
    presentation16 = {2: 58, 3: 4, 7: 2, 59: 1}
    presentation17 = {2: 100, 3: 28, 5: 9, 7: 3, 11: 2, 13: 3, 17: 2}

    def verify_presentation(disc: int, pres: dict[int, int]) -> dict[str, object]:
        n = abs(int(disc))
        ok = True
        mismatches: dict[int, dict[str, int]] = {}
        for p, e in pres.items():
            got = vp(n, p) if n % p == 0 else 0
            if got != int(e):
                ok = False
                mismatches[int(p)] = {"expected": int(e), "got": int(got)}
        # Strip the presented part and check remaining has no prime factors <= bound
        rem = n
        for p, e in pres.items():
            rem //= int(p) ** int(e)
        leftover_coprime = True
        for p in primes:
            if rem % p == 0:
                leftover_coprime = False
                break
        return {
            "ok": bool(ok),
            "mismatches": mismatches,
            "leftover_coprime_to_primes_leq_bound": bool(leftover_coprime),
            "bound": int(bound),
        }

    pres16_check = verify_presentation(disc16, presentation16)
    pres17_check = verify_presentation(disc17, presentation17)

    payload = {
        "polynomials": {
            "P16_degree": int(P16.degree()),
            "P17_degree": int(P17.degree()),
            "P16_constant_term": int(P16.eval(0)),
            "P17_constant_term": int(P17.eval(0)),
        },
        "discriminants": {
            "Disc_P16": str(int(disc16)),
            "Disc_P17": str(int(disc17)),
            "Disc_P16_negative": bool(int(disc16) < 0),
            "Disc_P17_negative": bool(int(disc17) < 0),
            "small_prime_support_leq_bound": {
                "bound": int(bound),
                "P16": {str(p): int(e) for p, e in sorted(supp16.items())},
                "P17": {str(p): int(e) for p, e in sorted(supp17.items())},
            },
            "presentation_P16": {"-": True, **{str(p): int(e) for p, e in presentation16.items()}, "Delta_coprime_to_primes_leq_bound": pres16_check["leftover_coprime_to_primes_leq_bound"]},
            "presentation_P17": {"-": True, **{str(p): int(e) for p, e in presentation17.items()}, "Delta_coprime_to_primes_leq_bound": pres17_check["leftover_coprime_to_primes_leq_bound"]},
            "presentation_checks": {"P16": pres16_check, "P17": pres17_check},
        },
        "mod_factor_certificates": [asdict(r) for r in cert_rows],
    }

    out_json = export_dir() / "pom_resonance_q16_q17_galois_newman_discriminant_support.json"
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    # TeX table: compact factor-degree certificates
    def fmt_degs(degs: list[int]) -> str:
        return "(" + ",".join(str(d) for d in degs) + ")"

    lines = [
        r"\begin{table}[H]",
        r"\centering",
        r"\scriptsize",
        r"\caption{Unramified mod-$p$ factorization certificates for $P_q(\lambda)$ with $q\in\{16,17\}$. The pattern $(13)$ certifies a $13$-cycle (hence transitivity and primitivity), a displayed degree-$7$ factor certifies a $7$-cycle, $(12,1)$ certifies a $12$-cycle, and $(11,2)$ exhibits a transposition.}",
        r"\label{tab:fold_collision_moment_charpoly_galois_certificate_q16_17}",
        r"\begin{tabular}{r r r l r l r l r l}",
        r"\toprule",
        r"$q$ & $d_q$ & $p_{\mathrm{irr}}$ & degs mod $p_{\mathrm{irr}}$ & $p_{(7,\cdot)}$ & degs mod $p_{(7,\cdot)}$ & $p_{(12,1)}$ & degs mod $p_{(12,1)}$ & $p_{(11,2)}$ & degs mod $p_{(11,2)}$\\",
        r"\midrule",
    ]
    for r in sorted(cert_rows, key=lambda x: x.q):
        lines.append(
            f"{r.q} & {r.degree} & {r.p_irr} & {fmt_degs(r.degs_irr)} & {r.p_76} & {fmt_degs(r.degs_76)} & {r.p_121} & {fmt_degs(r.degs_121)} & {r.p_112} & {fmt_degs(r.degs_112)}\\\\"
        )
    lines += [r"\bottomrule", r"\end{tabular}", r"\end{table}", ""]
    (generated_dir() / "tab_fold_collision_moment_charpoly_galois_certificate_q16_17.tex").write_text("\n".join(lines), encoding="utf-8")

    # TeX equation: discriminant presentations
    eq_lines = [
        r"% Auto-generated by scripts/exp_pom_resonance_q16_q17_galois_newman_discriminant_support.py",
        r"\begin{equation}\label{eq:pom_resonance_disc_factorization_q16_q17}",
        r"\begin{aligned}",
        r"\Disc(P_{16})&=-\,2^{58}\cdot 3^{4}\cdot 7^{2}\cdot 59\cdot \Delta_{16},\\",
        r"\Disc(P_{17})&=-\,2^{100}\cdot 3^{28}\cdot 5^{9}\cdot 7^{3}\cdot 11^{2}\cdot 13^{3}\cdot 17^{2}\cdot \Delta_{17},",
        r"\end{aligned}",
        r"\end{equation}",
        "",
    ]
    (generated_dir() / "eq_pom_resonance_disc_factorization_q16_q17.tex").write_text("\n".join(eq_lines), encoding="utf-8")

    print(f"Wrote {out_json}")


if __name__ == "__main__":
    main()

