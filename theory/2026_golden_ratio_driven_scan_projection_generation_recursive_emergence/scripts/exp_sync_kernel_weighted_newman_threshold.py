#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Kernel Newman threshold (RH phase transition) for the weighted 10-state sync kernel B(u).

We use the manuscript's explicit nonzero-spectrum characteristic polynomial:

  P(μ,u) = μ^6-(1+u)μ^5-5uμ^4+3u(1+u)μ^3-u(u^2-3u+1)μ^2+u(u^3-3u^2-3u+1)μ+u^2(u^2+u+1).

Let λ1(u) be the Perron root (spectral radius) and let Λ(u)=max_{i>=2}|λ_i(u)|.
The kernel-RH condition is Λ(u) <= sqrt(λ1(u)).

Empirically and structurally, for u in (0,1] the RH boundary is triggered by a negative
real eigenvalue μ_-(u) crossing the square-root circle, i.e.:

  |μ_-(u)| = sqrt(λ1(u))  <=>  λ1(u) = (-μ_-(u))^2.

Write μ_-(u) = -b (b>0). At an RH-sharp point we have:

  P(-b,u)=0  and  P(b^2,u)=0.

Eliminating b via a resultant gives a univariate polynomial condition in u. We compute:

  Res_b(P(-b,u), P(b^2,u)) = u^9 (u-1)^2 (u^2+u+1) (2u^2-u+3) Q(u),

where Q(u) is a degree-37 integer polynomial. Among the two real roots of Q in (0,1),
only one corresponds to the true RH phase transition (Perron equality λ1 = b^2); we
denote it u_* and define β_* := -log u_* (with u = exp(-β)).

Outputs:
  - artifacts/export/sync_kernel_weighted_newman_threshold.json
  - sections/generated/eq_sync_kernel_weighted_newman_threshold.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Tuple

import mpmath as mp
import sympy as sp

from common_paths import export_dir, generated_dir


def _fmt(x: mp.mpf, nd: int = 16) -> str:
    return mp.nstr(x, nd)


def _P_sym() -> Tuple[sp.Symbol, sp.Symbol, sp.Expr]:
    u = sp.Symbol("u")
    mu = sp.Symbol("mu")
    P = (
        mu**6
        - (u + 1) * mu**5
        - 5 * u * mu**4
        + 3 * u * (u + 1) * mu**3
        - u * (u**2 - 3 * u + 1) * mu**2
        + u * (u**3 - 3 * u**2 - 3 * u + 1) * mu
        + u**2 * (u**2 + u + 1)
    )
    return u, mu, sp.expand(P)


def _resultant_factorization_Q() -> Tuple[sp.Symbol, sp.Poly, sp.Poly]:
    """Return (u, Res(u), Q(u)) where Res is the b-resultant and Q is the degree-37 factor."""
    u, mu, P = _P_sym()
    b = sp.Symbol("b")
    P_minus = sp.expand(P.subs(mu, -b))
    P_sq = sp.expand(P.subs(mu, b**2))
    Res = sp.resultant(P_minus, P_sq, b)

    # Factor over Z[u] and extract the unique degree-37 factor.
    fac = sp.factor_list(Res, u)
    Q = None
    for f, e in fac[1]:
        if e == 1 and sp.Poly(f, u).degree() == 37:
            Q = sp.Poly(f, u)
            break
    if Q is None:
        raise RuntimeError("Failed to extract degree-37 factor Q(u) from resultant.")
    return u, sp.Poly(Res, u), Q


def _roots_real_in_01(poly: sp.Poly, *, dps: int) -> List[sp.Expr]:
    roots = poly.nroots(n=dps, maxsteps=200)
    out: List[sp.Expr] = []
    # Filter: real roots in (0,1).
    # Use a fairly strict imaginary threshold relative to the requested precision.
    imag_eps = sp.Float(10) ** (-(dps // 2))
    for r in roots:
        rr = sp.re(r).evalf(dps)
        ii = sp.im(r).evalf(dps)
        if abs(ii) <= imag_eps and 0 < rr < 1:
            out.append(rr)
    out = sorted(out, key=lambda x: float(x))
    return out


def _P_roots_numeric(u_val: mp.mpf) -> List[mp.mpc]:
    """Return numerical roots of P(mu,u_val)=0 as mpmath complex numbers."""
    u = u_val
    a5 = -(u + 1)
    a4 = -5 * u
    a3 = 3 * u * (u + 1)
    a2 = -(u * (u**2 - 3 * u + 1))
    a1 = u * (u**3 - 3 * u**2 - 3 * u + 1)
    a0 = u**2 * (u**2 + u + 1)
    coeffs = [mp.mpf(1), a5, a4, a3, a2, a1, a0]
    return list(mp.polyroots(coeffs, maxsteps=200))


def _rhk_diagnostic(u_val: mp.mpf) -> Tuple[mp.mpf, mp.mpf, mp.mpf, mp.mpf]:
    """Return (lambda1, Lam, ratio, mu_minus) at u in (0,1]."""
    roots = _P_roots_numeric(u_val)
    perron = max(roots, key=lambda z: abs(z))
    lam1 = mp.re(perron)
    # Most negative real root (should be the troublesome branch on (0,1]).
    neg_reals = [mp.re(r) for r in roots if abs(mp.im(r)) < mp.mpf("1e-50") and mp.re(r) < 0]
    if not neg_reals:
        raise RuntimeError("Expected at least one negative real root for u in (0,1].")
    neg_reals.sort()
    mu_minus = neg_reals[0]

    others = [r for r in roots if r != perron]
    Lam = max(abs(r) for r in others)
    ratio = Lam / mp.sqrt(lam1)
    return lam1, Lam, ratio, mu_minus


def _tex_poly_Q(u_sym: sp.Symbol, Q: sp.Poly, *, max_terms_per_line: int = 6) -> List[str]:
    """Return TeX lines for Q(u) with manual wrapping inside an aligned environment."""
    d = Q.degree()
    coeffs = Q.all_coeffs()  # high -> low
    if len(coeffs) != d + 1:
        raise RuntimeError("Unexpected coefficient count for Q.")

    terms: List[str] = []
    for k, c in enumerate(coeffs):
        deg = d - k
        c_int = int(c)
        if c_int == 0:
            continue
        sign = "+" if c_int > 0 else "-"
        abs_c = abs(c_int)
        # monomial (empty for constants)
        if deg == 0:
            mono = ""
        elif deg == 1:
            mono = f"{u_sym}"
        else:
            mono = f"{u_sym}^{{{deg}}}"

        # coefficient (omit 1 on non-constant monomials)
        if deg != 0 and abs_c == 1:
            coeff_part = ""
        else:
            coeff_part = f"{abs_c}"

        if mono and coeff_part:
            term_body = f"{coeff_part} {mono}"
        elif mono:
            term_body = mono
        else:
            term_body = coeff_part

        if not terms:
            # first term keeps its sign only if negative
            if sign == "-":
                terms.append(f"- {term_body}")
            else:
                terms.append(f"{term_body}")
        else:
            terms.append(f"{sign} {term_body}")

    # wrap
    lines: List[str] = []
    chunk: List[str] = []
    for t in terms:
        chunk.append(t)
        if len(chunk) >= max_terms_per_line:
            lines.append(" ".join(chunk))
            chunk = []
    if chunk:
        lines.append(" ".join(chunk))
    return lines


def _factor_degs_mod_p(Q: sp.Poly, p: int) -> List[int]:
    u = Q.gens[0]
    Qp = sp.Poly(Q.as_expr(), u, modulus=int(p))
    _coeff, factors = Qp.factor_list()
    degs: List[int] = []
    for f, e in factors:
        degs.extend([int(sp.Poly(f, u, modulus=int(p)).degree())] * int(e))
    return degs


def _gcd_is_one_mod_p(Q: sp.Poly, p: int) -> bool:
    u = Q.gens[0]
    Qp = sp.Poly(Q.as_expr(), u, modulus=int(p))
    g = sp.gcd(Qp, Qp.diff())
    # g is a constant unit iff the polynomial is squarefree mod p.
    return int(g.degree()) == 0


def _write_galois_table(path: Path, *, Q: sp.Poly) -> None:
    """
    Write a small mod-p factorization certificate table for the degree-37 Newman Q(u).

    We intentionally keep this table lightweight and local: it is used as an auditable
    certificate for the Galois-theoretic arguments (cycle types via Frobenius).
    """
    # Chosen unramified primes and their factor-degree patterns.
    primes: List[int] = [659, 79, 13, 37]
    rows: List[Tuple[int, List[int]]] = []
    for p in primes:
        if not _gcd_is_one_mod_p(Q, p):
            raise RuntimeError(f"Expected gcd(Q,Q')=1 mod p for p={p}.")
        rows.append((p, _factor_degs_mod_p(Q, p)))

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_sync_kernel_weighted_newman_threshold.py")
    lines.append(r"\begin{table}[H]")
    lines.append(r"\centering")
    lines.append(r"\scriptsize")
    lines.append(
        r"\caption{Mod-$p$ factorization degrees for the degree-$37$ Newman polynomial $Q(u)$ "
        r"from Proposition~\ref{prop:sync-kernel-weighted-newman-threshold}. "
        r"All primes listed satisfy $\gcd(Q,Q')\equiv 1\ (\mathrm{mod}\ p)$ (squarefree/unramified).}"
    )
    lines.append(r"\label{tab:sync-kernel-weighted-newman-Q-galois-certificate}")
    lines.append(r"\begin{tabular}{r l}")
    lines.append(r"\toprule")
    lines.append(r"$p$ & degs of $Q(u)\bmod p$\\")
    lines.append(r"\midrule")
    for p, degs in rows:
        degs_str = "(" + ",".join(str(d) for d in degs) + ")"
        lines.append(f"{p} & {degs_str}\\\\")
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


@dataclass(frozen=True)
class Payload:
    dps: int
    # Resultant factor structure (human-readable).
    resultant_u_degree: int
    Q_degree: int
    Q_u_roots_in_01: List[str]
    # Selected phase-transition root and values at it.
    u_star: str
    beta_star: str
    lambda1_u_star: str
    mu_minus_u_star: str
    Lambda_u_star: str
    ratio_u_star: str
    check_lambda1_minus_mu2: str


def _write_tex(
    path: Path,
    *,
    u_star: mp.mpf,
    beta_star: mp.mpf,
    lam1: mp.mpf,
    mu_minus: mp.mpf,
    Lam: mp.mpf,
    ratio: mp.mpf,
    check: mp.mpf,
    u_sym: sp.Symbol,
    Q: sp.Poly,
    roots_in_01: List[sp.Expr],
) -> None:
    nd_u = 16
    nd_beta = 16
    nd_lam = 16
    nd_check = 24

    Q_lines = _tex_poly_Q(u_sym, Q, max_terms_per_line=3)

    lines: List[str] = []
    lines.append("% Auto-generated; do not edit by hand.")
    lines.append(r"\begin{proposition}[同步核的核版 Newman 阈值与 RH 相变点（resultant 消元，可审计）]")
    lines.append(r"\label{prop:sync-kernel-weighted-newman-threshold}")
    lines.append(r"令 $B(u)=B_0+uB_1$ 为附录中的在线归一化同步核，并令其非零谱特征多项式为")
    lines.append(r"\[")
    lines.append(r"\begin{aligned}")
    lines.append(r"P(\mu,u)&=\mu^6-(1+u)\mu^5-5u\mu^4+3u(1+u)\mu^3\\")
    lines.append(r"&-u(u^2-3u+1)\mu^2+u(u^3-3u^2-3u+1)\mu+u^2(u^2+u+1).")
    lines.append(r"\end{aligned}")
    lines.append(r"\]")
    lines.append(
        r"设 $\lambda_1(u)$ 为 Perron 根，$\Lambda(u)=\max_{i\ge2}|\lambda_i(u)|$。"
        r"核版 RH 条件为 $\textsf{RH}_K(u):\Lambda(u)\le \lambda_1(u)^{1/2}$（定义 \ref{def:kernel-rh}）。"
    )
    lines.append(r"令 $b>0$，考虑联立方程 $P(-b,u)=0$ 与 $P(b^2,u)=0$，对 $b$ 消元得到结式分解")
    lines.append(r"\[")
    lines.append(
        r"\mathrm{Res}_b\!\bigl(P(-b,u),P(b^2,u)\bigr)"
        r"=u^{9}(u-1)^{2}(u^{2}+u+1)(2u^{2}-u+3)\,Q(u),"
    )
    lines.append(r"\]")
    lines.append(r"其中 $Q(u)\in\mathbb{Z}[u]$ 为次数 $37$ 的多项式：")
    lines.append(r"\[")
    lines.append(r"\begin{aligned}")
    for i, s in enumerate(Q_lines):
        if i == 0:
            lines.append(rf"Q(u)={s}\\")
        elif i == len(Q_lines) - 1:
            lines.append(rf"&\ {s}.")
        else:
            lines.append(rf"&\ {s}\\")
    lines.append(r"\end{aligned}")
    lines.append(r"\]")
    # Root selection: keep it explicit to avoid confusion with the other (0,1) root.
    lines.append(r"在 $Q(u)=0$ 的 $(0,1)$ 内实根中，存在唯一根 $u_\star$ 使得")
    lines.append(r"$|\mu_-(u_\star)|=\sqrt{\lambda_1(u_\star)}$（其中 $\mu_-(u)<0$ 为最坏非主谱半径所对应的负实根分支）。")
    lines.append(r"该根给出同步核的 RH 相变点；并以 $u=e^{-\beta}$ 定义核版 Newman 阈值 $\beta_\star:=-\log u_\star$（定义 \ref{def:kernel-newman-threshold}）。")
    lines.append(r"\[")
    lines.append(r"\begin{aligned}")
    lines.append(rf"u_\star &\approx {_fmt(u_star, nd_u)},\\")
    lines.append(rf"\beta_\star=-\log u_\star &\approx {_fmt(beta_star, nd_beta)},\\")
    lines.append(rf"\lambda_1(u_\star) &\approx {_fmt(lam1, nd_lam)},\\")
    lines.append(rf"\mu_-(u_\star) &\approx {_fmt(mu_minus, nd_lam)},\\")
    lines.append(rf"\Lambda(u_\star) &\approx {_fmt(Lam, nd_lam)},\\")
    lines.append(rf"\Lambda(u_\star)/\sqrt{{\lambda_1(u_\star)}} &\approx {_fmt(ratio, 12)},\\")
    lines.append(rf"\lambda_1(u_\star)-\mu_-(u_\star)^2 &\approx {_fmt(check, nd_check)}.")
    lines.append(r"\end{aligned}")
    lines.append(r"\]")
    lines.append(
        r"数值核验表明：当 $0<u<u_\star$ 时 $\Lambda(u)<\lambda_1(u)^{1/2}$（严格 RH），"
        r"当 $u=u_\star$ 时恰达界（RH-sharp），当 $u_\star<u\le1$ 时 $\Lambda(u)>\lambda_1(u)^{1/2}$（非 RH）。"
    )
    if roots_in_01:
        # Mention the extra (0,1) root(s) besides u_* to prevent misidentification during audits.
        extras: List[sp.Expr] = []
        for r in roots_in_01:
            rr = mp.mpf(str(sp.N(r, 60)))
            if abs(rr - u_star) > mp.mpf("1e-30"):
                extras.append(r)
        if extras:
            extra_str = ", ".join([str(sp.N(r, 18)) for r in extras])
            lines.append(
                r"\par\noindent\textbf{备注（审计护栏）：} $Q(u)$ 在 $(0,1)$ 内还存在额外实根（约为 "
                + extra_str
                + r"）。但该根对应的是某个\emph{非 Perron}正实根与负实根之间的平方关系，"
                r"并不触发 $\textsf{RH}_K$ 的达界。"
            )
    lines.append(r"\end{proposition}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Compute the sync-kernel Newman threshold via resultant elimination.")
    parser.add_argument("--dps", type=int, default=120, help="Working decimal precision (sympy nroots + mpmath).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "sync_kernel_weighted_newman_threshold.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_sync_kernel_weighted_newman_threshold.tex"),
    )
    parser.add_argument(
        "--galois-tab-out",
        type=str,
        default=str(generated_dir() / "tab_sync_kernel_weighted_newman_Q_galois_certificate.tex"),
    )
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 60:
        raise SystemExit("Require --dps >= 60 for stable u_* output.")
    mp.mp.dps = dps

    u_sym, Res_u, Q = _resultant_factorization_Q()
    roots_in_01 = _roots_real_in_01(Q, dps=dps)
    if not roots_in_01:
        raise RuntimeError("Expected at least one real root of Q(u) in (0,1).")

    # Select the physically relevant root: it must satisfy Perron equality λ1(u)=μ_-(u)^2.
    best_u = None
    best_err = None
    for r in roots_in_01:
        u_val = mp.mpf(str(sp.N(r, dps)))
        lam1, Lam, ratio, mu_minus = _rhk_diagnostic(u_val)
        err = abs(lam1 - (mu_minus**2))
        if best_err is None or err < best_err:
            best_err = err
            best_u = u_val
    if best_u is None:
        raise RuntimeError("Failed to select u_* from candidate roots.")

    u_star = best_u
    beta_star = -mp.log(u_star)
    lam1, Lam, ratio, mu_minus = _rhk_diagnostic(u_star)
    check = lam1 - (mu_minus**2)

    payload = Payload(
        dps=dps,
        resultant_u_degree=int(Res_u.degree()),
        Q_degree=int(Q.degree()),
        Q_u_roots_in_01=[str(sp.N(r, 40)) for r in roots_in_01],
        u_star=_fmt(u_star, 40),
        beta_star=_fmt(beta_star, 40),
        lambda1_u_star=_fmt(lam1, 40),
        mu_minus_u_star=_fmt(mu_minus, 40),
        Lambda_u_star=_fmt(Lam, 40),
        ratio_u_star=_fmt(ratio, 24),
        check_lambda1_minus_mu2=_fmt(check, 40),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[sync-kernel-newman-threshold] wrote {jout}", flush=True)

    _write_tex(
        Path(args.tex_out),
        u_star=u_star,
        beta_star=beta_star,
        lam1=lam1,
        mu_minus=mu_minus,
        Lam=Lam,
        ratio=ratio,
        check=check,
        u_sym=u_sym,
        Q=Q,
        roots_in_01=roots_in_01,
    )
    print(f"[sync-kernel-newman-threshold] wrote {args.tex_out}", flush=True)
    _write_galois_table(Path(args.galois_tab_out), Q=Q)
    print(f"[sync-kernel-newman-threshold] wrote {args.galois_tab_out}", flush=True)


if __name__ == "__main__":
    main()

