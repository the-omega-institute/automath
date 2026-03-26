#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Relative zeta bridge: sync-kernel B versus grammar SFT A (golden mean).

We compute:
  - traces a_n(B), a_n(A) and relative traces r_n = a_n(B) - a_n(A)
  - primitive orbit counts p_n(B), p_n(A) and relative q_n = p_n(B) - p_n(A)
  - Abel/Hadamard finite-part constants log M_A and log M_{B/A} = log M_B - log M_A
  - two strict audits:
      (i) q_n equals the Möbius transform of r_n
      (ii) the series of zeta_{B/A} from r_n matches zeta_B/zeta_A as rational functions

Outputs:
  - artifacts/export/relative_zeta_sync_vs_grammar.json
  - sections/generated/eq_relative_zeta_sync_vs_grammar.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List

import mpmath as mp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


A_MATRIX: List[List[int]] = [
    [1, 1],
    [1, 0],
]

B_MATRIX: List[List[int]] = [
    [1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    [1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
    [0, 0, 0, 1, 1, 0, 0, 0, 1, 0],
    [0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
    [0, 1, 1, 0, 0, 0, 0, 1, 0, 0],
]


def mat_mul(A: List[List[int]], B: List[List[int]]) -> List[List[int]]:
    n = len(A)
    m = len(B[0])
    p = len(B)
    out = [[0] * m for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        for k in range(p):
            aik = Ai[k]
            if aik == 0:
                continue
            Bk = B[k]
            for j in range(m):
                out[i][j] += aik * Bk[j]
    return out


def mat_trace(A: List[List[int]]) -> int:
    return sum(A[i][i] for i in range(len(A)))


def mat_pow_traces(M: List[List[int]], n_max: int, prog: Progress, label: str) -> List[int]:
    if n_max <= 0:
        return []
    P = [row[:] for row in M]
    out: List[int] = []
    for n in range(1, n_max + 1):
        if n > 1:
            P = mat_mul(P, M)
        out.append(mat_trace(P))
        prog.tick(f"traces {label} n={n}/{n_max}")
    return out


def mobius(n: int) -> int:
    if n == 1:
        return 1
    x = n
    mu = 1
    p = 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            mu = -mu
            if x % p == 0:
                return 0
            while x % p == 0:
                x //= p
        p = 3 if p == 2 else p + 2
    if x > 1:
        mu = -mu
    return mu


def divisors(n: int) -> List[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def primitive_counts_from_traces(traces: List[int], prog: Progress, label: str) -> List[int]:
    pvals: List[int] = []
    for n in range(1, len(traces) + 1):
        s = 0
        for d in divisors(n):
            s += mobius(d) * traces[n // d - 1]
        if s % n != 0:
            raise ValueError(f"non-integer primitive count for {label} n={n}: {s}/{n}")
        pvals.append(s // n)
        prog.tick(f"primitive {label} n={n}/{len(traces)}")
    return pvals


def series_mul(a: List[mp.mpf], b: List[mp.mpf], n: int) -> List[mp.mpf]:
    out = [mp.mpf("0")] * (n + 1)
    for i in range(0, min(len(a), n + 1)):
        ai = a[i]
        if ai == 0:
            continue
        for j in range(0, min(len(b), n + 1 - i)):
            out[i + j] += ai * b[j]
    return out


def series_inv(a: List[mp.mpf], n: int) -> List[mp.mpf]:
    if len(a) == 0 or a[0] == 0:
        raise ValueError("series_inv requires nonzero constant term")
    out = [mp.mpf("0")] * (n + 1)
    out[0] = 1 / a[0]
    for k in range(1, n + 1):
        s = mp.mpf("0")
        for j in range(1, k + 1):
            if j < len(a):
                s += a[j] * out[k - j]
        out[k] = -s / a[0]
    return out


def series_exp(f: List[mp.mpf], n: int) -> List[mp.mpf]:
    # f[0] is assumed 0 for our use.
    out = [mp.mpf("0")] * (n + 1)
    out[0] = 1
    for k in range(1, n + 1):
        s = mp.mpf("0")
        for j in range(1, k + 1):
            if j < len(f):
                s += mp.mpf(j) * f[j] * out[k - j]
        out[k] = s / mp.mpf(k)
    return out


def build_log_zeta_from_traces(traces: List[int], n: int) -> List[mp.mpf]:
    # log zeta = sum_{k>=1} Tr(M^k) z^k / k
    out = [mp.mpf("0")] * (n + 1)
    for k in range(1, min(len(traces), n) + 1):
        out[k] = mp.mpf(traces[k - 1]) / mp.mpf(k)
    return out


def zeta_A_rational_coeffs(n: int) -> List[mp.mpf]:
    # zeta_A(z)=1/(1 - z - z^2)
    denom = [mp.mpf("1"), mp.mpf("-1"), mp.mpf("-1")] + [mp.mpf("0")] * (n - 2)
    return series_inv(denom[: n + 1], n)


def det_I_minus_zB_coeffs(n: int) -> List[mp.mpf]:
    # det(I - zB) = (z-1)(z+1)(3z-1)(z^3 - z^2 + z + 1)
    # Expand as a polynomial in z.
    poly = [mp.mpf("-1"), mp.mpf("1")]  # (z-1)
    poly = series_mul(poly, [mp.mpf("1"), mp.mpf("1")], n)  # (z+1)
    poly = series_mul(poly, [mp.mpf("-1"), mp.mpf("3")], n)  # (3z-1)
    poly = series_mul(poly, [mp.mpf("1"), mp.mpf("1"), mp.mpf("-1"), mp.mpf("1")], n)  # (z^3 - z^2 + z + 1)
    return poly[: n + 1]


def zeta_B_rational_coeffs(n: int) -> List[mp.mpf]:
    denom = det_I_minus_zB_coeffs(n)
    return series_inv(denom, n)


def tail_bound_geom(q: mp.mpf, N: int) -> mp.mpf:
    # A conservative geometric tail: sum_{k>N} q^k/k <= q^{N+1}/((N+1)(1-q)).
    return (5 * q ** (N + 1)) / ((N + 1) * (1 - q))


@dataclass(frozen=True)
class Payload:
    n_max: int
    traces_A: List[int]
    traces_B: List[int]
    traces_r: List[int]
    prim_A: List[int]
    prim_B: List[int]
    prim_q: List[int]
    entropy_gap: str
    logM_A: str
    M_A: str
    logM_B: str
    M_B: str
    logM_rel: str
    M_rel: str
    audit_q_from_r_ok: bool
    audit_series_ratio_ok: bool
    audit_series_n: int
    logM_tail_bound: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Relative zeta bridge: sync-kernel vs grammar.")
    parser.add_argument("--n-max", type=int, default=20, help="Max n for trace/primitive audits and series checks.")
    parser.add_argument("--series-n", type=int, default=30, help="Series truncation order for rational-vs-trace check.")
    parser.add_argument("--mobius-N", type=int, default=200, help="Truncation N for logM_A Möbius sum (k>=2..N).")
    parser.add_argument("--dps", type=int, default=90, help="mpmath precision (decimal digits).")
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "relative_zeta_sync_vs_grammar.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "eq_relative_zeta_sync_vs_grammar.tex"),
    )
    args = parser.parse_args()

    n_max = int(args.n_max)
    series_n = int(args.series_n)
    mobius_N = int(args.mobius_N)
    mp.mp.dps = int(args.dps)

    prog = Progress("relative_zeta_sync_vs_grammar", every_seconds=20.0)

    n_traces = max(n_max, series_n)
    traces_A_all = mat_pow_traces(A_MATRIX, n_traces, prog, label="A")
    traces_B_all = mat_pow_traces(B_MATRIX, n_traces, prog, label="B")
    traces_r_all = [b - a for a, b in zip(traces_A_all, traces_B_all)]

    traces_A = traces_A_all[:n_max]
    traces_B = traces_B_all[:n_max]
    traces_r = traces_r_all[:n_max]

    prim_A = primitive_counts_from_traces(traces_A, prog, label="A")
    prim_B = primitive_counts_from_traces(traces_B, prog, label="B")
    prim_q = [pb - pa for pa, pb in zip(prim_A, prim_B)]

    # Audit: Möbius transform of r_n equals q_n
    q_from_r = primitive_counts_from_traces(traces_r, prog, label="r=B-A")
    audit_q_from_r_ok = (q_from_r == prim_q)

    # Audit: zeta_{B/A} from traces matches rational zeta_B/zeta_A in series up to series_n
    log_zeta_rel = build_log_zeta_from_traces(traces_r_all, series_n)
    zeta_rel_series = series_exp(log_zeta_rel, series_n)

    zetaA = zeta_A_rational_coeffs(series_n)
    zetaB = zeta_B_rational_coeffs(series_n)
    # zeta_B / zeta_A = zeta_B * (1 - z - z^2)
    poly_inv_zetaA = [mp.mpf("1"), mp.mpf("-1"), mp.mpf("-1")] + [mp.mpf("0")] * (series_n - 2)
    ratio_series = series_mul(zetaB, poly_inv_zetaA[: series_n + 1], series_n)

    audit_series_ratio_ok = True
    for k in range(0, series_n + 1):
        if mp.almosteq(zeta_rel_series[k], ratio_series[k]) is False:
            audit_series_ratio_ok = False
            break

    # logM_A via Möbius--zeta formula: logM = log C + sum_{k>=2} mu(k)/k log zeta(z_*^k)
    phi = (1 + mp.sqrt(5)) / 2
    z_star_A = 1 / phi
    # C_A = lim_{z->z_*} (1 - phi z) / (1 - z - z^2) = (phi^2)/(phi+2) = (phi+1)/(phi+2)
    C_A = (phi + 1) / (phi + 2)

    logM_A = mp.log(C_A)
    for k in range(2, mobius_N + 1):
        mu = mobius(k)
        if mu == 0:
            continue
        z = z_star_A ** k
        zeta = 1 / (1 - z - z * z)
        logM_A += mp.mpf(mu) * mp.log(zeta) / mp.mpf(k)
        prog.tick(f"logM_A k={k}/{mobius_N}")

    # A conservative tail bound (geometric envelope)
    tail_bd = tail_bound_geom(z_star_A, mobius_N)

    # logM_B is taken from the audited sync-kernel appendix output (high precision in manuscript).
    logM_B = mp.mpf("-0.3033268788310883")

    logM_rel = logM_B - logM_A
    entropy_gap = mp.log(3 / phi)

    payload = Payload(
        n_max=n_max,
        traces_A=traces_A,
        traces_B=traces_B,
        traces_r=traces_r,
        prim_A=prim_A,
        prim_B=prim_B,
        prim_q=prim_q,
        entropy_gap=mp.nstr(entropy_gap, 16),
        logM_A=mp.nstr(logM_A, 22),
        M_A=mp.nstr(mp.e**logM_A, 20),
        logM_B=mp.nstr(logM_B, 22),
        M_B=mp.nstr(mp.e**logM_B, 20),
        logM_rel=mp.nstr(logM_rel, 22),
        M_rel=mp.nstr(mp.e**logM_rel, 20),
        audit_q_from_r_ok=bool(audit_q_from_r_ok),
        audit_series_ratio_ok=bool(audit_series_ratio_ok),
        audit_series_n=series_n,
        logM_tail_bound=mp.nstr(tail_bd, 6),
    )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(asdict(payload), indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[relative-zeta] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    tout.parent.mkdir(parents=True, exist_ok=True)
    a10 = ", ".join(str(x) for x in traces_A[:10])
    b10 = ", ".join(str(x) for x in traces_B[:10])
    r10 = ", ".join(str(x) for x in traces_r[:10])
    pA10 = ", ".join(str(x) for x in prim_A[:10])
    pB10 = ", ".join(str(x) for x in prim_B[:10])
    q10 = ", ".join(str(x) for x in prim_q[:10])

    lines: List[str] = []
    lines.append("% Auto-generated by scripts/exp_relative_zeta_sync_vs_grammar.py")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ \\Delta h=\\log\\frac{\\rho(B)}{\\rho(A)}=\\log\\frac{3}{\\varphi}\\ \\approx\\ " + payload.entropy_gap + "\\ }")
    lines.append("\\end{equation*}")
    lines.append("")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (a_n(A))_{n=1}^{10}=(" + a10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (a_n(B))_{n=1}^{10}=(" + b10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (r_n)_{n=1}^{10}=(a_n(B)-a_n(A))_{n=1}^{10}=(" + r10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (p_n(A))_{n=1}^{10}=(" + pA10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (p_n(B))_{n=1}^{10}=(" + pB10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("\\begin{equation*}")
    lines.append("\\boxed{\\ (q_n)_{n=1}^{10}=(p_n(B)-p_n(A))_{n=1}^{10}=(" + q10 + ")\\ }")
    lines.append("\\end{equation*}")
    lines.append("")
    lines.append("\\begin{equation*}")
    lines.append(
        "\\boxed{\\ \\log\\mathfrak{M}_A\\approx "
        + payload.logM_A
        + ",\\quad \\mathfrak{M}_A\\approx "
        + payload.M_A
        + "\\ }"
    )
    lines.append("\\end{equation*}")
    lines.append("\\begin{equation*}")
    lines.append(
        "\\boxed{\\ \\log\\mathfrak{M}_{B/A}:=\\log\\mathfrak{M}_B-\\log\\mathfrak{M}_A\\approx "
        + payload.logM_rel
        + ",\\quad \\mathfrak{M}_{B/A}\\approx "
        + payload.M_rel
        + "\\ }"
    )
    lines.append("\\end{equation*}")
    lines.append("")
    lines.append("\\noindent\\textbf{Audits.} ")
    lines.append(
        "\\(q_n\\) from Möbius on \\(r_n\\): "
        + ("OK" if payload.audit_q_from_r_ok else "FAIL")
        + ".\\quad "
        + "Series check \\(\\zeta_{B/A}=\\zeta_B/\\zeta_A\\) up to order "
        + str(series_n)
        + ": "
        + ("OK" if payload.audit_series_ratio_ok else "FAIL")
        + ".\\quad "
        + "Tail bd (\\(\\log\\mathfrak{M}_A\\), N="
        + str(mobius_N)
        + "): "
        + payload.logM_tail_bound
        + "."
    )
    lines.append("")
    tout.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[relative-zeta] wrote {tout}", flush=True)

    if not payload.audit_q_from_r_ok:
        raise SystemExit("Audit failed: q_n != Mobius(r_n).")
    if not payload.audit_series_ratio_ok:
        raise SystemExit("Audit failed: series(zeta_{B/A}) != series(zeta_B/zeta_A).")


if __name__ == "__main__":
    main()

