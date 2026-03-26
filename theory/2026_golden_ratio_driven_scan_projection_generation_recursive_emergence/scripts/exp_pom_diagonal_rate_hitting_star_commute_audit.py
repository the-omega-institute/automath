#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit the closed-form hitting-time / commute-time / star-Kron-reduction identities
for the optimal diagonal-rate kernel K*_delta under the rank-one refresh decomposition.

This script is English-only by repository convention.

We verify (numerically, high precision) that for the optimal kernel
  K(y|x) = (1-r(x)) 1_{y=x} + r(x) pi(y),
the following identities hold:
  - Hitting-time PGF closed form (for x != y):
        E_x[s^{tau_y}] = G_x(s) * pi(y) / (1 - (1-pi(y)) * Gbar_{-y}(s)),
    where G_x(s) = r(x)s / (1-(1-r(x))s) and Gbar_{-y}(s) averages G_z(s) over pi(.|.!=y).
  - Mean hitting time closed form:
        E_x[tau_y] = 1/r(x) + (1/pi(y)) * sum_{z!=y} pi(z)/r(z).
  - Commute time star metric:
        Comm(x,y) := E_x[tau_y] + E_y[tau_x] = S * (1/pi(x) + 1/pi(y)),
    where S = sum_z pi(z)/r(z).
  - Off-diagonal conductances are rank-one:
        c_xy := w(x) K(y|x) (x!=y) = (1/S) pi(x) pi(y),
    hence the complete graph is the Kron reduction of a star.
  - Weighted spanning-tree total weight:
        tau = S^{-(n-1)} prod_x pi(x).
  - Kemeny constant closed form:
        Kemeny = S * sum_y w(y)(1-w(y))/pi(y).

Outputs:
  - artifacts/export/pom_diagonal_rate_hitting_star_commute_audit.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import mpmath as mp

from common_diagonal_rate import ScalarCollapseSolution, delta0_from_w, solve_scalar_collapse
from common_paths import export_dir


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _build_kernel_from_scalar_collapse(w: Sequence[mp.mpf], sol: ScalarCollapseSolution) -> Tuple[List[List[mp.mpf]], List[List[mp.mpf]]]:
    n = len(w)
    kappa = sol.kappa
    Z = sol.Z
    u = sol.u
    P: List[List[mp.mpf]] = [[mp.mpf(0) for _ in range(n)] for _ in range(n)]
    K: List[List[mp.mpf]] = [[mp.mpf(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            Pij = (u[i] * u[j]) / Z
            if i == j:
                Pij = (mp.mpf(1) + kappa) * (u[i] * u[i]) / Z
            P[i][j] = Pij
            K[i][j] = Pij / w[i]
    return P, K


def _submatrix(M: List[List[mp.mpf]], idx: Sequence[int]) -> List[List[mp.mpf]]:
    return [[M[i][j] for j in idx] for i in idx]


def _vec(M: List[List[mp.mpf]], i: int, idx: Sequence[int]) -> List[mp.mpf]:
    return [M[i][j] for j in idx]


def _solve_linear(A: List[List[mp.mpf]], b: List[mp.mpf]) -> List[mp.mpf]:
    n = len(b)
    Am = mp.matrix(n)
    bm = mp.matrix(n, 1)
    for i in range(n):
        bm[i] = b[i]
        for j in range(n):
            Am[i, j] = A[i][j]
    xm = mp.lu_solve(Am, bm)
    return [xm[i] for i in range(n)]


def _hitting_time_mean(K: List[List[mp.mpf]], y: int) -> List[mp.mpf]:
    # Solve m(y)=0, and for x!=y: m(x) = 1 + sum_z K(x,z) m(z).
    n = len(K)
    J = [i for i in range(n) if i != y]
    A = [[mp.mpf(0) for _ in J] for _ in J]
    b = [mp.mpf(1) for _ in J]
    for ii, x in enumerate(J):
        for jj, z in enumerate(J):
            A[ii][jj] = (mp.mpf(1) if x == z else mp.mpf(0)) - K[x][z]
        # K[x][y] * m(y) term drops since m(y)=0.
    sol = _solve_linear(A, b)
    out = [mp.mpf(0) for _ in range(n)]
    for ii, x in enumerate(J):
        out[x] = sol[ii]
    out[y] = mp.mpf(0)
    return out


def _hitting_time_pgf(K: List[List[mp.mpf]], y: int, s: mp.mpf) -> List[mp.mpf]:
    # Solve f(y)=1, and for x!=y: f(x) = s * sum_z K(x,z) f(z).
    n = len(K)
    J = [i for i in range(n) if i != y]
    A = [[mp.mpf(0) for _ in J] for _ in J]
    b = [mp.mpf(0) for _ in J]
    for ii, x in enumerate(J):
        b[ii] = s * K[x][y] * mp.mpf(1)  # f(y)=1
        for jj, z in enumerate(J):
            A[ii][jj] = (mp.mpf(1) if x == z else mp.mpf(0)) - s * K[x][z]
    sol = _solve_linear(A, b)
    out = [mp.mpf(0) for _ in range(n)]
    for ii, x in enumerate(J):
        out[x] = sol[ii]
    out[y] = mp.mpf(1)
    return out


def _cofactor_det(L: List[List[mp.mpf]], k: int) -> mp.mpf:
    n = len(L)
    idx = [i for i in range(n) if i != k]
    M = mp.matrix(n - 1)
    for ii, i in enumerate(idx):
        for jj, j in enumerate(idx):
            M[ii, jj] = L[i][j]
    return mp.det(M)


def _laplacian_from_conductance(c: List[List[mp.mpf]]) -> List[List[mp.mpf]]:
    n = len(c)
    L = [[mp.mpf(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        s = mp.mpf(0)
        for j in range(n):
            if i == j:
                continue
            s += c[i][j]
            L[i][j] = -c[i][j]
        L[i][i] = s
    return L


def _max_abs_diff(A: Sequence[mp.mpf], B: Sequence[mp.mpf]) -> mp.mpf:
    return max(abs(a - b) for a, b in zip(A, B))


@dataclass(frozen=True)
class CaseRow:
    delta_in: str
    kappa: str
    A: str
    S: str
    ok: bool
    max_abs_err_mean: str
    max_abs_err_commute: str
    max_abs_err_tau: str
    max_abs_err_kemeny: str
    max_abs_err_pgf: str


def main() -> None:
    parser = argparse.ArgumentParser(description="Audit hitting/commute/star identities for diagonal-rate kernel.")
    parser.add_argument("--dps", type=int, default=90, help="Decimal precision (default: 90).")
    parser.add_argument("--no-output", action="store_true", help="Skip writing JSON outputs.")
    args = parser.parse_args()

    dps = int(args.dps)
    if dps < 60:
        raise SystemExit("Require --dps >= 60 for stable outputs.")
    mp.mp.dps = dps

    # Deterministic example full-support distribution (exact decimal sum=1).
    w = [mp.mpf("0.37"), mp.mpf("0.21"), mp.mpf("0.17"), mp.mpf("0.13"), mp.mpf("0.12")]
    d0 = delta0_from_w(w)
    deltas = [mp.mpf("0.02"), mp.mpf("0.10"), mp.mpf("0.25")]

    rows: List[CaseRow] = []
    # Determinants / LU-solves can lose a noticeable number of digits; use a conservative tolerance.
    tol = mp.mpf(10) ** (-(mp.mp.dps // 3))
    hard_fail = mp.mpf("1e-20")

    for delta_in in deltas:
        sol = solve_scalar_collapse(w, delta_in, dps=dps)
        P, K = _build_kernel_from_scalar_collapse(w, sol)
        n = len(w)

        # Refresh decomposition parameters.
        A = sol.A
        kappa = sol.kappa
        u = sol.u
        pi = [ux / A for ux in u]
        r = [A / (A + kappa * ux) for ux in u]
        S = mp.fsum([pi[i] / r[i] for i in range(n)])

        # Mean hitting times: compare closed form to linear solve for each target y.
        max_err_mean = mp.mpf(0)
        m_all: List[List[mp.mpf]] = [[mp.mpf(0) for _ in range(n)] for _ in range(n)]
        for y in range(n):
            m = _hitting_time_mean(K, y)
            for x in range(n):
                m_all[x][y] = m[x]
            for x in range(n):
                if x == y:
                    continue
                closed = (mp.mpf(1) / r[x]) + (mp.mpf(1) / pi[y]) * mp.fsum(
                    [pi[z] / r[z] for z in range(n) if z != y]
                )
                max_err_mean = max(max_err_mean, abs(m[x] - closed))

        # Commute times: compare to star metric formula.
        max_err_comm = mp.mpf(0)
        for x in range(n):
            for y in range(n):
                if x == y:
                    continue
                comm = m_all[x][y] + m_all[y][x]
                closed = S * (mp.mpf(1) / pi[x] + mp.mpf(1) / pi[y])
                max_err_comm = max(max_err_comm, abs(comm - closed))

        # Conductance complete graph (off-diagonal): c_xy = P(x,y) for x!=y.
        c = [[mp.mpf(0) for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                c[i][j] = P[i][j]

        # Tree weight tau via matrix-tree theorem (cofactor determinant).
        L = _laplacian_from_conductance(c)
        tau_det = _cofactor_det(L, 0)
        tau_closed = (S ** (-(n - 1))) * mp.fprod(pi)
        max_err_tau = abs(tau_det - tau_closed)

        # Kemeny constant: compare closed form to definition via mean hitting times.
        # Use x=0; m(0,0)=0 by convention.
        kemeny_def = mp.fsum([w[y] * m_all[0][y] for y in range(n)])
        kemeny_closed = S * mp.fsum([w[y] * (mp.mpf(1) - w[y]) / pi[y] for y in range(n)])
        max_err_kemeny = abs(kemeny_def - kemeny_closed)

        # PGF identity: test a few (x,y,s) tuples with small |s|.
        max_err_pgf = mp.mpf(0)
        s_tests = [mp.mpf("0.21"), mp.mpf("0.47")]
        for y in range(n):
            for s in s_tests:
                f = _hitting_time_pgf(K, y, s)
                # Closed form is only for x!=y.
                for x in range(n):
                    if x == y:
                        continue
                    Gx = (r[x] * s) / (mp.mpf(1) - (mp.mpf(1) - r[x]) * s)
                    if pi[y] == 1:
                        closed = Gx  # degenerate, not expected for full support.
                    else:
                        Gbar = mp.fsum([(pi[z] / (mp.mpf(1) - pi[y])) * (r[z] * s) / (mp.mpf(1) - (mp.mpf(1) - r[z]) * s) for z in range(n) if z != y])
                        closed = Gx * (pi[y] / (mp.mpf(1) - (mp.mpf(1) - pi[y]) * Gbar))
                    max_err_pgf = max(max_err_pgf, abs(f[x] - closed))

        ok = (max_err_mean <= tol) and (max_err_comm <= tol) and (max_err_tau <= tol) and (max_err_kemeny <= tol) and (max_err_pgf <= tol)
        rows.append(
            CaseRow(
                delta_in=mp.nstr(delta_in, 25),
                kappa=mp.nstr(kappa, 25),
                A=mp.nstr(A, 25),
                S=mp.nstr(S, 25),
                ok=bool(ok),
                max_abs_err_mean=mp.nstr(max_err_mean, 10),
                max_abs_err_commute=mp.nstr(max_err_comm, 10),
                max_abs_err_tau=mp.nstr(max_err_tau, 10),
                max_abs_err_kemeny=mp.nstr(max_err_kemeny, 10),
                max_abs_err_pgf=mp.nstr(max_err_pgf, 10),
            )
        )

        print(
            "[pom-diagonal-rate-hitting-star]"
            f" delta={mp.nstr(delta_in, 8)}"
            f" err_mean={mp.nstr(max_err_mean, 6)}"
            f" err_comm={mp.nstr(max_err_comm, 6)}"
            f" err_tau={mp.nstr(max_err_tau, 6)}"
            f" err_kemeny={mp.nstr(max_err_kemeny, 6)}"
            f" err_pgf={mp.nstr(max_err_pgf, 6)}"
            f" ok={ok}",
            flush=True,
        )

        # Hard failure if something is wildly off (logic / implementation bug).
        if max(max_err_mean, max_err_comm, max_err_tau, max_err_kemeny, max_err_pgf) > hard_fail:
            raise SystemExit("Audit failed: residuals unexpectedly large; investigate implementation.")

    payload: Dict[str, object] = {
        "w": [mp.nstr(x, 25) for x in w],
        "delta0": mp.nstr(d0, 25),
        "cases": [asdict(r) for r in rows],
        "tol": mp.nstr(tol, 10),
    }

    if not args.no_output:
        out_json = export_dir() / "pom_diagonal_rate_hitting_star_commute_audit.json"
        _write_json(out_json, payload)
        print(f"[pom-diagonal-rate-hitting-star] wrote {out_json}", flush=True)


if __name__ == "__main__":
    main()

