#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Certificate for q=2 addition-as-projection collision Perron roots (sync10 vs real-input40).

This script is English-only by repository convention.

We record an auditable, self-contained certificate for:
  - the claimed integer minimal polynomials P(t) of the q=2 collision Perron roots,
  - mod-p factor-degree patterns used in full symmetric Galois group arguments,
  - discriminant non-square residue checks mod small primes,
  - a cyclic-submodule annihilation identity Q(A)·1 = 0 for the histogram moment-kernel A
    (hence a linear recurrence certificate for u^T A^m v on that cyclic module).

Outputs:
  - artifacts/export/addition_collision_q2_minpoly_galois_certificate.json
  - sections/generated/eq_addition_collision_real_input40_r2_minpoly.tex
  - sections/generated/eq_addition_collision_sync10_r2_minpoly.tex
  - sections/generated/tab_addition_collision_q2_minpoly_galois_certificate.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from exp_sync_kernel_addition_collision_spectrum import _build_real_input40_add_transducer, _build_sync10_add_transducer


def _write_json(path: Path, payload: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _factor_degrees_over_Q(P: sp.Poly) -> List[int]:
    x = P.gens[0]
    _, facs = sp.factor_list(P, domain=sp.QQ)
    degs: List[int] = []
    for f, e in facs:
        degs.extend([int(sp.Poly(f, x, domain=sp.QQ).degree())] * int(e))
    degs.sort(reverse=True)
    return degs


def _factor_degrees_mod_p(P_ZZ: sp.Poly, p: int) -> Tuple[bool, List[int]]:
    x = P_ZZ.gens[0]
    f = sp.Poly(P_ZZ.as_expr(), x, modulus=int(p))
    g = sp.gcd(f, f.diff())
    squarefree = bool(int(g.degree()) == 0)
    _, facs = sp.factor_list(f, modulus=int(p))
    degs: List[int] = []
    for ff, ee in facs:
        degs.extend([int(sp.Poly(ff, x, modulus=int(p)).degree())] * int(ee))
    degs.sort(reverse=True)
    return squarefree, degs


def _disc_mod_p(P_ZZ: sp.Poly, p: int) -> int:
    """Compute discriminant modulo p via resultant in F_p."""
    x = P_ZZ.gens[0]
    n = int(P_ZZ.degree())
    f = sp.Poly(P_ZZ.as_expr(), x, modulus=int(p))
    fp = sp.Poly(f.diff().as_expr(), x, modulus=int(p))
    # For monic f: Disc(f) = (-1)^{n(n-1)/2} * Res(f, f').
    res = sp.resultant(f.as_expr(), fp.as_expr(), x, modulus=int(p))
    sgn = -1 if ((n * (n - 1) // 2) % 2) else 1
    disc = (sgn * int(res)) % int(p)
    return int(disc)


def _is_quadratic_residue(a: int, p: int) -> bool:
    a %= p
    if a == 0:
        return True
    return pow(int(a), (int(p) - 1) // 2, int(p)) == 1


def _rows_to_int(rows: Sequence[List[Tuple[int, float]]]) -> List[List[Tuple[int, int]]]:
    out: List[List[Tuple[int, int]]] = []
    for row in rows:
        rr: List[Tuple[int, int]] = []
        for j, w in row:
            wi = int(w)
            if float(wi) != float(w):
                raise ValueError("non-integer weight encountered in moment-kernel rows")
            if wi:
                rr.append((int(j), wi))
        out.append(rr)
    return out


def _essential_scc_states(
    *,
    transducer,
    output_symbols: Sequence[object],
) -> List[int]:
    """Return the unique essential SCC state indices (by reachability condensation)."""
    Q = transducer.n_states()
    out_set = set(output_symbols)

    # Graph over states using only transitions emitting allowed output symbols.
    adj: List[List[int]] = [[] for _ in range(Q)]
    radj: List[List[int]] = [[] for _ in range(Q)]
    for s in range(Q):
        for a in transducer.input_symbols:
            s2, b = transducer.trans[(s, a)]
            if b not in out_set:
                continue
            adj[s].append(int(s2))
            radj[int(s2)].append(int(s))

    # Kosaraju SCC.
    seen = [False] * Q
    order: List[int] = []

    def dfs1(v: int) -> None:
        seen[v] = True
        for w in adj[v]:
            if not seen[w]:
                dfs1(w)
        order.append(v)

    for v in range(Q):
        if not seen[v]:
            dfs1(v)

    comp = [-1] * Q
    comps: List[List[int]] = []

    def dfs2(v: int, cid: int) -> None:
        comp[v] = cid
        comps[cid].append(v)
        for w in radj[v]:
            if comp[w] < 0:
                dfs2(w, cid)

    for v in reversed(order):
        if comp[v] >= 0:
            continue
        comps.append([])
        dfs2(v, len(comps) - 1)

    nC = len(comps)
    if nC == 0:
        return []

    out_deg = [0] * nC
    for v in range(Q):
        cv = comp[v]
        for w in adj[v]:
            cw = comp[w]
            if cv != cw:
                out_deg[cv] += 1

    essential = [i for i in range(nC) if out_deg[i] == 0]
    if len(essential) != 1:
        # Fall back: choose the largest closed SCC (deterministic, stable).
        essential.sort(key=lambda cid: (len(comps[cid]), cid), reverse=True)
    cid0 = essential[0]
    return sorted(comps[cid0])


def _build_q2_collision_kernel_sparse_rows(
    *,
    transducer,
    base_state_indices: Sequence[int],
    output_symbols: Sequence[object],
) -> List[List[Tuple[int, float]]]:
    """Build q=2 collision moment-kernel on Q^2 (restricted to chosen base states)."""
    out_set = set(output_symbols)
    base = list(base_state_indices)
    idx = {s: i for i, s in enumerate(base)}
    n = len(base)
    rows: List[List[Tuple[int, float]]] = []

    # State space = base^2 in lex order.
    def pair_index(i: int, j: int) -> int:
        return i * n + j

    for i in range(n):
        si = base[i]
        for j in range(n):
            sj = base[j]
            acc: Dict[int, int] = {}
            for a1 in transducer.input_symbols:
                ni, bi = transducer.trans[(si, a1)]
                if bi not in out_set:
                    continue
                for a2 in transducer.input_symbols:
                    nj, bj = transducer.trans[(sj, a2)]
                    if bj != bi:
                        continue
                    if bj not in out_set:
                        continue
                    ii = idx.get(int(ni))
                    jj = idx.get(int(nj))
                    if ii is None or jj is None:
                        continue
                    k = pair_index(ii, jj)
                    acc[k] = acc.get(k, 0) + 1
            row = [(k, float(w)) for k, w in sorted(acc.items()) if w]
            rows.append(row)
    return rows


def _mul_rows_vec(rows: Sequence[List[Tuple[int, int]]], v: Sequence[int]) -> List[int]:
    n = len(rows)
    if len(v) != n:
        raise ValueError("dimension mismatch")
    out = [0] * n
    for i, row in enumerate(rows):
        s = 0
        for j, w in row:
            s += int(w) * int(v[j])
        out[i] = s
    return out


def _apply_poly_to_one(rows: Sequence[List[Tuple[int, int]]], Q: sp.Poly) -> bool:
    """Return True iff Q(A)·1 = 0 exactly (A given by sparse rows)."""
    x = Q.gens[0]
    deg = int(Q.degree())
    coeffs_low_to_high = [int(c) for c in sp.Poly(Q.as_expr(), x, domain=sp.ZZ).all_coeffs()][::-1]
    if len(coeffs_low_to_high) != deg + 1:
        raise RuntimeError("unexpected coefficient length")

    n = len(rows)
    vecs: List[List[int]] = []
    v = [1] * n
    vecs.append(v)
    for _ in range(deg):
        v = _mul_rows_vec(rows, v)
        vecs.append(v)

    acc = [0] * n
    for k, ak in enumerate(coeffs_low_to_high):
        if ak == 0:
            continue
        vk = vecs[k]
        for i in range(n):
            acc[i] += int(ak) * int(vk[i])
    return all(x == 0 for x in acc)


def _tex_poly_aligned(P: sp.Poly, *, var_tex: str, name_tex: str, label: str) -> str:
    x = P.gens[0]
    deg = int(P.degree())
    coeffs = [int(c) for c in sp.Poly(P.as_expr(), x, domain=sp.ZZ).all_coeffs()]

    terms: List[str] = []
    for i, c in enumerate(coeffs):
        if c == 0:
            continue
        p = deg - i
        sign = "-" if c < 0 else "+"
        a = abs(int(c))

        if p == 0:
            mon = f"{a}"
        elif p == 1:
            mon = f"{var_tex}" if a == 1 else f"{a}{var_tex}"
        else:
            mon = f"{var_tex}^{{{p}}}" if a == 1 else f"{a}{var_tex}^{{{p}}}"

        terms.append((sign, mon))

    if not terms:
        raise ValueError("zero polynomial")

    # First term: include sign only if negative.
    s0, m0 = terms[0]
    out_terms = [m0 if s0 == "+" else f"-{m0}"]
    for sgn, mon in terms[1:]:
        out_terms.append(f" {sgn} {mon}")

    # Split into lines to keep TeX stable.
    per_line = 6
    chunks = ["".join(out_terms[i : i + per_line]) for i in range(0, len(out_terms), per_line)]

    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_addition_collision_q2_minpoly_galois_certificate.py")
    lines.append(f"\\begin{{equation}}\\label{{{label}}}")
    lines.append("\\begin{aligned}")
    if chunks:
        lines.append(f"{name_tex}({var_tex})=&{chunks[0]}\\\\")
        for ch in chunks[1:-1]:
            lines.append(f"&{ch}\\\\")
        if len(chunks) > 1:
            lines.append(f"&{chunks[-1]}")
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class PolyCertificateRow:
    model: str
    degree: int
    irreducible_over_Q: bool
    factor_degrees_over_Q: List[int]
    p_irreducible: int
    factor_degrees_mod_p_irreducible: List[int]
    p_cycle: int
    factor_degrees_mod_p_cycle: List[int]
    p_disc: int
    disc_mod_p: int
    disc_is_square_mod_p: bool
    annihilator_holds: bool


def _tex_table(rows: Sequence[PolyCertificateRow]) -> str:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_addition_collision_q2_minpoly_galois_certificate.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Audit certificate for the claimed $q=2$ addition-as-projection collision Perron roots: "
        "minimal-polynomial candidates, mod-$p$ factor-degree patterns, discriminant non-square residues, "
        "and a cyclic-submodule annihilator identity on the direct-product $q=2$ moment-kernel.}"
    )
    lines.append("\\label{tab:addition-collision-q2-minpoly-galois-certificate}")
    lines.append("\\begin{tabular}{l r l l l l l}")
    lines.append("\\toprule")
    lines.append("model & $\\deg P$ & irred.$\\,/\\QQ$ & irred.$\\,/\\FF_p$ & cycle $\\FF_p$ & $\\Disc\\bmod p$ & $Q(A)\\mathbf 1=0$\\\\")
    lines.append("\\midrule")
    for r in rows:
        irQ = "Y" if r.irreducible_over_Q else "N"
        irp = f"$p={r.p_irreducible}:\\,{r.factor_degrees_mod_p_irreducible}$"
        cyc = f"$p={r.p_cycle}:\\,{r.factor_degrees_mod_p_cycle}$"
        disc = f"$p={r.p_disc}:\\,{r.disc_mod_p}$ ({'sq' if r.disc_is_square_mod_p else 'nonsq'})"
        ann = "Y" if r.annihilator_holds else "N"
        lines.append(f"{r.model} & {r.degree} & {irQ} & {irp} & {cyc} & {disc} & {ann}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="q=2 addition collision minpoly + Galois audit certificate.")
    parser.add_argument(
        "--out-json",
        type=str,
        default=str(export_dir() / "addition_collision_q2_minpoly_galois_certificate.json"),
    )
    parser.add_argument(
        "--out-tab-tex",
        type=str,
        default=str(generated_dir() / "tab_addition_collision_q2_minpoly_galois_certificate.tex"),
    )
    parser.add_argument(
        "--out-real-eq-tex",
        type=str,
        default=str(generated_dir() / "eq_addition_collision_real_input40_r2_minpoly.tex"),
    )
    parser.add_argument(
        "--out-sync-eq-tex",
        type=str,
        default=str(generated_dir() / "eq_addition_collision_sync10_r2_minpoly.tex"),
    )
    args = parser.parse_args()

    t = sp.Symbol("t")

    # Real-input40 q=2 Perron root candidate minimal polynomial (degree 26, monic).
    P_real = sp.Poly(
        t**26
        - t**25
        - 21 * t**24
        + 3 * t**23
        + 165 * t**22
        + 37 * t**21
        - 729 * t**20
        - 289 * t**19
        + 2031 * t**18
        + 891 * t**17
        - 3541 * t**16
        - 1327 * t**15
        + 3618 * t**14
        + 646 * t**13
        - 1988 * t**12
        + 640 * t**11
        + 894 * t**10
        - 888 * t**9
        - 1086 * t**8
        + 356 * t**7
        + 1222 * t**6
        - 102 * t**5
        - 402 * t**4
        - 162 * t**3
        + 92 * t**2
        + 52 * t
        - 16,
        t,
        domain=sp.ZZ,
    )
    # The cyclic-submodule annihilator observed for the essential q=2 kernel includes a nilpotent factor t^6.
    Q_real = sp.Poly(t**6 * (t - 1) * (t + 1) * P_real.as_expr(), t, domain=sp.ZZ)

    # sync10 (unconstrained) q=2 Perron root candidate minimal polynomial (degree 14, monic).
    P_sync = sp.Poly(
        t**14
        - 12 * t**13
        - 4 * t**12
        + 416 * t**11
        - 908 * t**10
        - 3700 * t**9
        + 13849 * t**8
        + 2850 * t**7
        - 58444 * t**6
        + 52270 * t**5
        + 53866 * t**4
        - 97536 * t**3
        + 36024 * t**2
        + 1296 * t
        - 640,
        t,
        domain=sp.ZZ,
    )
    Q_sync = sp.Poly(t**2 * P_sync.as_expr(), t, domain=sp.ZZ)

    # Build q=2 collision moment-kernels on the direct product state space (restricted to essential SCC).
    T10 = _build_sync10_add_transducer()
    T40 = _build_real_input40_add_transducer()

    ess10 = _essential_scc_states(transducer=T10, output_symbols=[0, 1])
    ess40 = _essential_scc_states(transducer=T40, output_symbols=[0, 1])

    rows10 = _build_q2_collision_kernel_sparse_rows(transducer=T10, base_state_indices=ess10, output_symbols=[0, 1])
    rows40 = _build_q2_collision_kernel_sparse_rows(transducer=T40, base_state_indices=ess40, output_symbols=[0, 1])
    A10 = _rows_to_int(rows10)
    A40 = _rows_to_int(rows40)

    ann10 = _apply_poly_to_one(A10, Q_sync)
    ann40 = _apply_poly_to_one(A40, Q_real)

    # Galois-style mod-p fingerprints.
    degs_Q_real = _factor_degrees_over_Q(sp.Poly(P_real.as_expr(), t, domain=sp.QQ))
    degs_Q_sync = _factor_degrees_over_Q(sp.Poly(P_sync.as_expr(), t, domain=sp.QQ))
    irred_Q_real = (degs_Q_real == [int(P_real.degree())])
    irred_Q_sync = (degs_Q_sync == [int(P_sync.degree())])

    sf5, degs5 = _factor_degrees_mod_p(P_real, 5)
    sf71, degs71 = _factor_degrees_mod_p(P_real, 71)
    disc5 = _disc_mod_p(P_real, 5)

    sf167, degs167 = _factor_degrees_mod_p(P_sync, 167)
    sf19, degs19 = _factor_degrees_mod_p(P_sync, 19)
    disc23 = _disc_mod_p(P_sync, 23)

    row_real = PolyCertificateRow(
        model="real-input40 (q=2 addition collision)",
        degree=int(P_real.degree()),
        irreducible_over_Q=bool(irred_Q_real),
        factor_degrees_over_Q=degs_Q_real,
        p_irreducible=5,
        factor_degrees_mod_p_irreducible=degs5,
        p_cycle=71,
        factor_degrees_mod_p_cycle=degs71,
        p_disc=5,
        disc_mod_p=int(disc5),
        disc_is_square_mod_p=bool(_is_quadratic_residue(disc5, 5)),
        annihilator_holds=bool(ann40),
    )
    row_sync = PolyCertificateRow(
        model="sync10 full shift (q=2 addition collision)",
        degree=int(P_sync.degree()),
        irreducible_over_Q=bool(irred_Q_sync),
        factor_degrees_over_Q=degs_Q_sync,
        p_irreducible=167,
        factor_degrees_mod_p_irreducible=degs167,
        p_cycle=19,
        factor_degrees_mod_p_cycle=degs19,
        p_disc=23,
        disc_mod_p=int(disc23),
        disc_is_square_mod_p=bool(_is_quadratic_residue(disc23, 23)),
        annihilator_holds=bool(ann10),
    )

    payload: Dict[str, object] = {
        "polynomials": {
            "P_real_coeffs_high_to_low": [int(c) for c in P_real.all_coeffs()],
            "P_sync_coeffs_high_to_low": [int(c) for c in P_sync.all_coeffs()],
            "Q_real_coeffs_high_to_low": [int(c) for c in Q_real.all_coeffs()],
            "Q_sync_coeffs_high_to_low": [int(c) for c in Q_sync.all_coeffs()],
        },
        "moment_kernel_sizes": {
            "sync10_ess_state_count": int(len(ess10)),
            "real_input40_ess_state_count": int(len(ess40)),
            "sync10_q2_state_count": int(len(A10)),
            "real_input40_q2_state_count": int(len(A40)),
        },
        "cert_rows": [asdict(row_real), asdict(row_sync)],
        "sanity": {
            "P_real_squarefree_mod_5": bool(sf5),
            "P_real_squarefree_mod_71": bool(sf71),
            "P_sync_squarefree_mod_167": bool(sf167),
            "P_sync_squarefree_mod_19": bool(sf19),
        },
        "meta": {
            "script": Path(__file__).name,
            "sympy": sp.__version__,
        },
    }

    out_json = Path(args.out_json)
    out_tab = Path(args.out_tab_tex)
    out_real_eq = Path(args.out_real_eq_tex)
    out_sync_eq = Path(args.out_sync_eq_tex)

    _write_json(out_json, payload)
    _write_text(out_tab, _tex_table([row_sync, row_real]))
    _write_text(
        out_real_eq,
        _tex_poly_aligned(
            P_real,
            var_tex="t",
            name_tex="P^{\\oplus,\\mathrm{real}}_2",
            label="eq:addition-collision-real-input40-r2-minpoly",
        ),
    )
    _write_text(
        out_sync_eq,
        _tex_poly_aligned(
            P_sync,
            var_tex="t",
            name_tex="P^{\\oplus,\\mathrm{sync10}}_2",
            label="eq:addition-collision-sync10-r2-minpoly",
        ),
    )

    # Lightweight assertions: match the intended mod-p fingerprints and annihilator checks.
    assert row_real.factor_degrees_mod_p_irreducible == [26], "unexpected mod-5 factor degrees for P_real"
    assert row_real.factor_degrees_mod_p_cycle == [23, 2, 1], "unexpected mod-71 factor degrees for P_real"
    assert row_real.disc_mod_p == 2, "unexpected Disc(P_real) mod 5"
    assert not row_real.disc_is_square_mod_p, "Disc(P_real) mod 5 unexpectedly a square"
    assert row_real.annihilator_holds, "Q_real(A)·1 != 0 for the built q=2 moment-kernel"

    assert row_sync.factor_degrees_mod_p_irreducible == [14], "unexpected mod-167 factor degrees for P_sync"
    assert row_sync.factor_degrees_mod_p_cycle == [13, 1], "unexpected mod-19 factor degrees for P_sync"
    assert row_sync.disc_mod_p == 7, "unexpected Disc(P_sync) mod 23"
    assert not row_sync.disc_is_square_mod_p, "Disc(P_sync) mod 23 unexpectedly a square"
    assert row_sync.annihilator_holds, "Q_sync(A)·1 != 0 for the built q=2 moment-kernel"

    print(f"[add-collision-q2-minpoly-galois] wrote {out_json}", flush=True)
    print(f"[add-collision-q2-minpoly-galois] wrote {out_tab}", flush=True)
    print(f"[add-collision-q2-minpoly-galois] wrote {out_real_eq}", flush=True)
    print(f"[add-collision-q2-minpoly-galois] wrote {out_sync_eq}", flush=True)


if __name__ == "__main__":
    main()

