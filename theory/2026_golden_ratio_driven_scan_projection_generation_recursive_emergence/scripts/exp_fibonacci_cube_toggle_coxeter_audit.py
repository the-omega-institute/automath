#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fibonacci-cube toggle/Coxeter audit.

We work on the Fibonacci cube Γ_n (Definition~\\ref{def:pom-fibonacci-cube}): vertices are
length-n 0/1 words with no adjacent 11, edges are single-bit flips staying legal.

Define the toggle (switch) involution τ_i on V(Γ_n) by:
  - attempt to flip bit i; if the result is Fibonacci-legal then apply the flip,
    otherwise do nothing.

This script verifies, for each n<=n_max, the Coxeter relations on the path:
  - τ_i^2 = 1
  - τ_i τ_j = τ_j τ_i for |i-j|>1
  - (τ_i τ_{i+1})^6 = 1
and audits the scan element c_n = τ_1 τ_2 ... τ_n by computing:
  - its permutation order T(n)=ord(c_n),
  - its cycle-length multiset and sign (cyclotomic fingerprint).

It also audits the maximal orbit length (maximum cycle length) under c_n, and checks the
explicit long-orbit witness S*_n used in the paper:
  - for n>=4, |Orb_{c_n}(S*_n)| = 3n-7.

Outputs:
  - artifacts/export/fibonacci_cube_toggle_coxeter_audit.json
  - sections/generated/tab_fibonacci_cube_toggle_coxeter_audit.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from math import gcd
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto


def _is_legal(bits: str) -> bool:
    return "11" not in bits


def _vertices_gamma(n: int) -> List[str]:
    n = int(n)
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return [""]
    out: List[str] = []
    for x in range(1 << n):
        s = format(x, "0%db" % n)
        if _is_legal(s):
            out.append(s)
    out.sort()
    return out


def _toggle_perm(vertices: List[str], i1: int) -> List[int]:
    """Return permutation τ_i as a list p where p[idx] = idx'."""
    n = len(vertices[0]) if vertices else 0
    i = int(i1) - 1
    if i < 0 or i >= n:
        raise ValueError("toggle index out of range")
    idx = {v: j for j, v in enumerate(vertices)}
    p = list(range(len(vertices)))
    for j, v in enumerate(vertices):
        if n == 0:
            p[j] = j
            continue
        w = list(v)
        w[i] = "1" if w[i] == "0" else "0"
        w2 = "".join(w)
        if _is_legal(w2):
            p[j] = idx[w2]
        else:
            p[j] = j
    return p


def _compose(p: List[int], q: List[int]) -> List[int]:
    """Return composition p∘q (apply q then p)."""
    if len(p) != len(q):
        raise ValueError("perm size mismatch")
    return [p[q[i]] for i in range(len(p))]


def _is_identity(p: List[int]) -> bool:
    return all(i == p[i] for i in range(len(p)))


def _perm_order(p: List[int]) -> int:
    """Permutation order via cycle lcm."""
    n = len(p)
    seen = [False] * n
    l = 1
    for i in range(n):
        if seen[i]:
            continue
        # Follow cycle.
        j = i
        clen = 0
        while not seen[j]:
            seen[j] = True
            j = p[j]
            clen += 1
        if clen <= 0:
            continue
        l = (l // gcd(l, clen)) * clen
    return int(l)


def _cycle_lengths(p: List[int]) -> List[int]:
    n = len(p)
    seen = [False] * n
    lens: List[int] = []
    for i in range(n):
        if seen[i]:
            continue
        j = i
        clen = 0
        while not seen[j]:
            seen[j] = True
            j = p[j]
            clen += 1
        lens.append(int(clen))
    return lens


def _perm_sign(p: List[int]) -> int:
    # sign = (-1)^(N - number_of_cycles)
    n = len(p)
    c = len(_cycle_lengths(p))
    return -1 if ((n - c) % 2 == 1) else 1


def _pow_perm(p: List[int], k: int) -> List[int]:
    """Return p^k by repeated squaring."""
    k = int(k)
    if k < 0:
        raise ValueError("k must be >= 0")
    n = len(p)
    # identity
    out = list(range(n))
    base = p[:]
    e = k
    while e > 0:
        if e & 1:
            out = _compose(out, base)
        e >>= 1
        if e:
            base = _compose(base, base)
    return out


def _eq_perm(p: List[int], q: List[int]) -> bool:
    return p == q


@dataclass(frozen=True)
class Row:
    n: int
    v: int
    invol_ok: bool
    comm_ok: bool
    adj6_ok: bool
    ord_c: int
    cycle_type: str
    cycle_max: int
    witness: str
    witness_orbit: int
    sign_c: int

    def ok(self) -> bool:
        return self.invol_ok and self.comm_ok and self.adj6_ok

    def to_dict(self) -> Dict[str, object]:
        return {
            "n": int(self.n),
            "V": int(self.v),
            "invol_ok": bool(self.invol_ok),
            "comm_ok": bool(self.comm_ok),
            "adj6_ok": bool(self.adj6_ok),
            "ord_c": int(self.ord_c),
            "cycle_type": str(self.cycle_type),
            "cycle_max": int(self.cycle_max),
            "witness": str(self.witness),
            "witness_orbit": int(self.witness_orbit),
            "sign_c": int(self.sign_c),
            "ok": bool(self.ok()),
        }


def _format_cycle_type(p: List[int]) -> str:
    lens = _cycle_lengths(p)
    # Count multiplicities.
    counts: Dict[int, int] = {}
    for d in lens:
        counts[d] = counts.get(d, 0) + 1
    parts: List[str] = []
    for d in sorted(counts.keys()):
        m = counts[d]
        if m == 1:
            parts.append(str(d))
        else:
            parts.append(f"{d}x{m}")
    return ",".join(parts)


def _cycle_max(p: List[int]) -> int:
    lens = _cycle_lengths(p)
    return int(max(lens) if lens else 0)


def _witness_s_star(n: int) -> str:
    """Explicit long-orbit witness S*_n (as a 0/1 word) used in the paper."""
    n = int(n)
    if n <= 0:
        return ""
    if n < 4:
        return "0" * n
    a = ((n + 1) % 3) + 1  # 1-based
    bits = ["0"] * n
    j = 0
    while True:
        pos = a + 3 * j
        if pos > n - 4:
            break
        bits[pos - 1] = "1"
        j += 1
    return "".join(bits)


def _orbit_len_from_word(vertices: List[str], p: List[int], w: str) -> int:
    idx = {v: j for j, v in enumerate(vertices)}
    if w not in idx:
        raise ValueError("witness word not a vertex")
    s = idx[w]
    seen = {s: 0}
    cur = s
    t = 0
    while True:
        t += 1
        cur = p[cur]
        if cur in seen:
            return int(t - seen[cur])
        seen[cur] = t


def write_table(rows: List[Row], out_path: Path, n_max: int) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        (
            "\\caption{Toggle--Coxeter 审计：在 $\\Gamma_n$ 上的开关算子 $\\tau_i$（定义~\\ref{def:pom-fiber-toggle-group}）"
            "在 $n\\le %d$ 上满足六角 Coxeter 关系（定理~\\ref{thm:pom-toggle-coxeter-relations-path}），"
            "并给出扫描元 $c_n=\\tau_1\\cdots\\tau_n$ 的周期 $T(n)=\\mathrm{ord}(c_n)$ 及循环分解指纹（定义~\\ref{def:pom-toggle-coxeter-element}--定理~\\ref{thm:pom-coxeter-monodromy-cyclotomic}）。}"
        )
        % int(n_max)
    )
    lines.append("\\label{tab:fibonacci_cube_toggle_coxeter_audit}")
    lines.append("\\begin{tabular}{r r r r r r r l r}")
    lines.append("\\toprule")
    lines.append(
        "$n$ & $|V(\\Gamma_n)|$ & invol & comm & adj6 & $T(n)$ & $L_{\\max}(n)$ & cycle type & $\\mathrm{sgn}(c_n)$\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        invol = "OK" if r.invol_ok else "FAIL"
        comm = "OK" if r.comm_ok else "FAIL"
        adj6 = "OK" if r.adj6_ok else "FAIL"
        sgn = "+1" if r.sign_c > 0 else "-1"
        cyc = "\\texttt{" + r.cycle_type + "}"
        lines.append(
            f"{r.n} & {r.v} & {invol} & {comm} & {adj6} & {r.ord_c} & {r.cycle_max} & {cyc} & {sgn}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Audit toggle/Coxeter relations on the Fibonacci cube Γ_n.")
    ap.add_argument("--n-max", type=int, default=12)
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fibonacci_cube_toggle_coxeter_audit.json"),
    )
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    n_max = int(args.n_max)
    if n_max < 0:
        raise SystemExit("Require --n-max >= 0")

    # Precompute Fibonacci numbers for |V(Γ_n)| = F_{n+2}, with F_1=F_2=1.
    fib = fib_upto(n_max + 2)

    rows: List[Row] = []
    for n in range(0, n_max + 1):
        verts = _vertices_gamma(n)
        v_expected = fib[n + 1] if n >= 0 else 0  # F_{n+2}
        if len(verts) != int(v_expected):
            raise AssertionError(f"vertex count mismatch for n={n}: got {len(verts)} expected {v_expected}")

        taus: List[List[int]] = []
        for i in range(1, n + 1):
            taus.append(_toggle_perm(verts, i1=i))

        invol_ok = True
        comm_ok = True
        adj6_ok = True

        # τ_i^2 = id
        for i in range(n):
            if not _is_identity(_compose(taus[i], taus[i])):
                invol_ok = False
                break

        # τ_i τ_j = τ_j τ_i for |i-j|>1
        if comm_ok and n >= 3:
            for i in range(n):
                for j in range(n):
                    if abs(i - j) > 1:
                        lhs = _compose(taus[i], taus[j])
                        rhs = _compose(taus[j], taus[i])
                        if not _eq_perm(lhs, rhs):
                            comm_ok = False
                            break
                if not comm_ok:
                    break

        # hexagon Coxeter relation: (τ_i τ_{i+1})^6 = id
        if adj6_ok and n >= 2:
            for i in range(n - 1):
                st = _compose(taus[i], taus[i + 1])
                if not _is_identity(_pow_perm(st, 6)):
                    adj6_ok = False
                    break

        # c_n = τ_1 τ_2 ... τ_n (functional composition, rightmost applied first).
        c = list(range(len(verts)))
        for i in range(n):
            c = _compose(c, taus[i])
        ord_c = _perm_order(c)
        cycle_type = _format_cycle_type(c)
        cycle_max = _cycle_max(c)
        sign_c = _perm_sign(c)
        witness = _witness_s_star(n)
        witness_orbit = _orbit_len_from_word(verts, c, witness) if verts else 0

        # Assert the explicit long-orbit formula for n>=4 (audited window).
        if n >= 4 and witness_orbit != (3 * n - 7):
            raise AssertionError(f"S*_n long-orbit mismatch for n={n}: got {witness_orbit}, expected {3*n-7}")
        if n >= 4 and cycle_max < (3 * n - 7):
            raise AssertionError(f"cycle_max too small for n={n}: {cycle_max} < {3*n-7}")

        rows.append(
            Row(
                n=n,
                v=len(verts),
                invol_ok=invol_ok,
                comm_ok=comm_ok,
                adj6_ok=adj6_ok,
                ord_c=int(ord_c),
                cycle_type=str(cycle_type),
                cycle_max=int(cycle_max),
                witness=str(witness),
                witness_orbit=int(witness_orbit),
                sign_c=int(sign_c),
            )
        )

    bad = [r for r in rows if not r.ok()]
    if bad:
        msgs = ", ".join(
            f"n={r.n}(invol={r.invol_ok},comm={r.comm_ok},adj6={r.adj6_ok},ord={r.ord_c})"
            for r in bad
        )
        raise AssertionError(f"toggle/Coxeter audit failed: {msgs}")

    payload: Dict[str, object] = {
        "params": {"n_max": n_max},
        "rows": [r.to_dict() for r in rows],
    }
    json_out = Path(args.json_out)
    if not json_out.is_absolute():
        json_out = Path.cwd() / json_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    write_table(rows, out_path=(generated_dir() / "tab_fibonacci_cube_toggle_coxeter_audit.tex"), n_max=n_max)


if __name__ == "__main__":
    main()

