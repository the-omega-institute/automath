#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Max-fiber achievers with hidden-bit (b) two-layer decomposition for Fold_m.

For omega in {0,1}^m, define
  N(omega) = sum_{k=1}^m omega_k F_{k+1}.
In the paper we have the unique one-bit decomposition:
  N(omega) = V_m(Fold_m(omega)) + b(omega) * F_{m+2},   b(omega) in {0,1},
and the congruence characterization:
  Fold_m(omega)=Fold_m(omega')  <->  N(omega) ≡ N(omega') (mod F_{m+2}).

Since max N(omega) = F_{m+3}-2 < 2*F_{m+2} for m>=2, the hidden bit b(omega) is
exactly the quotient of N(omega) by F_{m+2}.

For each stable type x in X_m with residue r:=V_m(x) in [0,F_{m+2}),
define the b-layer fiber counts:
  d_{m,0}(x) = #{omega : Fold_m(omega)=x, b(omega)=0} = #{omega : N(omega)=r}
  d_{m,1}(x) = #{omega : Fold_m(omega)=x, b(omega)=1} = #{omega : N(omega)=r+F_{m+2}}
and d_m(x)=d_{m,0}(x)+d_{m,1}(x).

This script computes, for m<=M:
  - D_m (closed form consistency check),
  - the maximizer residues r where d_m(x)=D_m,
  - for each maximizer, the pair (d_{m,0}, d_{m,1}),
  - summary multiplicities of distinct split-pairs.

Outputs:
  - artifacts/export/fold_max_fiber_achievers_bsplit.json
  - sections/generated/tab_fold_max_fiber_achievers_bsplit.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


def fib_upto(n: int) -> List[int]:
    if n < 0:
        raise ValueError("n must be >= 0")
    F = [0, 1]
    for _ in range(2, n + 1):
        F.append(F[-1] + F[-2])
    return F[: n + 1]


def D_closed(m: int) -> int:
    if m < 2:
        raise ValueError("m must be >= 2")
    F = fib_upto((m // 2) + 2)
    if m % 2 == 0:
        k = m // 2
        return int(F[k + 2])
    k = (m - 1) // 2
    return int(2 * F[k + 1])


def zeckendorf_word(m: int, r: int) -> str:
    """Unique x in X_m (no adjacent 11) with V_m(x)=r."""
    if m < 1:
        raise ValueError("m must be >= 1")
    F = fib_upto(m + 2)
    if r < 0 or r >= F[m + 2]:
        raise ValueError("r out of range for modulus F_{m+2}")
    rem = int(r)
    x = [0] * m
    prev_one = False
    for k in range(m, 0, -1):
        w = F[k + 1]
        if (not prev_one) and rem >= w:
            x[k - 1] = 1
            rem -= w
            prev_one = True
        else:
            x[k - 1] = 0
            prev_one = False
    if rem != 0:
        raise ValueError("Greedy Zeckendorf failed")
    for i in range(m - 1):
        if x[i] == 1 and x[i + 1] == 1:
            raise ValueError("Adjacent 11 produced")
    return "".join(str(b) for b in x)


@dataclass(frozen=True)
class Achiever:
    r: int
    d0: int
    d1: int
    word: str


@dataclass(frozen=True)
class Row:
    m: int
    D_closed: int
    kappa: int
    # distinct split-pairs with multiplicities, sorted by decreasing max(d0,d1) then d0
    split_pair_mults: List[Tuple[int, int, int]]  # (d0,d1,mult)
    achievers: List[Achiever]  # truncated to show_words for table


def _pair_mults(pairs: List[Tuple[int, int]]) -> List[Tuple[int, int, int]]:
    mp: Dict[Tuple[int, int], int] = {}
    for a, b in pairs:
        mp[(int(a), int(b))] = mp.get((int(a), int(b)), 0) + 1
    out = [(a, b, mult) for (a, b), mult in mp.items()]
    out.sort(key=lambda t: (-max(t[0], t[1]), -t[0], -t[1]))
    return out


def write_table_tex(path: Path, rows: List[Row]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Max-fiber achievers with hidden-bit split for Fold$_m$. "
        "For each maximizer $x$ attaining $d_m(x)=D_m$, we report the pair "
        "$(d_{m,0}(x),d_{m,1}(x))$ coming from the unique one-bit decomposition "
        "$N(\\omega)=V_m(x)+b(\\omega)F_{m+2}$ (so $b\\in\\{0,1\\}$). "
        "Pairs are listed with multiplicities among all achievers at that $m$. "
        "The column $\\kappa_m^{\\mathrm{max}}$ is the achiever multiplicity "
        "$\\#\\{x\\in X_m:\\ d_m(x)=D_m\\}$.}"
    )
    lines.append("\\label{tab:fold_max_fiber_achievers_bsplit}")
    lines.append("\\begin{tabular}{r r r l}")
    lines.append("\\toprule")
    lines.append("$m$ & $D_m$ & $\\kappa_m^{\\mathrm{max}}$ & achiever split-pairs (mult.)\\\\")
    lines.append("\\midrule")
    for r in rows:
        pieces = []
        for (d0, d1, mult) in r.split_pair_mults:
            if mult == 1:
                pieces.append(f"$({d0},{d1})$")
            else:
                pieces.append(f"$({d0},{d1})\\times {mult}$")
        s = ",\\;".join(pieces) if pieces else "--"
        lines.append(f"{r.m} & {r.D_closed} & {r.kappa} & {s}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Max-fiber achievers with hidden-bit split (m<=M).")
    parser.add_argument("--m-min", type=int, default=2)
    parser.add_argument("--m-max", type=int, default=30)
    parser.add_argument("--show-words", type=int, default=4)
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fold_max_fiber_achievers_bsplit.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_fold_max_fiber_achievers_bsplit.tex"),
    )
    args = parser.parse_args()

    if args.m_min < 2 or args.m_max < args.m_min:
        raise SystemExit("Require m_max >= m_min >= 2")
    if args.show_words < 1:
        raise SystemExit("Require --show-words >= 1")

    m_max = int(args.m_max)
    F = fib_upto(m_max + 3)  # need up to F_{m+3}
    # Global max sum for m_max is F_{m+3}-2, hence array length is F_{m+3}-1.
    Lmax = int(F[m_max + 3] - 1)

    prog = Progress("fold-max-fiber-bsplit", every_seconds=20.0)

    dp = np.zeros(Lmax, dtype=np.uint64)
    dp[0] = 1
    dp_next = np.zeros(Lmax, dtype=np.uint64)

    rows: List[Row] = []

    cur_len = 1  # dp[:cur_len] is active
    for m in range(1, m_max + 1):
        w = int(F[m + 1])  # weight F_{m+1} for position m
        new_len = int(F[m + 3] - 1)  # max sum + 1 for this m
        if new_len > Lmax:
            raise RuntimeError("unexpected length overflow")
        dp_next[:new_len] = 0
        dp_next[:cur_len] = dp[:cur_len]
        dp_next[w : w + cur_len] += dp[:cur_len]
        dp, dp_next = dp_next, dp
        cur_len = new_len

        if m < args.m_min:
            continue

        mod = int(F[m + 2])
        Dc = int(D_closed(m))

        # Compute c_m(r)=d0+d1 using the exact dp:
        d0 = dp[:mod].astype(np.uint64, copy=False)
        d1 = np.zeros(mod, dtype=np.uint64)
        upper = min(cur_len - mod, mod)
        if upper > 0:
            d1[:upper] = dp[mod : mod + upper]
        c = d0 + d1

        Ddp = int(np.max(c))
        if Ddp != Dc:
            raise ValueError(f"D mismatch at m={m}: exact={Ddp}, closed={Dc}")

        residues = np.flatnonzero(c == Ddp).astype(int).tolist()
        kappa = int(len(residues))

        pairs: List[Tuple[int, int]] = []
        achievers: List[Achiever] = []
        for r in residues:
            a0 = int(d0[r])
            a1 = int(d1[r])
            pairs.append((a0, a1))
        mults = _pair_mults(pairs)

        # Representative achievers for audit (smallest residues):
        for r in sorted(residues)[: int(args.show_words)]:
            a0 = int(d0[r])
            a1 = int(d1[r])
            achievers.append(Achiever(r=int(r), d0=a0, d1=a1, word=zeckendorf_word(m, int(r))))

        rows.append(
            Row(
                m=int(m),
                D_closed=Dc,
                kappa=kappa,
                split_pair_mults=mults,
                achievers=achievers,
            )
        )
        print(f"[fold-max-fiber-bsplit] m={m} mod={mod} D={Ddp} kappa={kappa}", flush=True)

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    payload = {"m_min": int(args.m_min), "m_max": int(args.m_max), "rows": [asdict(r) for r in rows]}
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[fold-max-fiber-bsplit] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[fold-max-fiber-bsplit] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

