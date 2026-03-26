#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fibonacci-cube Gray–Hamilton audit.

We verify the recursive Gray–Hamilton construction used in the paper for Γ_n:
  G_0 = (ε),  G_1 = (0,1),
  G_n = 0·rev(G_{n-1})  concatenated with  10·rev(G_{n-2})  (n>=2),
where rev is list reversal and prefixing is applied to each word in the list.

For each n<=n_max we check:
  - all words are Fibonacci-legal (no adjacent 11),
  - all words are unique and count equals |V(Γ_n)| = F_{n+2},
  - consecutive words differ in exactly one bit (Gray adjacency).

Outputs:
  - artifacts/export/fibonacci_cube_gray_hamilton_audit.json
  - sections/generated/tab_fibonacci_cube_gray_hamilton_audit.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_phi_fold import fib_upto


def _is_fibonacci_legal(bits: str) -> bool:
    return "11" not in bits


def _ham_dist(a: str, b: str) -> int:
    if len(a) != len(b):
        raise ValueError("Hamming distance requires equal-length strings")
    return sum(1 for x, y in zip(a, b) if x != y)


def gray_hamilton_path(n: int) -> List[str]:
    n = int(n)
    if n < 0:
        raise ValueError("n must be >= 0")
    if n == 0:
        return [""]
    if n == 1:
        return ["0", "1"]
    g_nm1 = gray_hamilton_path(n - 1)
    g_nm2 = gray_hamilton_path(n - 2)
    left = ["0" + w for w in reversed(g_nm1)]
    right = ["10" + w for w in reversed(g_nm2)]
    return left + right


@dataclass(frozen=True)
class Row:
    n: int
    v_expected: int
    path_len: int
    legal_ok: bool
    unique_ok: bool
    adjacency_ok: bool
    first: str
    last: str

    def ok(self) -> bool:
        return self.legal_ok and self.unique_ok and self.adjacency_ok and (self.path_len == self.v_expected)

    def to_dict(self) -> Dict[str, object]:
        return {
            "n": int(self.n),
            "v_expected": int(self.v_expected),
            "path_len": int(self.path_len),
            "legal_ok": bool(self.legal_ok),
            "unique_ok": bool(self.unique_ok),
            "adjacency_ok": bool(self.adjacency_ok),
            "first": str(self.first),
            "last": str(self.last),
            "ok": bool(self.ok()),
        }


def write_table(rows: List[Row], out_path: Path, n_max: int) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append(
        (
            "\\caption{Gray--Hamilton 审计：递归序列 $\\mathcal G_n$ 在 $n\\le %d$ 上均为 $\\Gamma_n$ 的 Hamilton 路径，"
            "且相邻仅差一位（定理~\\ref{thm:pom-fibcube-gray-hamilton}）。}"
        )
        % int(n_max)
    )
    lines.append("\\label{tab:fibonacci_cube_gray_hamilton_audit}")
    lines.append("\\begin{tabular}{r r r r r r l l}")
    lines.append("\\toprule")
    lines.append(
        "$n$ & $|V(\\Gamma_n)|$ & $|\\mathcal G_n|$ & legal & unique & Gray & first & last\\\\"
    )
    lines.append("\\midrule")
    for r in rows:
        legal = "OK" if r.legal_ok else "FAIL"
        uniq = "OK" if r.unique_ok else "FAIL"
        adj = "OK" if r.adjacency_ok else "FAIL"
        first = "\\texttt{" + (r.first if r.first != "" else "\\ensuremath{\\epsilon}") + "}"
        last = "\\texttt{" + (r.last if r.last != "" else "\\ensuremath{\\epsilon}") + "}"
        lines.append(
            f"{r.n} & {r.v_expected} & {r.path_len} & {legal} & {uniq} & {adj} & {first} & {last}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Audit the Fibonacci-cube Gray–Hamilton construction.")
    ap.add_argument("--n-max", type=int, default=12)
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "fibonacci_cube_gray_hamilton_audit.json"),
    )
    return ap.parse_args()


def main() -> None:
    args = parse_args()
    n_max = int(args.n_max)
    if n_max < 0:
        raise SystemExit("Require --n-max >= 0")

    fib = fib_upto(n_max + 2)  # F_1..F_{n_max+2}, with F_1=F_2=1

    rows: List[Row] = []
    for n in range(0, n_max + 1):
        v_expected = fib[n + 1]  # F_{n+2}
        path = gray_hamilton_path(n)

        legal_ok = all(len(w) == n and _is_fibonacci_legal(w) for w in path)
        unique_ok = len(set(path)) == len(path)
        adjacency_ok = all(_ham_dist(path[i], path[i + 1]) == 1 for i in range(len(path) - 1))

        first = path[0] if path else ""
        last = path[-1] if path else ""

        rows.append(
            Row(
                n=n,
                v_expected=int(v_expected),
                path_len=len(path),
                legal_ok=bool(legal_ok),
                unique_ok=bool(unique_ok),
                adjacency_ok=bool(adjacency_ok),
                first=first,
                last=last,
            )
        )

    # Hard fail if any n is not OK; this is an audit script.
    bad = [r for r in rows if not r.ok()]
    if bad:
        msgs = ", ".join(f"n={r.n}(legal={r.legal_ok},unique={r.unique_ok},adj={r.adjacency_ok},len={r.path_len},V={r.v_expected})" for r in bad)
        raise AssertionError(f"Gray–Hamilton audit failed: {msgs}")

    payload: Dict[str, object] = {
        "params": {
            "n_max": n_max,
            "definition": {"Gamma_n": "Fibonacci cube on length-n Fibonacci-legal 0/1 words"},
        },
        "rows": [r.to_dict() for r in rows],
    }
    json_out = Path(args.json_out)
    if not json_out.is_absolute():
        json_out = Path.cwd() / json_out
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    write_table(rows, out_path=(generated_dir() / "tab_fibonacci_cube_gray_hamilton_audit.tex"), n_max=n_max)


if __name__ == "__main__":
    main()

