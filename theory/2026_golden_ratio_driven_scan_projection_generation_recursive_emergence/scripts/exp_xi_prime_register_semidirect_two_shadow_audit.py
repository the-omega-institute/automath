#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit certificate for:
  1) shift-semidirect Godel register embedding of free-monoid trajectories,
  2) two-invariant ellipse classification over Q,
  3) two-shadow rigidity witness (finite prime shadow + real ellipse shadow).

All code is English-only by repository convention.

Outputs:
  - artifacts/export/xi_prime_register_semidirect_two_shadow_audit.json
  - sections/generated/eq_xi_prime_register_semidirect_two_shadow_audit.tex
  - sections/generated/tab_xi_elliptic_two_shadow_invariants_audit.tex
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

import sympy as sp

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


ALPHABET: Tuple[str, ...] = ("a", "b", "c")
CODE: Dict[str, int] = {"a": 1, "b": 2, "c": 3}
REVERSE_CODE: Dict[int, str] = {v: k for k, v in CODE.items()}


def _first_primes(n: int) -> List[int]:
    out: List[int] = []
    p = 2
    while len(out) < n:
        if sp.isprime(p):
            out.append(p)
        p += 1
    return out


def _all_words(alphabet: Sequence[str], max_len: int) -> List[str]:
    out = [""]
    for n in range(1, max_len + 1):
        for tup in product(alphabet, repeat=n):
            out.append("".join(tup))
    return out


def _godel(word: str, code: Dict[str, int], primes: Sequence[int]) -> int:
    if len(word) > len(primes):
        raise ValueError("Prime table is too short for this word length.")
    v = 1
    for i, ch in enumerate(word):
        v *= int(primes[i]) ** int(code[ch])
    return int(v)


def _shift_prime_indices(value: int, shift_k: int, primes: Sequence[int]) -> int:
    if value <= 0:
        raise ValueError("Shift is defined on positive integers.")
    if value == 1:
        return 1
    fac = sp.factorint(value)
    p_to_idx = {int(p): i for i, p in enumerate(primes)}
    out = 1
    for p, e in fac.items():
        pp = int(p)
        ee = int(e)
        if pp not in p_to_idx:
            raise RuntimeError(f"Prime {pp} not found in prime table.")
        j = p_to_idx[pp] + int(shift_k)
        if j >= len(primes):
            raise RuntimeError("Prime table is too short for shifted index.")
        out *= int(primes[j]) ** ee
    return int(out)


def _register_mul(
    left: Tuple[int, int],
    right: Tuple[int, int],
    primes: Sequence[int],
) -> Tuple[int, int]:
    n, A = left
    m, B = right
    return (int(n + m), int(A * _shift_prime_indices(B, n, primes)))


def _J(word: str, code: Dict[str, int], primes: Sequence[int]) -> Tuple[int, int]:
    return (len(word), _godel(word, code, primes))


def _decode_register(
    length: int,
    godel_value: int,
    code_inv: Dict[int, str],
    primes: Sequence[int],
) -> str:
    if length < 0:
        raise ValueError("length must be non-negative")
    fac = sp.factorint(godel_value)
    chars: List[str] = []
    for i in range(length):
        p = int(primes[i])
        exp = int(fac.get(p, 0))
        if exp not in code_inv:
            raise RuntimeError(f"Prime exponent {exp} at index {i+1} is outside coding range.")
        chars.append(code_inv[exp])
        if p in fac:
            del fac[p]
    if fac:
        raise RuntimeError("Found extra prime factors beyond encoded length.")
    return "".join(chars)


def _perm_compose(p: Tuple[int, ...], q: Tuple[int, ...]) -> Tuple[int, ...]:
    # (p ∘ q)(i) = p(q(i))
    n = len(p)
    return tuple(int(p[int(q[i]) - 1]) for i in range(n))


def _perm_inverse(p: Tuple[int, ...]) -> Tuple[int, ...]:
    n = len(p)
    inv = [0] * n
    for i, img in enumerate(p, start=1):
        inv[int(img) - 1] = i
    return tuple(inv)


def _perm_commutator(a: Tuple[int, ...], b: Tuple[int, ...]) -> Tuple[int, ...]:
    return _perm_compose(
        _perm_compose(_perm_compose(a, b), _perm_inverse(a)),
        _perm_inverse(b),
    )


@dataclass(frozen=True)
class MatrixAuditRow:
    name: str
    det: str
    delta1: str
    delta2: str
    sigma1_numeric: float
    sigma2_numeric: float


def _rat(x: Fraction) -> sp.Rational:
    return sp.Rational(int(x.numerator), int(x.denominator))


def _ellipse_invariants(A: sp.Matrix) -> Tuple[sp.Rational, sp.Rational]:
    detA = sp.Rational(A.det())
    delta1 = sp.Rational(detA * detA)
    delta2 = sp.Rational((A.T * A).trace())
    return delta1, delta2


def _sigmas_from_invariants(delta1: sp.Rational, delta2: sp.Rational) -> Tuple[sp.Expr, sp.Expr]:
    disc = sp.sqrt(sp.simplify(delta2 * delta2 - 4 * delta1))
    t1 = sp.simplify((delta2 + disc) / 2)
    t2 = sp.simplify((delta2 - disc) / 2)
    s1 = sp.sqrt(t1)
    s2 = sp.sqrt(t2)
    # Order descending in the real-positive branch.
    if float(sp.N(s1, 50)) < float(sp.N(s2, 50)):
        s1, s2 = s2, s1
    return s1, s2


def _matrix_to_tex(A: sp.Matrix) -> str:
    return (
        "\\begin{psmallmatrix}"
        + f"{sp.sstr(A[0,0])} & {sp.sstr(A[0,1])}\\\\"
        + f"{sp.sstr(A[1,0])} & {sp.sstr(A[1,1])}"
        + "\\end{psmallmatrix}"
    )


def _enumerate_orthogonal_integer_2x2() -> Tuple[List[sp.Matrix], List[sp.Matrix]]:
    all_mats: List[sp.Matrix] = []
    so_mats: List[sp.Matrix] = []
    I2 = sp.eye(2)
    for a, b, c, d in product([-1, 0, 1], repeat=4):
        M = sp.Matrix([[a, b], [c, d]])
        if M.det() not in (1, -1):
            continue
        if (M.T * M) != I2:
            continue
        all_mats.append(M)
        if M.det() == 1:
            so_mats.append(M)
    # Deduplicate by entries.
    uniq_all: Dict[Tuple[int, int, int, int], sp.Matrix] = {}
    uniq_so: Dict[Tuple[int, int, int, int], sp.Matrix] = {}
    for M in all_mats:
        key = (int(M[0, 0]), int(M[0, 1]), int(M[1, 0]), int(M[1, 1]))
        uniq_all[key] = M
    for M in so_mats:
        key = (int(M[0, 0]), int(M[0, 1]), int(M[1, 0]), int(M[1, 1]))
        uniq_so[key] = M
    return list(uniq_all.values()), list(uniq_so.values())


def _write_eq_tex(
    *,
    commutator_perm: Tuple[int, ...],
    moved_index: int,
    max_word_len: int,
    o2_size: int,
    so2_size: int,
    out_path: Path,
) -> None:
    comm_str = "(" + ",".join(str(x) for x in commutator_perm) + ")"
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_xi_prime_register_semidirect_two_shadow_audit.py")
    lines.append("\\begin{equation}\\label{eq:xi_prime_register_semidirect_two_shadow_audit}")
    lines.append("\\begin{aligned}")
    lines.append(
        "\\rho([\\alpha,\\beta])&="
        + comm_str
        + ",\\qquad \\rho([\\alpha,\\beta])("
        + str(moved_index)
        + ")\\neq "
        + str(moved_index)
        + ",\\\\"
    )
    lines.append(
        "J(uv)&=J(u)\\odot J(v)\\ \\text{(checked for all words with }|u|,|v|\\le "
        + str(max_word_len)
        + "\\text{)},\\\\"
    )
    lines.append(
        "\\left|O_2(\\ZZ)\\right|&="
        + str(o2_size)
        + ",\\qquad \\left|SO_2(\\ZZ)\\right|="
        + str(so2_size)
        + "."
    )
    lines.append("\\end{aligned}")
    lines.append("\\end{equation}")
    lines.append("")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def _write_table_tex(rows: Sequence[MatrixAuditRow], out_path: Path) -> None:
    lines: List[str] = []
    lines.append("% AUTO-GENERATED by scripts/exp_xi_prime_register_semidirect_two_shadow_audit.py")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{有理矩阵样本的椭圆二元不变量审计："
        "$\\Delta_1=(\\det A)^2$ 与 $\\Delta_2=\\mathrm{tr}(A^\\top A)$。}"
    )
    lines.append("\\label{tab:xi_elliptic_two_shadow_invariants_audit}")
    lines.append("\\begin{tabular}{l l l l r r}")
    lines.append("\\toprule")
    lines.append("id & $\\det A$ & $\\Delta_1(A)$ & $\\Delta_2(A)$ & $\\sigma_1$ (num.) & $\\sigma_2$ (num.)\\\\")
    lines.append("\\midrule")
    for r in rows:
        name_tex = f"${r.name}$"
        lines.append(
            f"{name_tex} & ${r.det}$ & ${r.delta1}$ & ${r.delta2}$ & "
            f"{r.sigma1_numeric:.9f} & {r.sigma2_numeric:.9f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit semidirect prime register and two-shadow rigidity claims.")
    ap.add_argument("--max-word-len", type=int, default=4, help="Max word length for explicit finite checks.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "xi_prime_register_semidirect_two_shadow_audit.json"),
    )
    ap.add_argument(
        "--tex-eq-out",
        type=str,
        default=str(generated_dir() / "eq_xi_prime_register_semidirect_two_shadow_audit.tex"),
    )
    ap.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_xi_elliptic_two_shadow_invariants_audit.tex"),
    )
    args = ap.parse_args()

    max_word_len = int(args.max_word_len)
    if max_word_len < 1:
        raise SystemExit("Require --max-word-len >= 1")

    progress = Progress("xi_prime_register_two_shadow")
    primes = _first_primes(max_word_len + 16)

    # ------------------------------------------------------------------
    # (A) Non-abelian monodromy witness via S4 commutator.
    # ------------------------------------------------------------------
    # alpha=(1 2), beta=(1 2 3 4) in one-line notation.
    alpha = (2, 1, 3, 4)
    beta = (2, 3, 4, 1)
    comm = _perm_commutator(alpha, beta)
    identity = (1, 2, 3, 4)
    if comm == identity:
        raise RuntimeError("Unexpected: chosen commutator is identity.")
    moved_index = next(i for i in range(1, 5) if comm[i - 1] != i)
    progress.tick("computed explicit S4 commutator witness")

    # ------------------------------------------------------------------
    # (B) Shift-semidirect Godel register checks.
    # ------------------------------------------------------------------
    words = _all_words(ALPHABET, max_word_len)
    hom_ok = True
    inj_ok = True
    noncomm_ok = True

    for u in words:
        Ju = _J(u, CODE, primes)
        decoded_u = _decode_register(Ju[0], Ju[1], REVERSE_CODE, primes)
        if decoded_u != u:
            inj_ok = False
            break

    if inj_ok:
        for u in words:
            for v in words:
                lhs = _J(u + v, CODE, primes)
                rhs = _register_mul(_J(u, CODE, primes), _J(v, CODE, primes), primes)
                if lhs != rhs:
                    hom_ok = False
                    break
            if not hom_ok:
                break
    progress.tick("checked semidirect homomorphism and injective decoding")

    if max_word_len >= 2:
        noncomm_ok = (
            _register_mul(_J("a", CODE, primes), _J("b", CODE, primes), primes)
            != _register_mul(_J("b", CODE, primes), _J("a", CODE, primes), primes)
        )
    if not noncomm_ok:
        raise RuntimeError("Unexpected: semidirect register multiplication became commutative.")

    # ------------------------------------------------------------------
    # (C) Ellipse two-invariant checks and two-shadow witness.
    # ------------------------------------------------------------------
    A1 = sp.Matrix(
        [
            [_rat(Fraction(3, 2)), _rat(Fraction(1, 3))],
            [_rat(Fraction(2, 5)), _rat(Fraction(5, 4))],
        ]
    )
    Q90 = sp.Matrix([[0, -1], [1, 0]])
    B1 = A1 * Q90
    A2 = sp.Matrix(
        [
            [_rat(Fraction(4, 3)), _rat(Fraction(1, 2))],
            [_rat(Fraction(1, 7)), _rat(Fraction(9, 5))],
        ]
    )

    delta1_A1, delta2_A1 = _ellipse_invariants(A1)
    delta1_B1, delta2_B1 = _ellipse_invariants(B1)
    delta1_A2, delta2_A2 = _ellipse_invariants(A2)

    if (delta1_A1 != delta1_B1) or (delta2_A1 != delta2_B1):
        raise RuntimeError("A1 and B1 must share the same two invariants.")
    if (delta1_A1 == delta1_A2) and (delta2_A1 == delta2_A2):
        raise RuntimeError("A1 and A2 must not share the same two invariants.")

    s1_A1, s2_A1 = _sigmas_from_invariants(delta1_A1, delta2_A1)
    s1_B1, s2_B1 = _sigmas_from_invariants(delta1_B1, delta2_B1)
    s1_A2, s2_A2 = _sigmas_from_invariants(delta1_A2, delta2_A2)

    # Equality of ellipse shadows E_A = E_B is equivalent to A A^T = B B^T.
    ellipse_equal_A1_B1 = bool((A1 * A1.T) == (B1 * B1.T))
    if not ellipse_equal_A1_B1:
        raise RuntimeError("A1 and B1 should induce the same ellipse shadow.")

    C = A1.inv() * B1
    C_is_int = all(sp.Integer(c) == c for c in list(C))
    C_orth = bool((C.T * C) == sp.eye(2))
    if not (C_is_int and C_orth):
        raise RuntimeError("Recovered C=A^{-1}B must be an integer orthogonal matrix.")

    O2Z, SO2Z = _enumerate_orthogonal_integer_2x2()
    if len(O2Z) != 8 or len(SO2Z) != 4:
        raise RuntimeError(f"Unexpected orthogonal-integer counts: |O2Z|={len(O2Z)}, |SO2Z|={len(SO2Z)}")
    progress.tick("verified two-invariant and two-shadow matrix witnesses")

    rows = [
        MatrixAuditRow(
            name="A_1",
            det=sp.sstr(sp.Rational(A1.det())),
            delta1=sp.sstr(delta1_A1),
            delta2=sp.sstr(delta2_A1),
            sigma1_numeric=float(sp.N(s1_A1, 40)),
            sigma2_numeric=float(sp.N(s2_A1, 40)),
        ),
        MatrixAuditRow(
            name="B_1=A_1Q_{90}",
            det=sp.sstr(sp.Rational(B1.det())),
            delta1=sp.sstr(delta1_B1),
            delta2=sp.sstr(delta2_B1),
            sigma1_numeric=float(sp.N(s1_B1, 40)),
            sigma2_numeric=float(sp.N(s2_B1, 40)),
        ),
        MatrixAuditRow(
            name="A_2",
            det=sp.sstr(sp.Rational(A2.det())),
            delta1=sp.sstr(delta1_A2),
            delta2=sp.sstr(delta2_A2),
            sigma1_numeric=float(sp.N(s1_A2, 40)),
            sigma2_numeric=float(sp.N(s2_A2, 40)),
        ),
    ]

    payload: Dict[str, object] = {
        "alphabet": list(ALPHABET),
        "code": CODE,
        "max_word_len_checked": max_word_len,
        "s4_commutator_witness": {
            "alpha": list(alpha),
            "beta": list(beta),
            "commutator": list(comm),
            "identity": list(identity),
            "moved_index": int(moved_index),
            "nontrivial": bool(comm != identity),
        },
        "semidirect_register": {
            "homomorphism_check_passed": bool(hom_ok),
            "injective_decode_check_passed": bool(inj_ok),
            "noncommutative_product_witness_passed": bool(noncomm_ok),
            "word_witness": {
                "ab": list(_register_mul(_J("a", CODE, primes), _J("b", CODE, primes), primes)),
                "ba": list(_register_mul(_J("b", CODE, primes), _J("a", CODE, primes), primes)),
            },
        },
        "ellipse_invariants": {
            "A1": {
                "A": _matrix_to_tex(A1),
                "delta1": sp.sstr(delta1_A1),
                "delta2": sp.sstr(delta2_A1),
                "det": sp.sstr(sp.Rational(A1.det())),
                "area_multiplier_abs_det": sp.sstr(abs(sp.Rational(A1.det()))),
            },
            "B1": {
                "A": _matrix_to_tex(B1),
                "delta1": sp.sstr(delta1_B1),
                "delta2": sp.sstr(delta2_B1),
                "det": sp.sstr(sp.Rational(B1.det())),
            },
            "A2": {
                "A": _matrix_to_tex(A2),
                "delta1": sp.sstr(delta1_A2),
                "delta2": sp.sstr(delta2_A2),
                "det": sp.sstr(sp.Rational(A2.det())),
            },
            "A1_B1_same_invariants": True,
            "A1_A2_distinct_invariants": True,
        },
        "two_shadow_witness": {
            "A1_B1_same_ellipse_shadow": bool(ellipse_equal_A1_B1),
            "C_equals_A1inv_B1": _matrix_to_tex(C),
            "C_is_integer": bool(C_is_int),
            "C_is_orthogonal": bool(C_orth),
            "C_det": int(C.det()),
            "O2Z_size": len(O2Z),
            "SO2Z_size": len(SO2Z),
            "SO2Z_elements": [_matrix_to_tex(M) for M in SO2Z],
        },
        "matrix_rows": [asdict(r) for r in rows],
    }

    json_out = Path(str(args.json_out))
    json_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    tex_eq_out = Path(str(args.tex_eq_out))
    _write_eq_tex(
        commutator_perm=comm,
        moved_index=int(moved_index),
        max_word_len=max_word_len,
        o2_size=len(O2Z),
        so2_size=len(SO2Z),
        out_path=tex_eq_out,
    )

    tex_tab_out = Path(str(args.tex_tab_out))
    _write_table_tex(rows, tex_tab_out)

    print(f"[xi_prime_register_two_shadow] wrote {json_out}", flush=True)
    print(f"[xi_prime_register_two_shadow] wrote {tex_eq_out}", flush=True)
    print(f"[xi_prime_register_two_shadow] wrote {tex_tab_out}", flush=True)


if __name__ == "__main__":
    main()

