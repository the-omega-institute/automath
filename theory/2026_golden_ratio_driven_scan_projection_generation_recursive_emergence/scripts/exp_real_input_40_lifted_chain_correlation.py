#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Lifted chain congruence-fiber autocorrelation envelope certificate for ((3,3,5)) modulus.

We compute the eta_m envelope bound for the correlation decay of fiber observables
on the lifted chain with modulus spec ((3,3,5)) and third axis N2 mod 5.

Definitions:
  - Base chain: 40-state real-input sync kernel with untwisted transfer matrix M.
  - Lift: product of base chain with G = Z/3 x Z/3 x Z/5 (|G|=45).
  - Character blocks: M_{chi}(i,j) = M(i,j) * chi(cocycle(i->j)) for chi in G^hat.
  - Spectral radii: rho(M_{chi}) for each chi.
  - eta_m := max_{chi != 1} rho(M_{chi}) / rho(M_{1}), where chi=1 is the trivial character.
  - Envelope certificate: for a fiber observable f, the correlation C_f(n) satisfies
    |C_f(n)| <= const * eta_m^n for all n >= 0.

Outputs:
  - artifacts/export/real_input_40_lifted_chain_correlation.json
  - sections/generated/tab_real_input_40_lifted_chain_eta_envelope.tex

All stdout is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Tuple

import numpy as np

from common_paths import export_dir, generated_dir
from common_phi_fold import Progress


@dataclass(frozen=True)
class KernelEdge:
    src: str
    dst: str
    d: int
    e: int


KERNEL_STATES = [
    "000",
    "001",
    "002",
    "010",
    "100",
    "101",
    "0-12",
    "1-12",
    "01-1",
    "11-1",
]


def build_kernel_edges() -> List[KernelEdge]:
    edges: List[KernelEdge] = []
    for d in (0, 1, 2):
        edges.append(KernelEdge("000", f"00{d}", d, 0))
    for d in (0, 1, 2):
        edges.append(KernelEdge("100", f"00{d}", d, 1))
    edges += [
        KernelEdge("001", "010", 0, 0),
        KernelEdge("001", "100", 1, 0),
        KernelEdge("001", "101", 2, 0),
        KernelEdge("002", "11-1", 0, 0),
        KernelEdge("002", "000", 1, 1),
        KernelEdge("002", "001", 2, 1),
        KernelEdge("010", "100", 0, 0),
        KernelEdge("010", "101", 1, 0),
        KernelEdge("010", "0-12", 2, 1),
        KernelEdge("101", "010", 0, 1),
        KernelEdge("101", "100", 1, 1),
        KernelEdge("101", "101", 2, 1),
        KernelEdge("0-12", "01-1", 0, 0),
        KernelEdge("0-12", "010", 1, 0),
        KernelEdge("0-12", "100", 2, 0),
        KernelEdge("1-12", "01-1", 0, 1),
        KernelEdge("1-12", "010", 1, 1),
        KernelEdge("1-12", "100", 2, 1),
        KernelEdge("01-1", "001", 0, 0),
        KernelEdge("01-1", "002", 1, 0),
        KernelEdge("01-1", "1-12", 2, 0),
        KernelEdge("11-1", "001", 0, 1),
        KernelEdge("11-1", "002", 1, 1),
        KernelEdge("11-1", "1-12", 2, 1),
    ]
    return edges


def build_kernel_map(edges: List[KernelEdge]) -> Dict[Tuple[str, int], Tuple[str, int]]:
    return {(edge.src, edge.d): (edge.dst, edge.e) for edge in edges}


def build_real_input_states() -> List[Tuple[str, int, int]]:
    states: List[Tuple[str, int, int]] = []
    for s in KERNEL_STATES:
        for px in (0, 1):
            for py in (0, 1):
                states.append((s, px, py))
    return states


def build_character_block(
    j1: int,
    j2: int,
    j3: int,
    m1: int,
    m2: int,
    m3: int,
    states: List[Tuple[str, int, int]],
    kernel_map: Dict[Tuple[str, int], Tuple[str, int]],
) -> np.ndarray:
    """Build the character-twisted transfer matrix M_{chi} for chi = (j1, j2, j3).

    Cocycle components:
      - c1 = chi (arity charge) = e - 1_{d=2}  in {-1, 0, 1}
      - c2 = N_- = 1 if dst_state has '-' else 0
      - c3 = N_2 = 1_{d=2}  (third axis = N2 mod m3)

    Character value: chi(c1, c2, c3) = omega_m1^{j1*c1} * omega_m2^{j2*c2} * omega_m3^{j3*c3}.
    """
    idx = {state: i for i, state in enumerate(states)}
    n = len(states)
    omega1 = cmath.exp(2j * cmath.pi / float(m1)) if m1 > 0 else 1.0
    omega2 = cmath.exp(2j * cmath.pi / float(m2)) if m2 > 0 else 1.0
    omega3 = cmath.exp(2j * cmath.pi / float(m3)) if m3 > 0 else 1.0

    M = np.zeros((n, n), dtype=complex)
    for s, px, py in states:
        for x in (0, 1):
            if px == 1 and x == 1:
                continue
            for y in (0, 1):
                if py == 1 and y == 1:
                    continue
                d = x + y
                dst_state, e = kernel_map[(s, d)]

                # Cocycle components
                two = 1 if d == 2 else 0
                c1 = e - two  # chi (arity charge)
                c2 = 1 if "-" in dst_state else 0  # N_-
                c3 = two  # N_2 (third axis)

                # Character twist
                chi_val = (
                    (omega1 ** (j1 * c1))
                    * (omega2 ** (j2 * c2))
                    * (omega3 ** (j3 * c3))
                )

                i_src = idx[(s, px, py)]
                i_dst = idx[(dst_state, x, y)]
                M[i_src, i_dst] += chi_val

    return M


def spectral_radius(M: np.ndarray) -> float:
    vals = np.linalg.eigvals(M)
    return float(np.max(np.abs(vals)))


def pick_pf_eigpair(B: np.ndarray) -> Tuple[float, np.ndarray, np.ndarray]:
    """Pick Perron-Frobenius eigenvector pair (right and left) for real non-negative matrix."""
    eigvals, eigvecs = np.linalg.eig(B)
    k = int(np.argmax(np.abs(eigvals)))
    lam = float(np.real(eigvals[k]))
    v = np.real(eigvecs[:, k])

    eigvals_t, eigvecs_t = np.linalg.eig(B.T)
    kt = int(np.argmax(np.abs(eigvals_t)))
    u = np.real(eigvecs_t[:, kt])

    if float(np.sum(v)) < 0:
        v = -v
    if float(np.sum(u)) < 0:
        u = -u

    return lam, v, u


def parry_markov(
    B: np.ndarray, lam: float, v: np.ndarray, u: np.ndarray
) -> Tuple[np.ndarray, np.ndarray]:
    """Construct Parry measure and Markov transition matrix."""
    n = B.shape[0]
    v = np.maximum(v, 1e-300)
    u = np.maximum(u, 1e-300)
    pi_unnorm = u * v
    pi = pi_unnorm / float(np.sum(pi_unnorm))

    P = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(n):
            if B[i, j] == 0.0:
                continue
            P[i, j] = (B[i, j] * v[j]) / (lam * v[i])
    rs = np.sum(P, axis=1)
    P = (P.T / np.maximum(rs, 1e-300)).T
    return pi, P


def compute_fiber_correlation(
    M_chi: np.ndarray,
    M_trivial: np.ndarray,
    pi: np.ndarray,
    v_trivial: np.ndarray,
    lam: float,
    n_max: int,
) -> List[float]:
    """Compute fiber correlation C_f(n) for a character observable.

    For a nontrivial character chi, the normalized twisted operator is:
      L_chi(i,j) = M_chi(i,j) * v_trivial(j) / (lam * v_trivial(i))

    The correlation is computed as:
      C_f(n) = <pi, L_chi^n 1> / (normalization)

    We use the spectral representation: the correlation decays at rate rho(M_chi)/lam.
    """
    n = M_chi.shape[0]
    v = np.maximum(v_trivial, 1e-300)

    # Build normalized twisted operator
    L_chi = np.zeros((n, n), dtype=complex)
    for i in range(n):
        for j in range(n):
            if M_chi[i, j] != 0.0:
                L_chi[i, j] = M_chi[i, j] * v[j] / (lam * v[i])

    # Compute correlations via matrix powers
    corr: List[float] = []
    cur = np.ones(n, dtype=complex)
    for k in range(n_max + 1):
        c = float(np.abs(np.dot(pi, cur)))
        corr.append(c)
        cur = L_chi @ cur

    return corr


def write_json(path: Path, payload: Dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def write_tex_table(
    path: Path,
    modulus_spec: Tuple[int, int, int],
    eta_m: float,
    rho_trivial: float,
    worst_char: Tuple[int, int, int],
    rho_worst: float,
    corr_samples: List[Dict[str, Any]],
    envelope_certificate: Dict[str, Any],
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    m1, m2, m3 = modulus_spec

    def fmt(x: float) -> str:
        if not math.isfinite(x):
            return "\\infty"
        return f"{x:.12f}"

    lines: List[str] = []
    lines.append(
        "% AUTO-GENERATED by scripts/exp_real_input_40_lifted_chain_correlation.py"
    )
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\small")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append("\\renewcommand{\\arraystretch}{1.15}")
    lines.append(
        f"\\caption{{提升链同余纤维自相关的 $\\eta_m$ 包络证书："
        f"模数规约 $(({m1},{m2},{m3}))$ 下（第三轴为 $N_2\\bmod {m3}$），"
        f"最坏扭曲角色的谱半径比 $\\eta_m:=\\max_{{\\chi\\neq 1}}\\rho(M_{{m,\\chi}})/\\rho(M_{{m,1}})$ "
        f"控制纤维可观测的时间相关函数的指数衰减包络。}}"
    )
    lines.append("\\label{tab:real-input-40-lifted-chain-eta-envelope}")
    lines.append("\\begin{tabular}{l r}")
    lines.append("\\toprule")
    lines.append("Quantity & Value \\\\")
    lines.append("\\midrule")
    lines.append(f"Modulus spec & $(({m1},{m2},{m3}))$ \\\\")
    lines.append(f"$\\rho(M_{{m,1}})$ (trivial character) & ${fmt(rho_trivial)}$ \\\\")
    lines.append(
        f"$\\rho(M_{{m,\\chi^\\star}})$ (worst nontrivial) & ${fmt(rho_worst)}$ \\\\"
    )
    lines.append(
        f"Worst character $j^\\star$ & $({worst_char[0]},{worst_char[1]},{worst_char[2]})$ \\\\"
    )
    lines.append(
        f"$\\eta_m := \\rho(M_{{m,\\chi^\\star}})/\\rho(M_{{m,1}})$ & ${fmt(eta_m)}$ \\\\"
    )
    lines.append("\\midrule")
    lines.append(
        f"Envelope max ratio $\\max_n |C_f(n)|/\\eta_m^n$ & ${fmt(envelope_certificate['max_ratio'])}$ \\\\"
    )
    lines.append(f"Argmax position & $n = {envelope_certificate['argmax_n']}$ \\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    # Add correlation samples table
    lines.append("")
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{4pt}")
    lines.append(
        f"\\caption{{前若干时刻的纤维相关函数 $|C_f(n)|$ 与包络界 $\\eta_m^n$（$\\eta_m\\approx {eta_m:.8f}$）。}}"
    )
    lines.append("\\label{tab:real-input-40-lifted-chain-corr-samples}")
    lines.append("\\begin{tabular}{r r r r}")
    lines.append("\\toprule")
    lines.append("$n$ & $|C_f(n)|$ & $\\eta_m^n$ & $|C_f(n)|/\\eta_m^n$ \\\\")
    lines.append("\\midrule")
    for sample in corr_samples[:20]:  # Show first 20 samples
        n = sample["n"]
        corr = sample["corr"]
        bound = sample["bound"]
        ratio = sample["ratio"]
        lines.append(f"{n} & {corr:.12e} & {bound:.12e} & {ratio:.8f} \\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")

    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Lifted chain congruence-fiber autocorrelation envelope certificate"
    )
    parser.add_argument(
        "--mod-spec",
        type=str,
        default="3x3x5",
        help="Modulus spec as m1xm2xm3 (default: 3x3x5)",
    )
    parser.add_argument(
        "--N",
        type=int,
        default=100,
        help="Maximum lag for correlation computation (default: 100)",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default="",
        help="Output JSON path (default: artifacts/export/real_input_40_lifted_chain_correlation.json)",
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default="",
        help="Output TeX path (default: sections/generated/tab_real_input_40_lifted_chain_eta_envelope.tex)",
    )
    parser.add_argument("--no-output", action="store_true", help="Skip writing outputs")
    args = parser.parse_args()

    prog = Progress(label="lifted-chain-correlation", every_seconds=20.0)

    # Parse modulus spec
    parts = args.mod_spec.split("x")
    if len(parts) != 3:
        raise SystemExit(f"Invalid mod-spec: {args.mod_spec} (expected m1xm2xm3)")
    m1, m2, m3 = int(parts[0]), int(parts[1]), int(parts[2])
    if m1 < 2 or m2 < 2 or m3 < 2:
        raise SystemExit(f"Modulus components must be >= 2, got ({m1},{m2},{m3})")

    print(f"[lifted-chain-correlation] modulus spec = (({m1},{m2},{m3}))", flush=True)
    print(f"[lifted-chain-correlation] third axis = N2 mod {m3}", flush=True)
    print(f"[lifted-chain-correlation] N = {args.N}", flush=True)

    # Build base chain infrastructure
    edges = build_kernel_edges()
    kernel_map = build_kernel_map(edges)
    states = build_real_input_states()
    n_states = len(states)

    print(f"[lifted-chain-correlation] base chain has {n_states} states", flush=True)
    prog.tick("built kernel infrastructure")

    # Build trivial character block (untwisted transfer matrix)
    M_trivial = build_character_block(0, 0, 0, m1, m2, m3, states, kernel_map)
    M_trivial_real = np.real(M_trivial).astype(float)
    rho_trivial = spectral_radius(M_trivial)

    # Get PF eigenpair for Parry measure
    lam, v_pf, u_pf = pick_pf_eigpair(M_trivial_real)
    pi, P = parry_markov(M_trivial_real, lam, v_pf, u_pf)

    print(f"[lifted-chain-correlation] rho(M_trivial) = {rho_trivial:.12f}", flush=True)
    print(f"[lifted-chain-correlation] lambda (PF) = {lam:.12f}", flush=True)
    prog.tick("computed trivial character block")

    # Compute spectral radii for all nontrivial characters
    char_radii: Dict[Tuple[int, int, int], float] = {}
    total_chars = m1 * m2 * m3
    count = 0

    for j1 in range(m1):
        for j2 in range(m2):
            for j3 in range(m3):
                if j1 == 0 and j2 == 0 and j3 == 0:
                    continue  # Skip trivial character
                M_chi = build_character_block(
                    j1, j2, j3, m1, m2, m3, states, kernel_map
                )
                rho = spectral_radius(M_chi)
                char_radii[(j1, j2, j3)] = rho
                count += 1
                if count % 10 == 0:
                    prog.tick(
                        f"computed character ({j1},{j2},{j3}), {count}/{total_chars - 1} done"
                    )

    # Find worst (maximum) spectral radius among nontrivial characters
    worst_char = max(char_radii, key=lambda k: char_radii[k])
    rho_worst = char_radii[worst_char]
    eta_m = rho_worst / rho_trivial

    print(
        f"[lifted-chain-correlation] worst nontrivial character = {worst_char}",
        flush=True,
    )
    print(f"[lifted-chain-correlation] rho_worst = {rho_worst:.12f}", flush=True)
    print(f"[lifted-chain-correlation] eta_m = {eta_m:.12f}", flush=True)
    prog.tick("found worst twist ratio")

    # Compute fiber correlations for the worst character
    M_worst = build_character_block(
        worst_char[0], worst_char[1], worst_char[2], m1, m2, m3, states, kernel_map
    )
    corr = compute_fiber_correlation(M_worst, M_trivial_real, pi, v_pf, lam, args.N)

    # Build correlation samples with envelope bound
    corr_samples: List[Dict[str, Any]] = []
    max_ratio = 0.0
    argmax_n = 0

    for n in range(len(corr)):
        c = corr[n]
        bound = eta_m**n
        ratio = (c / bound) if bound > 0 else 0.0
        corr_samples.append(
            {
                "n": n,
                "corr": c,
                "bound": bound,
                "ratio": ratio,
            }
        )
        if ratio > max_ratio:
            max_ratio = ratio
            argmax_n = n

    envelope_certificate = {
        "max_ratio": max_ratio,
        "argmax_n": argmax_n,
        "N": args.N,
    }

    print(
        f"[lifted-chain-correlation] envelope max_ratio = {max_ratio:.12f} at n = {argmax_n}",
        flush=True,
    )
    prog.tick("computed envelope certificate")

    # Build all character radii for JSON output
    all_char_radii: List[Dict[str, Any]] = []
    for (j1, j2, j3), rho in sorted(char_radii.items()):
        all_char_radii.append(
            {
                "j": [j1, j2, j3],
                "rho": rho,
                "ratio": rho / rho_trivial,
            }
        )

    # Build payload
    payload: Dict[str, Any] = {
        "modulus_spec": [m1, m2, m3],
        "third_axis": "N2",
        "n_base_states": n_states,
        "rho_trivial": rho_trivial,
        "rho_worst": rho_worst,
        "worst_char": list(worst_char),
        "eta_m": eta_m,
        "corr_samples": corr_samples,
        "envelope_certificate": envelope_certificate,
        "all_char_radii": all_char_radii,
    }

    # Write outputs
    if not args.no_output:
        json_path = (
            Path(args.json_out)
            if args.json_out
            else export_dir() / "real_input_40_lifted_chain_correlation.json"
        )
        tex_path = (
            Path(args.tex_out)
            if args.tex_out
            else generated_dir() / "tab_real_input_40_lifted_chain_eta_envelope.tex"
        )

        write_json(json_path, payload)
        print(f"[lifted-chain-correlation] wrote {json_path}", flush=True)

        write_tex_table(
            tex_path,
            (m1, m2, m3),
            eta_m,
            rho_trivial,
            worst_char,
            rho_worst,
            corr_samples,
            envelope_certificate,
        )
        print(f"[lifted-chain-correlation] wrote {tex_path}", flush=True)

    print("[lifted-chain-correlation] done", flush=True)


if __name__ == "__main__":
    main()
