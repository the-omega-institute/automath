#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Unified CLI for:
  1) Projection-word normalization (rewrite-to-normal-form + certificate trace)
  2) Fold_m collision-moment / Renyi-q fingerprint summaries

This file is intentionally small and composes existing, audited scripts in this
paper directory (instead of re-implementing math in a new codepath).

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple


def _write_json(path: str, payload: Dict[str, Any]) -> None:
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _normalize_fragment(fragment: str, raw: Sequence[str], word: Optional[str]) -> Dict[str, Any]:
    """Return a standard normalized payload dict."""
    if fragment == "ze":
        import exp_pom_projword_ze_normalizer as ze

        raw2 = list(raw)
        if (not raw2) and (word is not None):
            raw2 = word.split()
        if not raw2:
            raise SystemExit("Empty word. Provide tokens or --word.")
        toks = ze.parse_tokens(raw2)
        nf = ze.normalize(toks)
        return {
            "fragment": fragment,
            "input": " ".join(str(t) for t in toks),
            "normal_form": " ".join(str(t) for t in nf),
            "rewrite_trace": [],
        }

    if fragment == "zepq":
        import exp_pom_projword_zepq_normalizer as zepq

        raw2 = list(raw)
        if (not raw2) and (word is not None):
            raw2 = word.split()
        if not raw2:
            raise SystemExit("Empty word. Provide tokens or --word.")
        toks = zepq.parse_tokens(raw2)
        nf = zepq.normalize(toks)
        return {
            "fragment": fragment,
            "input": " ".join(str(t) for t in toks),
            "normal_form": " ".join(str(t) for t in nf),
            "rewrite_trace": [],
        }

    if fragment == "liftproj":
        import exp_pom_projword_lift_proj_normalizer_demo as lp

        if word is None:
            word = " ".join(raw)
        if not word.strip():
            raise SystemExit("Empty word. Provide tokens or --word.")
        toks = lp.parse_word(word)
        nf, trace = lp.normalize(toks)
        return {
            "fragment": fragment,
            "input": lp.word_to_str(toks),
            "normal_form": lp.word_to_str(nf),
            "rewrite_trace": trace,
        }

    if fragment == "full":
        import exp_pom_projword_full_normalizer_demo as full

        if word is None:
            word = " ".join(raw)
        if not word.strip():
            raise SystemExit("Empty word. Provide tokens or --word.")
        toks = full.parse_word(word)
        nf, trace = full.normalize(toks)
        return {
            "fragment": fragment,
            "input": full.word_to_str(toks),
            "normal_form": full.word_to_str(nf),
            "rewrite_trace": trace,
        }

    if fragment == "momtwist":
        import exp_pom_projword_mom_twist_normalizer_demo as mt

        if word is None:
            word = " ".join(raw)
        if not word.strip():
            raise SystemExit("Empty word. Provide tokens or --word.")
        toks = mt.parse_word(word)
        nf, trace, certs = mt.normalize(toks)
        return {
            "fragment": fragment,
            "input": mt.word_to_str(toks),
            "normal_form": mt.word_to_str(nf),
            "rewrite_trace": trace,
            "certificates": certs,
        }

    if fragment == "threegen":
        import exp_pom_projword_three_gen_anom_normalizer as tg

        if word is None:
            word = " ".join(raw)
        if not word.strip():
            raise SystemExit("Empty word. Provide tokens or --word.")
        toks = tg.parse_word(word)
        nf, trace, anom, certs = tg.normalize_with_anom(toks)
        params = tg.extract_interface_params(nf)
        hol = tg.holonomy_counter_from_certs(certs)
        return {
            "fragment": fragment,
            "input": tg.word_to_str(toks),
            "normal_form": tg.word_to_str(nf),
            "interface_params": params,
            "rewrite_trace": trace,
            "anom_counter": anom,
            "holonomy_counter": hol,
            "certificates": certs,
        }

    if fragment == "val":
        import exp_pom_rewriting_engine_demo as val

        if word is None:
            word = "; ".join(raw)
        if not word.strip():
            raise SystemExit("Empty word. Provide tokens or --word.")
        toks = val.parse_word(word)
        nf, trace = val.normalize(toks)
        return {
            "fragment": fragment,
            "input": val.word_to_str(toks),
            "normal_form": val.word_to_str(nf),
            "rewrite_trace": trace,
        }

    raise SystemExit(f"Unknown fragment {fragment!r}. Use one of: ze, zepq, liftproj, full, momtwist, threegen, val.")


def cmd_normalize(args: argparse.Namespace) -> None:
    payload = _normalize_fragment(args.fragment, args.tokens, args.word)
    print(f"[pom-cli] fragment={payload['fragment']}", flush=True)
    print(f"[pom-cli] in:  {payload['input']}", flush=True)
    print(f"[pom-cli] nf:  {payload['normal_form']}", flush=True)
    if "interface_params" in payload and isinstance(payload["interface_params"], dict):
        p = payload["interface_params"]
        print(
            f"[pom-cli] params: u={p.get('u')} m={p.get('m')} group={p.get('group')}",
            flush=True,
        )
    if payload["rewrite_trace"]:
        print(f"[pom-cli] trace: {' '.join(payload['rewrite_trace'])}", flush=True)
    if "anom_counter" in payload and payload["anom_counter"]:
        print(f"[pom-cli] anom: {json.dumps(payload['anom_counter'], sort_keys=True)}", flush=True)
    if "holonomy_counter" in payload and payload["holonomy_counter"]:
        print(f"[pom-cli] hol: {json.dumps(payload['holonomy_counter'], sort_keys=True)}", flush=True)
    if args.json_out:
        _write_json(args.json_out, payload)
        print(f"[pom-cli] wrote {args.json_out}", flush=True)


def cmd_equiv(args: argparse.Namespace) -> None:
    if args.word1 is None or args.word2 is None:
        raise SystemExit("equiv requires --word1 and --word2.")

    if args.fragment in ("ze", "zepq"):
        p1 = _normalize_fragment(args.fragment, args.word1.split(), None)
        p2 = _normalize_fragment(args.fragment, args.word2.split(), None)
    else:
        p1 = _normalize_fragment(args.fragment, [], args.word1)
        p2 = _normalize_fragment(args.fragment, [], args.word2)
    eq = (p1["normal_form"] == p2["normal_form"])
    if ("anom_counter" in p1) or ("anom_counter" in p2):
        eq = eq and (p1.get("anom_counter") == p2.get("anom_counter"))
    print(f"[pom-cli] fragment={args.fragment}", flush=True)
    print(f"[pom-cli] nf1: {p1['normal_form']}", flush=True)
    print(f"[pom-cli] nf2: {p2['normal_form']}", flush=True)
    if ("anom_counter" in p1) or ("anom_counter" in p2):
        print(f"[pom-cli] anom1: {json.dumps(p1.get('anom_counter', {}), sort_keys=True)}", flush=True)
        print(f"[pom-cli] anom2: {json.dumps(p2.get('anom_counter', {}), sort_keys=True)}", flush=True)
    print(f"[pom-cli] equivalent: {eq}", flush=True)
    raise SystemExit(0 if eq else 1)


@dataclass(frozen=True)
class RecRow:
    k: int
    order: int
    m0: int
    coeffs: List[int]


def _fold_rec_rows(k_max: int) -> List[RecRow]:
    import exp_fold_collision_moment_spectrum_k2_8 as k2_8
    import exp_fold_collision_moment_recursions_mod_dp as moddp

    rows: List[RecRow] = []
    for rec in k2_8.RECS:
        if rec.k <= k_max:
            rows.append(RecRow(k=rec.k, order=len(rec.coeffs), m0=int(rec.m0), coeffs=list(rec.coeffs)))
    for r in moddp.PRECOMPUTED_RECS_9_17:
        if int(r["k"]) <= k_max:
            rows.append(
                RecRow(
                    k=int(r["k"]),
                    order=int(r["order"]),
                    m0=int(r["m0"]),
                    coeffs=[int(c) for c in r["coeffs"]],
                )
            )
    rows.sort(key=lambda z: z.k)
    return rows


def cmd_fold_recs(args: argparse.Namespace) -> None:
    rows = _fold_rec_rows(k_max=int(args.k_max))
    payload = {"k_max": int(args.k_max), "rows": [r.__dict__ for r in rows]}
    for r in rows:
        coeffs = ", ".join(str(c) for c in r.coeffs)
        print(f"[pom-cli] k={r.k:>2} order={r.order:>2} m0={r.m0:>2} coeffs=({coeffs})", flush=True)
    if args.json_out:
        _write_json(args.json_out, payload)
        print(f"[pom-cli] wrote {args.json_out}", flush=True)


def _sqrt_phi() -> float:
    phi = (1.0 + 5.0 ** 0.5) / 2.0
    return phi**0.5


def cmd_fold_spectrum(args: argparse.Namespace) -> None:
    # We intentionally reuse the "paper-canonical" Perron roots stored in the audited script.
    import exp_fold_collision_renyi_spectrum as rs

    q_max = int(args.q_max)
    if q_max < 2:
        raise SystemExit("Require q_max >= 2")

    r2 = rs.perron_root_r2()
    r3 = rs.perron_root_r3()
    r4 = rs.perron_root_r4()

    sqphi = _sqrt_phi()
    rows: List[Dict[str, Any]] = []
    for q in range(2, q_max + 1):
        if q == 2:
            rq = float(r2)
            note = "exact (A2)"
        elif q == 3:
            rq = float(r3)
            note = "exact (A3)"
        elif q == 4:
            rq = float(r4)
            note = "exact (A4)"
        elif q in rs.PRECOMPUTED_RQ:
            rq = float(rs.PRECOMPUTED_RQ[q])
            note = "exact (recurrence)"
        else:
            raise SystemExit(f"Missing r_q for q={q}. Use q<=17, or run the DP estimator scripts.")

        hq = q * math.log(2.0) - math.log(rq)
        rows.append(
            {
                "q": q,
                "r_q": rq,
                "h_q": hq,
                "r_q_pow_1_over_q": rq ** (1.0 / q),
                "sqrt_phi": sqphi,
                "gap_to_sqrt_phi": (rq ** (1.0 / q)) - sqphi,
                "note": note,
            }
        )

    # Print a compact, audit-friendly table.
    print("[pom-cli] Fold_m Renyi-q fingerprint (paper-canonical r_q)", flush=True)
    print("[pom-cli] columns: q  r_q  h_q=log(2^q/r_q)  r_q^(1/q)  gap_to_sqrt(phi)", flush=True)
    for r in rows:
        print(
            f"[pom-cli] q={r['q']:>2}  r_q={r['r_q']:.12f}  h_q={r['h_q']:.12f}  "
            f"r_q^(1/q)={r['r_q_pow_1_over_q']:.12f}  gap={r['gap_to_sqrt_phi']:.12f}  {r['note']}",
            flush=True,
        )

    if args.json_out:
        _write_json(args.json_out, {"q_max": q_max, "rows": rows})
        print(f"[pom-cli] wrote {args.json_out}", flush=True)


def _fold_rq_by_q(q_max: int) -> Dict[int, float]:
    """Return the paper-canonical r_q table for q=2..q_max (q_max<=17)."""
    import exp_fold_collision_renyi_spectrum as rs

    if q_max < 2:
        raise ValueError("q_max must be >= 2")
    if q_max > 17:
        raise ValueError("Missing r_q beyond q=17 in this CLI. Use the pressure/multifractal scripts to export r_q up to 60.")

    r2 = float(rs.perron_root_r2())
    r3 = float(rs.perron_root_r3())
    r4 = float(rs.perron_root_r4())
    out: Dict[int, float] = {}
    for q in range(2, q_max + 1):
        if q == 2:
            out[q] = r2
        elif q == 3:
            out[q] = r3
        elif q == 4:
            out[q] = r4
        elif q in rs.PRECOMPUTED_RQ:
            out[q] = float(rs.PRECOMPUTED_RQ[q])
        else:
            raise ValueError(f"Missing r_q for q={q}")
    return out


def cmd_tail_budget(args: argparse.Namespace) -> None:
    from common_tail_budget import B_from_logB, gamma_cert_from_rq, logB_from_gamma, prime_list_for_log_target

    m = int(args.m)
    eps = float(args.eps)
    q_max = int(args.q_max)
    if m <= 0:
        raise SystemExit("Require --m >= 1")
    if not (0.0 < eps < 1.0):
        raise SystemExit("Require --eps in (0,1)")

    rq_by_q = _fold_rq_by_q(q_max=q_max)
    cert = gamma_cert_from_rq(m=m, eps=eps, rq_by_q=rq_by_q, out_alphabet_size=2)
    logB = logB_from_gamma(m=m, gamma=cert.gamma)
    B = B_from_logB(logB)

    primes = None
    logP = None
    if not args.no_primes:
        primes, logP = prime_list_for_log_target(math.log(2.0) + float(logB))

    payload: Dict[str, Any] = {
        "m": m,
        "eps": eps,
        "q_max": q_max,
        "q_star": int(cert.q_star),
        "gamma_cert": float(cert.gamma),
        "logB_cert": float(logB),
        "B_cert": B,
        "gamma_by_q": {str(k): float(v) for k, v in sorted(cert.gamma_by_q.items())},
        "primes": primes,
        "logP": float(logP) if logP is not None else None,
        "condition_P_gt_2B": (bool(logP is not None and logP > math.log(2.0) + float(logB))),
    }

    print(
        f"[pom-cli] tail-budget Fold_m: m={m} eps={eps:g} q*={cert.q_star} gamma={cert.gamma:.6g} logB={logB:.6g}",
        flush=True,
    )
    if primes is not None and logP is not None:
        print(f"[pom-cli] prime-register suggestion: n_primes={len(primes)} logP~{float(logP):.6g}", flush=True)

    if args.json_out:
        _write_json(args.json_out, payload)
        print(f"[pom-cli] wrote {args.json_out}", flush=True)


def _sync10_transducer():
    import exp_sync_kernel_10_state_uniform_input_fingerprint as sync10
    from common_moment_kernel_hist import build_transducer_from_edges

    edges = sync10.build_edges()
    states = list(sync10.STATES)
    input_symbols = sorted({int(e.d) for e in edges})
    return build_transducer_from_edges(
        states=states,
        input_symbols=input_symbols,
        edges=edges,
        src_attr="src",
        dst_attr="dst",
        in_attr="d",
        out_attr="e",
    )


def cmd_moment_kernel(args: argparse.Namespace) -> None:
    from common_moment_kernel_hist import (
        build_collision_moment_kernel_sparse,
        estimate_spectral_radius_sparse,
        histogram_state_count,
        pressure_from_rho,
    )

    kernel = str(args.kernel)
    k = int(args.k)
    if k < 1:
        raise SystemExit("Require --k >= 1")
    if kernel != "sync10":
        raise SystemExit("Only --kernel=sync10 is supported in this CLI for now.")

    T = _sync10_transducer()
    dim = histogram_state_count(k, T.n_states())
    print(f"[pom-cli] moment-kernel kernel={kernel} k={k} |Q|={T.n_states()} |H_k|={dim}", flush=True)

    max_dim = int(args.max_dim)
    if (not args.force) and dim > max_dim:
        raise SystemExit(f"|H_k|={dim} exceeds --max-dim={max_dim}. Rerun with --force to execute.")

    _states, rows = build_collision_moment_kernel_sparse(T, k=k, progress_every=int(args.progress_every))
    rho = estimate_spectral_radius_sparse(rows, iters=int(args.iters), tol=float(args.tol))
    P = pressure_from_rho(float(rho), k=k, out_alphabet_size=2)
    print(f"[pom-cli] rho(A_k)~{float(rho):.12g}  pressure~{float(P):.12g}", flush=True)

    if args.json_out:
        _write_json(
            args.json_out,
            {
                "kernel": kernel,
                "k": k,
                "n_states": int(T.n_states()),
                "dim_Hk": int(dim),
                "rho_est": float(rho),
                "pressure": float(P),
                "iters": int(args.iters),
                "tol": float(args.tol),
            },
        )
        print(f"[pom-cli] wrote {args.json_out}", flush=True)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="POM CLI: normalize projection-words; summarize Fold_m fingerprints.")
    sub = p.add_subparsers(dest="cmd", required=True)

    p_norm = sub.add_parser("normalize", help="Normalize a projection word (rewrite to normal form).")
    p_norm.add_argument(
        "--fragment",
        choices=["ze", "zepq", "liftproj", "full", "momtwist", "threegen", "val"],
        default="liftproj",
    )
    p_norm.add_argument("--word", type=str, default=None, help="Optional raw word string (fragment-dependent).")
    p_norm.add_argument("--json-out", type=str, default=None, help="Write normalization payload to JSON.")
    p_norm.add_argument("tokens", nargs="*", help="Token list (used when --word is omitted).")
    p_norm.set_defaults(func=cmd_normalize)

    p_eq = sub.add_parser("equiv", help="Decide equivalence by comparing normal forms.")
    p_eq.add_argument("--fragment", choices=["ze", "zepq", "liftproj", "full", "momtwist", "threegen", "val"], default="liftproj")
    p_eq.add_argument("--word1", type=str, required=True, help="Word 1 (fragment-dependent string form).")
    p_eq.add_argument("--word2", type=str, required=True, help="Word 2 (fragment-dependent string form).")
    p_eq.set_defaults(func=cmd_equiv)

    p_recs = sub.add_parser("fold-recs", help="Print verified integer recurrences for S_k(m).")
    p_recs.add_argument("--k-max", type=int, default=17)
    p_recs.add_argument("--json-out", type=str, default=None)
    p_recs.set_defaults(func=cmd_fold_recs)

    p_spec = sub.add_parser("fold-spectrum", help="Print Renyi-q fingerprint spectrum (canonical r_q).")
    p_spec.add_argument("--q-max", type=int, default=17)
    p_spec.add_argument("--json-out", type=str, default=None)
    p_spec.set_defaults(func=cmd_fold_spectrum)

    p_tb = sub.add_parser("tail-budget", help="Optimize gamma_cert_m(eps) over q (Fold_m tail budget).")
    p_tb.add_argument("--m", type=int, default=24, help="Resolution parameter m.")
    p_tb.add_argument("--eps", type=float, default=1e-6, help="Target tail failure probability epsilon in (0,1).")
    p_tb.add_argument("--q-max", type=int, default=17, help="Max q to scan (requires q<=17 in this CLI).")
    p_tb.add_argument("--no-primes", action="store_true", help="Skip prime-register suggestion.")
    p_tb.add_argument("--json-out", type=str, default=None)
    p_tb.set_defaults(func=cmd_tail_budget)

    p_mk = sub.add_parser(
        "moment-kernel",
        help="Build histogram collision moment-kernel A_k and estimate rho(A_k).",
    )
    p_mk.add_argument("--kernel", choices=["sync10"], default="sync10")
    p_mk.add_argument("--k", type=int, default=6, help="Moment order k (>=1).")
    p_mk.add_argument("--iters", type=int, default=2500, help="Power-iteration max iterations.")
    p_mk.add_argument("--tol", type=float, default=1e-13, help="Relative tolerance for power iteration.")
    p_mk.add_argument("--max-dim", type=int, default=50_000, help="Safety cap on |H_k| (use --force to override).")
    p_mk.add_argument("--force", action="store_true", help="Override --max-dim safety cap.")
    p_mk.add_argument("--progress-every", type=int, default=0, help="Optional progress print cadence (rows).")
    p_mk.add_argument("--json-out", type=str, default=None)
    p_mk.set_defaults(func=cmd_moment_kernel)

    return p


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()

