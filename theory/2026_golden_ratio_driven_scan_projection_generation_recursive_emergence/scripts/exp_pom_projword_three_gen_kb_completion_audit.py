#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: bounded Knuth–Bendix-style critical-pair check for the three-generator
projection-word fragment (PROJ[u], E[m], LIFT[G]).

We enumerate all length-3 overlap contexts under bounded parameter domains and test:
  - local confluence: the two overlap reductions join to the same normal form
  - residual coherence: accumulated anomaly/holonomy counters coincide

Rule fragment (paper; oriented for interface normal form):
  (RPROJ)   PROJ[u] ∘ PROJ[v]   -> PROJ[uv]
  (RLIFT)   LIFT[G] ∘ LIFT[H]   -> LIFT[G×H]
  (RE)      E[m1] ∘ E[m2]       -> E[min(m1,m2)]
  (RPL)     PROJ[u] ∘ LIFT[G]   -> LIFT[G] ∘ PROJ[u]
  (REL)     E[m] ∘ LIFT[G]      -> LIFT[G] ∘ E[m]  (+ anomaly signature placeholder)

We run the joinability test under two rewrite-priority strategies:
  - merge_first: merge rules before swaps
  - swap_first : swaps before merges

Outputs (default):
  - artifacts/export/pom_projword_three_gen_kb_completion_audit.json
  - sections/generated/tab_pom_projword_three_gen_kb_completion_audit.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import time
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Tok:
    kind: str  # "E", "LIFT", "PROJ"
    arg: str

    def render(self) -> str:
        if self.kind == "E":
            return f"E[{self.arg}]"
        return f"{self.kind}[{self.arg}]"


def word_to_str(w: Sequence[Tok]) -> str:
    return " ".join(t.render() for t in w)


def _parse_int_list(s: str) -> List[int]:
    out: List[int] = []
    for p in str(s).split(","):
        p = p.strip()
        if not p:
            continue
        out.append(int(p))
    return out


def _parse_str_list(s: str) -> List[str]:
    out: List[str] = []
    for p in str(s).split(","):
        p = p.strip()
        if not p:
            continue
        out.append(p)
    return out


def _is_finite_number_str(s: str) -> bool:
    try:
        x = float(str(s))
    except Exception:
        return False
    return math.isfinite(x)


def _proj_param_factors(u: str) -> Tuple[Fraction, Tuple[str, ...]]:
    """
    Canonicalize a PROJ parameter string into (numeric_coeff, symbols).

    - Decimal-like strings (e.g. '0.5') are parsed as exact rationals via Fraction.
    - Everything else is treated as an atomic symbol factor.

    This avoids false "nonconfluence" from parenthesization in symbolic products.
    """
    us = str(u).strip()
    if us == "":
        return Fraction(1), tuple()
    try:
        # Fraction('0.5') is exact; Fraction('u') raises.
        c = Fraction(us)
        return c, tuple()
    except Exception:
        return Fraction(1), (us,)


def _render_coeff(c: Fraction) -> str:
    if c.denominator == 1:
        return str(c.numerator)
    # Deterministic, compact float rendering from the exact rational.
    return f"{float(c):.12g}"


def _mul_u(u: str, v: str) -> str:
    cu, su = _proj_param_factors(u)
    cv, sv = _proj_param_factors(v)
    c = cu * cv
    syms = tuple(sorted(su + sv))
    if syms:
        if c == 1:
            return "*".join(syms)
        return f"{_render_coeff(c)}*{'*'.join(syms)}"
    return _render_coeff(c)


def _split_group_factors(g: str) -> List[str]:
    # Canonicalize a direct-product expression like "C3xC5" or "C3×C5".
    raw = re.split(r"[x×]", str(g))
    out: List[str] = []
    for p in raw:
        p = p.strip()
        if not p:
            continue
        if p.startswith("(") and p.endswith(")") and len(p) >= 2:
            p = p[1:-1].strip()
        out.append(p)
    return out if out else [str(g).strip()]


def _group_product(g1: str, g2: str) -> str:
    f = _split_group_factors(g1) + _split_group_factors(g2)
    f_sorted = sorted(f)
    return "x".join(f_sorted)


@dataclass(frozen=True)
class Step:
    rule: str
    pos: int
    before: str
    after: str
    certificate: Optional[Dict[str, object]] = None


@dataclass(frozen=True)
class Proof:
    strategy: str
    input_word: str
    normal_form: str
    steps: List[Step]
    anom_counter: Dict[str, int]
    holonomy_counter: Dict[str, int]


def _redex_rule(a: Tok, b: Tok) -> str | None:
    if a.kind == "E" and b.kind == "E":
        return "RE"
    if a.kind == "PROJ" and b.kind == "PROJ":
        return "RPROJ"
    if a.kind == "LIFT" and b.kind == "LIFT":
        return "RLIFT"
    if a.kind == "PROJ" and b.kind == "LIFT":
        return "RPL"
    if a.kind == "E" and b.kind == "LIFT":
        return "REL"
    return None


def _apply_at_pos(w: List[Tok], pos: int) -> Tuple[List[Tok], str, Optional[Dict[str, object]]]:
    """Apply the unique redex rule at (pos,pos+1)."""
    if pos < 0 or pos + 1 >= len(w):
        raise IndexError("pos out of range for 2-token rewrite")
    a, b = w[pos], w[pos + 1]
    rule = _redex_rule(a, b)
    if rule is None:
        raise ValueError("No redex at requested position")

    cert: Optional[Dict[str, object]] = None
    if rule == "RE":
        m1 = int(a.arg)
        m2 = int(b.arg)
        rep = [Tok("E", str(min(m1, m2)))]
    elif rule == "RPROJ":
        rep = [Tok("PROJ", _mul_u(a.arg, b.arg))]
    elif rule == "RLIFT":
        rep = [Tok("LIFT", _group_product(a.arg, b.arg))]
    elif rule == "RPL":
        rep = [b, a]
    elif rule == "REL":
        m = int(a.arg)
        group = str(b.arg)
        cert = {
            "type": "ResidualSwap",
            "swap": "E<->LIFT",
            "m": int(m),
            "group": group,
            "basis": f"E{m}<->LIFT[{group}]",
            "anom_signature": f"Anom_{group}(K;theta)",
        }
        rep = [b, a]
    else:
        raise RuntimeError(f"Unhandled rule: {rule!r}")

    nw = w[:pos] + rep + w[pos + 2 :]
    return nw, rule, cert


def _priority(strategy: str) -> Tuple[str, ...]:
    if strategy == "merge_first":
        return ("RE", "RPROJ", "RLIFT", "RPL", "REL")
    if strategy == "swap_first":
        return ("RPL", "REL", "RE", "RPROJ", "RLIFT")
    raise ValueError(f"Unknown strategy: {strategy!r}")


def _rewrite_once(
    w: List[Tok],
    *,
    strategy: str,
) -> Tuple[List[Tok], bool, str, int, Optional[Dict[str, object]]]:
    """One deterministic rewrite step under a priority strategy."""
    pr = _priority(strategy)
    for rule in pr:
        for i in range(len(w) - 1):
            if _redex_rule(w[i], w[i + 1]) != rule:
                continue
            nw, _r, cert = _apply_at_pos(w, i)
            return nw, True, rule, i, cert
    return w, False, "", -1, None


def _normalize(
    w: List[Tok],
    *,
    strategy: str,
    step_cap: int,
    record_steps: bool,
) -> Tuple[List[Tok], Dict[str, int], Dict[str, int], List[Step]]:
    cur = list(w)
    anom = Counter()
    hol = Counter()
    steps: List[Step] = []
    for _ in range(int(step_cap)):
        before = word_to_str(cur) if record_steps else ""
        cur, changed, rule, pos, cert = _rewrite_once(cur, strategy=strategy)
        if not changed:
            return cur, dict(anom), dict(hol), steps
        if cert is not None and cert.get("type") == "ResidualSwap":
            sig = str(cert.get("anom_signature", ""))
            bas = str(cert.get("basis", ""))
            if sig:
                anom[sig] += 1
            if bas:
                hol[bas] += 1
        if record_steps:
            after = word_to_str(cur)
            steps.append(Step(rule=rule, pos=int(pos), before=before, after=after, certificate=cert))
    raise RuntimeError("rewrite did not terminate within cap (unexpected)")


def reduce_branch(
    w0: List[Tok],
    *,
    first_pos: int,
    strategy: str,
    step_cap: int,
    record_steps: bool,
) -> Proof:
    w = list(w0)
    steps: List[Step] = []
    anom = Counter()
    hol = Counter()

    before0 = word_to_str(w) if record_steps else ""
    w, rule0, cert0 = _apply_at_pos(w, int(first_pos))
    if cert0 is not None and cert0.get("type") == "ResidualSwap":
        sig = str(cert0.get("anom_signature", ""))
        bas = str(cert0.get("basis", ""))
        if sig:
            anom[sig] += 1
        if bas:
            hol[bas] += 1
    if record_steps:
        steps.append(
            Step(
                rule=rule0,
                pos=int(first_pos),
                before=before0,
                after=word_to_str(w),
                certificate=cert0,
            )
        )

    nf, an2, hol2, st2 = _normalize(w, strategy=strategy, step_cap=step_cap, record_steps=record_steps)
    for k, v in an2.items():
        anom[k] += int(v)
    for k, v in hol2.items():
        hol[k] += int(v)
    steps.extend(st2)

    return Proof(
        strategy=str(strategy),
        input_word=word_to_str(w0),
        normal_form=word_to_str(nf),
        steps=steps,
        anom_counter=dict(anom),
        holonomy_counter=dict(hol),
    )


def _fast_nf_and_counters(
    w0: List[Tok],
    *,
    first_pos: int,
    strategy: str,
    step_cap: int,
) -> Tuple[str, Dict[str, int], Dict[str, int]]:
    """Fast path: reduce branch without recording steps."""
    p = reduce_branch(w0, first_pos=first_pos, strategy=strategy, step_cap=step_cap, record_steps=False)
    return p.normal_form, p.anom_counter, p.holonomy_counter


def _tex_escape_tt(s: str) -> str:
    return (
        s.replace("\\", "\\textbackslash{}")
        .replace("_", "\\_")
        .replace("{", "\\{")
        .replace("}", "\\}")
        .replace("%", "\\%")
        .replace("&", "\\&")
        .replace("#", "\\#")
        .replace("^", "\\^{}")
        .replace("~", "\\~{}")
    )


def _write_summary_table_tex(path: Path, summary: Dict[str, object]) -> None:
    # Keep the table small: strategy-level mismatch counts.
    rows = summary.get("by_strategy", {})
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Bounded critical-pair audit (Knuth--Bendix style) for the "
        "$(\\mathrm{PROJ}_u,E_m,\\mathrm{LIFT}_G)$ rewrite fragment. "
        "We enumerate all length-3 overlap contexts under bounded parameters and check "
        "joinability of the two overlap reductions, including residual (holonomy/anomaly) "
        "counter agreement.}"
    )
    lines.append("\\label{tab:pom_projword_three_gen_kb_completion_audit}")
    lines.append("\\begin{tabular}{l r r r}")
    lines.append("\\toprule")
    lines.append("strategy & overlap contexts & NF mismatches & residual mismatches\\\\")
    lines.append("\\midrule")
    for strat, d in rows.items():
        strat_s = _tex_escape_tt(str(strat))
        ov = int(d.get("overlap_contexts", 0))
        nf = int(d.get("nf_mismatches", 0))
        res = int(d.get("residual_mismatches", 0))
        lines.append(f"\\texttt{{{strat_s}}} & {ov} & {nf} & {res}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit bounded critical pairs for three-generator PROJ/E/LIFT rewrite fragment.")
    ap.add_argument("--m-max", type=int, default=12, help="Max m for E[m] tokens.")
    ap.add_argument("--group-orders", type=str, default="2,3,4,5", help="Comma list for cyclic group orders in LIFT[Cn].")
    ap.add_argument(
        "--u-values",
        type=str,
        default="0.5,0.25,0.2",
        help="Comma list for PROJ[u] parameters (numeric strongly recommended).",
    )
    ap.add_argument("--strategies", type=str, default="merge_first,swap_first", help="Comma list of strategies to audit.")
    ap.add_argument("--step-cap", type=int, default=200_000, help="Safety cap on rewrite steps (per branch).")
    ap.add_argument("--keep", type=int, default=12, help="Max mismatch cases to keep in JSON.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "pom_projword_three_gen_kb_completion_audit.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_pom_projword_three_gen_kb_completion_audit.tex"),
    )
    args = ap.parse_args()

    m_max = int(args.m_max)
    if m_max < 1:
        raise SystemExit("--m-max must be >= 1")
    group_orders = _parse_int_list(args.group_orders)
    if not group_orders:
        raise SystemExit("Empty --group-orders")
    if any(n <= 0 for n in group_orders):
        raise SystemExit("All group orders must be positive")
    u_values = _parse_str_list(args.u_values)
    if not u_values:
        raise SystemExit("Empty --u-values")
    # Encourage numeric u to avoid semantic ambiguity; we still support symbolic atoms.
    if any((not _is_finite_number_str(u)) for u in u_values):
        print("[kb-audit] warning: non-numeric u-values detected; canonicalization treats them as atomic symbols.", flush=True)

    strategies = _parse_str_list(args.strategies)
    if not strategies:
        raise SystemExit("Empty --strategies")
    for s in strategies:
        _priority(s)  # validates

    atoms: List[Tok] = []
    atoms.extend([Tok("E", str(m)) for m in range(1, m_max + 1)])
    atoms.extend([Tok("LIFT", f"C{n}") for n in group_orders])
    atoms.extend([Tok("PROJ", str(u)) for u in u_values])

    t0 = time.time()
    triples = 0
    overlap_contexts = 0
    by_strategy: Dict[str, Dict[str, int]] = {
        s: {"overlap_contexts": 0, "nf_mismatches": 0, "residual_mismatches": 0} for s in strategies
    }

    mismatches: List[dict] = []
    residual_completion: Dict[str, dict] = {}

    last_print = time.time()
    for a in atoms:
        for b in atoms:
            for c in atoms:
                triples += 1
                w = [a, b, c]
                r0 = _redex_rule(w[0], w[1])
                r1 = _redex_rule(w[1], w[2])
                if r0 is None or r1 is None:
                    continue
                overlap_contexts += 1
                w_str = word_to_str(w)
                for strat in strategies:
                    by_strategy[strat]["overlap_contexts"] += 1

                    nfL, anL, holL = _fast_nf_and_counters(w, first_pos=0, strategy=strat, step_cap=int(args.step_cap))
                    nfR, anR, holR = _fast_nf_and_counters(w, first_pos=1, strategy=strat, step_cap=int(args.step_cap))

                    nf_ok = (nfL == nfR)
                    res_ok = (anL == anR) and (holL == holR)

                    if not nf_ok:
                        by_strategy[strat]["nf_mismatches"] += 1
                    if nf_ok and (not res_ok):
                        by_strategy[strat]["residual_mismatches"] += 1
                        # Record the signed delta as a completion candidate (2-cell/boundary correction).
                        d_hol = Counter(holL)
                        d_hol.subtract(holR)
                        d_hol_nz = {k: int(v) for k, v in d_hol.items() if int(v) != 0}
                        d_an = Counter(anL)
                        d_an.subtract(anR)
                        d_an_nz = {k: int(v) for k, v in d_an.items() if int(v) != 0}
                        cls = f"{r0}+{r1}"
                        ent = residual_completion.get(cls)
                        if ent is None:
                            ent = {"count": 0, "examples": []}
                            residual_completion[cls] = ent
                        ent["count"] = int(ent.get("count", 0)) + 1
                        ex = ent.get("examples", [])
                        if isinstance(ex, list) and len(ex) < 6:
                            ex.append(
                                {
                                    "strategy": strat,
                                    "word": w_str,
                                    "normal_form": nfL,
                                    "delta_holonomy": d_hol_nz,
                                    "delta_anom": d_an_nz,
                                    "delta_total_swaps": int(sum(d_hol_nz.values())),
                                }
                            )
                            ent["examples"] = ex

                    if (not nf_ok) or (not res_ok):
                        if len(mismatches) < int(args.keep):
                            proofL = reduce_branch(
                                w,
                                first_pos=0,
                                strategy=strat,
                                step_cap=int(args.step_cap),
                                record_steps=True,
                            )
                            proofR = reduce_branch(
                                w,
                                first_pos=1,
                                strategy=strat,
                                step_cap=int(args.step_cap),
                                record_steps=True,
                            )
                            mismatches.append(
                                {
                                    "strategy": strat,
                                    "word": w_str,
                                    "left_redex_rule": r0,
                                    "right_redex_rule": r1,
                                    "left_first": {
                                        "normal_form": proofL.normal_form,
                                        "anom_counter": proofL.anom_counter,
                                        "holonomy_counter": proofL.holonomy_counter,
                                        "steps": [
                                            {
                                                "rule": s.rule,
                                                "pos": s.pos,
                                                "before": s.before,
                                                "after": s.after,
                                                "certificate": s.certificate,
                                            }
                                            for s in proofL.steps
                                        ],
                                    },
                                    "right_first": {
                                        "normal_form": proofR.normal_form,
                                        "anom_counter": proofR.anom_counter,
                                        "holonomy_counter": proofR.holonomy_counter,
                                        "steps": [
                                            {
                                                "rule": s.rule,
                                                "pos": s.pos,
                                                "before": s.before,
                                                "after": s.after,
                                                "certificate": s.certificate,
                                            }
                                            for s in proofR.steps
                                        ],
                                    },
                                }
                            )

                now = time.time()
                if now - last_print >= 2.0:
                    last_print = now
                    print(
                        f"[kb-audit] triples={triples} overlaps={overlap_contexts} "
                        f"elapsed_s={now - t0:.1f}",
                        flush=True,
                    )

    summary = {
        "triples_enumerated": int(triples),
        "overlap_contexts": int(overlap_contexts),
        "by_strategy": by_strategy,
        "word_confluent": all((d["nf_mismatches"] == 0) for d in by_strategy.values()),
        "strict_residual_confluent": all((d["residual_mismatches"] == 0) for d in by_strategy.values()),
        "elapsed_s": float(time.time() - t0),
    }
    payload = {
        "params": {
            "m_max": int(m_max),
            "group_orders": [int(x) for x in group_orders],
            "u_values": list(u_values),
            "strategies": list(strategies),
            "step_cap": int(args.step_cap),
            "keep": int(args.keep),
        },
        "summary": summary,
        "completion_candidates": residual_completion,
        "mismatches": mismatches,
    }

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        f"[kb-audit] wrote {jout} word_confluent={summary['word_confluent']} "
        f"strict_residual_confluent={summary['strict_residual_confluent']} "
        f"overlaps={summary['overlap_contexts']} elapsed_s={summary['elapsed_s']:.3f}",
        flush=True,
    )

    tout = Path(str(args.tex_out))
    _write_summary_table_tex(tout, summary)
    print(f"[kb-audit] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

