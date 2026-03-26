#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Audit: bounded Knuth–Bendix-style critical-pair check for the four-generator
projection-word fragment (PROJ[u], E[m], LIFT[G], MOM[q]) including the RMOML rule.

We enumerate all length-3 overlap contexts under bounded parameter domains and test:
  - local confluence: the two overlap reductions join to the same normal form
  - residual coherence: accumulated residual counters coincide

Rule fragment (paper; oriented for an interface-style normal form):
  (RPROJ)     PROJ[u] ∘ PROJ[v]    -> PROJ[uv]
  (RLIFT)     LIFT[G] ∘ LIFT[H]    -> LIFT[G×H]
  (RE)        E[m1] ∘ E[m2]        -> E[min(m1,m2)]
  (RPL)       PROJ[u] ∘ LIFT[G]    -> LIFT[G] ∘ PROJ[u]
  (REL)       E[m] ∘ LIFT[G]       -> LIFT[G] ∘ E[m]   (+ anomaly placeholder)

Moment extensions (syntactic, certificate-oriented):
  (RMOM)      MOM[q1] ∘ MOM[q2]    -> MOM[q1*q2]
  (RBUB)      X ∘ MOM[q]           -> MOM[q] ∘ X'       (bubble left; X' may update types)
              - if X=LIFT[G] then X' = LIFT[G^q]         (typed lift power)
              - if X=E[m] then emit a moment anomaly placeholder
  (RMOML)     MOM[q] ∘ LIFT[G]     -> MOML[q;G]          (+ Anom^(q)_G tower placeholder)

Completion helpers for bounded critical-pair joinability:
  (RMOML_FUSE) MOML[q;G] ∘ LIFT[H] -> MOML[q;G×H]
  (RMOML_BUB)  X ∘ MOML[q;G]       -> MOML[q;G'] ∘ X''   (bubble/absorb)

We run the joinability test under two rewrite-priority strategies:
  - merge_first: merges before swaps/bubbles/expansions
  - swap_first : swaps/bubbles/expansions before merges

Outputs (default):
  - artifacts/export/pom_projword_four_gen_kb_completion_audit.json
  - sections/generated/tab_pom_projword_four_gen_kb_completion_audit.tex

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
    kind: str  # "E", "LIFT", "PROJ", "MOM", "MOML"
    arg: str

    def render(self) -> str:
        if self.kind == "E":
            return f"E[{self.arg}]"
        if self.kind == "MOM":
            return f"MOM[{self.arg}]"
        if self.kind == "MOML":
            return f"MOML[{self.arg}]"
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

    - Decimal-like strings are parsed as exact rationals via Fraction.
    - Everything else is treated as an atomic symbol factor.
    """

    us = str(u).strip()
    if us == "":
        return Fraction(1), tuple()
    try:
        c = Fraction(us)
        return c, tuple()
    except Exception:
        return Fraction(1), (us,)


def _render_coeff(c: Fraction) -> str:
    if c.denominator == 1:
        return str(c.numerator)
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


def _group_power(group: str, q: int) -> str:
    """
    Canonicalize the "q-fold product lift axis" G^{×q} for the audit token language.

    For direct products we distribute powers factor-wise:
      (G×H)^{×q}  ≅  G^{×q} × H^{×q}
    and we normalize cyclic factors as Cn^k with exponent multiplication.
    """

    if q == 1:
        return str(group).strip()

    def _pow_factor(f: str, qq: int) -> str:
        ff = str(f).strip()
        m = re.fullmatch(r"C(\d+)(?:\^(\d+))?", ff)
        if m:
            n = int(m.group(1))
            e = int(m.group(2)) if (m.group(2) is not None and m.group(2) != "") else 1
            ee = int(e) * int(qq)
            return f"C{n}^{ee}" if ee != 1 else f"C{n}"
        if re.fullmatch(r"[A-Za-z0-9_]+", ff):
            return f"{ff}^{qq}"
        return f"({ff})^{qq}"

    g = str(group).strip()
    factors = _split_group_factors(g)
    if len(factors) > 1:
        pf = [_pow_factor(f, q) for f in factors]
        return "x".join(sorted(pf))
    return _pow_factor(g, q)


def _parse_moml_arg(arg: str) -> Tuple[int, str]:
    # Expect "q;G" (G may contain 'x', '^', parentheses, etc).
    s = str(arg)
    if ";" not in s:
        raise ValueError(f"Bad MOML arg (expected 'q;G'): {arg!r}")
    q_s, g_s = s.split(";", 1)
    return int(q_s), str(g_s)


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
    if a.kind == "MOM" and b.kind == "MOM":
        return "RMOM"
    # Merge MOM with an already-expanded MOML token (completion helper to avoid bubble loops).
    if (a.kind == "MOM" and b.kind == "MOML") or (a.kind == "MOML" and b.kind == "MOM"):
        return "RMOML_MERGE"
    # Bubble moment-like gates leftwards (structural).
    if b.kind == "MOM" and a.kind != "MOM":
        return "RBUB"
    if b.kind == "MOML" and a.kind != "MOML":
        return "RMOML_BUB"
    # Fourier distribution law (moment-lift coupling).
    if a.kind == "MOM" and b.kind == "LIFT":
        return "RMOML"
    # Fuse lifts after expansion.
    if a.kind == "MOML" and b.kind == "LIFT":
        return "RMOML_FUSE"
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
    rep: List[Tok]

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
    elif rule == "RMOM":
        q1 = int(a.arg)
        q2 = int(b.arg)
        rep = [Tok("MOM", str(q1 * q2))]
    elif rule == "RMOML_MERGE":
        # MOM[p] MOML[q;G] -> MOML[pq;G] and MOML[q;G] MOM[p] -> MOML[pq;G]
        if a.kind == "MOM" and b.kind == "MOML":
            p = int(a.arg)
            q, group = _parse_moml_arg(b.arg)
            rep = [Tok("MOML", f"{p*q};{group}")]
        elif a.kind == "MOML" and b.kind == "MOM":
            q, group = _parse_moml_arg(a.arg)
            p = int(b.arg)
            # Beck--Chevalley typing pushes the trailing MOM through the lift-axis:
            #   (MOM_q ∘ LIFT_G) ∘ MOM_p  ~  MOM_{pq} ∘ LIFT_{G^{×p}}
            rep = [Tok("MOML", f"{p*q};{_group_power(group, p)}")]
        else:
            raise RuntimeError("RMOML_MERGE applied to non-(MOM,MOML) pair (bug)")
    elif rule == "RBUB":
        # a = X, b = MOM[q]
        q = int(b.arg)
        X = a
        if X.kind == "LIFT":
            g0 = str(X.arg)
            g1 = _group_power(g0, q)
            cert = {"type": "LiftPower", "group": g0, "q": int(q), "group_power": g1}
            rep = [Tok("MOM", str(q)), Tok("LIFT", g1)]
        elif X.kind == "E":
            m = int(X.arg)
            cert = {
                "type": "ResidualSwap",
                "swap": "E<->MOM",
                "m": int(m),
                "q": int(q),
                "basis": f"E{m}<->MOM[{q}]",
                "anom_signature": f"Anom_mom^{q}(K;theta)",
            }
            rep = [Tok("MOM", str(q)), X]
        else:
            rep = [Tok("MOM", str(q)), X]
    elif rule == "RMOML":
        q = int(a.arg)
        group = str(b.arg)
        cert = {
            "type": "ResidualExpand",
            "expand": "MOM∘LIFT Fourier distribution (RMOML)",
            "q": int(q),
            "group": group,
            "basis": f"MOM[{q}]∘LIFT[{group}]",
            "anom_signature": f"Anom^({q})_{group}(K;theta)",
        }
        rep = [Tok("MOML", f"{q};{group}")]
    elif rule == "RMOML_FUSE":
        q, group = _parse_moml_arg(a.arg)
        group2 = str(b.arg)
        rep = [Tok("MOML", f"{q};{_group_product(group, group2)}")]
    elif rule == "RMOML_BUB":
        # a = X, b = MOML[q;G]
        q, group = _parse_moml_arg(b.arg)
        X = a
        if X.kind == "LIFT":
            # absorb lift into the MOML group parameter, dropping the explicit LIFT token.
            # Beck--Chevalley typing: LIFT_H ∘ MOM_q  ≃  MOM_q ∘ LIFT_{H^{×q}}.
            rep = [Tok("MOML", f"{q};{_group_product(group, _group_power(X.arg, q))}")]
        elif X.kind == "E":
            m = int(X.arg)
            cert = {
                "type": "ResidualSwap",
                "swap": "E<->MOML",
                "m": int(m),
                "q": int(q),
                "basis": f"E{m}<->MOML[{q};{group}]",
                "anom_signature": f"Anom_mom^{q}(K;theta)",
            }
            rep = [Tok("MOML", f"{q};{group}"), X]
        else:
            rep = [Tok("MOML", f"{q};{group}"), X]
    else:
        raise RuntimeError(f"Unhandled rule: {rule!r}")

    nw = w[:pos] + rep + w[pos + 2 :]
    return nw, rule, cert


def _priority(strategy: str) -> Tuple[str, ...]:
    if strategy == "merge_first":
        return (
            "RE",
            "RPROJ",
            "RLIFT",
            "RMOM",
            "RMOML_MERGE",
            "RBUB",
            "RPL",
            "REL",
            "RMOML",
            "RMOML_FUSE",
            "RMOML_BUB",
        )
    if strategy == "swap_first":
        return (
            "RBUB",
            "RMOML_BUB",
            "RMOML_MERGE",
            "RPL",
            "REL",
            "RMOML",
            "RMOML_FUSE",
            "RE",
            "RPROJ",
            "RLIFT",
            "RMOM",
        )
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
        if cert is not None:
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
    if cert0 is not None:
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
    rows = summary.get("by_strategy", {})
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Bounded critical-pair audit (Knuth--Bendix style) for the "
        "$(\\mathrm{PROJ}_u,E_m,\\mathrm{LIFT}_G,\\mathrm{MOM}_q)$ rewrite fragment, "
        "including the RMOML (moment--lift Fourier distribution) certificate rule. "
        "We enumerate all length-3 overlap contexts under bounded parameters and check "
        "joinability of the two overlap reductions, including residual counter agreement.}"
    )
    lines.append("\\label{tab:pom_projword_four_gen_kb_completion_audit}")
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
    ap = argparse.ArgumentParser(
        description="Audit bounded critical pairs for four-generator PROJ/E/LIFT/MOM rewrite fragment (incl. RMOML)."
    )
    ap.add_argument("--m-max", type=int, default=8, help="Max m for E[m] tokens.")
    ap.add_argument("--group-orders", type=str, default="2,3,5", help="Comma list for cyclic group orders in LIFT[Cn].")
    ap.add_argument(
        "--u-values",
        type=str,
        default="0.5,0.25",
        help="Comma list for PROJ[u] parameters (numeric strongly recommended).",
    )
    ap.add_argument("--q-values", type=str, default="2,3", help="Comma list for MOM[q] orders.")
    ap.add_argument("--strategies", type=str, default="merge_first,swap_first", help="Comma list of strategies to audit.")
    ap.add_argument("--step-cap", type=int, default=250_000, help="Safety cap on rewrite steps (per branch).")
    ap.add_argument("--keep", type=int, default=12, help="Max mismatch cases to keep in JSON.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "pom_projword_four_gen_kb_completion_audit.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_pom_projword_four_gen_kb_completion_audit.tex"),
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
    if any((not _is_finite_number_str(u)) for u in u_values):
        print("[kb-audit-4gen] warning: non-numeric u-values detected; canonicalization treats them as atomic symbols.", flush=True)
    q_values = _parse_int_list(args.q_values)
    if not q_values:
        raise SystemExit("Empty --q-values")
    if any(q < 2 for q in q_values):
        raise SystemExit("All q must be >= 2")

    strategies = _parse_str_list(args.strategies)
    if not strategies:
        raise SystemExit("Empty --strategies")
    for s in strategies:
        _priority(s)

    atoms: List[Tok] = []
    atoms.extend([Tok("E", str(m)) for m in range(1, m_max + 1)])
    atoms.extend([Tok("LIFT", f"C{n}") for n in group_orders])
    atoms.extend([Tok("PROJ", str(u)) for u in u_values])
    atoms.extend([Tok("MOM", str(q)) for q in q_values])

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

                    nf_ok = nfL == nfR
                    res_ok = (anL == anR) and (holL == holR)

                    if not nf_ok:
                        by_strategy[strat]["nf_mismatches"] += 1
                    if nf_ok and (not res_ok):
                        by_strategy[strat]["residual_mismatches"] += 1
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
                                        "steps": [s.__dict__ for s in proofL.steps],
                                    },
                                    "right_first": {
                                        "normal_form": proofR.normal_form,
                                        "anom_counter": proofR.anom_counter,
                                        "holonomy_counter": proofR.holonomy_counter,
                                        "steps": [s.__dict__ for s in proofR.steps],
                                    },
                                }
                            )

                if time.time() - last_print > 20.0:
                    last_print = time.time()
                    print(f"[kb-audit-4gen] triples={triples} overlaps={overlap_contexts}", flush=True)

    summary: Dict[str, object] = {
        "atoms": [t.render() for t in atoms],
        "triples_total": triples,
        "overlap_contexts_total": overlap_contexts,
        "by_strategy": by_strategy,
        "residual_completion_candidates": residual_completion,
        "mismatch_cases": mismatches,
        "elapsed_s": time.time() - t0,
    }

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[kb-audit-4gen] wrote {jout}", flush=True)

    tout = Path(str(args.tex_out))
    _write_summary_table_tex(tout, summary)
    print(f"[kb-audit-4gen] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

