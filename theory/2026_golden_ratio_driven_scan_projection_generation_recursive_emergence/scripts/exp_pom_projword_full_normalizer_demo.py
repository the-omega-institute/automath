#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Executable demo: a combined projection-word normalizer (PZ, E[m], P[m], Q[m], K[m], LIFT[G], PROJ[u]).

This script merges two existing rewrite fragments in this repo into a single
auditable normalizer:
  - PW_{Z,E,P,Q}  (split-epi + tower calculus; see exp_pom_projword_zepq_normalizer.py)
  - PW_{Z,E,LIFT,PROJ} (tower + Beck--Chevalley swap + Artin factorization; see
    exp_pom_projword_lift_proj_normalizer_demo.py)

Token convention:
  - Tokens are written left-to-right in categorical composition order.
    (Rightmost token acts first.)

Supported tokens:
  - PZ                 : normalization projection gate P_Z (idempotent)
  - E[m] / Em / E5     : conditional expectation tower gate E_m
  - P[m] / Pm / P5     : pushforward (Fold_m)_*
  - Q[m] / Qm / Q5     : uniform lift (fiber-uniform section)
  - K[m] / Km / K5     : reflector K_m := Q_m ∘ P_m (idempotent)
  - LIFT[Cn]           : finite cyclic lift C_n (demo model)
  - PROJ[u]            : readout projection with parameter u (demo token)
  - PROD[...]          : atomic tensor-bundle token produced by Artin rewrite

Rewrite rules (oriented for normalization):
  (RZ)   PZ ∘ PZ                 -> PZ
  (RE)   E[m1] ∘ E[m2]           -> E[min(m1,m2)]
  (RPQ)  P[m] ∘ Q[m]             -> Id
  (RQP)  Q[m] ∘ P[m]             -> K[m]
  (RKK)  K[m] ∘ K[m]             -> K[m]
  (RPK)  P[m] ∘ K[m]             -> P[m]
  (RKQ)  K[m] ∘ Q[m]             -> Q[m]
  (RBC)  E[m] ∘ LIFT[G]          -> LIFT[G] ∘ E[m]
  (RA)   PROJ[u] ∘ LIFT[Cn]      -> PROD[PROJ[u,chi0] OTIMES ... OTIMES PROJ[u,chi_{n-1}]]

Outputs:
  - artifacts/export/pom_projword_full_normalizer_demo.json
  - sections/generated/tab_pom_projword_full_normalizer_demo.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Tok:
    kind: str  # PZ, E, P, Q, K, LIFT, PROJ, PROD
    arg: str | None = None

    def render(self) -> str:
        if self.kind == "PZ":
            return "PZ"
        if self.arg is None:
            return self.kind
        if self.kind in ("E", "P", "Q", "K"):
            return f"{self.kind}{self.arg}"
        return f"{self.kind}[{self.arg}]"


_E_RE = re.compile(r"^E\[?(\d+)\]?$")
_P_RE = re.compile(r"^P\[?(\d+)\]?$")
_Q_RE = re.compile(r"^Q\[?(\d+)\]?$")
_K_RE = re.compile(r"^K\[?(\d+)\]?$")
_LIFT_RE = re.compile(r"^LIFT\[(.+)\]$")
_PROJ_RE = re.compile(r"^PROJ\[(.+)\]$")
_PROD_RE = re.compile(r"^PROD\[(.+)\]$")


def parse_word(s: str) -> List[Tok]:
    parts = [p.strip() for p in s.split() if p.strip()]
    out: List[Tok] = []
    for p in parts:
        if p == "PZ":
            out.append(Tok("PZ"))
            continue
        m = _E_RE.match(p)
        if m:
            out.append(Tok("E", m.group(1)))
            continue
        m = _P_RE.match(p)
        if m:
            out.append(Tok("P", m.group(1)))
            continue
        m = _Q_RE.match(p)
        if m:
            out.append(Tok("Q", m.group(1)))
            continue
        m = _K_RE.match(p)
        if m:
            out.append(Tok("K", m.group(1)))
            continue
        m = _LIFT_RE.match(p)
        if m:
            out.append(Tok("LIFT", m.group(1)))
            continue
        m = _PROJ_RE.match(p)
        if m:
            out.append(Tok("PROJ", m.group(1)))
            continue
        m = _PROD_RE.match(p)
        if m:
            out.append(Tok("PROD", m.group(1)))
            continue
        raise SystemExit(f"Bad token: {p}. Use PZ, E[m], P[m], Q[m], K[m], LIFT[...], PROJ[...], PROD[...].")
    return out


def word_to_str(w: List[Tok]) -> str:
    return " ".join(t.render() for t in w)


def _same_arg(a: Tok, b: Tok) -> bool:
    return (a.arg is not None) and (b.arg is not None) and (a.arg == b.arg)


def _lift_chars(group: str) -> List[str]:
    # Demo: only cyclic groups Cn.
    if not group.startswith("C"):
        raise ValueError(f"Only cyclic groups Cn supported in this demo, got {group!r}")
    n = int(group[1:])
    if n <= 0:
        raise ValueError("Cyclic group order must be positive")
    return [f"chi{i}" for i in range(n)]


def _holonomy_key(*, m: int, group: str) -> str:
    return f"E{m}<->LIFT[{group}]"


def rewrite_once_cert(
    w: List[Tok],
    *,
    strategy: str = "tower_first",
) -> Tuple[List[Tok], bool, str, Optional[Dict[str, object]]]:
    """Apply a single rewrite step; optionally emit a holonomy certificate on (RBC)."""
    if strategy not in ("tower_first", "swap_first"):
        raise ValueError(f"Unknown strategy: {strategy!r}")

    # (RZ) PZ PZ -> PZ
    for i in range(len(w) - 1):
        if w[i].kind == "PZ" and w[i + 1].kind == "PZ":
            return w[:i] + [Tok("PZ")] + w[i + 2 :], True, "RZ", None

    def _rule_RE(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "E" and cur[i + 1].kind == "E":
                m1 = int(cur[i].arg or "0")
                m2 = int(cur[i + 1].arg or "0")
                return cur[:i] + [Tok("E", str(min(m1, m2)))] + cur[i + 2 :], "RE", None
        return None

    def _rule_RBC(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "E" and cur[i + 1].kind == "LIFT":
                m = int(cur[i].arg or "0")
                group = cur[i + 1].arg or "G"
                cert: Dict[str, object] = {
                    "kind": "HolonomySwap",
                    "swap": "E<->LIFT",
                    "m": m,
                    "group": group,
                    "anom": None,
                    "basis": _holonomy_key(m=m, group=group),
                }
                return cur[:i] + [cur[i + 1], cur[i]] + cur[i + 2 :], "RBC", cert
        return None

    # Strategy-dependent early preference (keeps tower_first identical to the original demo):
    #   - tower_first: run (RE) before split-epi rules
    #   - swap_first : prioritize (RBC) over (RE) when both are available
    if strategy == "tower_first":
        out = _rule_RE(w)
        if out is not None:
            nw, rule, cert = out
            return nw, True, rule, cert
    else:
        out = _rule_RBC(w)
        if out is not None:
            nw, rule, cert = out
            return nw, True, rule, cert
        out = _rule_RE(w)
        if out is not None:
            nw, rule, cert = out
            return nw, True, rule, cert

    # (RPQ) P[m] Q[m] -> Id
    for i in range(len(w) - 1):
        if w[i].kind == "P" and w[i + 1].kind == "Q" and _same_arg(w[i], w[i + 1]):
            return w[:i] + w[i + 2 :], True, "RPQ", None

    # (RQP) Q[m] P[m] -> K[m]
    for i in range(len(w) - 1):
        if w[i].kind == "Q" and w[i + 1].kind == "P" and _same_arg(w[i], w[i + 1]):
            return w[:i] + [Tok("K", w[i].arg)] + w[i + 2 :], True, "RQP", None

    # (RKK) K[m] K[m] -> K[m]
    for i in range(len(w) - 1):
        if w[i].kind == "K" and w[i + 1].kind == "K" and _same_arg(w[i], w[i + 1]):
            return w[:i] + [Tok("K", w[i].arg)] + w[i + 2 :], True, "RKK", None

    # (RPK) P[m] K[m] -> P[m]
    for i in range(len(w) - 1):
        if w[i].kind == "P" and w[i + 1].kind == "K" and _same_arg(w[i], w[i + 1]):
            return w[:i] + [Tok("P", w[i].arg)] + w[i + 2 :], True, "RPK", None

    # (RKQ) K[m] Q[m] -> Q[m]
    for i in range(len(w) - 1):
        if w[i].kind == "K" and w[i + 1].kind == "Q" and _same_arg(w[i], w[i + 1]):
            return w[:i] + [Tok("Q", w[i + 1].arg)] + w[i + 2 :], True, "RKQ", None

    # (RBC) swap: E[m] LIFT[G] -> LIFT[G] E[m] (holonomy certificate stub)
    out = _rule_RBC(w)
    if out is not None:
        nw, rule, cert = out
        return nw, True, rule, cert

    # (RA) Artin/character factorization: PROJ[u] LIFT[Cn] -> PROD[...]
    for i in range(len(w) - 1):
        if w[i].kind == "PROJ" and w[i + 1].kind == "LIFT":
            u = w[i].arg or "u"
            group = w[i + 1].arg or "C1"
            chis = _lift_chars(group)
            parts = [f"PROJ[{u},{chi}]" for chi in chis]
            prod = Tok("PROD", " OTIMES ".join(parts))
            return w[:i] + [prod] + w[i + 2 :], True, "RA", None

    return w, False, "", None


def rewrite_once(w: List[Tok]) -> Tuple[List[Tok], bool, str]:
    nw, changed, rule, _cert = rewrite_once_cert(w, strategy="tower_first")
    return nw, changed, rule


def normalize(w: List[Tok], step_cap: int = 200_000) -> Tuple[List[Tok], List[str]]:
    cur = list(w)
    trace: List[str] = []
    for _ in range(step_cap):
        cur, changed, rule = rewrite_once(cur)
        if not changed:
            return cur, trace
        trace.append(rule)
    raise RuntimeError("rewrite did not terminate within cap (unexpected)")


def normalize_with_holonomy(
    w: List[Tok],
    *,
    strategy: str = "tower_first",
    step_cap: int = 200_000,
) -> Tuple[List[Tok], List[str], Dict[str, int], List[Dict[str, object]]]:
    cur = list(w)
    trace: List[str] = []
    certs: List[Dict[str, object]] = []
    hol = Counter()
    for _ in range(step_cap):
        cur, changed, rule, cert = rewrite_once_cert(cur, strategy=strategy)
        if not changed:
            return cur, trace, dict(hol), certs
        trace.append(rule)
        if cert is not None:
            certs.append(cert)
            if cert.get("kind") == "HolonomySwap":
                key = str(cert.get("basis", ""))
                if key:
                    hol[key] += 1
    raise RuntimeError("rewrite did not terminate within cap (unexpected)")


def tex_escape_tt(s: str) -> str:
    # Minimal escaping for \texttt
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


def write_table_tex(path: Path, rows: List[dict]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Executable demo of a combined projection-word normalizer (split-epi + tower + lift/proj). "
        "We show the input word, its normal form, and the rewrite certificate trace length.}"
    )
    lines.append("\\label{tab:pom_projword_full_normalizer_demo}")
    lines.append("\\begin{tabular}{l l r}")
    lines.append("\\toprule")
    lines.append("input word & normal form & \\#rewrite steps\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(f"\\texttt{{{r['input_tex']}}} & \\texttt{{{r['nf_tex']}}} & {r['steps']}\\\\")
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


DEFAULT_WORDS = [
    # tower + idempotence
    "PZ PZ E5 E12 PZ",
    # split-epi
    "Q5 P5 Q5 P5",
    "PZ E7 Q5 P5 Q5 P5 PZ",
    # Beck--Chevalley swap + Artin factorization
    "E7 LIFT[C5] E3",
    "PROJ[u] LIFT[C3] E10 E2",
    # combined
    "PZ E8 PROJ[u] LIFT[C4] Q5 P5 PZ E1",
]


def main() -> None:
    ap = argparse.ArgumentParser(description="Demo: combined PW normalizer (PZ,E,P,Q,K,LIFT,PROJ).")
    ap.add_argument(
        "--words",
        type=str,
        default="|".join(DEFAULT_WORDS),
        help="Pipe-separated list of space-separated token words.",
    )
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "pom_projword_full_normalizer_demo.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_pom_projword_full_normalizer_demo.tex"),
    )
    args = ap.parse_args()

    word_strs = [w.strip() for w in str(args.words).split("|") if w.strip()]
    rows: List[dict] = []
    for ws in word_strs:
        w = parse_word(ws)
        nf, trace = normalize(w)
        rows.append(
            {
                "input": word_to_str(w),
                "normal_form": word_to_str(nf),
                "rewrite_trace": trace,
                "steps": len(trace),
                "input_tex": tex_escape_tt(word_to_str(w)),
                "nf_tex": tex_escape_tt(word_to_str(nf)),
            }
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"rows": rows}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[pw-full-normalizer-demo] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[pw-full-normalizer-demo] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

