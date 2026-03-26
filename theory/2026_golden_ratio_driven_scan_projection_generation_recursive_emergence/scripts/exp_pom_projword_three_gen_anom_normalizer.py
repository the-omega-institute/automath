#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Executable demo: three-generator projection-word normalization with residual-swap certificates.

This script implements the manuscript's (PROJ_u, E_m, LIFT_G) rewrite fragment:

  (RPROJ)   PROJ[u] ∘ PROJ[v]        -> PROJ[uv]
  (RLIFT)   LIFT[G] ∘ LIFT[H]        -> LIFT[G×H]
  (RE)      E[m1] ∘ E[m2]            -> E[min(m1,m2)]
  (RPL)     PROJ[u] ∘ LIFT[G]        -> LIFT[G] ∘ PROJ[u]
  (REL)     E[m] ∘ LIFT[G]           -> LIFT[G] ∘ E[m]   (+ residual anomaly signature stub)

Normalization target (interface normal form):
  LIFT[G] ∘ PROJ[u] ∘ E[m]

Token convention:
  Tokens are written left-to-right in categorical composition order.
  (Rightmost token acts first.)

Notes:
  - The E/LIFT swap emits an auditable certificate record with a symbolic
    "Anom_G(K;theta)" placeholder. Numerical filling is intentionally deferred.
  - We do NOT introduce an explicit central ANOM token in the word. Instead we
    return (normal_form, anom_counter) which is equivalent for execution/audit.

Outputs (default):
  - artifacts/export/pom_projword_three_gen_anom_normalizer_demo.json

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from common_paths import export_dir


@dataclass(frozen=True)
class Tok:
    kind: str  # E, PROJ, LIFT
    arg: str

    def render(self) -> str:
        if self.kind == "E":
            return f"E[{self.arg}]"
        return f"{self.kind}[{self.arg}]"


_E_RE = re.compile(r"^E(?:\[?(\d+)\]?)?$")
_LIFT_RE = re.compile(r"^LIFT\[(.+)\]$")
_PROJ_RE = re.compile(r"^PROJ\[(.+)\]$")


def parse_word(s: str) -> List[Tok]:
    parts = [p.strip() for p in str(s).split() if p.strip()]
    out: List[Tok] = []
    for p in parts:
        m = _E_RE.match(p)
        if m:
            mm = m.group(1)
            if mm is None or mm == "":
                raise SystemExit("Bad E token: missing integer m. Use E[m] or Em.")
            out.append(Tok("E", str(int(mm))))
            continue
        m = _PROJ_RE.match(p)
        if m:
            out.append(Tok("PROJ", m.group(1).strip()))
            continue
        m = _LIFT_RE.match(p)
        if m:
            out.append(Tok("LIFT", m.group(1).strip()))
            continue
        raise SystemExit(f"Bad token: {p}. Use E[m], PROJ[u], LIFT[G].")
    return out


def word_to_str(w: List[Tok]) -> str:
    return " ".join(t.render() for t in w)


def _try_float(s: str) -> Optional[float]:
    try:
        x = float(str(s))
    except Exception:
        return None
    if not math.isfinite(x):
        return None
    return x


def _mul_u(u: str, v: str) -> str:
    fu = _try_float(u)
    fv = _try_float(v)
    if fu is not None and fv is not None:
        # Keep a stable, compact representation.
        return f"{(fu * fv):.12g}"
    # Symbolic fallback.
    return f"({u}*{v})"


def _split_group_factors(g: str) -> List[str]:
    # Canonicalize a direct-product expression like "C3xC5" or "C3×C5".
    raw = re.split(r"[x×]", str(g))
    out: List[str] = []
    for p in raw:
        p = p.strip()
        if not p:
            continue
        # Drop a single pair of wrapping parentheses (best-effort).
        if p.startswith("(") and p.endswith(")") and len(p) >= 2:
            p = p[1:-1].strip()
        out.append(p)
    return out if out else [str(g).strip()]


def _group_product(g1: str, g2: str) -> str:
    f = _split_group_factors(g1) + _split_group_factors(g2)
    # For finite abelian direct products, ordering is canonical up to isomorphism.
    f_sorted = sorted(f)
    return "x".join(f_sorted)


def extract_interface_params(nf: List[Tok]) -> Dict[str, object]:
    """Extract (u,m,G) from a three-generator interface normal form.

    The interface normal form is (possibly with missing identities):
      LIFT[G] ∘ PROJ[u] ∘ E[m]
    """
    u: str | None = None
    m: int | None = None
    group: str | None = None
    for t in nf:
        if t.kind == "PROJ":
            u = str(t.arg)
        elif t.kind == "E":
            m = int(t.arg)
        elif t.kind == "LIFT":
            group = str(t.arg)
    return {"u": u, "m": m, "group": group}


def holonomy_counter_from_certs(certs: List[Dict[str, object]]) -> Dict[str, int]:
    """Count E<->LIFT residual swaps by basis label (holonomy counter)."""
    hol = Counter()
    for cert in certs:
        if cert.get("kind") != "ResidualSwap":
            continue
        basis = cert.get("basis")
        if basis is None or str(basis).strip() == "":
            m = cert.get("m")
            group = cert.get("group")
            basis = f"E{m}<->LIFT[{group}]"
        hol[str(basis)] += 1
    return dict(hol)


def rewrite_once_cert(
    w: List[Tok],
    *,
    strategy: str = "merge_first",
) -> Tuple[List[Tok], bool, str, Optional[Dict[str, object]]]:
    """Apply one rewrite step. Returns (new_word, changed, rule, certificate_or_None)."""
    if strategy not in ("merge_first", "swap_first"):
        raise ValueError(f"Unknown strategy: {strategy!r}")

    def rule_RE(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "E" and cur[i + 1].kind == "E":
                m1 = int(cur[i].arg)
                m2 = int(cur[i + 1].arg)
                return cur[:i] + [Tok("E", str(min(m1, m2)))] + cur[i + 2 :], "RE", None
        return None

    def rule_RPROJ(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "PROJ" and cur[i + 1].kind == "PROJ":
                u = cur[i].arg
                v = cur[i + 1].arg
                return cur[:i] + [Tok("PROJ", _mul_u(u, v))] + cur[i + 2 :], "RPROJ", None
        return None

    def rule_RLIFT(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "LIFT" and cur[i + 1].kind == "LIFT":
                g = _group_product(cur[i].arg, cur[i + 1].arg)
                return cur[:i] + [Tok("LIFT", g)] + cur[i + 2 :], "RLIFT", None
        return None

    def rule_RPL(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "PROJ" and cur[i + 1].kind == "LIFT":
                return cur[:i] + [cur[i + 1], cur[i]] + cur[i + 2 :], "RPL", None
        return None

    def rule_REL(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "E" and cur[i + 1].kind == "LIFT":
                m = int(cur[i].arg)
                group = cur[i + 1].arg
                cert: Dict[str, object] = {
                    "kind": "ResidualSwap",
                    "swap": "E<->LIFT",
                    "m": int(m),
                    "group": str(group),
                    "basis": f"E{int(m)}<->LIFT[{str(group)}]",
                    # Symbolic placeholder for the paper's anomaly signature:
                    #   Anom_G(K;theta) = (log Mfrak_chi(theta))_{chi != chi0}.
                    "anom_signature": f"Anom_{group}(K;theta)",
                }
                return cur[:i] + [cur[i + 1], cur[i]] + cur[i + 2 :], "REL", cert
        return None

    priority = (
        ("RE", "RPROJ", "RLIFT", "RPL", "REL") if strategy == "merge_first" else ("RPL", "REL", "RE", "RPROJ", "RLIFT")
    )
    rules = {"RE": rule_RE, "RPROJ": rule_RPROJ, "RLIFT": rule_RLIFT, "RPL": rule_RPL, "REL": rule_REL}
    for name in priority:
        out = rules[name](w)
        if out is None:
            continue
        nw, rule, cert = out
        return nw, True, rule, cert

    return w, False, "", None


def normalize_with_anom(
    w: List[Tok],
    *,
    strategy: str = "merge_first",
    step_cap: int = 200_000,
) -> Tuple[List[Tok], List[str], Dict[str, int], List[Dict[str, object]]]:
    """Normalize and accumulate residual swaps into an anom counter."""
    cur = list(w)
    trace: List[str] = []
    certs: List[Dict[str, object]] = []
    anom = Counter()

    for _ in range(int(step_cap)):
        cur, changed, rule, cert = rewrite_once_cert(cur, strategy=strategy)
        if not changed:
            return cur, trace, dict(anom), certs
        trace.append(rule)
        if cert is not None:
            certs.append(cert)
            if cert.get("kind") == "ResidualSwap":
                key = str(cert.get("anom_signature", ""))
                if key:
                    anom[key] += 1

    raise RuntimeError("rewrite did not terminate within cap (unexpected)")


DEFAULT_WORDS = [
    # Residual swap + tower merge (E/LIFT noncommutativity witnessed by a certificate stub).
    "E[7] LIFT[C5] E[3]",
    # Strict swap (PROJ/LIFT) + tower merge.
    "PROJ[u] LIFT[C3] E[10] E[2]",
    # Full interface normal form with merges on all three generator types.
    "PROJ[0.5] PROJ[0.25] LIFT[C2] LIFT[C4] E[12] E[5]",
    # Already-normal word (fixed point).
    "LIFT[C5] PROJ[u] E[3]",
]


def main() -> None:
    ap = argparse.ArgumentParser(description="Three-generator (PROJ,E,LIFT) projection-word normalizer with anomaly stubs.")
    ap.add_argument("--word", type=str, default=None, help="Optional raw word string (space-separated tokens).")
    ap.add_argument("--strategy", choices=["merge_first", "swap_first"], default="merge_first")
    ap.add_argument(
        "--words",
        type=str,
        default="|".join(DEFAULT_WORDS),
        help="Pipe-separated list of words (used when --word is omitted).",
    )
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "pom_projword_three_gen_anom_normalizer_demo.json"),
        help="Output JSON path.",
    )
    args = ap.parse_args()

    if args.word is not None:
        word_strs = [str(args.word).strip()]
    else:
        word_strs = [w.strip() for w in str(args.words).split("|") if w.strip()]
    if not word_strs:
        raise SystemExit("No words provided.")

    rows: List[dict] = []
    for ws in word_strs:
        toks = parse_word(ws)
        nf, trace, anom, certs = normalize_with_anom(toks, strategy=str(args.strategy))
        params = extract_interface_params(nf)
        hol = holonomy_counter_from_certs(certs)
        rows.append(
            {
                "input": word_to_str(toks),
                "normal_form": word_to_str(nf),
                "interface_params": params,
                "rewrite_trace": trace,
                "anom_counter": anom,
                "holonomy_counter": hol,
                "certificates": certs,
                "steps": len(trace),
            }
        )
        print(f"[threegen-normalizer] in:  {word_to_str(toks)}", flush=True)
        print(f"[threegen-normalizer] nf:  {word_to_str(nf)}", flush=True)
        if anom:
            print(f"[threegen-normalizer] anom: {json.dumps(anom, sort_keys=True)}", flush=True)

    payload = {"strategy": str(args.strategy), "rows": rows}
    out = Path(str(args.json_out))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[threegen-normalizer] wrote {out}", flush=True)


if __name__ == "__main__":
    main()

