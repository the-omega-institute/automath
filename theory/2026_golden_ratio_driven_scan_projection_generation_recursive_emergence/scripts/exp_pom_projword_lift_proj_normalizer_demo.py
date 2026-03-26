#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Executable demo: projection-word rewriting with E[m], LIFT(G), PROJ(u).

This is a small, auditable witness for the extended PW rewriting fragment
discussed in the paper (PW 2-category + rewrite certificates).

Token convention (matches other PW normalizers in this repo):
- Tokens are written left-to-right in categorical composition order.
  That is, the rightmost token acts first.

We support a minimal typed fragment with tokens:
- PZ                 : normalization projection gate P_Z (idempotent)
- E[m] (or Em)       : conditional expectation tower gate E_m
- LIFT[Cn]           : a finite abelian lift; here we model cyclic group C_n
- PROJ[u]            : readout projection with temperature parameter u

Rewrite rules (oriented for normalization):
  (RZ)     PZ ∘ PZ              -> PZ
  (RE)     E[m1] ∘ E[m2]        -> E[min(m1,m2)]   (tower)
  (RBC)    E[m] ∘ LIFT[G]       -> LIFT[G] ∘ E[m]  (Beck–Chevalley style swap)
  (RA)     PROJ[u] ∘ LIFT[Cn]   -> PROD( PROJ[u,chi0] ⊗ ... ⊗ PROJ[u,chi_{n-1}] )
           (Artin/character factorization as a 2-morphism witness)

We treat PROD(...) as an atomic "parallel/tensor bundle" token in this demo.

Outputs:
  - artifacts/export/pom_projword_lift_proj_normalizer_demo.json
  - sections/generated/tab_pom_projword_lift_proj_normalizer_demo.tex

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
    kind: str  # PZ, E, LIFT, PROJ, PROD
    arg: str | None = None

    def render(self) -> str:
        if self.arg is None:
            return self.kind
        return f"{self.kind}[{self.arg}]"


_E_RE = re.compile(r"^E\[?(\d+)\]?$")
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
        raise SystemExit(f"Bad token: {p}. Use PZ, E[m], LIFT[...], PROJ[...].")
    return out


def word_to_str(w: List[Tok]) -> str:
    return " ".join(t.render() for t in w)


def _lift_chars(group: str) -> List[str]:
    # Minimal model: only cyclic groups Cn.
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
    """Apply a single rewrite step.

    Returns:
        (new_word, changed, rule_name, certificate_or_None)

    Notes:
    - `strategy` only changes rewrite *priority*, not the rule set.
    - The (RBC) swap can emit a holonomy/anomaly certificate stub, matching the
      paper's "swap failure -> residual -> signature" interface.
    """
    if strategy not in ("tower_first", "swap_first"):
        raise ValueError(f"Unknown strategy: {strategy!r}")

    def rule_RZ(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "PZ" and cur[i + 1].kind == "PZ":
                return cur[:i] + [Tok("PZ")] + cur[i + 2 :], "RZ", None
        return None

    def rule_RE(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "E" and cur[i + 1].kind == "E":
                m1 = int(cur[i].arg or "0")
                m2 = int(cur[i + 1].arg or "0")
                return cur[:i] + [Tok("E", str(min(m1, m2)))] + cur[i + 2 :], "RE", None
        return None

    def rule_RBC(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "E" and cur[i + 1].kind == "LIFT":
                m = int(cur[i].arg or "0")
                group = cur[i + 1].arg or "G"
                cert: Dict[str, object] = {
                    "kind": "HolonomySwap",
                    "swap": "E<->LIFT",
                    "m": m,
                    "group": group,
                    # The executable pipeline can fill this with a numerical vector:
                    #   Anom_G(K;theta) = (log M_chi(theta))_{chi!=chi0}.
                    "anom": None,
                    "basis": _holonomy_key(m=m, group=group),
                }
                return cur[:i] + [cur[i + 1], cur[i]] + cur[i + 2 :], "RBC", cert
        return None

    def rule_RA(cur: List[Tok]) -> Optional[Tuple[List[Tok], str, Optional[Dict[str, object]]]]:
        for i in range(len(cur) - 1):
            if cur[i].kind == "PROJ" and cur[i + 1].kind == "LIFT":
                u = cur[i].arg or "u"
                group = cur[i + 1].arg or "C1"
                chis = _lift_chars(group)
                parts = [f"PROJ[{u},{chi}]" for chi in chis]
                # Keep ASCII-only in artifacts/tex for portability.
                prod = Tok("PROD", " OTIMES ".join(parts))
                return cur[:i] + [prod] + cur[i + 2 :], "RA", None
        return None

    priority = ("RZ", "RE", "RBC", "RA") if strategy == "tower_first" else ("RZ", "RBC", "RE", "RA")
    rules = {"RZ": rule_RZ, "RE": rule_RE, "RBC": rule_RBC, "RA": rule_RA}
    for name in priority:
        out = rules[name](w)
        if out is None:
            continue
        nw, rule, cert = out
        return nw, True, rule, cert

    return w, False, "", None


def rewrite_once(w: List[Tok]) -> Tuple[List[Tok], bool, str]:
    nw, changed, rule, _cert = rewrite_once_cert(w, strategy="tower_first")
    return nw, changed, rule


def normalize(w: List[Tok], step_cap: int = 100_000) -> Tuple[List[Tok], List[str]]:
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
    step_cap: int = 100_000,
) -> Tuple[List[Tok], List[str], Dict[str, int], List[Dict[str, object]]]:
    """Normalize and accumulate holonomy from (RBC) swap certificates."""
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
        "\\caption{Executable demo of an extended projection-word normal form with "
        "$P_Z$, $E_m$, $\\mathrm{LIFT}_G$, and $\\mathrm{PROJ}_u$ rewrite certificates "
        "(idempotence, tower, Beck--Chevalley swap, Artin/character factorization).}"
    )
    lines.append("\\label{tab:pom_projword_lift_proj_normalizer_demo}")
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
    "PZ PZ E5 E12 PZ",
    "E7 LIFT[C5] E3",
    "PROJ[u] LIFT[C3] E10 E2",
    "PZ E8 PROJ[u] LIFT[C4] PZ E1",
    "E9 E4 PROJ[u] LIFT[C2] LIFT[C2]",
]


def main() -> None:
    parser = argparse.ArgumentParser(description="Demo PW rewriting with E/LIFT/PROJ (normal form witness).")
    parser.add_argument(
        "--words",
        type=str,
        default="|".join(DEFAULT_WORDS),
        help="Pipe-separated list of space-separated token words.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "pom_projword_lift_proj_normalizer_demo.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_pom_projword_lift_proj_normalizer_demo.tex"),
    )
    args = parser.parse_args()

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
    print(f"[pw-lift-proj-demo] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[pw-lift-proj-demo] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

