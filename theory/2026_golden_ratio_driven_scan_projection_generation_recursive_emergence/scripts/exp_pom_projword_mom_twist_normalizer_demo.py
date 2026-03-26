#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Executable demo: projection-word rewriting with MOM[q] and TWIST[chi] extensions.

This script is an "engineering witness" for turning the interface-level generator
list into an executable rewriting + certificate pipeline.

We extend the combined normalizer (PZ, E[m], P[m], Q[m], K[m], LIFT[G], PROJ[u])
by adding:
  - MOM[q]      : moment/collision lift operator (syntactic proxy for Lift_q)
  - TWIST[chi]  : character twist operator (kept symbolic here; can be fused into PROJ)
  - MOML[q;G]   : symbolic placeholder produced by the RMOML (Fourier distribution) rewrite

Normalization intent (oriented rules):
  - bubble MOM[q] leftwards to a prefix position (structural operator),
  - fuse PROJ[u] with an adjacent TWIST[chi] into PROJ[u,chi],
  - optionally reduce an adjacent MOM[q]∘LIFT[G] via RMOML into a MOML[...] token,
  - keep the existing audited fragment rules (tower, split-epi, Beck--Chevalley swap,
    Artin/character factorization witness).

Certificate interface:
  - Rewrites that are semantically "not strictly commuting" in the paper can emit a
    symbolic certificate record (e.g. a MOM/E Beck--Chevalley anomaly placeholder).

Outputs:
  - artifacts/export/pom_projword_mom_twist_normalizer_demo.json
  - sections/generated/tab_pom_projword_mom_twist_normalizer_demo.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Tok:
    kind: str  # PZ, E, P, Q, K, LIFT, PROJ, PROD, MOM, MOML, TWIST
    arg: str | None = None

    def render(self) -> str:
        if self.kind == "PZ":
            return "PZ"
        if self.arg is None:
            return self.kind
        if self.kind in ("E", "P", "Q", "K"):
            return f"{self.kind}{self.arg}"
        if self.kind == "MOM":
            return f"MOM[{self.arg}]"
        if self.kind == "MOML":
            return f"MOML[{self.arg}]"
        return f"{self.kind}[{self.arg}]"


_E_RE = re.compile(r"^E\[?(\d+)\]?$")
_P_RE = re.compile(r"^P\[?(\d+)\]?$")
_Q_RE = re.compile(r"^Q\[?(\d+)\]?$")
_K_RE = re.compile(r"^K\[?(\d+)\]?$")
_MOM_RE = re.compile(r"^MOM(?:\[?(\d+)\]?)?$")
_LIFT_RE = re.compile(r"^LIFT\[(.+)\]$")
_PROJ_RE = re.compile(r"^PROJ\[(.+)\]$")
_PROD_RE = re.compile(r"^PROD\[(.+)\]$")
_TWIST_RE = re.compile(r"^TWIST\[(.+)\]$")


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
        m = _MOM_RE.match(p)
        if m:
            q = m.group(1)
            if q is None or q == "":
                raise SystemExit("Bad MOM token: missing integer order. Use MOM[q].")
            out.append(Tok("MOM", q))
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
        m = _TWIST_RE.match(p)
        if m:
            out.append(Tok("TWIST", m.group(1)))
            continue
        raise SystemExit(
            f"Bad token: {p}. Use PZ, E[m], P[m], Q[m], K[m], LIFT[...], PROJ[...], PROD[...], MOM[q], TWIST[chi]."
        )
    return out


def word_to_str(w: List[Tok]) -> str:
    return " ".join(t.render() for t in w)


def _same_arg(a: Tok, b: Tok) -> bool:
    return (a.arg is not None) and (b.arg is not None) and (a.arg == b.arg)


def _lift_chars(group: str) -> List[str]:
    # Demo: only simple cyclic groups Cn.
    if not re.fullmatch(r"C\d+", group):
        raise ValueError(f"Only cyclic groups Cn supported in this demo, got {group!r}")
    n = int(group[1:])
    if n <= 0:
        raise ValueError("Cyclic group order must be positive")
    return [f"chi{i}" for i in range(n)]


def _group_power(group: str, q: int) -> str:
    if q == 1:
        return group
    # Keep purely syntactic (typed) information; do not expand characters for products.
    if re.fullmatch(r"[A-Za-z0-9_]+", group):
        return f"{group}^{q}"
    return f"({group})^{q}"


def _group_order(group: str) -> int | None:
    """
    Best-effort parse of a (syntactic) finite abelian group descriptor used in demo tokens.

    Supported (non-exhaustive):
      - Cn
      - Cn^k
      - direct products like C2xC3xC5^2 (order multiplies)
    """

    g = str(group).strip()
    if not g:
        return None

    # Split direct products.
    parts = re.split(r"[x×]", g)
    if len(parts) > 1:
        ord_prod = 1
        for p in parts:
            p = p.strip()
            if not p:
                continue
            o = _group_order(p)
            if o is None:
                return None
            ord_prod *= int(o)
        return int(ord_prod)

    # Single factor.
    m = re.fullmatch(r"C(\d+)(?:\^(\d+))?", g)
    if not m:
        return None
    n = int(m.group(1))
    if n <= 0:
        return None
    k = int(m.group(2)) if (m.group(2) is not None and m.group(2) != "") else 1
    if k <= 0:
        return None
    return int(n**k)


def _pow_compact_str(base: int, exp: int, *, max_digits: int = 48) -> str:
    if exp < 0:
        return f"{base}^{exp}"
    try:
        v = pow(int(base), int(exp))
    except Exception:
        return f"{base}^{exp}"
    s = str(v)
    if len(s) > int(max_digits):
        return f"{base}^{exp}"
    return s


def rewrite_once(w: List[Tok]) -> Tuple[List[Tok], bool, str, Optional[Dict[str, object]]]:
    """Apply a single rewrite step; return (new_word, changed, rule_name, certificate_or_None)."""
    # ---- Existing audited fragment rules (same orientation as exp_pom_projword_full_normalizer_demo.py) ----

    # (RZ) PZ PZ -> PZ
    for i in range(len(w) - 1):
        if w[i].kind == "PZ" and w[i + 1].kind == "PZ":
            return w[:i] + [Tok("PZ")] + w[i + 2 :], True, "RZ", None

    # (RE) E[m1] E[m2] -> E[min(m1,m2)]
    for i in range(len(w) - 1):
        if w[i].kind == "E" and w[i + 1].kind == "E":
            m1 = int(w[i].arg or "0")
            m2 = int(w[i + 1].arg or "0")
            return w[:i] + [Tok("E", str(min(m1, m2)))] + w[i + 2 :], True, "RE", None

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

    # (RBC) swap: E[m] LIFT[G] -> LIFT[G] E[m]
    for i in range(len(w) - 1):
        if w[i].kind == "E" and w[i + 1].kind == "LIFT":
            m = int(w[i].arg or "0")
            group = w[i + 1].arg or "G"
            cert = {
                "kind": "HolonomySwap",
                "swap": "E<->LIFT",
                "m": m,
                "group": group,
                "anom": None,
                "basis": f"E{m}<->LIFT[{group}]",
            }
            return w[:i] + [w[i + 1], w[i]] + w[i + 2 :], True, "RBC", cert

    # (RA) Artin/character factorization witness: PROJ[u] LIFT[Cn] -> PROD[...]
    for i in range(len(w) - 1):
        if w[i].kind == "PROJ" and w[i + 1].kind == "LIFT":
            u = w[i].arg or "u"
            group = w[i + 1].arg or "C1"
            # Only expand for simple cyclic Cn (avoid combinatorial explosion for products/powers).
            if not re.fullmatch(r"C\d+", group):
                continue
            chis = _lift_chars(group)
            parts = [f"PROJ[{u},{chi}]" for chi in chis]
            prod = Tok("PROD", " OTIMES ".join(parts))
            return w[:i] + [prod] + w[i + 2 :], True, "RA", None

    # ---- Extensions: TWIST fusion + MOM bubbling + symbolic certificates ----

    # (RTW) fuse: PROJ[u] TWIST[chi] -> PROJ[u,chi]
    for i in range(len(w) - 1):
        if w[i].kind == "PROJ" and w[i + 1].kind == "TWIST":
            u = w[i].arg or "u"
            chi = w[i + 1].arg or "chi"
            return w[:i] + [Tok("PROJ", f"{u},{chi}")] + w[i + 2 :], True, "RTW", None

    # (RTW_SWAP) swap: TWIST[chi] PROJ[u] -> PROJ[u] TWIST[chi]
    for i in range(len(w) - 1):
        if w[i].kind == "TWIST" and w[i + 1].kind == "PROJ":
            return w[:i] + [w[i + 1], w[i]] + w[i + 2 :], True, "RTW_SWAP", None

    # (RMOM_MUL) combine adjacent MOMs: MOM[q1] MOM[q2] -> MOM[q1*q2]
    for i in range(len(w) - 1):
        if w[i].kind == "MOM" and w[i + 1].kind == "MOM":
            q1 = int(w[i].arg or "1")
            q2 = int(w[i + 1].arg or "1")
            return w[:i] + [Tok("MOM", str(q1 * q2))] + w[i + 2 :], True, "RMOM_MUL", None

    # (RMOM_BUBBLE) bubble MOM[q] leftwards across an adjacent token X:
    #   X MOM[q] -> MOM[q] X'   (X' may be structurally updated; certificate optional)
    for i in range(len(w) - 1):
        if w[i + 1].kind != "MOM":
            continue
        q = int(w[i + 1].arg or "1")
        X = w[i]

        if X.kind == "LIFT":
            g0 = X.arg or "G"
            g1 = _group_power(g0, q)
            cert = {"kind": "LiftPower", "group": g0, "q": q, "group_power": g1}
            return w[:i] + [Tok("MOM", str(q)), Tok("LIFT", g1)] + w[i + 2 :], True, "RMOM_LIFT", cert

        if X.kind == "E":
            m = int(X.arg or "0")
            cert = {"kind": "AnomPlaceholder", "via": "E<->MOM", "m": m, "q": q}
            return w[:i] + [Tok("MOM", str(q)), X] + w[i + 2 :], True, "RMOM_E", cert

        # Default: strict swap (no certificate).
        return w[:i] + [Tok("MOM", str(q)), X] + w[i + 2 :], True, "RMOM_SWAP", None

    # (RMOML) Fourier distribution law (symbolic): MOM[q] LIFT[G] -> MOML[q;G]
    # This is a certificate-producing rewrite that "evaluates" the adjacent MOM∘LIFT coupling
    # into a character-domain expansion placeholder (paper: Anom_G^(q) tower).
    for i in range(len(w) - 1):
        if w[i].kind == "MOM" and w[i + 1].kind == "LIFT":
            q = int(w[i].arg or "1")
            group = w[i + 1].arg or "G"
            g_order = _group_order(group)
            cert: Dict[str, object] = {
                "kind": "FourierDistribution",
                "rule": "RMOML",
                "q": q,
                "group": group,
                "basis": f"MOM[{q}]∘LIFT[{group}]",
                "anom_signature_tower": f"Anom^({q})_{group}(K;theta)",
                "channel_count": None,
            }
            if g_order is not None and q >= 2:
                cert["group_order"] = int(g_order)
                cert["channel_count"] = _pow_compact_str(int(g_order), int(q - 1))
                cert["channel_count_formula"] = f"|G|^{q-1}"
            return w[:i] + [Tok("MOML", f"{q};{group}")] + w[i + 2 :], True, "RMOML", cert

    return w, False, "", None


def normalize(w: List[Tok], step_cap: int = 200_000) -> Tuple[List[Tok], List[str], List[Dict[str, object]]]:
    cur = list(w)
    trace: List[str] = []
    certs: List[Dict[str, object]] = []
    for _ in range(step_cap):
        cur, changed, rule, cert = rewrite_once(cur)
        if not changed:
            return cur, trace, certs
        trace.append(rule)
        if cert is not None:
            certs.append(cert)
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
        "\\caption{Executable demo of a projection-word normalizer extended with "
        "\\texttt{MOM[q]} and \\texttt{TWIST[chi]} tokens. "
        "We show the input word, its normal form, and the rewrite/certificate sizes.}"
    )
    lines.append("\\label{tab:pom_projword_mom_twist_normalizer_demo}")
    lines.append("\\begin{tabular}{l l r r}")
    lines.append("\\toprule")
    lines.append("input word & normal form & \\#rewrite steps & \\#certs\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"\\texttt{{{r['input_tex']}}} & \\texttt{{{r['nf_tex']}}} & {r['steps']} & {r['n_certs']}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


DEFAULT_WORDS = [
    # MOM bubbling + Beck--Chevalley placeholders
    "E7 LIFT[C5] MOM[2] PROJ[u] PZ",
    "PZ Q5 P5 TWIST[chi1] PROJ[u] LIFT[C3] MOM[3] E10",
    # TWIST fusion + Artin witness
    "PZ PROJ[u] TWIST[chi2] LIFT[C4] E3",
    # Adjacent MOM combine
    "MOM[2] MOM[3] PROJ[u] LIFT[C2] E9",
]


def main() -> None:
    ap = argparse.ArgumentParser(description="Demo: extended PW normalizer with MOM/TWIST.")
    ap.add_argument(
        "--words",
        type=str,
        default="|".join(DEFAULT_WORDS),
        help="Pipe-separated list of space-separated token words.",
    )
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "pom_projword_mom_twist_normalizer_demo.json"),
    )
    ap.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_pom_projword_mom_twist_normalizer_demo.tex"),
    )
    args = ap.parse_args()

    word_strs = [w.strip() for w in str(args.words).split("|") if w.strip()]
    rows: List[dict] = []
    for ws in word_strs:
        toks = parse_word(ws)
        nf, trace, certs = normalize(toks)
        rows.append(
            {
                "input": word_to_str(toks),
                "normal_form": word_to_str(nf),
                "rewrite_trace": trace,
                "certificates": certs,
                "steps": len(trace),
                "n_certs": len(certs),
                "input_tex": tex_escape_tt(word_to_str(toks)),
                "nf_tex": tex_escape_tt(word_to_str(nf)),
            }
        )

    jout = Path(str(args.json_out))
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"rows": rows}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[pw-mom-twist-demo] wrote {jout}", flush=True)

    tout = Path(str(args.tex_out))
    write_table_tex(tout, rows)
    print(f"[pw-mom-twist-demo] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

