#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Demonstrate the value-layer POM rewriting system (RZ, RNF) as an executable artifact.

Paper reference:
  - Definition: def:pom-rewriting-val (RZ, RNF)
  - Proposition: prop:pom-rewriting-terminating (termination + normal form)

We implement a tiny term-rewriting engine over the value-layer word language:
  - EVOLVE(op): an opaque "process-layer" token (op in {add,mul,trace,...})
  - PROJ_NORM: normalization projection gate (P_Z)
  - CLEAN: a post-processing token (kept opaque)

Rewrite rules:
  (RZ)  PROJ_NORM; PROJ_NORM  ->  PROJ_NORM
  (RNF) PROJ_NORM; w; PROJ_NORM  ->  w; PROJ_NORM   if w contains no PROJ_NORM

Outputs:
  - artifacts/export/pom_rewriting_engine_demo.json
  - sections/generated/tab_pom_rewriting_engine_demo.tex

All output is English-only by repository convention.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Tuple

from common_paths import export_dir, generated_dir


@dataclass(frozen=True)
class Tok:
    kind: str
    arg: str | None = None

    def render(self) -> str:
        if self.arg is None:
            return self.kind
        return f"{self.kind}({self.arg})"


def parse_word(s: str) -> List[Tok]:
    """Parse a semicolon-separated word like 'PROJ_NORM; EVOLVE(add); PROJ_NORM'."""
    parts = [p.strip() for p in s.split(";") if p.strip()]
    out: List[Tok] = []
    for p in parts:
        if "(" in p and p.endswith(")"):
            k = p[: p.index("(")].strip()
            a = p[p.index("(") + 1 : -1].strip()
            out.append(Tok(k, a))
        else:
            out.append(Tok(p))
    return out


def word_to_str(w: List[Tok]) -> str:
    return "; ".join(t.render() for t in w)


def contains_proj_norm(w: List[Tok]) -> bool:
    return any(t.kind == "PROJ_NORM" for t in w)


def rewrite_once(w: List[Tok]) -> Tuple[List[Tok], bool, str]:
    """Apply a single rewrite step; return (new_word, changed, rule_name)."""
    # (RZ) local contraction
    for i in range(len(w) - 1):
        if w[i].kind == "PROJ_NORM" and w[i + 1].kind == "PROJ_NORM":
            nw = w[:i] + [Tok("PROJ_NORM")] + w[i + 2 :]
            return nw, True, "RZ"

    # (RNF) slide-middle normalization: PROJ_NORM; w; PROJ_NORM -> w; PROJ_NORM
    # where the middle block contains no PROJ_NORM.
    for i in range(len(w)):
        if w[i].kind != "PROJ_NORM":
            continue
        # Find the next PROJ_NORM after i.
        for j in range(i + 1, len(w)):
            if w[j].kind != "PROJ_NORM":
                continue
            middle = w[i + 1 : j]
            if middle and (not contains_proj_norm(middle)):
                nw = w[:i] + middle + [Tok("PROJ_NORM")] + w[j + 1 :]
                return nw, True, "RNF"
            break

    return w, False, ""


def normalize(w: List[Tok], step_cap: int = 10_000) -> Tuple[List[Tok], List[str]]:
    trace: List[str] = []
    cur = list(w)
    for _ in range(step_cap):
        cur, changed, rule = rewrite_once(cur)
        if not changed:
            return cur, trace
        trace.append(rule)
    raise RuntimeError("rewrite did not terminate within cap (unexpected)")


def cost_stats(w: List[Tok]) -> dict:
    total = sum(1 for t in w if t.kind == "PROJ_NORM")
    nonterminal = 0
    if total > 0:
        # Count PROJ_NORM occurrences except the last token if it is PROJ_NORM.
        last_is = (w[-1].kind == "PROJ_NORM")
        for i, t in enumerate(w):
            if t.kind != "PROJ_NORM":
                continue
            if last_is and i == len(w) - 1:
                continue
            nonterminal += 1
    return {"proj_norm_total": total, "proj_norm_nonterminal": nonterminal}


def write_table_tex(path: Path, rows: List[dict]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{6pt}")
    lines.append(
        "\\caption{Executable demo of the value-layer rewriting system "
        "(RZ,RNF) for \\texttt{PROJ\\_NORM} normalization. "
        "We show the input word, its normal form, and the number of normalization gates "
        "before/after rewriting.}"
    )
    lines.append("\\label{tab:pom_rewriting_engine_demo}")
    lines.append("\\begin{tabular}{l l r r}")
    lines.append("\\toprule")
    lines.append("input word & normal form & \\#norm (in) & \\#norm (nf)\\\\")
    lines.append("\\midrule")
    for r in rows:
        lines.append(
            f"\\texttt{{{r['input_tex']}}} & \\texttt{{{r['nf_tex']}}} & {r['n_in']} & {r['n_nf']}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


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


DEFAULT_WORDS = [
    "PROJ_NORM; PROJ_NORM",
    "EVOLVE(add); PROJ_NORM; CLEAN",
    "PROJ_NORM; EVOLVE(add); PROJ_NORM; CLEAN",
    "EVOLVE(mul); PROJ_NORM; EVOLVE(add); PROJ_NORM; CLEAN",
    "PROJ_NORM; EVOLVE(mul); EVOLVE(add); PROJ_NORM; PROJ_NORM; CLEAN",
    "EVOLVE(trace); PROJ_NORM; EVOLVE(add); PROJ_NORM; EVOLVE(mul); PROJ_NORM",
]


def main() -> None:
    parser = argparse.ArgumentParser(description="Demo executable rewriting for value-layer POM words.")
    parser.add_argument(
        "--words",
        type=str,
        default="|".join(DEFAULT_WORDS),
        help="Pipe-separated list of semicolon-separated words.",
    )
    parser.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "pom_rewriting_engine_demo.json"),
    )
    parser.add_argument(
        "--tex-out",
        type=str,
        default=str(generated_dir() / "tab_pom_rewriting_engine_demo.tex"),
    )
    args = parser.parse_args()

    word_strs = [w.strip() for w in str(args.words).split("|") if w.strip()]
    rows: List[dict] = []
    for ws in word_strs:
        w = parse_word(ws)
        nf, rules = normalize(w)
        st_in = cost_stats(w)
        st_nf = cost_stats(nf)
        rows.append(
            {
                "input": word_to_str(w),
                "normal_form": word_to_str(nf),
                "rewrite_trace": rules,
                "stats_in": st_in,
                "stats_nf": st_nf,
                "n_in": st_in["proj_norm_total"],
                "n_nf": st_nf["proj_norm_total"],
                "input_tex": tex_escape_tt(word_to_str(w)),
                "nf_tex": tex_escape_tt(word_to_str(nf)),
            }
        )

    jout = Path(args.json_out)
    jout.parent.mkdir(parents=True, exist_ok=True)
    jout.write_text(json.dumps({"rows": rows}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"[pom-rewrite-demo] wrote {jout}", flush=True)

    tout = Path(args.tex_out)
    write_table_tex(tout, rows)
    print(f"[pom-rewrite-demo] wrote {tout}", flush=True)


if __name__ == "__main__":
    main()

