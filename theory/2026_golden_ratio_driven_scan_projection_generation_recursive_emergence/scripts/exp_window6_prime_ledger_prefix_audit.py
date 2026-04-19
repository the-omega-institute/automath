#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Window-6 dynamic prime-ledger prefix audit.

Outputs:
  - artifacts/export/window6_prime_ledger_prefix_audit.json
  - sections/generated/tab_window6_prime_ledger_prefix_audit.tex
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Dict, List

from common_paths import export_dir, generated_dir
from common_window6_audit import (
    EVENT_CODES_6,
    LEDGER_BASE_6,
    event_stream,
    fold_bin_word,
    ledger_prefix_addresses,
    ledger_prefix_integers,
    sigma_vector,
    window6_data,
)


def _write_table_tex(path: Path, rows: List[Dict[str, object]]) -> None:
    lines: List[str] = []
    lines.append("\\begin{table}[H]")
    lines.append("\\centering")
    lines.append("\\scriptsize")
    lines.append("\\setlength{\\tabcolsep}{5pt}")
    lines.append("\\caption{Window-6 dynamic prime-ledger prefix audit for representative microstates.}")
    lines.append("\\label{tab:window6_prime_ledger_prefix_audit}")
    lines.append("\\begin{tabular}{l r l r r}")
    lines.append("\\toprule")
    lines.append("representative & microstate & stable word & final $\\log_2 N_T$ & final address\\\\")
    lines.append("\\midrule")
    for row in rows:
        lines.append(
            f"{row['label']} & {row['microstate']} & \\texttt{{{row['word']}}} & "
            f"{row['log2_final']:.3f} & {row['address_final']:.6f}\\\\"
        )
    lines.append("\\bottomrule")
    lines.append("\\end{tabular}")
    lines.append("\\end{table}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    ap = argparse.ArgumentParser(description="Audit the dynamic prime-ledger prefixes for window-6.")
    ap.add_argument(
        "--json-out",
        type=str,
        default=str(export_dir() / "window6_prime_ledger_prefix_audit.json"),
    )
    ap.add_argument(
        "--tex-tab-out",
        type=str,
        default=str(generated_dir() / "tab_window6_prime_ledger_prefix_audit.tex"),
    )
    args = ap.parse_args()

    wd = window6_data()
    reps = [
        ("cyclic", wd.representative_microstates["cyclic"]),
        ("boundary-lower", wd.representative_microstates["boundary_lower"]),
        ("boundary-upper", wd.representative_microstates["boundary_upper"]),
    ]

    rep_payload: List[Dict[str, object]] = []
    tab_rows: List[Dict[str, object]] = []

    for label, n in reps:
        events = event_stream(n, wd)
        ints = ledger_prefix_integers(events)
        addrs = ledger_prefix_addresses(events, base=LEDGER_BASE_6)
        log2s = [math.log2(float(v)) for v in ints]
        word = fold_bin_word(n, wd.m)
        sig = list(sigma_vector(n, wd))
        rep_payload.append(
            {
                "label": label,
                "microstate": int(n),
                "stable_word": word,
                "sigma": sig,
                "events": list(events),
                "codes": [int(EVENT_CODES_6[e]) for e in events],
                "prefix_integers": [int(v) for v in ints],
                "prefix_addresses": [float(v) for v in addrs],
                "prefix_log2": [float(v) for v in log2s],
            }
        )
        tab_rows.append(
            {
                "label": label,
                "microstate": int(n),
                "word": word,
                "log2_final": float(log2s[-1]),
                "address_final": float(addrs[-1]),
            }
        )

    payload = {
        "window": 6,
        "event_alphabet": dict(EVENT_CODES_6),
        "ledger_base": LEDGER_BASE_6,
        "representatives": rep_payload,
    }
    out_json = Path(args.json_out)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    _write_table_tex(Path(args.tex_tab_out), tab_rows)

    print("[window6-prime-ledger] wrote JSON and TeX table artifacts", flush=True)


if __name__ == "__main__":
    main()
