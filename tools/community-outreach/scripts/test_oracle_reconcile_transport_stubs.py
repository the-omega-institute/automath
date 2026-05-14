#!/usr/bin/env python3
"""Regression tests for Oracle reconcile transport-stub filtering."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[3]
MODULE_PATH = REPO / "tools/community-outreach/outreach_oracle_reconcile.py"


def _load_reconcile():
    spec = importlib.util.spec_from_file_location("outreach_oracle_reconcile_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load outreach_oracle_reconcile")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


def main() -> int:
    rec = _load_reconcile()
    stubs = [
        "ERROR: No assistant output after 300s (page=15357, url=...)",
        "No assistant output after 300s (page=15357, url=...)",
        "ERROR: Task cancelled by server: deep_demo",
        "ERROR (re-extract): re-extract: nothing meaningful (0 chars)",
    ]
    for text in stubs:
        if not rec._is_transport_stub_response(text):
            raise AssertionError(f"transport stub was not filtered: {text!r}")

    substantive = "Theorem. Let X be a curve. Proof. This is not a transport failure."
    if rec._is_transport_stub_response(substantive):
        raise AssertionError("substantive text was incorrectly filtered")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
