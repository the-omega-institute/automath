#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Automatic wall-time footer for paper-local scripts.

Python's `site` module (imported at interpreter startup) will attempt to import
`sitecustomize` from `sys.path`. Since our paper scripts are executed from the
`scripts/` directory, placing this file here makes *all* scripts print an
auditable total runtime line at process exit without editing each script.

Disable by setting:
  OMEGA_DISABLE_WALLTIME=1
"""

from __future__ import annotations

import atexit
import os
import time


_DISABLE = os.environ.get("OMEGA_DISABLE_WALLTIME", "").strip() in {"1", "true", "TRUE", "yes", "YES"}
_T0 = time.time()


def _script_name() -> str:
    try:
        import __main__  # noqa: PLC0415

        p = getattr(__main__, "__file__", None)
        if not p:
            return "<interactive>"
        return os.path.basename(str(p))
    except Exception:
        return "<unknown>"


def _walltime_footer() -> None:
    if _DISABLE:
        return
    dt = time.time() - _T0
    print(f"[walltime] script={_script_name()} elapsed_s={dt:.3f}", flush=True)


atexit.register(_walltime_footer)

