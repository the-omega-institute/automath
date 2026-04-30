#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Common path utilities (paper-local, reproducible pipeline)."""

from __future__ import annotations

import atexit
import os
from pathlib import Path
import sys
import time


_WALLTIME_DISABLE = os.environ.get("OMEGA_DISABLE_WALLTIME", "").strip() in {"1", "true", "TRUE", "yes", "YES"}
_WALLTIME_T0 = time.time()
_WALLTIME_SCRIPT = (
    Path(str(sys.argv[0])).name
    if (hasattr(sys, "argv") and isinstance(sys.argv, list) and sys.argv and str(sys.argv[0]) not in {"", "-c"})
    else "<interactive>"
)


def _walltime_footer() -> None:
    if _WALLTIME_DISABLE:
        return
    dt = time.time() - _WALLTIME_T0
    print(f"[walltime] script={_WALLTIME_SCRIPT} elapsed_s={dt:.3f}", flush=True)


atexit.register(_walltime_footer)


def paper_root() -> Path:
    return Path(__file__).resolve().parents[1]


def scripts_dir() -> Path:
    return paper_root() / "scripts"


def artifacts_dir() -> Path:
    return paper_root() / "artifacts"


def export_dir() -> Path:
    return artifacts_dir() / "export"


def generated_dir() -> Path:
    return paper_root() / "sections" / "generated"

