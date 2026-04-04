#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compatibility wrapper for publication workspace synchronization."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def main() -> int:
    here = Path(__file__).resolve()
    paper_dir = here.parents[1]
    target = paper_dir / "automation" / here.name
    if not target.is_file():
        raise FileNotFoundError(f"Missing automation entry point: {target}")
    cmd = [sys.executable, str(target), *sys.argv[1:]]
    return subprocess.call(cmd, cwd=str(paper_dir))


if __name__ == "__main__":
    raise SystemExit(main())
