#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Automation entry point forwarding to the canonical experiment pipeline."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path


def main() -> int:
    here = Path(__file__).resolve()
    paper_dir = here.parents[1]
    target = paper_dir / "scripts" / here.name
    if not target.is_file():
        raise FileNotFoundError(f"Missing script entry point: {target}")
    cmd = [sys.executable, str(target), *sys.argv[1:]]
    return subprocess.call(cmd, cwd=str(paper_dir))


if __name__ == "__main__":
    raise SystemExit(main())
