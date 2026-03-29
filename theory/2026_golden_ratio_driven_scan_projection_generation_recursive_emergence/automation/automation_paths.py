#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Path helpers for the paper-level automation pipeline."""

from __future__ import annotations

from pathlib import Path


def paper_root() -> Path:
    return Path(__file__).resolve().parents[1]


def automation_dir() -> Path:
    return paper_root() / "automation"


def scripts_dir() -> Path:
    return paper_root() / "scripts"


def artifacts_dir() -> Path:
    return paper_root() / "artifacts"


def export_dir() -> Path:
    return artifacts_dir() / "export"


def generated_dir() -> Path:
    return paper_root() / "sections" / "generated"
