#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Compatibility import layer for the automation contract module."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


def _load_module():
    here = Path(__file__).resolve()
    automation_dir = here.parents[1] / "automation"
    target = automation_dir / "pipeline_contract.py"
    automation_dir_str = str(automation_dir)
    if automation_dir_str not in sys.path:
        sys.path.insert(0, automation_dir_str)
    spec = importlib.util.spec_from_file_location("omega_pipeline_contract_runtime", target)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Unable to load automation pipeline contract from {target}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


_MODULE = _load_module()

CONTRACT_SCHEMA_VERSION = _MODULE.CONTRACT_SCHEMA_VERSION
REQUIRED_CONTRACT_FILES = _MODULE.REQUIRED_CONTRACT_FILES
ContractValidationResult = _MODULE.ContractValidationResult
build_run_manifest = _MODULE.build_run_manifest
build_contract_report = _MODULE.build_contract_report
render_contract_report_markdown = _MODULE.render_contract_report_markdown
write_contract_outputs = _MODULE.write_contract_outputs
validate_contract_artifacts = _MODULE.validate_contract_artifacts
parser = _MODULE.parser


def main() -> int:
    return _MODULE.main()


if __name__ == "__main__":
    raise SystemExit(main())
