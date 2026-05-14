#!/usr/bin/env python3
"""Regression test for research-loop pre-Oracle grounding.

The research loop must not send Oracle a question that only mentions the target
slug/project name.  The question has to cite a local fact Codex observed during
the current target workup: a path, command result, hash, finite case label, or
explicit local failure.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "outreach_research_loop.py"


def _load_research_loop():
    spec = importlib.util.spec_from_file_location("outreach_research_loop_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _workup() -> str:
    return """
# Codex Workup

## Target claim now

The target is a finite certificate theorem whose current route is blocked by
one local verifier case.

## Local evidence checked

Codex inspected `tools/community-outreach/targets/demo/results.json` and found
that the artifact parses but has no certificate for case 7.

## Commands run

```bash
python3 tools/community-outreach/targets/demo/verify_demo.py --json
python3 -m json.tool tools/community-outreach/targets/demo/results.json
```

## Codex attempt before Oracle

Codex ran `python3 tools/community-outreach/targets/demo/verify_demo.py --json`.
The local finite verifier failed at case 7 because `results.json` has no
certificate for that case.  This is the first mathematical blocker.

## Verifier/artifact status

`tools/community-outreach/targets/demo/results.json` parses, but the finite
certificate is incomplete at case 7.

## Proof obligations still open

Prove the case-7 lemma or provide a checkable obstruction for the certificate
route.

## Next Oracle question

`tools/community-outreach/targets/demo/results.json` parses, but the command
`python3 tools/community-outreach/targets/demo/verify_demo.py --json` failed at
case 7. Prove the case-7 lemma or provide a checkable obstruction.
"""


def main() -> int:
    loop = _load_research_loop()
    workup = _workup()

    grounded = loop._question_is_grounded_in_local_work(
        (
            "`tools/community-outreach/targets/demo/results.json` parses, but "
            "`verify_demo.py --json` failed at case 7. Prove the case-7 lemma."
        ),
        workup,
        "demo",
    )
    if not grounded:
        raise AssertionError("question citing local path/command/case was not grounded")

    slug_only = loop._question_is_grounded_in_local_work(
        "For demo, prove the exact theorem and explain the remaining obstruction.",
        workup,
        "demo",
    )
    if slug_only:
        raise AssertionError("slug-only Oracle question should not count as locally grounded")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
