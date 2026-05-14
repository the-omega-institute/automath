#!/usr/bin/env python3
"""Regression test for oracle_consultant pre-Oracle Codex handoff parsing."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "oracle_consultant.py"


def _load_oracle_consultant():
    spec = importlib.util.spec_from_file_location("oracle_consultant_under_test", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {MODULE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _workup(*, include_attempt: bool = True) -> str:
    attempt = ""
    if include_attempt:
        attempt = """
## Codex attempt before Oracle

I ran `python3 tools/community-outreach/targets/demo/verify_demo.py --json` and the finite check failed at case 7 because `results.json` has no certificate for that case. This is the first local blocker, so Oracle must prove the case-7 lemma or provide a checkable obstruction.
"""
    return f"""
# Codex Workup

## Target claim now

The target is a finite certificate theorem whose local verifier should close a
bounded case split.

## Local evidence checked

I inspected `tools/community-outreach/targets/demo/results.json` and found that
the case-7 certificate is missing while the verifier script is present.

## Commands run

```bash
python3 tools/community-outreach/targets/demo/verify_demo.py --json
python3 -m json.tool tools/community-outreach/targets/demo/results.json
```

{attempt}

## Verifier/artifact status

The verifier exists, `results.json` parses, and the local failure is exactly the
missing case-7 certificate.

## Proof obligations still open

Prove the case-7 lemma or produce a checkable obstruction for the certificate
route.

## Next Oracle question

`tools/community-outreach/targets/demo/results.json` parses, but the local command `python3 tools/community-outreach/targets/demo/verify_demo.py --json` failed at case 7 because the case-7 certificate is missing. Prove the case-7 lemma or provide a checkable obstruction that closes this certificate route.

## Publication value / re-scope judgment

If the case-7 certificate closes, this becomes a bounded verifier note.
"""


def main() -> int:
    oracle = _load_oracle_consultant()
    section = oracle._extract_markdown_section(_workup(), "Commands run", max_chars=20000)
    if "verify_demo.py --json" not in section:
        raise AssertionError(f"failed to extract Commands run section: {section!r}")

    ok, reason = oracle._target_workup_local_trace_status(_workup())
    if not ok:
        raise AssertionError(f"valid local Codex workup was rejected: {reason}")

    ok, reason = oracle._target_workup_local_trace_status(_workup(include_attempt=False))
    if ok or "codex attempt before oracle" not in reason.lower():
        raise AssertionError(f"metadata-only workup was not rejected correctly: ok={ok} reason={reason!r}")

    grounded = oracle._question_is_grounded_in_local_work(
        (
            "`tools/community-outreach/targets/demo/results.json` parses, but "
            "`verify_demo.py --json` failed at case 7. Prove the case-7 lemma."
        ),
        _workup(),
        "demo",
    )
    if not grounded:
        raise AssertionError("grounded Oracle question was not recognized")

    slug_only = oracle._question_is_grounded_in_local_work(
        "For demo, prove the exact theorem and explain the remaining obstruction.",
        _workup(),
        "demo",
    )
    if slug_only:
        raise AssertionError("slug-only Oracle question should not count as locally grounded")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
