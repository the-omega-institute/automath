#!/usr/bin/env python3
"""Regression test for research-loop pre-Oracle grounding.

The research loop must not send Oracle a question that only mentions the target
slug/project name.  The question has to cite a local fact Codex observed during
the current target workup: a path, command result, hash, finite case label, or
explicit local failure.
"""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import time
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


def _local_repair_last(*, ok: bool = True) -> str:
    return json.dumps(
        {
            "ok": ok,
            "postcheck": {
                "codex_command_trace": {
                    "ok": True,
                    "target_command_count": 2,
                },
                "substantive_local_work": {
                    "ok": True,
                },
            },
        },
        indent=2,
    )


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

    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        state_dir = Path(tmp)
        target_root = state_dir / "targets"
        target_dir = target_root / "demo"
        target_dir.mkdir(parents=True)
        loop.TARGETS_DIR = target_root
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            (target_dir / name).write_text(workup, encoding="utf-8")
        (target_dir / "local_repair_last.json").write_text(_local_repair_last(), encoding="utf-8")

        ok, reason = loop._pre_oracle_workup_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(f"fresh Codex handoff should be reusable before Oracle: {reason}")

        time.sleep(0.02)
        (target_dir / "oracle_claim_packet_new.md").write_text(
            "# Oracle Claim Packet\n\n## Oracle Response\n\n"
            "Substantive claim: the case-7 certificate exists with sha256=abc123.\n",
            encoding="utf-8",
        )
        ok, reason = loop._pre_oracle_workup_recent("demo", max_age_seconds=3600)
        if ok or "older than latest substantive Oracle claim" not in reason:
            raise AssertionError(
                "handoff older than newest substantive Oracle claim should force local replay: "
                f"ok={ok} reason={reason!r}"
            )

        time.sleep(0.02)
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            path = target_dir / name
            path.write_text(path.read_text(encoding="utf-8") + "\nRefreshed after claim.\n", encoding="utf-8")
        ok, reason = loop._pre_oracle_workup_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(f"fresh post-claim Codex handoff should be reusable: {reason}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
