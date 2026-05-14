#!/usr/bin/env python3
"""Regression test for dispatch_worktree pre-Oracle Codex handoff reuse."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parents[1]
MODULE_PATH = SCRIPT_DIR / "dispatch_worktree.py"


def _load_dispatch_worktree():
    spec = importlib.util.spec_from_file_location("dispatch_worktree_under_test", MODULE_PATH)
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

## Codex attempt before Oracle

I ran `python3 tools/community-outreach/targets/demo/verify_demo.py --json` and
the finite check failed at case 7 because `results.json` has no certificate for
that case. This is the first local blocker, so Oracle must prove the case-7
lemma or provide a checkable obstruction.

## Verifier/artifact status

The verifier exists, `results.json` parses, and the local failure is exactly the
missing case-7 certificate.

## Proof obligations still open

Prove the case-7 lemma or produce a checkable obstruction for the certificate
route.

## Next Oracle question

`tools/community-outreach/targets/demo/results.json` parses, but the local
command `python3 tools/community-outreach/targets/demo/verify_demo.py --json`
failed at case 7 because the case-7 certificate is missing. Prove the case-7
lemma or provide a checkable obstruction that closes this certificate route.

## Publication value / re-scope judgment

If the case-7 certificate closes, this becomes a bounded verifier note.
"""


def _local_repair_last() -> str:
    return """
{
  "ok": true,
  "postcheck": {
    "codex_command_trace": {
      "ok": true,
      "target_command_count": 2
    },
    "substantive_local_work": {
      "ok": true
    }
  }
}
"""


def main() -> int:
    dispatch = _load_dispatch_worktree()
    with tempfile.TemporaryDirectory(dir=SCRIPT_DIR) as tmp:
        repo_root = Path(tmp)
        target_root = repo_root / "tools/community-outreach/targets"
        target_dir = target_root / "demo"
        target_dir.mkdir(parents=True)
        dispatch.REPO_ROOT_DEFAULT = repo_root
        dispatch.TARGETS_DIR_DEFAULT = target_root
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            (target_dir / name).write_text(_workup(), encoding="utf-8")
        (target_dir / "local_repair_last.json").write_text(_local_repair_last(), encoding="utf-8")

        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(f"fresh handoff without claim packet should pass: {reason}")

        time.sleep(0.02)
        (target_dir / "oracle_claim_packet_new.md").write_text(
            "# Oracle Claim Packet\n\n## Oracle Response\n\n"
            "Here is a substantive claim: the finite verifier closes case 7 with sha256=abc123.\n",
            encoding="utf-8",
        )
        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if ok or "older than latest substantive Oracle claim" not in reason:
            raise AssertionError(
                "dispatch reused a handoff older than newest substantive Oracle claim: "
                f"ok={ok} reason={reason!r}"
            )

        time.sleep(0.02)
        for name in ("codex_workup.md", "next_oracle_question.md", "local_repair_report.md"):
            path = target_dir / name
            path.write_text(path.read_text(encoding="utf-8") + "\nRefreshed after claim.\n", encoding="utf-8")
        ok, reason = dispatch._pre_oracle_codex_workup_recent("demo", max_age_seconds=3600)
        if not ok:
            raise AssertionError(f"handoff refreshed after claim should pass: {reason}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
