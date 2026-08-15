#!/usr/bin/env python3
"""Run the artifact tests and archive a timing-free LF transcript."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


MODULES = (
    "artifacts.test_verify_a5_results",
    "artifacts.test_verify_twisted_determinant_rigidity",
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("unittest_output.txt"),
    )
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    display_command = "python -m unittest -v " + " ".join(MODULES)
    command = [sys.executable, "-m", "unittest", "-v", *MODULES]
    completed = subprocess.run(
        command,
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    transcript = completed.stdout + completed.stderr
    print(transcript, end="")
    stable_transcript = re.sub(
        r"^(Ran \d+ tests?) in [0-9.]+s$",
        r"\1",
        transcript.replace("\r\n", "\n"),
        flags=re.MULTILINE,
    )
    archive = (
        f"Python version: {sys.version.split()[0]}\n"
        f"command: {display_command}\n"
        "random seed: none (deterministic)\n\n"
        + stable_transcript
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(archive, encoding="utf-8", newline="\n")
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
