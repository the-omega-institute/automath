#!/usr/bin/env python3
"""Measure the v0 false-branch search on the official sample JSON files."""

import json
import sys
from pathlib import Path

# Keep submission/ pristine: the official runner rejects a submission dir that
# contains anything but solver.py, so do NOT let importing it drop __pycache__.
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).parent / "submission"))

import selfcheck
import solver


ROOT = Path("/tmp/eqt2-stage2/examples/problems")
PROBLEM_FILES = (ROOT / "sample_20.json", ROOT / "sample_200.json")


def load_problems():
    problems = []
    for path in PROBLEM_FILES:
        with path.open() as f:
            for problem in json.load(f):
                item = dict(problem)
                item["_source"] = path.name
                problems.append(item)
    return problems


def run_one(problem, use_linear):
    return solver.search_counterexample(problem["equation1"], problem["equation2"], use_linear=use_linear)


def main():
    problems = load_problems()
    failures = []
    brute_pass = {}
    full_pass = {}

    for problem in problems:
        brute = run_one(problem, use_linear=False)
        if brute is not None:
            ok = selfcheck.verify_counterexample(problem["equation1"], problem["equation2"], brute["table"])
            if ok:
                brute_pass[problem["id"]] = brute
            else:
                failures.append({"id": problem["id"], "source": problem["_source"], "stage": "brute"})

        full = run_one(problem, use_linear=True)
        if full is not None:
            ok = selfcheck.verify_counterexample(problem["equation1"], problem["equation2"], full["table"])
            if ok:
                full_pass[problem["id"]] = full
            else:
                failures.append({"id": problem["id"], "source": problem["_source"], "stage": full.get("stage", "unknown")})

    brute_only = len(brute_pass)
    false_solved = len(full_pass)
    linear_extra = sum(1 for problem_id, found in full_pass.items() if problem_id not in brute_pass and found["stage"] == "linear")
    affine_extra = sum(1 for problem_id, found in full_pass.items() if problem_id not in brute_pass and found["stage"] == "affine")

    print("SAIR-EQT2 stage2_solver v0 harness")
    print("problem files: " + ", ".join(str(path) for path in PROBLEM_FILES))
    print(f"total problems: {len(problems)}")
    print(f"false-solved-and-selfcheck-PASS: {false_solved}")
    print(f"brute-only Fin2-3: {brute_only}")
    print(f"brute+linear extra: {linear_extra}")
    print(f"brute+linear+affine extra: {affine_extra}")
    print(f"selfcheck FAILURES: {len(failures)}")
    if failures:
        print("failures:")
        for failure in failures:
            print(json.dumps(failure, sort_keys=True))
    print("stage details:")
    for problem_id in sorted(full_pass):
        found = full_pass[problem_id]
        detail = f"{problem_id}: {found['stage']} n={found['n']}"
        if found["stage"] == "linear":
            detail += f" a={found['a']} b={found['b']}"
        elif found["stage"] == "affine":
            detail += f" a={found['a']} b={found['b']} c={found['c']}"
        print(detail)

    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
