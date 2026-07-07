#!/usr/bin/env python3
"""Verify ONE (problem, answer) against the official Lean judge.

Usage:  python3 verify_one.py --judge-root <path> <problem.json> <answer.json>
  problem.json : a single problem dict (id, eq1_id, eq2_id, equation1, equation2[, answer])
  answer.json  : raw judge answer  {"verdict": "true"|"false", "code": "<lean source>"}

Prints one JSON line: {"status": "...", "detail": "..."}.  status == "accepted" means the
certificate passed the full DEFAULT_PROOF_POLICY.
"""
import argparse
import json
import pathlib
import sys

# Mirror the OFFICIAL runner (pipeline/proxy.py): when a problem carries no
# proof_policy, inject DEFAULT_PROOF_POLICY. Without this, verify_answer defaults
# to empty allowed_axioms + no declaration check, which is BOTH too strict
# (rejects finOpTable's propext/Quot.sound/Classical.choice) and too lax
# (skips the declaration allowlist) vs the real judge.
DEFAULT_PROOF_POLICY = {
    "allowed_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "allowed_declarations": ["letFun"],
    "allowed_declaration_prefixes": [
        "And.", "Bool.", "Classical.", "Decidable.", "Eq.",
        "EquationLHS", "EquationRHS", "Goal", "Exists.", "False.",
        "Fin.", "Fintype.", "Function.", "HEq.", "Iff.", "Init.", "Int.", "Lean.",
        "List.", "Magma.", "Mathlib.", "MemoFinOp.", "Nat.", "Nonempty.", "Not.",
        "NthRewrites.", "OfNat.", "Option.", "Or.", "Prod.", "PUnit.",
        "RewriteCombinations.", "RewriteGoal.", "RewriteHypothesis.",
        "RewriteHypothesisAndGoal.", "SimpleRewrites.",
        "Std.", "Subgraph.", "Subtype.", "Sum.",
        "Trans.", "True.", "Unit.",
        "JudgeDecide.", "JudgeFinOp.", "JudgeMagma.",
        "inst", "of_decide_", "submission.",
        "congrArg", "congr_arg", "eq_self", "of_eq_true", "id",
        "eq_comm", "eq_mp", "eq_mpr", "rfl", "absurd",
    ],
}


def build_parser():
    parser = argparse.ArgumentParser(
        description="Verify one SAIR-EQT2 certificate against a local judge checkout."
    )
    parser.add_argument("--judge-root", required=True, type=pathlib.Path,
                        help="Local checkout of equational-theories-lean-stage2.")
    parser.add_argument("--work-dir", type=pathlib.Path,
                        help="Accepted for CLI symmetry; not used by this verifier.")
    parser.add_argument("--results-ref", type=pathlib.Path,
                        help="Accepted for CLI symmetry; not used by this verifier.")
    parser.add_argument("--parallel", type=int, default=5,
                        help="Accepted for CLI symmetry; not used by this verifier.")
    parser.add_argument("--timeout", type=int, default=1500,
                        help="Accepted for CLI symmetry; not used by this verifier.")
    parser.add_argument("--venv-python", default=None,
                        help="Accepted for CLI symmetry; not used by this verifier.")
    parser.add_argument("--lake-bin", type=pathlib.Path, default=None,
                        help="Path to lake. Default: resolved from PATH by judge config.")
    parser.add_argument("--lean-bin", type=pathlib.Path, default=None,
                        help="Path to lean. Default: resolved from PATH by judge config.")
    parser.add_argument("problem_json", type=pathlib.Path)
    parser.add_argument("answer_json", type=pathlib.Path)
    return parser


def main():
    args = build_parser().parse_args()
    judge_root = args.judge_root.resolve()
    sys.path.insert(0, str(judge_root))

    from judge.verify import JudgeConfig, verify_answer  # noqa: WPS433

    config_kwargs = {}
    if args.lake_bin is not None:
        config_kwargs["lake_bin"] = args.lake_bin
    if args.lean_bin is not None:
        config_kwargs["lean_bin"] = args.lean_bin
    config = JudgeConfig(**config_kwargs)

    problem = json.load(open(args.problem_json))
    problem["proof_policy"] = problem.get("proof_policy") or DEFAULT_PROOF_POLICY
    answer = open(args.answer_json).read()
    result = verify_answer(problem, answer, config=config)
    out = {"status": result.get("status"), "detail": result.get("detail") or result.get("message") or ""}
    print(json.dumps(out))


if __name__ == "__main__":
    main()
