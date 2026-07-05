#!/usr/bin/env python3
"""Verify ONE (problem, answer) against the official Lean judge.

Usage:  python3 verify_one.py <problem.json> <answer.json>
  problem.json : a single problem dict (id, eq1_id, eq2_id, equation1, equation2[, answer])
  answer.json  : raw judge answer  {"verdict": "true"|"false", "code": "<lean source>"}

Prints one JSON line: {"status": "...", "detail": "..."}.  status == "accepted" means the
certificate passed the full DEFAULT_PROOF_POLICY.  Run from the eqt2-stage2 repo root.
"""
import sys
import json
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from judge.verify import verify_answer, JudgeConfig  # noqa: E402

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

config = JudgeConfig(
    lake_bin=pathlib.Path("/Users/lexa/.elan/bin/lake"),
    lean_bin=pathlib.Path("/Users/lexa/.elan/bin/lean"),
)
problem = json.load(open(sys.argv[1]))
problem["proof_policy"] = problem.get("proof_policy") or DEFAULT_PROOF_POLICY
answer = open(sys.argv[2]).read()
result = verify_answer(problem, answer, config=config)
out = {"status": result.get("status"), "detail": result.get("detail") or result.get("message") or ""}
print(json.dumps(out))
