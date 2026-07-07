# SAIR-EQT2 codex certificate task — BLIND (verdict NOT given)

You produce a Lean certificate for one magma-implication problem `E1 ⇒ E2` and iterate it against
the real official Lean judge until accepted. **You are NOT told whether the answer is true or false —
you must determine it yourself.** Zero prose in the final artifact — only the answer JSON + a RESULT line.

## Repo / commands (run from repo root)
- Repo root: `/Users/lexa/Desktop/lexa/omega/eqt2-stage2` (cd here first)
- Once per shell: `source .env.judge`
- Verify a candidate:
  `.venv/bin/python verify_one.py <BLIND>/<id>.json <BLIND>/<id>.answer.json`
  where `<BLIND>` = `/private/tmp/claude-501/-Users-lexa-Desktop-lexa-omega-automath/212fb8e9-b173-4c53-b415-65750bbe217b/scratchpad/spike_blind`
  Prints `{"status": "...", "detail": "..."}`. **`status == "accepted"` is success.** `detail` on
  failure has the full Lean error/goal state.

## The problem
`<BLIND>/<id>.json` = `{id, eq1_id, eq2_id, equation1, equation2}` (magma op = `◇`). NO answer field.

## Answer file
Write `<BLIND>/<id>.answer.json` = `{"verdict": "true"|"false", "code": "<lean source>"}`.

## STRATEGY (how to decide the verdict yourself)
Run BOTH searches; keep whichever the judge accepts.
1. **First, try to DISPROVE (verdict=false).** Brute-force small finite magmas: enumerate n×n Cayley
   tables on `Fin 2`, `Fin 3`, `Fin 4`, `Fin 5` (write a scratch Python script). Look for a table where
   equation1 holds for ALL assignments but equation2 FAILS for some. If found, emit it via `finOpTable`
   on `Fin n` (single-digit entries, `decideFin!`) and verify — if accepted, verdict=false, DONE.
   (No custom `inductive` carrier — its `A.casesOn`/`ctorIdx` decls are disallowed. finOpTable ONLY.)
2. **If no counterexample turns up on Fin ≤ 5, try to PROVE (verdict=true).** The implication is likely
   universal: `intro G _ h; intro <vars>; <equational rewriting with h>` (rw / exact h.. / calc /
   congrArg / .symm). Often E1 forces a strong collapse — derive it and discharge E2. Verify — if
   accepted, verdict=true, DONE.
3. Alternate/iterate up to **8 total judge attempts** across both directions. Output only a judge-accepted
   certificate. If none passes in 8 attempts, leave your best attempt and report not-accepted.

## Certificate forms
TRUE (universal proof):
```lean
import JudgeProblem
def submission : Goal := by
  intro G _ h
  intro x y z
  rw [← h, h]
```
FALSE (finite counterexample):
```lean
import JudgeProblem
import JudgeDecide.DecideBang
import JudgeFinOp.MemoFinOp
open MemoFinOp
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
def submission : Goal := by
  let m : Magma (Fin 2) := { op := finOpTable "[[1, 1], [0, 0]]" }
  refine ⟨Fin 2, m, ?_⟩
  decideFin!
```

## Allowed declarations (anything else → DISALLOWED_DECLARATIONS)
axioms: propext, Quot.sound, Classical.choice. decl: letFun. prefixes: And. Bool. Classical. Decidable.
Eq. EquationLHS EquationRHS Goal Exists. False. Fin. Fintype. Function. HEq. Iff. Init. Int. Lean. List.
Magma. Mathlib. MemoFinOp. Nat. Nonempty. Not. NthRewrites. OfNat. Option. Or. Prod. PUnit.
RewriteCombinations. RewriteGoal. RewriteHypothesis. RewriteHypothesisAndGoal. SimpleRewrites. Std.
Subgraph. Subtype. Sum. Trans. True. Unit. JudgeDecide. JudgeFinOp. JudgeMagma. inst of_decide_
submission. congrArg congr_arg eq_self of_eq_true id eq_comm eq_mp eq_mpr rfl absurd.
(NOT allowed: HMul. HAdd. HMod. — no `+ * %` arithmetic in the op; no custom inductive carriers.)

## Limits
code ≤ 100000 chars; FALSE cert ≤ 20000 bytes; each judge call ≤ 300s.

## Final output (last message, SHORT)
`RESULT <id> status=<accepted|not-accepted> verdict=<true|false> attempts=<n>`
