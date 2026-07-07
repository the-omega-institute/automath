# SAIR-EQT2 codex certificate task (judge-in-the-loop)

You produce a **Lean certificate** for one magma-implication problem and iterate it against the
**real official Lean judge** until the judge accepts it (or you exhaust attempts). Zero prose in the
final artifact — only the answer JSON file + a final status line.

## Repo / commands (run everything from this dir)
- Repo root: `/Users/lexa/Desktop/lexa/omega/eqt2-stage2`  (cd here first)
- Before verifying, once per shell: `source .env.judge`
- Verify a candidate:
  `.venv/bin/python verify_one.py <SPIKE>/<id>.json <SPIKE>/<id>.answer.json`
  where `<SPIKE>` = `/private/tmp/claude-501/-Users-lexa-Desktop-lexa-omega-automath/212fb8e9-b173-4c53-b415-65750bbe217b/scratchpad/spike`
  It prints one JSON line: `{"status": "...", "detail": "..."}`. **`status == "accepted"` is success.**
  Any other status (`incorrect`, `malformed`, `DISALLOWED_DECLARATIONS`, `incomplete`, ...) means fix and retry.
  `detail` on failure contains the FULL Lean error + goal state — use it.

## The problem
`<SPIKE>/<id>.json` = `{id, eq1_id, eq2_id, equation1, equation2}`. The magma op is written `◇`.
You will be told the **target verdict** (`true` or `false`). Prove exactly that.

## Answer file format
Write `<SPIKE>/<id>.answer.json` = exactly `{"verdict": "true"|"false", "code": "<lean source>"}` (JSON,
`code` is the full Lean file as a string with `\n`).

## TRUE certificate (universal proof — E1 ⇒ E2 for all magmas)
`import JudgeProblem` supplies `Goal`, `Magma`, `EquationLHS`, `EquationRHS`. The goal is
`∀ (G) [Magma G], EquationLHS G → EquationRHS G`. After `intro G _ h` you have `h : EquationLHS G`
(equation1 as a ∀-statement over G) and must prove `EquationRHS G` (equation2). Introduce E2's
variables, then derive it from `h` by equational rewriting.
Accepted example (problem: `x◇x = x◇y ⊢ x◇y = x◇z`):
```lean
import JudgeProblem

def submission : Goal := by
  intro G _ h
  intro x y z
  rw [← h, h]
```
Tactics available include `intro`, `rw [h ...]`, `rw [← h ...]`, `exact h ...`, `simp only [h]`,
`calc`, `.symm`, `.trans`. `h` can be specialized: `h a b c` instantiates its universally
quantified vars. Think of it as term rewriting in a free magma.

## FALSE certificate (finite-magma counterexample — a model where E1 holds, E2 fails)
Emit the operation as a Cayley table through `finOpTable` on `Fin n` with **n ≤ 10 and single-digit
entries only** (the multi-digit parser is broken; `Fin ≥ 11` is NOT reachable — do not attempt it,
and do NOT use arithmetic ops `+ * %`, they hit `DISALLOWED_DECLARATIONS`). Close with `decideFin!`.
Accepted example:
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
Search strategy: try all magma tables on `Fin 2`, then `Fin 3`, then `Fin 4` (you may brute-force in a
scratch Python script: enumerate n×n tables, keep one where equation1 holds for all assignments and
equation2 fails for some, then emit that table string). Keep the table single-digit (entries 0..9).

CRITICAL — the counterexample MUST be emitted via `finOpTable` on `Fin n` (as in the accepted example
above). Do NOT define a custom `inductive` carrier type or a standalone `def op` match: their
auto-generated declarations (`A.casesOn`, `A.ctorIdx`, `noConfusion`, `inferInstance`, ...) are NOT in
the allowlist and the judge rejects them with `incomplete_proof: disallowed declarations`. Only the
`finOpTable "<table string>"` encoding + `decideFin!` is accepted for FALSE certs.

## Allowed declarations (HARD — anything else → DISALLOWED_DECLARATIONS)
axioms: propext, Quot.sound, Classical.choice. declarations: letFun. prefixes:
And. Bool. Classical. Decidable. Eq. EquationLHS EquationRHS Goal Exists. False. Fin. Fintype.
Function. HEq. Iff. Init. Int. Lean. List. Magma. Mathlib. MemoFinOp. Nat. Nonempty. Not.
NthRewrites. OfNat. Option. Or. Prod. PUnit. RewriteCombinations. RewriteGoal. RewriteHypothesis.
RewriteHypothesisAndGoal. SimpleRewrites. Std. Subgraph. Subtype. Sum. Trans. True. Unit.
JudgeDecide. JudgeFinOp. JudgeMagma. inst of_decide_ submission. congrArg congr_arg eq_self
of_eq_true id eq_comm eq_mp eq_mpr rfl absurd.
(NOT allowed: HMul. HAdd. HMod. — no `+ * %` arithmetic in the op.)

## Limits
`code` ≤ 100000 chars; a FALSE cert ≤ 20000 bytes; each judge call ≤ 300s Lean time.

## Loop protocol (do this)
1. Write your best `<id>.answer.json`.
2. Run verify_one.py. If `accepted` → STOP, you are done.
3. Else read `detail`, fix the Lean (or, for FALSE, refine the counterexample search), rewrite the
   answer file, verify again. **Up to 6 attempts.**
4. If still not accepted after 6 attempts, leave your best attempt in `<id>.answer.json`.

## Final output (your last message — keep it SHORT)
Report exactly: `RESULT <id> status=<accepted|not-accepted> attempts=<n> verdict=<true|false>`
and, if not accepted, the last judge status + a one-line reason.
