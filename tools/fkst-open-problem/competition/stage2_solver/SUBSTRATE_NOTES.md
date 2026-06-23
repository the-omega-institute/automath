# Suspected judge-substrate issue — `finOpTable` multi-digit table parsing

**Status:** recorded locally for user review. NOT filed upstream (per project rule:
suspected FKST/judge substrate issues are recorded and confirmed with the user
before any upstream report).

**Where:** `judge/JudgeFinOp/MemoFinOp.lean` in
`SAIRcompetition/equational-theories-lean-stage2` (cloned at `/tmp/eqt2-stage2`).

**The code:**

```lean
private def extractDigits (s : String) : List Nat :=
  s.toList.filterMap fun c =>
    if c.isDigit then some (c.toNat - '0'.toNat) else none

def finOpTable (s : String) (i j : Fin n) : Fin n :=
  let vals := extractDigits s
  let idx := i.val * n + j.val
  ⟨(vals.getD idx 0) % n, …⟩
```

**The bug:** `extractDigits` keeps **each digit character** as its own list entry.
For a Cayley table whose entries can reach `n-1 ≥ 10` (i.e. `Fin n` with `n ≥ 11`),
a value like `10` becomes two entries `1, 0`. The resulting `vals` list is longer
than `n²` and every index past the first multi-digit value is misaligned, so the
magma the judge builds is **not** the table the solver intended.

**Observed effect:** false-witnesses on `Fin ≤ 10` verify correctly; on `Fin ≥ 11`
they are rejected as `incorrect` with
`Tactic decide proved that the proposition EquationLHS (Fin 11) ∧ ¬EquationRHS (Fin 11) is false`.
Our `Fin 11`/`Fin 13` counterexamples are mathematically valid — two independent
Python evaluators (the solver's algebraic test and a from-scratch full-assignment
enumerator) both confirm eq1 holds for all assignments and eq2 fails for some.
Example: `hard2_0088`, linear magma `x◇y=(4x+8y) mod 11`, rejected though valid.

**`Fin ≥ 11` is genuinely NOT reachable contestant-side — both routes are blocked
(verified against the official runner, 2026-06-23).** An intermediate "arithmetic-op
unlock" idea was tried and **reverted** after the official judge disproved it; recorded
here so it isn't retried:

- *Tried:* emit the op as a closed form `fun i j => ⟨(a·i.val + b·j.val) % n, …⟩` instead
  of a `finOpTable` table, to dodge the multi-digit String-parse bug.
- *Why it looked like it worked:* the local `measure_b.py` harness injected only
  `allowed_axioms` and **omitted `allowed_declarations`**, so it was more permissive than
  the official judge and reported these certs `accepted` at `Fin 11`.
- *Why it actually fails:* the official `DEFAULT_PROOF_POLICY` (`pipeline/proxy.py`)
  enforces an `allowed_declaration_prefixes` list that has `Nat./Fin./MemoFinOp./…` but
  **not `HMul./HAdd./HMod.`**, nor bare `id`/`LT.lt`. The arithmetic op references those
  (via `*`, `+`, `%`, and `Nat.mod_lt`'s `<`), so the official runner rejects it with
  `DISALLOWED_DECLARATIONS`. `finOpTable` passes only because it hides all of that arithmetic
  *inside* the allow-listed `MemoFinOp.finOpTable` body — the submission references just the
  one allow-listed name. The list-based `magmaFin`/`[list].getD` routes also fail (they pull
  `propext`); a `namespace submission … end` wrapper collides with the harness's own
  `def submission`.
- *Damage it caused:* switching the **whole** F_p linear stage to the arithmetic op didn't
  just fail `Fin ≥ 11` — it broke the previously-passing `finOpTable` linear certs too,
  collapsing official `hard2` from ~56 to **23/200** (brute `Fin 2-3` only).
- *Fix:* reverted — all false certs go back through `finOpTable`, `PRIMES` clamped to
  `(2,3,5,7)` (Fin ≤ 10, no multi-digit bug). Official `hard2` recovered to **65/200**
  (the F₂² Fin-4 matrix-linear class, also emitted via `finOpTable`, adds +9 over the ~56
  baseline). So the only durable lesson about `Fin ≥ 11` is: the `extractDigits` upstream
  bug is real and worth reporting, but there is **no contestant-side route** around it for
  large carriers — confirmed from both the parser side and the declaration-allow-list side.

**Measure correctly:** use the official `pipeline.runner` with the full `DEFAULT_PROOF_POLICY`
and `PYTHONDONTWRITEBYTECODE=1` (a stray `__pycache__` makes the runner reject the
submission). The local `measure_b.py` was the source of the false positives above; only the
official runner's verdict counts. Committed official result JSONs are under `official_results/`.
