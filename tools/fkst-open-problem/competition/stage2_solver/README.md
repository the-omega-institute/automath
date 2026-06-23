# SAIR-EQT2 Stage 2 Solver v0

Zero-LLM, zero-token Solo-track solver for the SAIR Mathematics Distillation
Challenge — Equational Theories Stage 2 (`SAIRcompetition/equational-theories-lean-stage2`).
It decides magma implication problems `E1 ⇒ E2` on two fronts, both machine-checked by
the official Lean judge: **false** via a finite-magma witness (Cayley table through
`finOpTable`), and **true** via a singleton or substitution-instance (Birkhoff) proof.
Implications it can't settle are left unanswered (no guessing).

## Layout

- `submission/solver.py` — **the competition submission**. The official runner
  requires the submission directory to contain **only `solver.py`**; that is why
  it lives in its own clean subdir. Single file, stdlib-only.
- `harness.py`, `selfcheck.py` — **local dev tools, NOT part of the submission.**
  Keep them out of `submission/`.
- `.gitignore` — ignores `__pycache__/`.

## Search strategy (`solver.py`)

**False branch** (finite-magma counterexample, all emitted via `finOpTable`, `Fin ≤ 10`):
1. Exhaustive brute force over all magma tables on `Fin 2` and `Fin 3`.
2. Linear prime-field magmas `x ◇ y = (a·x + b·y) mod p`, `PRIMES = (2, 3, 5, 7)`
   (clamped to `Fin ≤ 10` — `finOpTable`'s multi-digit parser bug rejects larger
   carriers, and `Fin ≥ 11` is not contestant-reachable; see `SUBSTRATE_NOTES.md`).
3. F₂² (`Fin 4`) matrix-linear magmas `x ◇ y = A·x + B·y` over the 𝔽₂² vector space —
   a 2-D generalization of scalar-linear; the source of the official `hard2` +9.

**True branch** (universal proof, no LLM, no finite check):
4. **singleton** — `E1` of the form `x = <term without x>` collapses the magma to one
   element, so every `E2` follows.
5. **substitution-instance (Birkhoff)** — if `E2` is a first-order substitution instance
   of `E1`, the implication is a direct `exact h <σ-args>` (the source of `sample_200` +45).

If no stage produces a Lean-checkable certificate, the solver exits without a verdict
(no fabricated answers).

## Results

### Authoritative — a local clone of the official runner (zero LLM, zero tokens)

> Precision: scores below were produced by a **local clone** of the upstream
> `pipeline.runner`/Lean judge, not a hosted/official submission. The clone lived in
> `/tmp/eqt2-stage2` and was purged by OS cleanup, so its exact judge commit SHA is **not
> retained** — these are reproducible-in-principle local snapshots, not leaderboard or
> officially-endorsed results. See `official_results/README.md`.

```bash
# one-time: bash /tmp/eqt2-stage2/scripts/setup.sh   (builds local Lean judge)
cd /tmp/eqt2-stage2 && source .env.judge
rm -f pipeline/results/submission.json   # IMPORTANT: results file accumulates; clear it
python3 -m pipeline.runner --submission <abs-path>/submission \
  --problems examples/problems/<file>
```

All zero-LLM / zero-token, accepted by the official local Lean judge. The
certificate prepends `set_option maxRecDepth 1000000 in` + `maxHeartbeats 1000000 in`
(lifts `decideFin!`'s recursion/heartbeat budget for larger carriers).

Scores below are from the **official `pipeline.runner`** (full `DEFAULT_PROOF_POLICY`,
including `allowed_declarations`), run with `PYTHONDONTWRITEBYTECODE=1` (the runner
imports `solver.py` in-process; a stray `__pycache__` makes it reject every later
problem). The raw result JSONs are committed under `official_results/`.

| problem set | official Lean-accepted | baseline | note |
|---|---|---|---|
| `sample_200` | **160 / 200** | 115 | **+45**, all from the substitution true-proof stage (`official_results/sample200_final.json`) |
| `hard2`      | **65 / 200**  | 56  | **+9**, the F₂² matrix-linear stage emitted via `finOpTable` (`official_results/hard2_final.json`) |
| `sample_20`  | not re-run    | 14  | judge env was wiped (see below) before re-verification |
| `hard1`      | not re-run    | 21  | same |
| `hard3`      | not re-run    | —   | same |

**Honest provenance note (2026-06-23).** Earlier drafts of this file claimed
`sample_200 160 / hard2 68 / hard1 23` from a *local* measure harness (`measure_b.py`)
that injected only `allowed_axioms` and **omitted `allowed_declarations`**, so it was
more permissive than the official judge. Two corrections followed, both via the official
runner:

1. **The `Fin ≥ 11` "arithmetic-op unlock" was a measurement artifact.** A closed-form
   op `fun i j => ⟨(a*i+b*j) % n, …⟩` uses `HMul./HAdd./HMod./id/LT.lt`, none of which are
   in the official `allowed_declaration_prefixes`. The official runner rejects it with
   `DISALLOWED_DECLARATIONS`. Worse, switching the *whole* F_p linear stage from
   `finOpTable` to arithmetic **regressed `hard2` to 23/200** (only brute `Fin 2–3`
   survived). Reverted: all false certs go back through `finOpTable` and `PRIMES` is
   clamped to `(2,3,5,7)` (Fin ≤ 10, where `finOpTable`'s multi-digit bug never bites).
   `Fin ≥ 11` is genuinely **not reachable** contestant-side (the `finOpTable` parse bug
   and the declaration allowlist block it from both directions).
2. **The real, official-verified gains** are the **substitution-instance Birkhoff
   true-proof** (`sample_200` 115→160) and the **F₂² (Fin 4) matrix-linear** false class,
   emitted as a `finOpTable` table (`hard2` 56→65). Both are zero-LLM and pass the full
   official policy.

`sample_20`/`hard1`/`hard3` were not re-verified against the official runner before the
local `/tmp` judge clone was purged by macOS's 3-day cleanup, so their current-solver
numbers are unknown; do **not** quote the old measure-harness figures for them.

Two no-LLM stages, both Lean-judge-verified. Every certificate is emitted through
`finOpTable` (`Fin ≤ 10`, single-digit tables — the multi-digit `extractDigits` bug
never bites) and the proof closes with `decideFin!`:

- **false branch** — finite-magma counterexamples. Brute `Fin 2–3` (arbitrary tables)
  + the F_p **linear** scan `x ◇ y = (a·x + b·y) mod p`, `PRIMES = (2,3,5,7)`
  + the **F₂² (Fin 4) matrix-linear** class `x ◇ y = A·x + B·y` over the vector space
  𝔽₂² ≅ Fin 4 (a genuine 2-D generalization of scalar-linear; its 4×4 table is emitted
  via `finOpTable`). The F₂² class is the source of the official `hard2` 56→65 (+9).
- **true branch** — (1) **singleton**: `E1` of the form `x = <term without x>` forces a
  one-element magma, so every `E2` follows; (2) **substitution-instance (Birkhoff)**:
  if `E2` is a first-order substitution instance of `E1 = l = r` (some σ with
  `E2 = lσ = rσ`), the universal implication is `intro G _ h; intro …; exact h <σ-args>`
  (or `.symm`). This is a true ∀-over-all-carriers proof (not a finite check), zero-LLM,
  zero-axiom — it is the source of the official `sample_200` 115→160 (+45).

Why `decideFin!` is false-only: the judge's true `Goal` is `∀ (G) [Magma G], …` —
universal over *every* carrier and operation. `decideFin!` only evaluates a fixed
`Fin n`, so it can refute (exhibit one bad model) but can never *prove* a universal
implication; true verdicts need a real Birkhoff-style derivation (the substitution stage).

Pure-Python self-check passes a counterexample iff it is mathematically valid; it
is necessary but NOT sufficient — only the official Lean judge's verdict is the score.

### Local pure-Python self-check, `sample_20.json` + `sample_200.json`

```bash
python3 harness.py
```

- total problems: 220
- false-solved-and-selfcheck-PASS: 108
- brute-only Fin2-3: 104
- brute+linear extra: 4  ← counterexamples only the F_p linear layer finds
- selfcheck FAILURES: 0

`selfcheck.py` enumerates all assignments over `Fin n`: equation 1 must hold for
every assignment and equation 2 must fail for at least one, and the table must be
a valid `n×n` magma. It is a pure-Python pre-filter; the Lean judge is the
authoritative gate.

## Scope and claims

False (finite-magma counterexample) + true (singleton / substitution-instance) only;
no general true-proof search, no LLM, no network. The unsolved remainder is dominated by
true implications needing a real equational-reasoning engine, which this solver does not
attempt. The authoritative score is the **official `pipeline.runner`** number
(`sample_200` 160/200, `hard2` 65/200; see `official_results/`), NOT the local
`measure_b.py` harness — that harness omitted the official `allowed_declarations` policy
and produced inflated false positives (see `SUBSTRATE_NOTES.md`). Do not claim
`accepted`/`scored` for any problem the official judge has not confirmed, do not quote the
old measure-harness numbers, and do not claim the submission is registered or submitted —
registration and upload require the user's account and are not done automatically
(`FKST_GITHUB_WRITE=0`).

**Must-not-claim (explicit boundary).** Do not state or imply any of:
- that `sample_200 160/200` or `hard2 65/200` are leaderboard / officially-registered
  results — they are *local* official-runner snapshots only;
- that this solver decides general equational-theory implications — it only settles
  **false** (finite-magma) + **true** (singleton / substitution-instance Birkhoff); the
  rest is left unanswered;
- that `Fin ≥ 11` counterexamples are reachable — they are blocked from both sides
  (`finOpTable` parse bug + the official `allowed_declarations` allowlist);
- any `measure_b.py` number as a score (it omits `allowed_declarations` → inflated);
- a current-solver number for `sample_20` / `hard1` / `hard3` — those were not re-verified
  before the judge env was wiped (status: unknown);
- that the submission was solved/uploaded/ranked.
