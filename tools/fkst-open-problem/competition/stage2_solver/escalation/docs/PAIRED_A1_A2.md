# Paired guided/blind evaluation (A2/A1 cue-conditioning)

This is the paired experiment requested for the router-hypothesis collaboration: the same items,
run under two conditions differing only in whether the Lean verdict is provided as a cue.

## Design
- **Items**: the 175 deterministic-solver residuals (40 `sample_200` + 135 `hard2`) — every problem
  the zero-LLM solver left unsolved. Same set under both conditions.
- **A2 (cue-conditioned / "guided")**: codex is told the ground-truth verdict, then must produce a
  Lean certificate for it.
- **A1 (blind)**: codex is NOT told the verdict; it searches for a finite counterexample and/or a
  universal proof and keeps whichever the Lean judge accepts (judge as solve-time oracle).
- **Held fixed across conditions**: the residual set, the judge (commit `6805e232`,
  `DEFAULT_PROOF_POLICY`), the per-problem attempt budget class, the deterministic floor.
- Per-item records: `manifests/paired_guided_blind_manifest.jsonl` (id, set, truth, A2 status/verdict,
  A1 status/verdict, agreement). Aggregate: `results/paired_guided_blind.json`.

## Result
| | accepted / 175 |
|---|---|
| A2 guided (verdict cue) | 173 |
| A1 blind (no cue) | 174 |

Paired breakdown: **both 172, guided-only 1 (`hard2_0176`), blind-only 2 (`hard2_0027`, `hard2_0051`),
neither 0**. Net gap (guided − blind) = **−1**.

**Finding.** There is no measurable cost of blindness: the two conditions are statistically
indistinguishable. Providing the Lean verdict as a cue (A2) does not improve solve rate over blind
(A1), because the counterexample/proof search itself determines the verdict — deciding and certifying
are not separable steps here.

## Honest limits (must accompany the finding)
- **Ceiling saturation.** Both conditions sit at ~99% (173–174/175), so this paired design cannot
  resolve a small cue effect. The 3 differing items are within codex run-to-run stochasticity
  (6–8 attempts each), not a demonstrated systematic effect. Measuring a non-trivial gap requires a
  harder or larger item pool where neither condition saturates.
- **Relation to FiberRing A1/A2.** FiberRing measures *routing-to-proof-template* accuracy; this
  measures *solve rate* under the same cue-conditioning contrast. Same axis (verdict cue vs none),
  different dependent variable. A routing-accuracy version on this domain is future work.
- Guided (A2) totals remain an **upper bound** (see `HONEST_BOUNDARY.md`); local-runner scores only.
