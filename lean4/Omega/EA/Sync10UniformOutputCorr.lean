import Mathlib.Tactic
import Omega.EA.Sync10UniformInputOutput

namespace Omega.EA

open scoped BigOperators

/-- Exact lag-`n` joint law of the stationary output process, obtained by summing over the
initial state and over all length-`n + 1` uniform input words. -/
def sync10OutputLagPairProb (n : ℕ) (a b : Fin 2) : ℚ :=
  ∑ q, sync10UniformStationaryVector q *
    ∑ w : Fin (n + 1) → Fin 3,
      if sync10OutputBit q (w 0) = a ∧
          sync10OutputBit (sync10Run q ((List.ofFn w).take n)) (w (Fin.last n)) = b
      then (1 / (3 : ℚ) ^ (n + 1))
      else 0

/-- Exact one-step output-pair law under the verified stationary distribution and uniform input. -/
def sync10OutputPairProb (a b : Nat) : ℚ :=
  if ha : a < 2 then
    if hb : b < 2 then
      sync10OutputLagPairProb 1 ⟨a, ha⟩ ⟨b, hb⟩
    else
      0
  else
    0

/-- Exact stationary flip probability `P(e_{t+1} ≠ e_t)`. -/
def sync10FlipProb : ℚ :=
  sync10OutputPairProb 0 1 + sync10OutputPairProb 1 0

/-- Exact lag-`n` correlation of the stationary `{0,1}`-valued output process. Since
`P(e_t = 1) = 1 / 2`, the correlation is `4 P(e_t = 1, e_{t+n} = 1) - 1`. -/
def sync10OutputCorr (n : ℕ) : ℚ :=
  4 * sync10OutputLagPairProb n 1 1 - 1

/-- Exact two-step output-pair law, flip probability, and short-lag correlations for the
uniform-input `Sync10` output process.
    prop:sync10-uniform-output-corr -/
theorem paper_sync10_uniform_output_corr :
    sync10OutputPairProb 0 0 = 79 / 432 ∧ sync10OutputPairProb 1 1 = 79 / 432 ∧
      sync10OutputPairProb 0 1 = 137 / 432 ∧ sync10OutputPairProb 1 0 = 137 / 432 ∧
      sync10FlipProb = 137 / 216 ∧ sync10OutputCorr 1 = -29 / 108 ∧
      sync10OutputCorr 2 = -1 / 81 ∧ sync10OutputCorr 3 = -1 / 972 ∧
      sync10OutputCorr 4 = -5 / 1458 := by
  unfold sync10OutputPairProb sync10FlipProb sync10OutputCorr sync10OutputLagPairProb
  unfold sync10OutputBit sync10UniformStationaryVector
  native_decide

end Omega.EA
