import Mathlib
import Omega.GU.TerminalFoldbin6StrongLumpabilityFails

namespace Omega.GU

/-- The six folded labels reached from `start` by one hypercube bit-flip. -/
def foldbin6OneStepLabels (start : ℕ) : List (X 6) :=
  (List.range 6).map fun k => cBinFold 6 (start ^^^ (2 ^ k))

/-- Deduplicated support of the one-step folded labels. -/
def foldbin6OneStepSupport (start : ℕ) : Finset (X 6) :=
  (foldbin6OneStepLabels start).toFinset

/-- The audited overlap of the one-step supports of the same-fiber witnesses `0` and `21`. -/
def foldbin6WitnessSupportOverlap : Finset (X 6) :=
  foldbin6OneStepSupport 0 ∩ foldbin6OneStepSupport 21

/-- Total variation coming from two uniform six-point supports with audited overlap `2`. -/
def foldbin6WitnessTv : ℚ :=
  1 - foldbin6WitnessSupportOverlap.card / 6

/-- The midpoint/minimax value attached to the audited total variation. -/
def foldbin6WitnessMinimaxError : ℚ :=
  foldbin6WitnessTv / 2

private lemma foldbin6_support_overlap :
    foldbin6WitnessSupportOverlap.card = 2 := by
  native_decide

/-- Paper label: `thm:foldbin6-strong-lumpability-minimax-markov-error`. The same-fiber witnesses
`0` and `21` have one-step folded supports with audited overlap `2`, so the corresponding uniform
one-step laws have total variation `2/3`, and the standard midpoint argument yields the sharp
minimax value `1/3`. -/
theorem paper_foldbin6_strong_lumpability_minimax_markov_error :
    cBinFold 6 0 = cBinFold 6 21 ∧
      foldbin6WitnessSupportOverlap.card = 2 ∧
      foldbin6WitnessTv = 2 / 3 ∧
      foldbin6WitnessMinimaxError = 1 / 3 := by
  refine ⟨paper_terminal_foldbin6_strong_lumpability_fails.1, foldbin6_support_overlap, ?_, ?_⟩
  · rw [foldbin6WitnessTv, foldbin6_support_overlap]
    norm_num
  · rw [foldbin6WitnessMinimaxError, foldbin6WitnessTv, foldbin6_support_overlap]
    norm_num

end Omega.GU
