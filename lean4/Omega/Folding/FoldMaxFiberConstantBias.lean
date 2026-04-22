import Mathlib.Tactic
import Omega.Folding.FoldCriticalResonanceConstant
import Omega.Folding.FoldMaxFiberFourier

namespace Omega

/-- Paper-facing constant-bias package for the fold max fiber: the Fourier lower bound gives the
mean-plus-bias decomposition, rewriting isolates the normalized bias as the max-minus-mean gap,
and the critical-resonance endpoint package supplies the nonnegative resonance constant. -/
def fold_max_fiber_constant_bias_statement (m : ℕ) : Prop :=
  foldMeanMultiplicity m ≤ Omega.X.maxFiberMultiplicity m ∧
    foldMeanMultiplicity m + foldMaxNontrivialFourierAmplitude m =
      Omega.X.maxFiberMultiplicity m ∧
    (Omega.X.maxFiberMultiplicity m : ℚ) - foldMeanMultiplicity m =
      foldMaxNontrivialFourierAmplitude m ∧
    0 ≤ foldMaxNontrivialFourierAmplitude m ∧
    0 ≤ Omega.Folding.foldCriticalResonanceReversedCosineProduct m

/-- Paper label: `cor:fold-max-fiber-constant-bias`. -/
theorem paper_fold_max_fiber_constant_bias (m : ℕ) : fold_max_fiber_constant_bias_statement m := by
  rcases paper_fold_max_fiber_fourier m with ⟨hMean, hGap, hNonneg⟩
  have hBias :
      (Omega.X.maxFiberMultiplicity m : ℚ) - foldMeanMultiplicity m =
        foldMaxNontrivialFourierAmplitude m := by
    unfold foldMaxNontrivialFourierAmplitude
    ring
  have hResonance : 0 ≤ Omega.Folding.foldCriticalResonanceReversedCosineProduct m := by
    by_cases hm : 1 ≤ m
    · exact (Omega.Folding.paper_fold_critical_resonance_constant m hm).2
    · have hm0 : m = 0 := by omega
      subst hm0
      simp [Omega.Folding.foldCriticalResonanceReversedCosineProduct]
  exact ⟨hMean, hGap, hBias, hNonneg, hResonance⟩

end Omega
