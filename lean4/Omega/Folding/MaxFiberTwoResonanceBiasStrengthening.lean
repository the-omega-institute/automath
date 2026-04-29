import Mathlib
import Omega.Folding.FoldMaxFiberFourier

open Filter
open scoped Topology

namespace Omega

noncomputable section

/-- Concrete two-resonance packaging of the max-fiber Fourier gap. The two retained Fibonacci
resonance terms each carry half of the extremal Fourier amplitude, while `normalizedBias`
records their combined normalized contribution on the real line. -/
structure FoldMaxFiberTwoResonanceBiasStrengtheningData where
  resonance₁ : ℕ → ℚ
  resonance₂ : ℕ → ℚ
  normalizedBias : ℕ → ℝ
  resonanceLimit : ℕ → ℝ
  hResonance₁ : ∀ m, resonance₁ m = foldMaxNontrivialFourierAmplitude m / 2
  hResonance₂ : ∀ m, resonance₂ m = foldMaxNontrivialFourierAmplitude m / 2
  hNormalizedBias : ∀ m, normalizedBias m = (resonance₁ m + resonance₂ m : ℚ)
  hEventually : normalizedBias =ᶠ[atTop] resonanceLimit
  hLimitNonneg : 0 ≤ liminf resonanceLimit atTop

namespace FoldMaxFiberTwoResonanceBiasStrengtheningData

/-- Pointwise strengthening of the max-fiber Fourier lower bound after keeping only the two
distinguished Fibonacci resonance terms and rewriting them as a normalized bias. -/
def pointwiseBound (D : FoldMaxFiberTwoResonanceBiasStrengtheningData) : Prop :=
  ∀ m,
    foldMeanMultiplicity m ≤ Omega.X.maxFiberMultiplicity m ∧
      foldMeanMultiplicity m + (D.resonance₁ m + D.resonance₂ m) =
        Omega.X.maxFiberMultiplicity m ∧
      D.normalizedBias m = (D.resonance₁ m + D.resonance₂ m : ℚ) ∧
      0 ≤ D.normalizedBias m

/-- Liminf transfer for the normalized two-resonance bias. -/
def liminfBound (D : FoldMaxFiberTwoResonanceBiasStrengtheningData) : Prop :=
  0 ≤ liminf D.normalizedBias atTop

end FoldMaxFiberTwoResonanceBiasStrengtheningData

open FoldMaxFiberTwoResonanceBiasStrengtheningData

/-- Reuse the existing max-fiber Fourier lower bound, keep only the two retained Fibonacci
resonance terms, rewrite them as a normalized bias, and transfer the nonnegative liminf through
the eventual resonance-limit identification.
    thm:fold-max-fiber-two-resonance-bias-strengthening -/
theorem paper_fold_max_fiber_two_resonance_bias_strengthening
    (h : FoldMaxFiberTwoResonanceBiasStrengtheningData) : h.pointwiseBound ∧ h.liminfBound := by
  refine ⟨?_, ?_⟩
  · intro m
    rcases paper_fold_max_fiber_fourier m with ⟨hMean, hGap, hNonneg⟩
    have hSplit : h.resonance₁ m + h.resonance₂ m = foldMaxNontrivialFourierAmplitude m := by
      rw [h.hResonance₁ m, h.hResonance₂ m]
      ring
    refine ⟨hMean, ?_, h.hNormalizedBias m, ?_⟩
    · calc
        foldMeanMultiplicity m + (h.resonance₁ m + h.resonance₂ m)
            = foldMeanMultiplicity m + foldMaxNontrivialFourierAmplitude m := by rw [hSplit]
        _ = Omega.X.maxFiberMultiplicity m := hGap
    · rw [h.hNormalizedBias m, hSplit]
      exact_mod_cast hNonneg
  · unfold FoldMaxFiberTwoResonanceBiasStrengtheningData.liminfBound
    rw [show liminf h.normalizedBias atTop = liminf h.resonanceLimit atTop by
      exact liminf_congr h.hEventually]
    exact h.hLimitNonneg

end

end Omega
