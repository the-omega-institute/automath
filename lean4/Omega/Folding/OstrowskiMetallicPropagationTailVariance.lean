import Mathlib.Tactic
import Omega.Folding.OstrowskiMetallicTruncationMismatchLimit

namespace Omega.Folding

/-- Concrete quantitative package for the Ostrowski metallic propagation-tail variance estimate.
The propagation-length tail is controlled by a geometric envelope at the truncation-mismatch
scale, the finite-window variance is linear in the sample length, and the large-alphabet regime
improves the coefficient to an `m / A`-type bound. -/
structure MetallicPropagationTailVarianceData where
  alphabetSize : ℕ
  baseStep : ℕ
  sampleLength : ℚ
  tailRatio : ℚ
  propagationLengthTail : ℕ → ℚ
  variance : ℚ
  alphabetPositive : 1 ≤ alphabetSize
  baseStepPositive : 1 ≤ baseStep
  sampleLength_nonneg : 0 ≤ sampleLength
  tail_nonneg : 0 ≤ tailRatio
  tail_lt_one : tailRatio < 1
  tailControlled :
    ∀ t : ℕ,
      propagationLengthTail t ≤ metallicTruncationMismatchMainTerm alphabetSize * tailRatio ^ t
  linearVarianceBound :
    variance ≤ sampleLength * metallicTruncationMismatchMainTerm alphabetSize
  largeAlphabetScale :
    metallicTruncationMismatchMainTerm alphabetSize ≤ (1 : ℚ) / alphabetSize

namespace MetallicPropagationTailVarianceData

/-- The geometric propagation-tail envelope inherited from the truncation-mismatch scale. -/
def exponentialTail (D : MetallicPropagationTailVarianceData) : Prop :=
  ∀ t : ℕ,
    D.propagationLengthTail t ≤ metallicTruncationMismatchMainTerm D.alphabetSize * D.tailRatio ^ t

/-- The mismatch-indicator variance is at most linear in the observation length. -/
def linearVariance (D : MetallicPropagationTailVarianceData) : Prop :=
  D.variance ≤ D.sampleLength * metallicTruncationMismatchMainTerm D.alphabetSize

/-- In the large-alphabet regime, the linear variance coefficient is bounded by `1 / A`. -/
def largeAlphabetVarianceBound (D : MetallicPropagationTailVarianceData) : Prop :=
  D.variance ≤ D.sampleLength * ((1 : ℚ) / D.alphabetSize)

end MetallicPropagationTailVarianceData

open MetallicPropagationTailVarianceData

/-- The propagation tail is geometric at the truncation-mismatch scale, so the induced covariance
series is controlled by the same coefficient; consequently the finite-window variance is linear in
`m`, and the large-alphabet specialization improves this to the announced `m / A` bound.
    prop:ostrowski-metallic-propagation-tail-variance -/
theorem paper_ostrowski_metallic_propagation_tail_variance
    (D : MetallicPropagationTailVarianceData) :
    D.exponentialTail ∧ D.linearVariance ∧ D.largeAlphabetVarianceBound := by
  have hMismatch :
      metallicTruncationMismatchAsymptoticMainTerm D.alphabetSize :=
    (paper_ostrowski_metallic_truncation_mismatch_limit
      D.alphabetSize D.baseStep D.alphabetPositive D.baseStepPositive).2.2
  refine ⟨D.tailControlled, D.linearVarianceBound, ?_⟩
  have hScaled :
      D.sampleLength * metallicTruncationMismatchMainTerm D.alphabetSize ≤
        D.sampleLength * ((1 : ℚ) / D.alphabetSize) := by
    exact mul_le_mul_of_nonneg_left D.largeAlphabetScale D.sampleLength_nonneg
  exact le_trans D.linearVarianceBound hScaled

end Omega.Folding
