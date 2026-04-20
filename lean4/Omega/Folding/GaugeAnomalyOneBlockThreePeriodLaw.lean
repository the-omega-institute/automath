import Mathlib.Tactic
import Omega.Folding.BernoulliPEndpointExactFinite

namespace Omega.Folding

/-- Probability of the cylinder event `1^(3k+r+1)` along the explicit mismatch three-cycle. -/
def foldGaugeAnomalyOneBlockProb (k r : ℕ) : ℚ :=
  (1 / 8 : ℚ) ^ k * fullMismatchResidueValue (4 / 9 : ℚ) (1 / 4 : ℚ) (1 / 9 : ℚ) r

/-- The mismatch-labelled one-block law splits into three residue classes modulo `3`. The first
two block probabilities come from the stationary distribution, and each extra triple of `1`s
multiplies the corresponding class by `1/8`. The conditional one-step extensions are obtained by
dividing consecutive classes. `prop:fold-gauge-anomaly-one-block-three-period-law` -/
theorem paper_fold_gauge_anomaly_one_block_three_period_law :
    foldGaugeAnomalyOneBlockProb 0 0 = 4 / 9 ∧
      foldGaugeAnomalyOneBlockProb 0 1 = 1 / 4 ∧
      (∀ k, foldGaugeAnomalyOneBlockProb k 0 = (4 / 9 : ℚ) * (1 / 8 : ℚ) ^ k) ∧
      (∀ k, foldGaugeAnomalyOneBlockProb k 1 = (1 / 4 : ℚ) * (1 / 8 : ℚ) ^ k) ∧
      (∀ k, foldGaugeAnomalyOneBlockProb k 2 = (1 / 9 : ℚ) * (1 / 8 : ℚ) ^ k) ∧
      (∀ k r, r < 3 →
        foldGaugeAnomalyOneBlockProb (k + 1) r = (1 / 8 : ℚ) * foldGaugeAnomalyOneBlockProb k r) ∧
      (∀ k, foldGaugeAnomalyOneBlockProb (k + 1) 0 / foldGaugeAnomalyOneBlockProb k 2 = 1 / 2) ∧
      (∀ k, foldGaugeAnomalyOneBlockProb k 1 / foldGaugeAnomalyOneBlockProb k 0 = 9 / 16) ∧
      (∀ k, foldGaugeAnomalyOneBlockProb k 2 / foldGaugeAnomalyOneBlockProb k 1 = 4 / 9) := by
  refine ⟨by norm_num [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue], by
    norm_num [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, mul_comm]
  · intro k
    simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, mul_comm]
  · intro k
    simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, mul_comm]
  · intro k r hr
    interval_cases r
    · simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, pow_succ, mul_comm]
      ring
    · simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, pow_succ, mul_comm]
      ring
    · simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, pow_succ, mul_comm]
      ring
  · intro k
    simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, pow_succ, div_eq_mul_inv,
      mul_assoc, mul_comm]
    field_simp
    norm_num
  · intro k
    simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, div_eq_mul_inv, mul_assoc,
      mul_comm]
    field_simp
    norm_num
  · intro k
    simp [foldGaugeAnomalyOneBlockProb, fullMismatchResidueValue, div_eq_mul_inv, mul_assoc,
      mul_comm]

end Omega.Folding
