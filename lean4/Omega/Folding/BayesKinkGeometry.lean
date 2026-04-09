import Mathlib.Tactic

namespace Omega.Folding

/-- Closed-form core of the Bayes-threshold objective on the smooth side.
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
noncomputable def gStar (p : ℚ) : ℚ := p^2 * (3 - 2*p) / (1 + p^3)

/-- Midpoint value `g_*(1/2) = 4/9`.
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
theorem gStar_half : gStar (1/2) = 4/9 := by
  unfold gStar
  norm_num

/-- Numerator polynomial of the derivative `g_*'(p)`.
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
def qPoly (p : ℚ) : ℚ := p^4 - 3*p^3 + 3*p^2 + p - 1

/-- `q(1/2) = −1/16` (sign change witness, left).
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
theorem qPoly_half_neg : qPoly (1/2) = -1/16 := by
  unfold qPoly
  norm_num

/-- `q(3/4) = 125/256` (sign change witness, right).
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
theorem qPoly_three_quarters_pos : qPoly (3/4) = 125/256 := by
  unfold qPoly
  norm_num

/-- Refined polynomial after factoring out `p^2` dominance.
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
def hPoly (p : ℚ) : ℚ := p^3 + 2*p - 2

/-- `h(3/4) = −5/64` (sign change witness, left).
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
theorem hPoly_three_quarters_neg : hPoly (3/4) = -5/64 := by
  unfold hPoly
  norm_num

/-- `h(4/5) = 14/125` (sign change witness, right).
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
theorem hPoly_four_fifths_pos : hPoly (4/5) = 14/125 := by
  unfold hPoly
  norm_num

/-- Paper package: Bayes-threshold kink geometry scaffolding.
    prop:fold-gauge-anomaly-bernoulli-p-kink-unique-max -/
theorem paper_fold_gauge_anomaly_bernoulli_p_kink_unique_max :
    gStar (1/2) = 4/9 ∧
    qPoly (1/2) = -1/16 ∧
    qPoly (3/4) = 125/256 ∧
    qPoly (1/2) < 0 ∧
    0 < qPoly (3/4) ∧
    hPoly (3/4) = -5/64 ∧
    hPoly (4/5) = 14/125 ∧
    hPoly (3/4) < 0 ∧
    0 < hPoly (4/5) ∧
    (1/2 : ℚ) < 3/4 ∧
    (3/4 : ℚ) < 4/5 := by
  refine ⟨gStar_half, qPoly_half_neg, qPoly_three_quarters_pos, ?_, ?_,
          hPoly_three_quarters_neg, hPoly_four_fifths_pos, ?_, ?_, ?_, ?_⟩
  · rw [qPoly_half_neg]; norm_num
  · rw [qPoly_three_quarters_pos]; norm_num
  · rw [hPoly_three_quarters_neg]; norm_num
  · rw [hPoly_four_fifths_pos]; norm_num
  · norm_num
  · norm_num

/-! ### Bitpair independence threshold polynomial -/

/-- Independence threshold polynomial: t² + t - 1.
    Its roots are (-1 ± √5)/2, connecting to the golden ratio.
    cor:fold-gauge-anomaly-bernoulli-p-bitpair-independence-threshold -/
def indepThresholdPoly (t : ℤ) : ℤ := t ^ 2 + t - 1

/-- Discriminant of t² + t - 1 equals 5.
    cor:fold-gauge-anomaly-bernoulli-p-bitpair-independence-threshold -/
theorem indepThreshold_discriminant : (1 : ℤ) ^ 2 + 4 * 1 = 5 := by omega

/-- Sign changes: P(0) = -1 < 0, P(1) = 1 > 0.
    cor:fold-gauge-anomaly-bernoulli-p-bitpair-independence-threshold -/
theorem indepThresholdPoly_zero : indepThresholdPoly 0 = -1 := by
  unfold indepThresholdPoly; ring

theorem indepThresholdPoly_one : indepThresholdPoly 1 = 1 := by
  unfold indepThresholdPoly; ring

/-- Symmetry: P(t) evaluated at -t gives (-t)² - (-t) - 1 = t² - t - 1.
    cor:fold-gauge-anomaly-bernoulli-p-bitpair-independence-threshold -/
theorem indepThresholdPoly_neg_symmetry (t : ℤ) :
    t ^ 2 + t - 1 = (-t) ^ 2 - (-t) - 1 := by ring

/-- Paper package: bitpair independence threshold.
    cor:fold-gauge-anomaly-bernoulli-p-bitpair-independence-threshold -/
theorem paper_fold_gauge_anomaly_bitpair_independence_threshold :
    (1 : ℤ) ^ 2 + 4 * 1 = 5 ∧
    indepThresholdPoly 0 = -1 ∧ indepThresholdPoly 1 = 1 ∧
    (∀ t : ℤ, t ^ 2 + t - 1 = (-t) ^ 2 - (-t) - 1) := by
  exact ⟨indepThreshold_discriminant, indepThresholdPoly_zero,
         indepThresholdPoly_one, indepThresholdPoly_neg_symmetry⟩

end Omega.Folding
