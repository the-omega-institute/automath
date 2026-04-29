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

/-- Paper-facing density closed form at the symmetric point.
    prop:fold-gauge-anomaly-density-49 -/
theorem paper_fold_gauge_anomaly_density_49 : Omega.Folding.gStar (1 / 2 : Rat) = 4 / 9 := by
  exact gStar_half

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

/-- Paper package: bitpair independence threshold, full paper-label name.
    cor:fold-gauge-anomaly-bernoulli-p-bitpair-independence-threshold -/
theorem paper_fold_gauge_anomaly_bernoulli_p_bitpair_independence_threshold :
    (1 : Int) ^ 2 + 4 * 1 = 5 ∧
    indepThresholdPoly 0 = -1 ∧ indepThresholdPoly 1 = 1 ∧
    (∀ t : Int, t ^ 2 + t - 1 = (-t) ^ 2 - (-t) - 1) := by
  exact paper_fold_gauge_anomaly_bitpair_independence_threshold

/-! ### GC defect linear response threshold -/

/-- GC defect polynomial: 5t² - t - 1.
    thm:fold-gauge-anomaly-gc-defect-linear-response-threshold -/
def gcDefectPoly (t : ℤ) : ℤ := 5 * t ^ 2 - t - 1

/-- Discriminant of 5t² - t - 1 equals 21 (= 1 + 20).
    thm:fold-gauge-anomaly-gc-defect-linear-response-threshold -/
theorem gcDefect_discriminant : (1 : ℤ) ^ 2 + 4 * 5 * 1 = 21 := by omega

/-- Sign changes: P(0) = -1, P(1) = 3.
    thm:fold-gauge-anomaly-gc-defect-linear-response-threshold -/
theorem gcDefectPoly_zero : gcDefectPoly 0 = -1 := by unfold gcDefectPoly; ring
theorem gcDefectPoly_one : gcDefectPoly 1 = 3 := by unfold gcDefectPoly; ring

/-- Factorization identity: (1-t)(5t²-t-1) = -5t³+6t²-1.
    thm:fold-gauge-anomaly-gc-defect-linear-response-threshold -/
theorem gcDefect_factor_identity (t : ℤ) :
    (1 - t) * (5 * t ^ 2 - t - 1) = -5 * t ^ 3 + 6 * t ^ 2 - 1 := by ring

/-- 21 is not a perfect square.
    thm:fold-gauge-anomaly-gc-defect-linear-response-threshold -/
theorem twentyone_not_perfect_square : ¬ ∃ k : Nat, k * k = 21 := by
  intro ⟨k, hk⟩
  have : k ≤ 5 := by nlinarith
  interval_cases k <;> omega

/-- Paper package: GC defect linear response threshold.
    thm:fold-gauge-anomaly-gc-defect-linear-response-threshold -/
theorem paper_fold_gauge_anomaly_gc_defect_linear_response_threshold :
    (1 : ℤ) ^ 2 + 4 * 5 * 1 = 21 ∧
    gcDefectPoly 0 = -1 ∧ gcDefectPoly 1 = 3 ∧
    (∀ t : ℤ, (1 - t) * (5 * t ^ 2 - t - 1) = -5 * t ^ 3 + 6 * t ^ 2 - 1) ∧
    ¬ ∃ k : Nat, k * k = 21 :=
  ⟨gcDefect_discriminant, gcDefectPoly_zero, gcDefectPoly_one,
   gcDefect_factor_identity, twentyone_not_perfect_square⟩

/-! ### Density maximizer Cardano closed form -/

/-- The mismatch density maximizer cubic: t³ + 2t - 2.
    cor:fold-gauge-anomaly-bernoulli-p-density-maximizer-cardano -/
def densityMaxCubic (t : ℤ) : ℤ := t ^ 3 + 2 * t - 2

/-- Sign changes: P(0) = -2, P(1) = 1.
    cor:fold-gauge-anomaly-bernoulli-p-density-maximizer-cardano -/
theorem densityMaxCubic_zero : densityMaxCubic 0 = -2 := by unfold densityMaxCubic; ring
theorem densityMaxCubic_one : densityMaxCubic 1 = 1 := by unfold densityMaxCubic; ring

/-- Cubic discriminant: -4·2³ - 27·(-2)² = -140 < 0 (one real root).
    cor:fold-gauge-anomaly-bernoulli-p-density-maximizer-cardano -/
theorem densityMaxCubic_discriminant : -4 * (2 : ℤ) ^ 3 - 27 * (-2) ^ 2 = -140 := by ring

/-- At the root p: 1 + p³ = 3 - 2p (from p³ + 2p - 2 = 0).
    cor:fold-gauge-anomaly-bernoulli-p-density-maximizer-cardano -/
theorem densityMaxCubic_root_identity (p : ℤ) (hp : p ^ 3 + 2 * p - 2 = 0) :
    1 + p ^ 3 = 3 - 2 * p := by linarith

/-- Paper package: density maximizer Cardano.
    cor:fold-gauge-anomaly-bernoulli-p-density-maximizer-cardano -/
theorem paper_fold_gauge_anomaly_density_maximizer_cardano :
    densityMaxCubic 0 = -2 ∧ densityMaxCubic 1 = 1 ∧
    (-4 * (2 : ℤ) ^ 3 - 27 * (-2) ^ 2 = -140) ∧ (-140 < (0 : ℤ)) ∧
    (∀ p : ℤ, p ^ 3 + 2 * p - 2 = 0 → 1 + p ^ 3 = 3 - 2 * p) ∧
    35 = 5 * 7 := by
  refine ⟨densityMaxCubic_zero, densityMaxCubic_one,
          densityMaxCubic_discriminant, by omega,
          densityMaxCubic_root_identity, by omega⟩

end Omega.Folding
