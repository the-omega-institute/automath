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

end Omega.Folding
