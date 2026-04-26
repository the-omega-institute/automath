import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

private lemma pom_deltaq_linear_extrapolation_break_goldenRatio_lt_16181_div_10000 :
    Real.goldenRatio < (16181 : ℝ) / 10000 := by
  have hsqrt_lt : Real.sqrt (5 : ℝ) < (11181 : ℝ) / 5000 := by
    rw [Real.sqrt_lt' (by norm_num : 0 < (11181 : ℝ) / 5000)]
    norm_num
  rw [Real.goldenRatio]
  nlinarith

private lemma pom_deltaq_linear_extrapolation_break_log_goldenRatio_lt :
    Real.log Real.goldenRatio < (4817 : ℝ) / 10000 := by
  have hphi_exp : Real.goldenRatio < Real.exp ((4817 : ℝ) / 10000) := by
    have hsum_gt :
        (16181 : ℝ) / 10000 <
          ∑ m ∈ Finset.range 6, ((4817 : ℝ) / 10000) ^ m / (m.factorial : ℝ) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    have hsum_le :
        (∑ m ∈ Finset.range 6, ((4817 : ℝ) / 10000) ^ m / (m.factorial : ℝ)) ≤
          Real.exp ((4817 : ℝ) / 10000) :=
      Real.sum_le_exp_of_nonneg (by norm_num) 6
    exact lt_of_lt_of_le
      (lt_trans pom_deltaq_linear_extrapolation_break_goldenRatio_lt_16181_div_10000 hsum_gt)
      hsum_le
  exact (Real.log_lt_iff_lt_exp Real.goldenRatio_pos).2 hphi_exp

/-- Paper label: `cor:pom-deltaq-linear-extrapolation-break`.
The golden-envelope upper bound and the proposed linear extrapolation are already inconsistent at
`q = 58`. -/
theorem paper_pom_deltaq_linear_extrapolation_break
    (δ : ℕ → ℝ)
    (hEnvelope : ∀ q : ℕ, 18 ≤ q →
      δ q ≤ (((q : ℝ) / 2) + 1) * Real.log Real.goldenRatio)
    (hLinear : ∀ q : ℕ, 18 ≤ q →
      ((263694 : ℝ) / 1000000) * (q : ℝ) - ((842355 : ℝ) / 1000000) ≤ δ q) :
    False := by
  have hEnvelope58 := hEnvelope 58 (by norm_num)
  have hLinear58 := hLinear 58 (by norm_num)
  have hle :
      ((263694 : ℝ) / 1000000) * (58 : ℝ) - ((842355 : ℝ) / 1000000) ≤
        (((58 : ℝ) / 2) + 1) * Real.log Real.goldenRatio :=
    le_trans hLinear58 hEnvelope58
  have hlt :
      (((58 : ℝ) / 2) + 1) * Real.log Real.goldenRatio <
        ((263694 : ℝ) / 1000000) * (58 : ℝ) - ((842355 : ℝ) / 1000000) := by
    nlinarith [pom_deltaq_linear_extrapolation_break_log_goldenRatio_lt]
  exact (not_lt_of_ge hle) hlt

end Omega.POM
