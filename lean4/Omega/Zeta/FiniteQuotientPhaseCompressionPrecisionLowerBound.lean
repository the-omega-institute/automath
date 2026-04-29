import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

namespace Omega.Zeta

/-- Dyadic bit budget attached to phase resolution `δ`. -/
noncomputable def xi_finite_quotient_phase_compression_precision_lower_bound_bit_budget
    (δ : ℝ) : ℝ :=
  Real.logb 2 (1 / δ)

/-- Paper label: `thm:xi-finite-quotient-phase-compression-precision-lower-bound`.
Once phase separation forces `δ_n ≤ (n - 1)^(-(r / d))`, taking base-2 logarithms yields the
corresponding lower bound on the required bit precision. -/
theorem paper_xi_finite_quotient_phase_compression_precision_lower_bound
    (n r d : ℕ) (hn : 2 ≤ n) (_hd : 1 ≤ d) (δ_n : ℝ)
    (hδ_pos : 0 < δ_n)
    (hδ_bound : δ_n ≤ (((n - 1 : ℕ) : ℝ) ^ (-((r : ℝ) / d)))) :
    ((r : ℝ) / d) * Real.logb 2 (((n - 1 : ℕ) : ℝ)) ≤
      xi_finite_quotient_phase_compression_precision_lower_bound_bit_budget δ_n := by
  have hn1_pos_nat : 0 < n - 1 := by omega
  have hn1_pos : 0 < (((n - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hn1_pos_nat
  have hn1_nonneg : 0 ≤ (((n - 1 : ℕ) : ℝ)) := le_of_lt hn1_pos
  have hrecip :
      1 / ((((n - 1 : ℕ) : ℝ) ^ (-((r : ℝ) / d)))) ≤ 1 / δ_n :=
    one_div_le_one_div_of_le hδ_pos hδ_bound
  have hpow_le :
      (((n - 1 : ℕ) : ℝ) ^ ((r : ℝ) / d)) ≤ 1 / δ_n := by
    simpa [one_div, Real.rpow_neg hn1_nonneg] using hrecip
  have hlog :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (show 0 < (((n - 1 : ℕ) : ℝ) ^ ((r : ℝ) / d)) by positivity) hpow_le
  have hleft :
      Real.logb 2 ((((n - 1 : ℕ) : ℝ) ^ ((r : ℝ) / d))) =
        ((r : ℝ) / d) * Real.logb 2 (((n - 1 : ℕ) : ℝ)) := by
    unfold Real.logb
    rw [Real.log_rpow hn1_pos]
    ring
  unfold xi_finite_quotient_phase_compression_precision_lower_bound_bit_budget
  simpa [hleft] using hlog

end Omega.Zeta
