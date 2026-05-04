import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic
import Omega.Conclusion.ConclusionFrozenFirstDifferenceRecoversMaxfiberExponent
import Omega.Conclusion.MicroVsMacroFreezingMinentropyGap

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Concrete data for the frozen affine splitting: the macro/micro min-entropy identities are
paired with the pressure first-difference package. -/
structure conclusion_micro_macro_frozen_minentropy_affine_splitting_data where
  a : ℤ
  alpha_star : ℝ
  g_star : ℝ
  hMacro : ℝ
  hMicro : ℝ
  S : ℤ → ℕ → ℝ
  M : ℕ → ℝ
  P : ℤ → ℝ
  hmacro : hMacro = g_star
  hmicro : hMicro = alpha_star + g_star
  quotient_eq : ∀ m : ℕ, S a m / S (a - 1) m = M m
  maxfiber_tendsto : Tendsto (fun m : ℕ => Real.log (M m) / (m : ℝ)) atTop (𝓝 alpha_star)
  pressure_step : P a = P (a - 1) + alpha_star

/-- The micro branch is the macro branch plus the frozen first pressure difference, and this
difference is the max-fiber exponent. -/
def conclusion_micro_macro_frozen_minentropy_affine_splitting_statement
    (D : conclusion_micro_macro_frozen_minentropy_affine_splitting_data) : Prop :=
  D.hMicro = D.hMacro + (D.P D.a - D.P (D.a - 1)) ∧
    D.hMicro = D.alpha_star + D.g_star ∧
      D.hMicro - D.hMacro = D.P D.a - D.P (D.a - 1) ∧
        D.P D.a - D.P (D.a - 1) = D.alpha_star

/-- Paper label: `cor:conclusion-micro-macro-frozen-minentropy-affine-splitting`. -/
theorem paper_conclusion_micro_macro_frozen_minentropy_affine_splitting
    (D : conclusion_micro_macro_frozen_minentropy_affine_splitting_data) :
    conclusion_micro_macro_frozen_minentropy_affine_splitting_statement D := by
  rcases paper_conclusion_micro_vs_macro_freezing_minentropy_gap
      (0 : ℝ) D.alpha_star D.g_star D.hMacro D.hMicro D.hmacro D.hmicro with
    ⟨hmacro, hmicro, hgap⟩
  rcases paper_conclusion_frozen_first_difference_recovers_maxfiber_exponent D.a D.alpha_star
      D.S D.M D.P D.quotient_eq D.maxfiber_tendsto D.pressure_step with
    ⟨_hquot_limit, hdiff⟩
  refine ⟨?_, hmicro, ?_, hdiff⟩
  · rw [hmicro, hmacro, hdiff]
    ring
  · rw [hgap, hdiff]

end Omega.Conclusion
