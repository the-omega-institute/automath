import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-box data for the prime-torus holographic information bound. The domain has
`(N + 1)^r` points, the code is injective on that finite box, and the quantized torus output has
cardinality at most `P * C_d * δ^{-d}`. -/
structure conclusion_prime_torus_holographic_information_inequality_data where
  N : ℕ
  r : ℕ
  d : ℕ
  outputBound : ℕ
  P : ℝ
  C_d : ℝ
  delta : ℝ
  delta_pos : 0 < delta
  P_pos : 0 < P
  C_d_pos : 0 < C_d
  code : Fin ((N + 1) ^ r) → Fin outputBound
  code_injective : Function.Injective code
  output_bound : (outputBound : ℝ) ≤ P * C_d * delta ^ (-(d : ℝ))

namespace conclusion_prime_torus_holographic_information_inequality_data

/-- The injective finite-box code forces the expected logarithmic information budget. -/
def information_budget_inequality
    (D : conclusion_prime_torus_holographic_information_inequality_data) : Prop :=
  (D.r : ℝ) * Real.log (D.N + 1 : ℝ) ≤
    Real.log D.P + Real.log D.C_d - (D.d : ℝ) * Real.log D.delta

end conclusion_prime_torus_holographic_information_inequality_data

open conclusion_prime_torus_holographic_information_inequality_data

/-- Paper label: `thm:conclusion-prime-torus-holographic-information-inequality`. The code is
injective on `(N + 1)^r` box inputs, the output space has cardinality at most `P * C_d * δ^{-d}`,
and monotonicity of `log` turns the resulting cardinality comparison into the stated information
budget inequality. -/
theorem paper_conclusion_prime_torus_holographic_information_inequality
    (D : conclusion_prime_torus_holographic_information_inequality_data) :
    D.information_budget_inequality := by
  have hcard_nat : (D.N + 1) ^ D.r ≤ D.outputBound := by
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective D.code D.code_injective
  have hcard_real : (((D.N + 1) ^ D.r : ℕ) : ℝ) ≤ D.outputBound := by
    exact_mod_cast hcard_nat
  have hleft_pos : 0 < ((((D.N + 1) ^ D.r : ℕ) : ℝ)) := by
    positivity
  have hbound :
      ((((D.N + 1) ^ D.r : ℕ) : ℝ)) ≤ D.P * D.C_d * D.delta ^ (-(D.d : ℝ)) := by
    exact le_trans hcard_real D.output_bound
  have hlog := Real.log_le_log hleft_pos hbound
  have hN1_pos : 0 < (D.N + 1 : ℝ) := by
    positivity
  have hdelta_pow_pos : 0 < D.delta ^ (-(D.d : ℝ)) := by
    exact Real.rpow_pos_of_pos D.delta_pos _
  have hleft_eq :
      Real.log ((((D.N + 1) ^ D.r : ℕ) : ℝ)) = (D.r : ℝ) * Real.log (D.N + 1 : ℝ) := by
    rw [show ((((D.N + 1) ^ D.r : ℕ) : ℝ)) = (D.N + 1 : ℝ) ^ D.r by
      exact_mod_cast (show (D.N + 1) ^ D.r = (D.N + 1) ^ D.r by rfl)]
    rw [← Real.rpow_natCast, Real.log_rpow hN1_pos]
  have hright_eq :
      Real.log (D.P * D.C_d * D.delta ^ (-(D.d : ℝ))) =
        Real.log D.P + Real.log D.C_d - (D.d : ℝ) * Real.log D.delta := by
    have hPCd_pos : 0 < D.P * D.C_d := mul_pos D.P_pos D.C_d_pos
    calc
      Real.log (D.P * D.C_d * D.delta ^ (-(D.d : ℝ))) =
          Real.log (D.P * D.C_d) + Real.log (D.delta ^ (-(D.d : ℝ))) := by
            rw [Real.log_mul hPCd_pos.ne' hdelta_pow_pos.ne']
      _ = (Real.log D.P + Real.log D.C_d) + (-(D.d : ℝ) * Real.log D.delta) := by
            rw [Real.log_mul D.P_pos.ne' D.C_d_pos.ne', Real.log_rpow D.delta_pos]
      _ = Real.log D.P + Real.log D.C_d - (D.d : ℝ) * Real.log D.delta := by
            ring
  rw [hleft_eq, hright_eq] at hlog
  simpa [information_budget_inequality] using hlog

end Omega.Conclusion
