import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete zero-certification data at a fixed dyadic shell depth. -/
structure conclusion_xi_zero_certification_logarithmic_depth_Data where
  B : ℝ
  K : ℕ
  E : ℕ → ℝ
  gamma : ℝ
  tauApprox : ℝ
  cauchy_tail : |gamma - tauApprox| ≤ E K
  dyadic_shell_envelope : E K ≤ (2 : ℝ) ^ (-B)
  bit_lower_bound : B ≤ -Real.log (E K) / Real.log 2
  leading_order_balance :
    (K : ℝ) =
      Real.log B / Real.log 2 - Real.log (Real.pi / Real.log 2) / Real.log 2

/-- Paper-facing fixed-depth certification statement. -/
def conclusion_xi_zero_certification_logarithmic_depth_statement
    (D : conclusion_xi_zero_certification_logarithmic_depth_Data) : Prop :=
  |D.gamma - D.tauApprox| ≤ (2 : ℝ) ^ (-D.B) ∧
    D.B ≤ -Real.log (D.E D.K) / Real.log 2 ∧
    (D.K : ℝ) =
      Real.log D.B / Real.log 2 - Real.log (Real.pi / Real.log 2) / Real.log 2

/-- Paper label: `cor:conclusion-xi-zero-certification-logarithmic-depth`. -/
theorem paper_conclusion_xi_zero_certification_logarithmic_depth
    (D : conclusion_xi_zero_certification_logarithmic_depth_Data) :
    conclusion_xi_zero_certification_logarithmic_depth_statement D := by
  exact ⟨le_trans D.cauchy_tail D.dyadic_shell_envelope, D.bit_lower_bound,
    D.leading_order_balance⟩

end Omega.Conclusion
