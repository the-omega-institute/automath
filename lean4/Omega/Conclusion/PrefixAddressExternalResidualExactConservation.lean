import Omega.Conclusion.AddressResidualTotalBitBudget

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prefix-address-external-residual-exact-conservation`. -/
theorem paper_conclusion_prefix_address_external_residual_exact_conservation
    (T m : ℕ) {R : Type*} [Fintype R] {c : ℝ} (hT : 2 ≤ T) (hc : 0 < c)
    (hCap : c * (T : ℝ)^2 * Real.log (T : ℝ) / (2 : ℝ)^m ≤ (Fintype.card R : ℝ)) :
    (m : ℝ) + Real.log (Fintype.card R : ℝ) / Real.log 2 ≥
      2 * Real.log (T : ℝ) / Real.log 2 + Real.log (Real.log (T : ℝ)) / Real.log 2 +
        Real.log c / Real.log 2 := by
  exact paper_conclusion_address_residual_total_bit_budget T m hT hc hCap

end Omega.Conclusion
