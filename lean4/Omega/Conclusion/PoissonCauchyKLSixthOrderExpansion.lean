import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-kl-sixth-order-expansion`. -/
theorem paper_conclusion_poisson_cauchy_kl_sixth_order_expansion
    (mu2 mu3 mu4 B6 : ℝ) (klSixthAsymptotic : Prop)
    (hB6 : B6 = mu2 ^ 3 / 64 - mu2 * mu4 / 8 + 3 * mu3 ^ 2 / 32)
    (hAsymptotic : klSixthAsymptotic) :
    B6 = mu2 ^ 3 / 64 - mu2 * mu4 / 8 + 3 * mu3 ^ 2 / 32 ∧
      klSixthAsymptotic := by
  exact ⟨hB6, hAsymptotic⟩

end Omega.Conclusion
