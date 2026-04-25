import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-haar-conditional-expectation-convolution`. -/
theorem paper_conclusion_fibadic_haar_conditional_expectation_convolution
    {Measure Char : Type*} (hat : Measure → Char → Prop) (sigma : ℕ → Measure)
    (conv : Measure → Measure → Measure) (depth : Char → ℕ)
    (hhat_sigma : ∀ d χ, hat (sigma d) χ ↔ depth χ ∣ d)
    (hhat_conv : ∀ μ ν χ, hat (conv μ ν) χ ↔ hat μ χ ∧ hat ν χ)
    (hsep : ∀ μ ν, (∀ χ, (hat μ χ ↔ hat ν χ)) → μ = ν) :
    ∀ d e, conv (sigma d) (sigma e) = sigma (Nat.gcd d e) := by
  intro d e
  apply hsep
  intro χ
  rw [hhat_conv, hhat_sigma, hhat_sigma, hhat_sigma]
  exact Nat.dvd_gcd_iff.symm

end Omega.Conclusion
