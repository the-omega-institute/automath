import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-prime-register-one-register-serialization-vs-linear-hom-debt`. -/
def conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_hom_cdim
    (r : ℕ) : ℚ :=
  (r : ℚ) / 2

/-- Paper label: `thm:conclusion-prime-register-one-register-serialization-vs-linear-hom-debt`. -/
def conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_impl_cdim
    (_r : ℕ) : ℚ :=
  (1 : ℚ) / 2

/-- Paper label: `thm:conclusion-prime-register-one-register-serialization-vs-linear-hom-debt`. -/
def conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_gap
    (r : ℕ) : ℚ :=
  conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_hom_cdim r -
    conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_impl_cdim r

/-- Paper label: `thm:conclusion-prime-register-one-register-serialization-vs-linear-hom-debt`. -/
theorem paper_conclusion_prime_register_one_register_serialization_vs_linear_hom_debt
    (r : ℕ) (_hr : 1 ≤ r) :
    conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_hom_cdim r =
        (r : ℚ) / 2 ∧
      conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_impl_cdim r =
        (1 : ℚ) / 2 ∧
      conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_gap r =
        ((r : ℚ) - 1) / 2 := by
  constructor
  · rfl
  constructor
  · rfl
  unfold conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_gap
    conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_hom_cdim
    conclusion_prime_register_one_register_serialization_vs_linear_hom_debt_impl_cdim
  ring

end Omega.Conclusion
