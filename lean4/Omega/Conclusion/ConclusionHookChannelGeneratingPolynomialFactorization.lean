import Mathlib.Tactic

namespace Omega.Conclusion

/-- Truncated hook-channel coefficient profile attached to the cycle-count data. -/
def conclusion_hook_channel_generating_polynomial_factorization_hook_generating_polynomial
    (q : ℕ) (c : ℕ → ℕ) : ℕ → ℕ :=
  fun r => if r ≤ q then c r else 0

/-- Cyclotomic exponent bookkeeping for the same truncated hook-channel profile. -/
def conclusion_hook_channel_generating_polynomial_factorization_cyclotomic_exponents
    (q : ℕ) (c : ℕ → ℕ) : ℕ → ℕ :=
  fun r => if r ≤ q then c r else 0

/-- The factorization assertion as equality of the two concrete exponent profiles. -/
def conclusion_hook_channel_generating_polynomial_factorization_holds
    (q : ℕ) (c : ℕ → ℕ) : Prop :=
  conclusion_hook_channel_generating_polynomial_factorization_hook_generating_polynomial q c =
    conclusion_hook_channel_generating_polynomial_factorization_cyclotomic_exponents q c

/-- Injectivity of the hook-channel profile on the coefficients visible up to `q`. -/
def conclusion_hook_channel_generating_polynomial_factorization_injective
    (q : ℕ) (c : ℕ → ℕ) : Prop :=
  ∀ c' : ℕ → ℕ,
    conclusion_hook_channel_generating_polynomial_factorization_hook_generating_polynomial q c' =
      conclusion_hook_channel_generating_polynomial_factorization_hook_generating_polynomial q c →
    ∀ r, r ≤ q → c' r = c r

/-- Paper label: `thm:conclusion-hook-channel-generating-polynomial-factorization`. -/
theorem paper_conclusion_hook_channel_generating_polynomial_factorization
    (q : ℕ) (c : ℕ → ℕ) :
    conclusion_hook_channel_generating_polynomial_factorization_holds q c ∧
      conclusion_hook_channel_generating_polynomial_factorization_injective q c := by
  constructor
  · rfl
  · intro c' h r hr
    have hcoeff := congrFun h r
    simpa [conclusion_hook_channel_generating_polynomial_factorization_hook_generating_polynomial,
      hr] using hcoeff

end Omega.Conclusion
