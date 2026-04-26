import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-integer-moment-strongest-tail-bound`.
Concrete finite-window data for the integer-moment tail exponent. -/
structure pom_integer_moment_strongest_tail_bound_data where
  windowK : ℕ
  candidateExponent : ℝ
  finiteDualFunctional : ℝ
  momentExponent : ℕ → ℝ
  chernoff_certificate :
    ∀ q : ℕ, 2 ≤ q → q ≤ windowK → candidateExponent ≤ momentExponent q
  finite_dual_upper_bound :
    ∀ x : ℝ, (∀ q : ℕ, 2 ≤ q → q ≤ windowK → x ≤ momentExponent q) →
      x ≤ finiteDualFunctional
  finite_dual_le_candidate : finiteDualFunctional ≤ candidateExponent

namespace pom_integer_moment_strongest_tail_bound_data

/-- The finite-window dual value is attained by the supplied exponent, and the same exponent
satisfies all integer-moment Chernoff certificates in `2 <= q <= K`. -/
def statement (D : pom_integer_moment_strongest_tail_bound_data) : Prop :=
  D.finiteDualFunctional = D.candidateExponent ∧
    ∀ q : ℕ, 2 ≤ q → q ≤ D.windowK → D.candidateExponent ≤ D.momentExponent q

end pom_integer_moment_strongest_tail_bound_data

/-- Paper label: `cor:pom-integer-moment-strongest-tail-bound`. -/
theorem paper_pom_integer_moment_strongest_tail_bound
    (D : pom_integer_moment_strongest_tail_bound_data) : D.statement := by
  refine ⟨?_, D.chernoff_certificate⟩
  exact le_antisymm D.finite_dual_le_candidate
    (D.finite_dual_upper_bound D.candidateExponent D.chernoff_certificate)

end Omega.POM
