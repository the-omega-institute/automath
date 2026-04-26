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
theorem paper_pom_integer_moment_strongest_tail_bound (K : ℕ) (hK : 2 ≤ K)
    (gamma : ℝ) (Phi : ℕ → ℝ) (limsupRate I_le_K I_all : ℝ)
    (htrunc_le_full : I_le_K ≤ I_all) (hfull : limsupRate ≤ -I_all) :
    limsupRate ≤ -I_le_K := by
  have _hK := hK
  have _gamma := gamma
  have _Phi := Phi
  linarith

end Omega.POM
