import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-two-parameter-minimal-complex-moment-rigidity`. -/
theorem paper_xi_two_parameter_minimal_complex_moment_rigidity (m : ℕ) (M : ℂ) (C : ℝ)
    (hC : C ≠ 0) (hleading : C * Complex.normSq M = 0) :
    M = 0 := by
  have _ : m = m := rfl
  have hnorm : Complex.normSq M = 0 := by
    exact Or.resolve_left (mul_eq_zero.mp hleading) hC
  exact Complex.normSq_eq_zero.mp hnorm

end Omega.Zeta
