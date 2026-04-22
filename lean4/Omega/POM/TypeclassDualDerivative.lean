import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The active-regime part of the dual-derivative identity is exactly the derivative hypothesis
rewritten in terms of `deriv`.
    thm:pom-typeclass-dual-derivative -/
theorem pom_typeclass_dual_derivative_active_regime (Rw lam : ℝ → ℝ) (p0 δ : ℝ)
    (hderiv : p0 < 1 - δ → HasDerivAt Rw (- lam δ) δ) :
    p0 < 1 - δ → -deriv Rw δ = lam δ := by
  intro hp
  have h := (hderiv hp).deriv
  linarith

end Omega.POM
