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

/-- The dual-derivative identity holds by splitting into the active and inactive regimes.
    thm:pom-typeclass-dual-derivative -/
theorem paper_pom_typeclass_dual_derivative (Rw lam : ℝ → ℝ) (p0 δ : ℝ)
    (hactive : p0 < 1 - δ → HasDerivAt Rw (-lam δ) δ)
    (hinactive : 1 - δ ≤ p0 → HasDerivAt Rw 0 δ ∧ lam δ = 0) :
    -deriv Rw δ = lam δ := by
  by_cases hp : p0 < 1 - δ
  · exact pom_typeclass_dual_derivative_active_regime Rw lam p0 δ hactive hp
  · have hp' : 1 - δ ≤ p0 := le_of_not_gt hp
    rcases hinactive hp' with ⟨hderiv, hlam⟩
    have hderiv' : deriv Rw δ = 0 := hderiv.deriv
    linarith

end Omega.POM
