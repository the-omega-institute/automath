import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

lemma indexGapGammaDerivFormula
    {lam Gamma : ℝ → ℝ}
    (hGamma : ∀ τ, Gamma τ = -Real.log (lam τ))
    (hlamPos : ∀ τ, 0 < lam τ)
    (hlamDeriv : ∀ τ, HasDerivAt lam (deriv lam τ) τ) :
    deriv Gamma = fun τ => -(deriv lam τ / lam τ) := by
  funext τ
  have hGammaEq : Gamma = fun s => -Real.log (lam s) := by
    funext s
    exact hGamma s
  rw [hGammaEq]
  exact (((hlamDeriv τ).log (ne_of_gt (hlamPos τ))).neg).deriv

/-- Abstract second-variation formula for the index gap `Γ = -log λ`: the second derivative
splits into the quadratic Fisher term and the normalized curvature term, and therefore is
nonnegative at a local minimizer of `Γ` / local maximizer of `λ`.
    cor:op-algebra-index-gap-curvature-second-variation -/
theorem paper_op_algebra_index_gap_curvature_second_variation
    {lam Gamma : ℝ → ℝ}
    (hGamma : ∀ τ, Gamma τ = -Real.log (lam τ))
    (hlamPos : ∀ τ, 0 < lam τ)
    (hlamDeriv : ∀ τ, HasDerivAt lam (deriv lam τ) τ)
    (hlamSecond : HasDerivAt (deriv lam) (deriv (deriv lam) 0) 0) :
    deriv (deriv Gamma) 0 = (deriv lam 0 / lam 0) ^ 2 - deriv (deriv lam) 0 / lam 0 ∧
      (deriv lam 0 = 0 → deriv (deriv lam) 0 ≤ 0 → 0 ≤ deriv (deriv Gamma) 0) := by
  have hGamma' : deriv Gamma = fun τ => -(deriv lam τ / lam τ) :=
    indexGapGammaDerivFormula hGamma hlamPos hlamDeriv
  have hlam0_ne : lam 0 ≠ 0 := ne_of_gt (hlamPos 0)
  have hsecond :
      HasDerivAt (fun τ => -(deriv lam τ / lam τ))
        ((deriv lam 0 / lam 0) ^ 2 - deriv (deriv lam) 0 / lam 0) 0 := by
    have hquot : HasDerivAt (fun τ => deriv lam τ / lam τ)
        ((deriv (deriv lam) 0 * lam 0 - deriv lam 0 * deriv lam 0) / (lam 0) ^ 2) 0 := by
      exact (hlamSecond.div (hlamDeriv 0) hlam0_ne)
    convert hquot.neg using 1
    field_simp [hlam0_ne]
    ring
  have hGammaSecond : HasDerivAt (deriv Gamma)
      ((deriv lam 0 / lam 0) ^ 2 - deriv (deriv lam) 0 / lam 0) 0 := by
    simpa [hGamma'] using hsecond
  constructor
  · exact hGammaSecond.deriv
  · intro hcrit hconcave
    rw [hGammaSecond.deriv, hcrit]
    have hdiv_nonpos : deriv (deriv lam) 0 / lam 0 ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hconcave (le_of_lt (hlamPos 0))
    nlinarith

end Omega.OperatorAlgebra
