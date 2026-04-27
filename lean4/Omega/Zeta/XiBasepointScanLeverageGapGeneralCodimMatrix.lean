import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-basepoint-scan-leverage-gap-general-codim-matrix`.

The leverage gap is exactly the quadratic form induced by the finite residual moment matrix,
and positive semidefiniteness of that form gives pointwise nonnegativity. -/
theorem paper_xi_basepoint_scan_leverage_gap_general_codim_matrix {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (r : ℝ → Fin m → ℝ) (ell : ℝ → ℝ)
    (hquad : ∀ x, ell x = dotProduct (r x) (M.mulVec (r x)))
    (hpos : ∀ v : Fin m → ℝ, 0 ≤ dotProduct v (M.mulVec v)) :
    (∀ x, ell x = dotProduct (r x) (M.mulVec (r x))) ∧ (∀ x, 0 ≤ ell x) := by
  refine ⟨hquad, ?_⟩
  intro x
  rw [hquad x]
  exact hpos (r x)

end Omega.Zeta
