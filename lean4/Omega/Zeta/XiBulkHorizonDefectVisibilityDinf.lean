import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-bulk-horizon-defect-visibility-Dinfty`. -/
theorem paper_xi_bulk_horizon_defect_visibility_dinfty
    (Dinf h gamma delta scale : Real) :
    0 < delta →
      h = 4 * delta / (gamma ^ 2 + (1 + delta) ^ 2) →
        scale = Real.exp (Dinf * Real.log (1 / h)) →
          scale =
            Real.exp
              (Dinf * Real.log ((gamma ^ 2 + (1 + delta) ^ 2) / (4 * delta))) := by
  intro hdelta hh hscale
  rw [hscale]
  have hdenom_pos : 0 < gamma ^ 2 + (1 + delta) ^ 2 := by
    have hgamma_sq : 0 ≤ gamma ^ 2 := sq_nonneg gamma
    have hone_delta_pos : 0 < 1 + delta := by linarith
    have hone_delta_sq_pos : 0 < (1 + delta) ^ 2 :=
      sq_pos_of_ne_zero (by linarith)
    nlinarith
  have hdenom_ne : gamma ^ 2 + (1 + delta) ^ 2 ≠ 0 := ne_of_gt hdenom_pos
  have hdelta_ne : delta ≠ 0 := ne_of_gt hdelta
  have harg :
      1 / h = (gamma ^ 2 + (1 + delta) ^ 2) / (4 * delta) := by
    rw [hh]
    field_simp [hdenom_ne, hdelta_ne]
  rw [harg]

end Omega.Zeta
