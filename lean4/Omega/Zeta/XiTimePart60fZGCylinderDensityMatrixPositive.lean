import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60f-zg-cylinder-density-matrix-positive`. -/
theorem paper_xi_time_part60f_zg_cylinder_density_matrix_positive
    (density lowerEnvelope : List Bool → ℝ) (admissible : List Bool → Prop)
    (hmatrix_lower : ∀ z, admissible z → lowerEnvelope z ≤ density z)
    (hlower_pos : ∀ z, admissible z → 0 < lowerEnvelope z) :
    ∀ z, admissible z → 0 < density z := by
  intro z hz
  exact lt_of_lt_of_le (hlower_pos z hz) (hmatrix_lower z hz)

end Omega.Zeta
