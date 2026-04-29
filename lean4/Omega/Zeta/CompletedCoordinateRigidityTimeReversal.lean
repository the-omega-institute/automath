import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_completed_coordinate_rigidity_time_reversal (z u s : ℂ) (hs : s ^ 2 = u)
    (hs0 : s ≠ 0) :
    (u * z) * s⁻¹ = z * s := by
  rw [← hs]
  field_simp [hs0]

end Omega.Zeta
