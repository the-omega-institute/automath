import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- In trace coordinates `x = (u + u⁻¹) / 2 = (u^2 + 1) / (2u)`, the Lee--Yang gate
`J(u) = -u / (1 + u)^2` becomes the Möbius map `-1 / (2(1 + x))`, and the trace coordinate is
recovered by the inverse Möbius transform. -/
theorem paper_leyang_trace_mobius_invertibility (u : ℂ) (hu0 : u ≠ 0) (hu1 : u ≠ -1) :
    let x : ℂ := (u ^ 2 + 1) / (2 * u)
    (-u / (1 + u) ^ 2 = -1 / (2 * (1 + x))) ∧
      (x = -(2 * (-u / (1 + u) ^ 2) + 1) / (2 * (-u / (1 + u) ^ 2))) := by
  have huplus : 1 + u ≠ 0 := by
    intro h
    exact hu1 (eq_neg_of_add_eq_zero_right h)
  dsimp
  refine ⟨?_, ?_⟩
  · have hden : 2 * (1 + (u ^ 2 + 1) / (2 * u)) = (1 + u) ^ 2 / u := by
      field_simp [hu0]
      ring
    rw [hden]
    field_simp [hu0, huplus]
  · field_simp [hu0, huplus]
    ring_nf

end Omega.UnitCirclePhaseArithmetic
