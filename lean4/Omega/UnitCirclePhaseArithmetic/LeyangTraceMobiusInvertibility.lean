import Mathlib.Analysis.RCLike.Sqrt
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

/-- The quadratic formula gives the two explicit inverse branches of the Lee--Yang gate, and
Vieta's relation recovers the unit-circle product constraint. -/
theorem paper_leyang_j_explicit_inversion (t : ℂ) (ht : t ≠ 0) :
    let uPlus := (-(2 * t + 1) + Complex.sqrt (1 + 4 * t)) / (2 * t)
    let uMinus := (-(2 * t + 1) - Complex.sqrt (1 + 4 * t)) / (2 * t)
    t * uPlus ^ 2 + (2 * t + 1) * uPlus + t = 0 ∧
      t * uMinus ^ 2 + (2 * t + 1) * uMinus + t = 0 ∧
      uPlus * uMinus = 1 := by
  dsimp
  set s : ℂ := Complex.sqrt (1 + 4 * t)
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have h2t : (2 * t : ℂ) ≠ 0 := mul_ne_zero htwo ht
  have hsq : s ^ 2 = 1 + 4 * t := by
    simpa [s, Complex.sqrt] using (Complex.isSquare (1 + 4 * t)).choose_spec
  refine ⟨?_, ?_, ?_⟩
  · field_simp [h2t]
    ring_nf
    rw [hsq]
    ring
  · field_simp [h2t]
    ring_nf
    rw [hsq]
    ring
  · field_simp [h2t]
    ring_nf
    rw [hsq]
    ring

end Omega.UnitCirclePhaseArithmetic
