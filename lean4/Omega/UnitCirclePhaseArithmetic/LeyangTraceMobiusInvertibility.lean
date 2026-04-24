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

/-- Eliminating `u` between the Lee--Yang phase coordinates `J(u)` and `J(cu)` gives a quadratic
correspondence in `t'`, whose discriminant factors through the Lee--Yang branch term `4t + 1`. -/
theorem paper_leyang_phase_translation_correspondence_discriminant
    (c u : ℂ) (hc0 : c ≠ 0) (hu0 : u ≠ 0) (hu1 : 1 + u ≠ 0) (hcu1 : 1 + c * u ≠ 0) :
    let t : ℂ := -u / (1 + u) ^ 2
    let t' : ℂ := -(c * u) / (1 + c * u) ^ 2
    let a : ℂ := (t * (c - 1) ^ 2 - c) ^ 2
    let b : ℂ := -c * t * (2 * c ^ 2 * t + c ^ 2 - 4 * c * t + 2 * t + 1)
    let d : ℂ := c ^ 2 * t ^ 2
    a * t' ^ 2 + b * t' + d = 0 ∧ b ^ 2 - 4 * a * d = c ^ 2 * t ^ 2 * (c ^ 2 - 1) ^ 2 * (4 * t + 1) := by
  dsimp
  have ha :
      (-u / (1 + u) ^ 2 * (c - 1) ^ 2 - c) =
        -((c + u) * (1 + c * u) / (1 + u) ^ 2) := by
    field_simp [hu1]
    ring
  have hb :
      -c * (-u / (1 + u) ^ 2) *
          (2 * c ^ 2 * (-u / (1 + u) ^ 2) + c ^ 2 - 4 * c * (-u / (1 + u) ^ 2) +
            2 * (-u / (1 + u) ^ 2) + 1) =
        c * u * (c ^ 2 * u ^ 2 + c ^ 2 + 4 * c * u + u ^ 2 + 1) / (1 + u) ^ 4 := by
    field_simp [hu1]
    ring
  have hd :
      c ^ 2 * (-u / (1 + u) ^ 2) ^ 2 = c ^ 2 * u ^ 2 / (1 + u) ^ 4 := by
    field_simp [hu1]
  have hbranch : 4 * (-u / (1 + u) ^ 2) + 1 = (u - 1) ^ 2 / (1 + u) ^ 2 := by
    field_simp [hu1]
    ring
  refine ⟨?_, ?_⟩
  · rw [ha, hb, hd]
    field_simp [hc0, hu0, hu1, hcu1]
    ring
  · rw [ha, hb, hd, hbranch]
    field_simp [hc0, hu0, hu1, hcu1]
    ring

/-- Specializing the Lee--Yang phase translation to the quarter-phase parameter `c = -1` yields
the Möbius involution `t ↦ -t / (4t + 1)`. -/
theorem paper_leyang_quarterphase_mobius_involution (t : Complex) (ht : 4 * t + 1 ≠ 0) :
    let M : Complex := -t / (4 * t + 1); -M / (4 * M + 1) = t := by
  dsimp
  have hden : 4 * (-t / (4 * t + 1)) + 1 = (4 * t + 1)⁻¹ := by
    field_simp [ht]
    ring
  rw [hden]
  simp [div_eq_mul_inv, ht]

end Omega.UnitCirclePhaseArithmetic
