import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:leyang-lissajous-singular-ring-normal-form`. -/
theorem paper_leyang_lissajous_singular_ring_normal_form (a b : ℕ) (t δ : ℝ) :
    let φ := (b : ℝ) * δ
    let U := Real.cos ((((a * b : ℕ) : ℝ) * t) + φ)
    let V := Real.cos (((a * b : ℕ) : ℝ) * t)
    let p := -(1 / (4 * U ^ 2))
    let q := -(1 / (4 * V ^ 2))
    U ≠ 0 →
      V ≠ 0 →
        (p + q + 4 * Real.sin φ ^ 2 * p * q) ^ 2 = 4 * Real.cos φ ^ 2 * p * q := by
  dsimp
  set φ : ℝ := (b : ℝ) * δ
  set θ : ℝ := (((a * b : ℕ) : ℝ) * t)
  intro hU hV
  have hbase :
      Real.cos (θ + φ) ^ 2 - 2 * Real.cos φ * Real.cos (θ + φ) * Real.cos θ +
        Real.cos θ ^ 2 - Real.sin φ ^ 2 = 0 := by
    rw [Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]
  have hsquare :
      (Real.cos (θ + φ) ^ 2 + Real.cos θ ^ 2 - Real.sin φ ^ 2) ^ 2 =
        4 * Real.cos φ ^ 2 * Real.cos (θ + φ) ^ 2 * Real.cos θ ^ 2 := by
    have hlin :
        Real.cos (θ + φ) ^ 2 + Real.cos θ ^ 2 - Real.sin φ ^ 2 =
          2 * Real.cos φ * Real.cos (θ + φ) * Real.cos θ := by
      linarith
    nlinarith [hlin]
  have hsquare' :
      (-(Real.cos (θ + φ) ^ 2 + Real.cos θ ^ 2 - Real.sin φ ^ 2)) ^ 2 =
        4 * Real.cos φ ^ 2 * Real.cos (θ + φ) ^ 2 * Real.cos θ ^ 2 := by
    nlinarith [hsquare]
  have hU' : Real.cos (θ + φ) ≠ 0 := by simpa [θ, φ] using hU
  have hV' : Real.cos θ ≠ 0 := by simpa [θ] using hV
  field_simp [hU', hV']
  simpa [pow_two, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
    add_comm] using hsquare'

end Omega.UnitCirclePhaseArithmetic
