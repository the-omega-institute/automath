import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangInverseSquareDihedralUniqueness

namespace Omega.UnitCirclePhaseArithmetic

/-- The explicit Lee--Yang anchor on the unit circle. -/
noncomputable def leyang_anchor_minus4_qsqrtm15_zstar : ℂ :=
  ((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4

/-- Paper label: `cor:leyang-anchor-minus4-qsqrtm15`. -/
theorem paper_leyang_anchor_minus4_qsqrtm15 :
    let z := leyang_anchor_minus4_qsqrtm15_zstar
    2 * z ^ 2 + z + 2 = 0 ∧
      z ≠ 0 ∧
      z + z⁻¹ = (-(1 / 2 : ℂ)) ∧
      leyangInverseSquareDihedralModel z = (-4 : ℂ) ∧
      z.re = (-1 / 4 : ℝ) ∧
      z.im = -(Real.sqrt 15 / 4) := by
  dsimp [leyang_anchor_minus4_qsqrtm15_zstar]
  have hsqrt : (Real.sqrt 15) ^ 2 = 15 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 15 by positivity)]
  have hnorm : Complex.normSq ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) = 1 := by
    simp [Complex.normSq]
    nlinarith [hsqrt]
  have hquad : 2 * (((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) ^ 2) +
      ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) + 2 = 0 := by
    apply Complex.ext <;> simp [pow_two] <;> nlinarith [hsqrt]
  have hne : ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) ≠ 0 := by
    intro hz
    have hzero : Complex.normSq ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) = 0 := by
      simp [hz]
    rw [hzero] at hnorm
    norm_num at hnorm
  have hinv : ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4))⁻¹ =
      (((-1 : ℂ) + Complex.I * Real.sqrt 15) / 4) := by
    apply inv_eq_of_mul_eq_one_right
    apply Complex.ext <;> simp <;> nlinarith [hsqrt]
  have hsum : ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) +
      (((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4))⁻¹) = (-(1 / 2 : ℂ)) := by
    rw [hinv]
    apply Complex.ext <;> simp <;> try norm_num <;> ring
  have hmodel : leyangInverseSquareDihedralModel ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) =
      (-4 : ℂ) := by
    calc
      leyangInverseSquareDihedralModel ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) =
          -(1 / (((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)) +
            (((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4))⁻¹)) ^ 2) := by
        simpa using congrArg (fun f : ℂ → ℂ =>
          f ((((-1 : ℂ) - Complex.I * Real.sqrt 15) / 4)))
          paper_leyang_inverse_square_dihedral_uniqueness
      _ = -(1 / (-(1 / 2 : ℂ)) ^ 2) := by rw [hsum]
      _ = (-4 : ℂ) := by norm_num
  refine ⟨hquad, hne, hsum, hmodel, ?_, ?_⟩
  · norm_num
  · norm_num
    ring

end Omega.UnitCirclePhaseArithmetic
