import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped goldenRatio

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:real-input-40-length-sign-L1`.
Evaluating the explicit determinant factorization at `z = -1 / λ` with
`λ = (3 + √5) / 2 = φ²` gives the closed radical formula for the length-sign Euler product. -/
theorem paper_real_input_40_length_sign_l1 :
    let lam : ℝ := (3 + Real.sqrt 5) / 2
    let z : ℝ := -1 / lam
    (((1 - z) ^ 2 * (1 + z) ^ 3 * (1 - 3 * z + z ^ 2) * (1 + z - z ^ 2)) : ℝ)⁻¹ =
      (41 : ℝ) / 40 + (11 : ℝ) / 24 * Real.sqrt 5 := by
  dsimp
  have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    simp
  have hsqrt5_nonneg : 0 ≤ (Real.sqrt 5 : ℝ) := by positivity
  have hphi_ne : (φ : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hlam : ((3 + Real.sqrt 5) / 2 : ℝ) = φ ^ 2 := by
    rw [Real.goldenRatio, Real.goldenRatio_sq]
    ring
  have hz : (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) = -(φ ^ 2)⁻¹ := by
    rw [hlam, div_eq_mul_inv]
    ring
  have hA : (1 - (-1 / ((3 + Real.sqrt 5) / 2 : ℝ))) = Real.sqrt 5 / φ := by
    rw [hz]
    field_simp [hphi_ne]
    nlinarith [Real.goldenRatio_sq, Real.goldenRatio_sub_goldenConj, Real.goldenRatio_add_goldenConj]
  have hB : (1 + (-1 / ((3 + Real.sqrt 5) / 2 : ℝ))) = φ⁻¹ := by
    rw [hz]
    field_simp [hphi_ne]
    nlinarith [Real.goldenRatio_sq]
  have hC :
      (1 - 3 * (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) + (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) ^ 2) =
        6 * (φ ^ 2)⁻¹ := by
    rw [hz]
    field_simp [hphi_ne]
    nlinarith [Real.goldenRatio_sq]
  have hD :
      (1 + (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) - (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) ^ 2) =
        2 * (φ ^ 3)⁻¹ := by
    rw [hz]
    field_simp [hphi_ne]
    nlinarith [Real.goldenRatio_sq]
  have hD' :
      (φ⁻¹ - (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) ^ 2) = 2 * (φ ^ 3)⁻¹ := by
    simpa [hB] using hD
  have hsqrt5_cube : (Real.sqrt 5 : ℝ) ^ 3 = 5 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5 : ℝ) ^ 3 = (Real.sqrt 5 : ℝ) ^ 2 * Real.sqrt 5 := by ring
      _ = 5 * Real.sqrt 5 := by rw [hsqrt5_sq]
  have hsqrt5_four : (Real.sqrt 5 : ℝ) ^ 4 = 25 := by
    calc
      (Real.sqrt 5 : ℝ) ^ 4 = ((Real.sqrt 5 : ℝ) ^ 2) ^ 2 := by ring
      _ = 25 := by rw [hsqrt5_sq]; norm_num
  have hsqrt5_five : (Real.sqrt 5 : ℝ) ^ 5 = 25 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5 : ℝ) ^ 5 = (Real.sqrt 5 : ℝ) ^ 4 * Real.sqrt 5 := by ring
      _ = 25 * Real.sqrt 5 := by rw [hsqrt5_four]
  have hsqrt5_six : (Real.sqrt 5 : ℝ) ^ 6 = 125 := by
    nlinarith [hsqrt5_sq]
  have hsqrt5_seven : (Real.sqrt 5 : ℝ) ^ 7 = 125 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5 : ℝ) ^ 7 = (Real.sqrt 5 : ℝ) ^ 6 * Real.sqrt 5 := by ring
      _ = 125 * Real.sqrt 5 := by rw [hsqrt5_six]
  have hsqrt5_eight : (Real.sqrt 5 : ℝ) ^ 8 = 625 := by
    nlinarith [hsqrt5_sq]
  have hsqrt5_nine : (Real.sqrt 5 : ℝ) ^ 9 = 625 * Real.sqrt 5 := by
    calc
      (Real.sqrt 5 : ℝ) ^ 9 = (Real.sqrt 5 : ℝ) ^ 8 * Real.sqrt 5 := by ring
      _ = 625 * Real.sqrt 5 := by rw [hsqrt5_eight]
  have hsqrt5_ten : (Real.sqrt 5 : ℝ) ^ 10 = 3125 := by
    nlinarith [hsqrt5_sq]
  calc
    (((1 - -1 / ((3 + Real.sqrt 5) / 2 : ℝ)) ^ 2 * (1 + -1 / ((3 + Real.sqrt 5) / 2 : ℝ)) ^ 3 *
          (1 - 3 * (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) + (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) ^ 2) *
          (1 + -1 / ((3 + Real.sqrt 5) / 2 : ℝ) - (-1 / ((3 + Real.sqrt 5) / 2 : ℝ)) ^ 2)) : ℝ)⁻¹
        = (((Real.sqrt 5 / φ) ^ 2 * (φ⁻¹) ^ 3 * (6 * (φ ^ 2)⁻¹) * (2 * (φ ^ 3)⁻¹)) : ℝ)⁻¹ := by
            rw [hA, hB, hC, hD']
    _ = ((60 : ℝ) * (φ ^ 10)⁻¹)⁻¹ := by
      congr 1
      field_simp [hphi_ne]
      rw [hsqrt5_sq]
      ring
    _ = φ ^ 10 / 60 := by
      field_simp [pow_ne_zero 10 Real.goldenRatio_ne_zero]
    _ = (41 : ℝ) / 40 + (11 : ℝ) / 24 * Real.sqrt 5 := by
      rw [Real.goldenRatio]
      field_simp
      ring_nf
      rw [hsqrt5_ten, hsqrt5_nine, hsqrt5_eight, hsqrt5_seven, hsqrt5_six, hsqrt5_five,
        hsqrt5_four, hsqrt5_cube, hsqrt5_sq]
      ring_nf

end Omega.SyncKernelWeighted
