import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-ty-three-branch-profile`. -/
theorem paper_xi_leyang_ty_three_branch_profile :
    (let t : ℝ → ℝ :=
      fun y => (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16) / (8 * (2 * y + 1) ^ 3);
      (∀ y : ℝ, y ≠ -(1 / 2 : ℝ) →
        HasDerivAt t (-(27 / 8 : ℝ) * (2 * y ^ 2 - 6 * y + 1) / (2 * y + 1) ^ 4) y) ∧
        t ((3 + Real.sqrt 7) / 2) = 139 / 72 + 7 * Real.sqrt 7 / 144 ∧
        t ((3 - Real.sqrt 7) / 2) = 139 / 72 - 7 * Real.sqrt 7 / 144) := by
  dsimp
  constructor
  · intro y hy
    have hyden : 2 * y + 1 ≠ 0 := by
      intro h
      apply hy
      linarith
    have hyden' : 8 * (2 * y + 1) ^ 3 ≠ 0 := by
      exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hyden)
    have hnum :
        HasDerivAt
          (fun y : ℝ => 128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16)
          (384 * y ^ 2 + 438 * y + 69) y := by
      convert
        ((((hasDerivAt_id y).pow 3).const_mul (128 : ℝ)).add
          ((((hasDerivAt_id y).pow 2).const_mul (219 : ℝ)).add
            (((hasDerivAt_id y).const_mul (69 : ℝ)).add (hasDerivAt_const y (16 : ℝ)))))
        using 1
      · ext z
        simp [id]
        ring_nf
      · simp [id]
        ring_nf
    have hden :
        HasDerivAt (fun y : ℝ => 8 * (2 * y + 1) ^ 3)
          (8 * (3 * (2 * y + 1) ^ 2 * 2)) y := by
      have hlin : HasDerivAt (fun y : ℝ => 2 * y + 1) 2 y := by
        convert ((hasDerivAt_id y).const_mul (2 : ℝ)).add_const (1 : ℝ) using 1
        · ring_nf
      convert (hlin.pow 3).const_mul (8 : ℝ) using 1
    have hderiv :
        HasDerivAt
          (fun y : ℝ => (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16) / (8 * (2 * y + 1) ^ 3))
          (((384 * y ^ 2 + 438 * y + 69) * (8 * (2 * y + 1) ^ 3) -
              (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16) *
                (8 * (3 * (2 * y + 1) ^ 2 * 2))) /
            (8 * (2 * y + 1) ^ 3) ^ 2)
          y := by
      exact hnum.div hden hyden'
    convert hderiv using 1
    field_simp [hyden]
    ring_nf
  · constructor
    · have hsqrt : (Real.sqrt 7) ^ 2 = (7 : ℝ) := by
        exact Real.sq_sqrt (by norm_num)
      have hsqrt3 : (Real.sqrt 7) ^ 3 = 7 * Real.sqrt 7 := by
        rw [pow_succ, hsqrt]
      have hsqrt4 : (Real.sqrt 7) ^ 4 = (49 : ℝ) := by
        rw [show (Real.sqrt 7) ^ 4 = ((Real.sqrt 7) ^ 2) ^ 2 by ring, hsqrt]
        norm_num
      have hden : 8 * (2 * ((3 + Real.sqrt 7) / 2) + 1) ^ 3 ≠ 0 := by
        positivity
      field_simp
      ring_nf
      rw [hsqrt4, hsqrt3, hsqrt]
      ring
    · have hsqrt : (Real.sqrt 7) ^ 2 = (7 : ℝ) := by
        exact Real.sq_sqrt (by norm_num)
      have hsqrt3 : (Real.sqrt 7) ^ 3 = 7 * Real.sqrt 7 := by
        rw [pow_succ, hsqrt]
      have hsqrt4 : (Real.sqrt 7) ^ 4 = (49 : ℝ) := by
        rw [show (Real.sqrt 7) ^ 4 = ((Real.sqrt 7) ^ 2) ^ 2 by ring, hsqrt]
        norm_num
      have hsqrt_lt_four : Real.sqrt 7 < (4 : ℝ) := by
        rw [Real.sqrt_lt' (by norm_num)]
        norm_num
      have hden : 8 * (2 * ((3 - Real.sqrt 7) / 2) + 1) ^ 3 ≠ 0 := by
        apply mul_ne_zero
        · norm_num
        · apply pow_ne_zero
          linarith
      have hden_small : (3 - Real.sqrt 7 + 1) ^ 3 ≠ 0 := by
        apply pow_ne_zero
        linarith
      field_simp [hden, hden_small]
      ring_nf
      rw [hsqrt3]
      rw [hsqrt]
      ring_nf
      have hden148 : 148 - Real.sqrt 7 * 55 ≠ 0 := by
        intro h
        nlinarith [hsqrt]
      rw [show
        -(Real.sqrt 7 * (148 - Real.sqrt 7 * 55)⁻¹ * 75230208) +
            (148 - Real.sqrt 7 * 55)⁻¹ * 202010112 =
          (202010112 - Real.sqrt 7 * 75230208) * (148 - Real.sqrt 7 * 55)⁻¹ by
        ring]
      rw [mul_inv_eq_iff_eq_mul₀ hden148]
      ring_nf
      rw [hsqrt]
      ring

end Omega.Zeta
