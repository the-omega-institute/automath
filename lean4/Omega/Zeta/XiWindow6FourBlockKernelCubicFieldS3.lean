import Mathlib.Tactic

namespace Omega.Zeta

/-- The mod-13 reduction of the integer cubic certificate. -/
def xi_window6_four_block_kernel_cubic_field_s3_mod13_poly (t : Fin 13) : ZMod 13 :=
  let x : ZMod 13 := t.val
  x ^ 3 + (9 : ZMod 13) * x ^ 2 + x + 10

/-- The displayed integer discriminant factorization for the cubic certificate. -/
def xi_window6_four_block_kernel_cubic_field_s3_disc : ℤ :=
  (2 : ℤ)^2 * 3^2 * 11^2 * 13^2 * 23

lemma xi_window6_four_block_kernel_cubic_field_s3_disc_not_square :
    ∀ n : ℤ, n * n ≠ xi_window6_four_block_kernel_cubic_field_s3_disc := by
  intro n h
  rw [xi_window6_four_block_kernel_cubic_field_s3_disc] at h
  norm_num at h
  have hmod : n * n % 5 = (16931772 : ℤ) % 5 := congrArg (fun z : ℤ => z % 5) h
  norm_num at hmod
  have hs : n * n % 5 = (n % 5) * (n % 5) % 5 := by
    rw [Int.mul_emod]
  have hnonneg : 0 ≤ n % 5 := Int.emod_nonneg n (by norm_num : (5 : ℤ) ≠ 0)
  have hlt : n % 5 < 5 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 5)
  interval_cases n % 5 <;> norm_num at hs <;> omega

/-- Paper label: `thm:xi-window6-four-block-kernel-cubic-field-s3`. -/
theorem paper_xi_window6_four_block_kernel_cubic_field_s3 :
    (∀ t : Fin 13, xi_window6_four_block_kernel_cubic_field_s3_mod13_poly t ≠ 0) ∧
      xi_window6_four_block_kernel_cubic_field_s3_disc =
        (2 : ℤ)^2 * 3^2 * 11^2 * 13^2 * 23 ∧
      (∀ n : ℤ, n * n ≠ xi_window6_four_block_kernel_cubic_field_s3_disc) := by
  refine ⟨?_, ?_, xi_window6_four_block_kernel_cubic_field_s3_disc_not_square⟩
  · intro t
    decide +revert
  · rfl

end Omega.Zeta
