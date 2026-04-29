import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part64b-optimal-partial-invertibility-overflow`. -/
theorem paper_xi_time_part64b_optimal_partial_invertibility_overflow {X : Type*}
    [Fintype X] (m B : ℕ) (d : X → ℕ)
    (h_total : (Finset.univ.sum fun x : X => d x) = 2 ^ m) :
    1 - ((((Finset.univ.sum fun x : X => min (d x) (2 ^ B)) : ℕ) : ℝ) /
        (2 ^ m : ℝ)) =
      ((((Finset.univ.sum fun x : X => d x - min (d x) (2 ^ B)) : ℕ) : ℝ) /
        (2 ^ m : ℝ)) := by
  classical
  let capped : X → ℕ := fun x => min (d x) (2 ^ B)
  have h_capped_le_total : Finset.univ.sum capped ≤ Finset.univ.sum fun x : X => d x := by
    exact Finset.sum_le_sum fun x _ => min_le_left (d x) (2 ^ B)
  have h_capped_le_pow : Finset.univ.sum capped ≤ 2 ^ m := by
    simpa [h_total] using h_capped_le_total
  have h_overflow_sum :
      (Finset.univ.sum fun x : X => d x - capped x) =
        (Finset.univ.sum fun x : X => d x) - Finset.univ.sum capped := by
    simpa using
      (Finset.sum_tsub_distrib (Finset.univ) (f := d) (g := capped)
        (by intro x _; exact min_le_left (d x) (2 ^ B)))
  have hden_ne : (2 ^ m : ℝ) ≠ 0 := by
    exact pow_ne_zero m (by norm_num : (2 : ℝ) ≠ 0)
  have hpow_cast : ((2 ^ m : ℕ) : ℝ) = (2 ^ m : ℝ) := by
    norm_num
  calc
    1 - ((((Finset.univ.sum fun x : X => min (d x) (2 ^ B)) : ℕ) : ℝ) /
        (2 ^ m : ℝ)) =
        1 - (((Finset.univ.sum capped : ℕ) : ℝ) / (2 ^ m : ℝ)) := by
      simp [capped]
    _ =
        ((2 ^ m : ℝ) - ((Finset.univ.sum capped : ℕ) : ℝ)) / (2 ^ m : ℝ) := by
      field_simp [hden_ne]
    _ = (((2 ^ m - Finset.univ.sum capped : ℕ) : ℝ) / (2 ^ m : ℝ)) := by
      rw [← hpow_cast, Nat.cast_sub h_capped_le_pow]
    _ =
        ((((Finset.univ.sum fun x : X => d x) - Finset.univ.sum capped : ℕ) : ℝ) /
          (2 ^ m : ℝ)) := by
      rw [← h_total]
    _ =
        ((((Finset.univ.sum fun x : X => d x - min (d x) (2 ^ B)) : ℕ) : ℝ) /
          (2 ^ m : ℝ)) := by
      rw [← h_overflow_sum]

end Omega.Zeta
