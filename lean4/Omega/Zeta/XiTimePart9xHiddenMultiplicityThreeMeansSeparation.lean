import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

lemma xi_time_part9x_hidden_multiplicity_three_means_separation_two_bound :
    Real.rpow (2 : ℝ) (11 / 8 : ℝ) < (13 : ℝ) / 5 := by
  have hpow : (2 : ℝ) ^ 11 < ((13 : ℝ) / 5) ^ 8 := by
    norm_num
  have hroot := Real.rpow_lt_rpow (by positivity : 0 ≤ (2 : ℝ) ^ 11) hpow
    (by norm_num : 0 < (1 / 8 : ℝ))
  change Real.rpow ((2 : ℝ) ^ 11) (1 / 8 : ℝ) <
    Real.rpow (((13 : ℝ) / 5) ^ 8) (1 / 8 : ℝ) at hroot
  have hleft : Real.rpow ((2 : ℝ) ^ 11) (1 / 8 : ℝ) =
      Real.rpow (2 : ℝ) (11 / 8 : ℝ) := by
    change ((2 : ℝ) ^ (11 : ℕ)) ^ (1 / 8 : ℝ) = Real.rpow (2 : ℝ) (11 / 8 : ℝ)
    rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)) 11 (1 / 8 : ℝ)]
    norm_num
  have hright : Real.rpow (((13 : ℝ) / 5) ^ 8) (1 / 8 : ℝ) = (13 : ℝ) / 5 := by
    change (((13 : ℝ) / 5) ^ (8 : ℕ)) ^ (1 / 8 : ℝ) = (13 : ℝ) / 5
    rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num : 0 ≤ (13 : ℝ) / 5)
      (by norm_num : (8 : ℕ) ≠ 0)
  rw [hleft, hright] at hroot
  exact hroot

lemma xi_time_part9x_hidden_multiplicity_three_means_separation_three_bound :
    Real.rpow (3 : ℝ) (3 / 16 : ℝ) < (5 : ℝ) / 4 := by
  have hpow : (3 : ℝ) ^ 3 < ((5 : ℝ) / 4) ^ 16 := by
    norm_num
  have hroot := Real.rpow_lt_rpow (by positivity : 0 ≤ (3 : ℝ) ^ 3) hpow
    (by norm_num : 0 < (1 / 16 : ℝ))
  change Real.rpow ((3 : ℝ) ^ 3) (1 / 16 : ℝ) <
    Real.rpow (((5 : ℝ) / 4) ^ 16) (1 / 16 : ℝ) at hroot
  have hleft : Real.rpow ((3 : ℝ) ^ 3) (1 / 16 : ℝ) =
      Real.rpow (3 : ℝ) (3 / 16 : ℝ) := by
    change ((3 : ℝ) ^ (3 : ℕ)) ^ (1 / 16 : ℝ) = Real.rpow (3 : ℝ) (3 / 16 : ℝ)
    rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (3 : ℝ)) 3 (1 / 16 : ℝ)]
    norm_num
  have hright : Real.rpow (((5 : ℝ) / 4) ^ 16) (1 / 16 : ℝ) = (5 : ℝ) / 4 := by
    change (((5 : ℝ) / 4) ^ (16 : ℕ)) ^ (1 / 16 : ℝ) = (5 : ℝ) / 4
    rw [show (1 / 16 : ℝ) = (16 : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by norm_num : 0 ≤ (5 : ℝ) / 4)
      (by norm_num : (16 : ℕ) ≠ 0)
  rw [hleft, hright] at hroot
  exact hroot

/-- Paper label: `cor:xi-time-part9x-hidden-multiplicity-three-means-separation`. -/
theorem paper_xi_time_part9x_hidden_multiplicity_three_means_separation :
    Real.rpow (2 : ℝ) (11 / 8 : ℝ) * Real.rpow (3 : ℝ) (3 / 16 : ℝ) <
        (53 : ℝ) / 16 ∧
      (53 : ℝ) / 16 < 4 := by
  refine ⟨?_, by norm_num⟩
  have h2 := xi_time_part9x_hidden_multiplicity_three_means_separation_two_bound
  have h3 := xi_time_part9x_hidden_multiplicity_three_means_separation_three_bound
  have hmul :
      Real.rpow (2 : ℝ) (11 / 8 : ℝ) * Real.rpow (3 : ℝ) (3 / 16 : ℝ) <
        ((13 : ℝ) / 5) * ((5 : ℝ) / 4) := by
    exact mul_lt_mul h2 (le_of_lt h3) (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
  nlinarith

end

end Omega.Zeta
