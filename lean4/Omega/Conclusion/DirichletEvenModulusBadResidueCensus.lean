import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- A finite mean-square lower bound forces at least one residue class to reach the corresponding
absolute-value threshold.
    thm:conclusion-dirichlet-even-modulus-bad-residue-census -/
theorem paper_conclusion_dirichlet_even_modulus_bad_residue_census {m : ℕ} (hm : 0 < m)
    (E : Fin m → ℝ) (pminus : ℝ)
    (hmean :
      (∑ a : Fin m, (E a)^2) / (m : ℝ) ≥ pminus^2 / (m : ℝ)^2) :
    ∃ a : Fin m, |E a| ≥ |pminus| / (m : ℝ) := by
  classical
  let threshold : ℝ := |pminus| / (m : ℝ)
  let a0 : Fin m := ⟨0, hm⟩
  have hm_pos_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos_real
  have hthreshold_sq : threshold ^ 2 = pminus ^ 2 / (m : ℝ) ^ 2 := by
    dsimp [threshold]
    rw [div_pow, sq_abs]
  by_contra hNo
  have hlt : ∀ a : Fin m, |E a| < threshold := by
    intro a
    exact not_le.mp (fun ha => hNo ⟨a, by simpa [threshold] using ha⟩)
  have hsq_lt : ∀ a : Fin m, (E a) ^ 2 < threshold ^ 2 := by
    intro a
    have hnonneg : 0 ≤ threshold := div_nonneg (abs_nonneg _) (le_of_lt hm_pos_real)
    have hsq_abs : |E a| ^ 2 < threshold ^ 2 :=
      (sq_lt_sq₀ (abs_nonneg _) hnonneg).mpr (hlt a)
    simpa [sq_abs] using hsq_abs
  have hsum_lt :
      (∑ a : Fin m, (E a) ^ 2) < ∑ _a : Fin m, threshold ^ 2 := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro a ha
      exact le_of_lt (hsq_lt a)
    · exact ⟨a0, by simp [a0], hsq_lt a0⟩
  have havg_lt : (∑ a : Fin m, (E a) ^ 2) / (m : ℝ) < threshold ^ 2 := by
    calc
      (∑ a : Fin m, (E a) ^ 2) / (m : ℝ)
          < (∑ _a : Fin m, threshold ^ 2) / (m : ℝ) := by
              exact div_lt_div_of_pos_right hsum_lt hm_pos_real
      _ = threshold ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul, hm_ne]
  have hcontr : threshold ^ 2 ≤ (∑ a : Fin m, (E a) ^ 2) / (m : ℝ) := by
    simpa [hthreshold_sq] using hmean
  exact not_lt_of_ge hcontr havg_lt

end Omega.Conclusion
