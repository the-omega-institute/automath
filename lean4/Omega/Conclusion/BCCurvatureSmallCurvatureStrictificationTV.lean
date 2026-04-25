import Mathlib

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-bc-small-curvature-strictification-tv`. Bounding every
Beck--Chevalley layer energy by `ε` bounds the total KL defect and, via Pinsker, the total
variation distance. -/
theorem paper_conclusion_bc_small_curvature_strictification_tv {k : ℕ} (hk : 2 ≤ k) {ε D tv : ℝ}
    (E : Fin (k - 1) → ℝ) (hdecomp : D = (1 / 2 : ℝ) * ∑ i : Fin (k - 1), E i)
    (hbound : ∀ i, E i ≤ ε) (hpinsker : tv ≤ Real.sqrt (D / 2)) :
    D ≤ ((k - 1 : ℕ) : ℝ) * ε / 2 ∧ tv ≤ Real.sqrt (((k - 1 : ℕ) : ℝ) * ε / 4) := by
  have hk1_pos_nat : 0 < k - 1 := by
    omega
  have hk1_nonneg : 0 ≤ ((k - 1 : ℕ) : ℝ) := by
    exact le_of_lt (by exact_mod_cast hk1_pos_nat)
  have hsum_le : ∑ i : Fin (k - 1), E i ≤ ((k - 1 : ℕ) : ℝ) * ε := by
    calc
      ∑ i : Fin (k - 1), E i ≤ ∑ _i : Fin (k - 1), ε := by
        exact Finset.sum_le_sum (fun i _ => hbound i)
      _ = ((k - 1 : ℕ) : ℝ) * ε := by simp
  have hD_le : D ≤ ((k - 1 : ℕ) : ℝ) * ε / 2 := by
    rw [hdecomp]
    linarith
  have htv_le : tv ≤ Real.sqrt (((k - 1 : ℕ) : ℝ) * ε / 4) := by
    have hinner : D / 2 ≤ ((k - 1 : ℕ) : ℝ) * ε / 4 := by
      linarith [hD_le, hk1_nonneg]
    exact hpinsker.trans (Real.sqrt_le_sqrt hinner)
  exact ⟨hD_le, htv_le⟩

end Omega.Conclusion
