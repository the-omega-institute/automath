import Mathlib.Analysis.PSeries
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Positive summable weight profile for the weighted `pro`-circle model. -/
def conclusion_additive_scalar_procircle_weighted_model_weights (p : ℕ) : ℝ :=
  (((p : ℝ) + 1) ^ 2)⁻¹

/-- Paper label: `cor:conclusion-additive-scalar-procircle-weighted-model`. -/
theorem paper_conclusion_additive_scalar_procircle_weighted_model :
    ∃ w : ℕ → ℝ, Summable w ∧ (∀ p, 0 < w p) ∧
      (∀ M : ℕ, Summable (fun p => (M : ℝ) * w p)) ∧
      (∀ m : ℕ → ℕ, (∃ M : ℕ, ∀ p, m p ≤ M) → Summable (fun p => (m p : ℝ) * w p)) := by
  refine ⟨conclusion_additive_scalar_procircle_weighted_model_weights, ?_⟩
  have hsummable_w : Summable conclusion_additive_scalar_procircle_weighted_model_weights := by
    have hbase : Summable (fun p : ℕ => ((p : ℝ) ^ 2)⁻¹) := by
      convert (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)) using 1
      funext p
      simp
    simpa [conclusion_additive_scalar_procircle_weighted_model_weights] using
      (summable_nat_add_iff 1).2 hbase
  refine ⟨hsummable_w, ?_, ?_, ?_⟩
  · intro p
    have hpos : 0 < ((p : ℝ) + 1) ^ 2 := by positivity
    simpa [conclusion_additive_scalar_procircle_weighted_model_weights] using inv_pos.mpr hpos
  · intro M
    exact hsummable_w.mul_left (M : ℝ)
  · intro m hm
    rcases hm with ⟨M, hM⟩
    have hconst :
        Summable
          (fun p => (M : ℝ) * conclusion_additive_scalar_procircle_weighted_model_weights p) := by
      exact hsummable_w.mul_left (M : ℝ)
    refine hconst.of_nonneg_of_le ?_ ?_
    · intro p
      exact mul_nonneg (show 0 ≤ (m p : ℝ) by exact_mod_cast Nat.zero_le _) <|
        inv_nonneg.mpr (sq_nonneg ((p : ℝ) + 1))
    · intro p
      have hm' : (m p : ℝ) ≤ M := by
        exact_mod_cast hM p
      have hw_nonneg :
          0 ≤ conclusion_additive_scalar_procircle_weighted_model_weights p := by
        exact inv_nonneg.mpr (sq_nonneg ((p : ℝ) + 1))
      nlinarith

end

end Omega.Conclusion
