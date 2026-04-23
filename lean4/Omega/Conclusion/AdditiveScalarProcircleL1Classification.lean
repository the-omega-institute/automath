import Mathlib.Analysis.PSeries
import Mathlib.Tactic
import Omega.Conclusion.AdditiveScalarProcircleObstruction

namespace Omega.Conclusion

noncomputable section

/-- Concrete `ℓ¹` weight profile used for the additive-scalar `pro`-circle classification seed. -/
def conclusion_additive_scalar_procircle_l1_classification_weights (p : ℕ) : ℝ :=
  ((p : ℝ) ^ 2)⁻¹

/-- Paper-facing `ℓ¹` classification seed: the weight profile is summable, constant profiles and
bounded multiplicity profiles are evaluated by absolutely convergent series, uniqueness is pointwise,
and the existing obstruction theorem rules out any uniform positive lower bound under a global cap. -/
def conclusion_additive_scalar_procircle_l1_classification_statement : Prop :=
  let w := conclusion_additive_scalar_procircle_l1_classification_weights
  Summable w ∧
    (∀ M : ℕ, Summable (fun p => (M : ℝ) * w p)) ∧
    (∀ (m : ℕ → ℕ) (M : ℕ), (∀ p, m p ≤ M) → Summable (fun p => (m p : ℝ) * w p)) ∧
    (∀ M : ℕ, ∑' p, (M : ℝ) * w p = (M : ℝ) * ∑' p, w p) ∧
    (∀ v : ℕ → ℝ, (∀ p, v p = w p) → v = w) ∧
    (∀ (Dhat c0 : ENNReal) (D : ℕ → ENNReal), 0 < c0 →
      (∀ n : ℕ, (n : ENNReal) * c0 ≤ D n) →
        (∀ n : ℕ, D n ≤ Dhat) → Dhat = ⊤)

/-- Paper label: `thm:conclusion-additive-scalar-procircle-l1-classification`. -/
theorem paper_conclusion_additive_scalar_procircle_l1_classification :
    conclusion_additive_scalar_procircle_l1_classification_statement := by
  dsimp [conclusion_additive_scalar_procircle_l1_classification_statement]
  have hsummable_w : Summable conclusion_additive_scalar_procircle_l1_classification_weights := by
    convert (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)) using 1
    funext p
    simp [conclusion_additive_scalar_procircle_l1_classification_weights]
  refine ⟨hsummable_w, ?_, ?_, ?_, ?_, ?_⟩
  · intro M
    exact hsummable_w.mul_left (M : ℝ)
  · intro m M hm
    have hconst :
        Summable (fun p => (M : ℝ) * conclusion_additive_scalar_procircle_l1_classification_weights p) := by
      exact hsummable_w.mul_left (M : ℝ)
    refine hconst.of_nonneg_of_le ?_ ?_
    · intro p
      exact mul_nonneg (show 0 ≤ (m p : ℝ) by exact_mod_cast Nat.zero_le _) <|
        inv_nonneg.mpr (sq_nonneg (p : ℝ))
    · intro p
      have hm' : (m p : ℝ) ≤ M := by
        exact_mod_cast hm p
      have hw_nonneg : 0 ≤ conclusion_additive_scalar_procircle_l1_classification_weights p := by
        exact inv_nonneg.mpr (sq_nonneg (p : ℝ))
      nlinarith
  · intro M
    simpa using hsummable_w.tsum_mul_left (M : ℝ)
  · intro v hv
    funext p
    exact hv p
  · intro Dhat c0 D hc0 hlower hupper
    exact paper_conclusion_additive_scalar_procircle_obstruction Dhat c0 D hc0 hlower hupper

end

end Omega.Conclusion
