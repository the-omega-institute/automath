import Mathlib

open Filter
open scoped BigOperators Topology

namespace Omega.Conclusion

noncomputable section

/-- Eventual upper-bound form of a limsup inequality. -/
def conclusion_solenoidal_rh_fold_strong_converse_eventualUpper
    (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ m in atTop, u m ≤ a + ε

/-- Concrete success formula and asymptotic-transfer data for the fold strong converse. -/
structure conclusion_solenoidal_rh_fold_strong_converse_data where
  conclusion_solenoidal_rh_fold_strong_converse_card : ℕ → ℕ
  conclusion_solenoidal_rh_fold_strong_converse_fiber :
    ∀ m, Fin (conclusion_solenoidal_rh_fold_strong_converse_card m) → ℕ
  conclusion_solenoidal_rh_fold_strong_converse_budget : ℕ → ℕ
  conclusion_solenoidal_rh_fold_strong_converse_success : ℕ → ℕ → ℝ
  conclusion_solenoidal_rh_fold_strong_converse_success_formula :
    ∀ m B,
      conclusion_solenoidal_rh_fold_strong_converse_success m B =
        ((2 : ℝ) ^ m)⁻¹ *
          ∑ x : Fin (conclusion_solenoidal_rh_fold_strong_converse_card m),
            (min
              (conclusion_solenoidal_rh_fold_strong_converse_fiber m x)
              (2 ^ B) : ℝ)
  conclusion_solenoidal_rh_fold_strong_converse_successLogRate : ℕ → ℝ
  conclusion_solenoidal_rh_fold_strong_converse_budgetLogRate : ℕ → ℝ
  conclusion_solenoidal_rh_fold_strong_converse_threshold : ℝ
  conclusion_solenoidal_rh_fold_strong_converse_limsup_transfer :
    (∀ m,
      conclusion_solenoidal_rh_fold_strong_converse_success m
          (conclusion_solenoidal_rh_fold_strong_converse_budget m) ≤
        ((2 : ℝ) ^ m)⁻¹ *
          (conclusion_solenoidal_rh_fold_strong_converse_card m : ℝ) *
            (2 : ℝ) ^ conclusion_solenoidal_rh_fold_strong_converse_budget m) →
      conclusion_solenoidal_rh_fold_strong_converse_eventualUpper
        conclusion_solenoidal_rh_fold_strong_converse_successLogRate
        (limsup conclusion_solenoidal_rh_fold_strong_converse_budgetLogRate atTop -
          conclusion_solenoidal_rh_fold_strong_converse_threshold)

namespace conclusion_solenoidal_rh_fold_strong_converse_data

def conclusion_solenoidal_rh_fold_strong_converse_pointwiseBound
    (D : conclusion_solenoidal_rh_fold_strong_converse_data) : Prop :=
  ∀ m,
    D.conclusion_solenoidal_rh_fold_strong_converse_success m
        (D.conclusion_solenoidal_rh_fold_strong_converse_budget m) ≤
      ((2 : ℝ) ^ m)⁻¹ *
        (D.conclusion_solenoidal_rh_fold_strong_converse_card m : ℝ) *
          (2 : ℝ) ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m

def conclusion_solenoidal_rh_fold_strong_converse_claim
    (D : conclusion_solenoidal_rh_fold_strong_converse_data) : Prop :=
  D.conclusion_solenoidal_rh_fold_strong_converse_pointwiseBound ∧
    conclusion_solenoidal_rh_fold_strong_converse_eventualUpper
      D.conclusion_solenoidal_rh_fold_strong_converse_successLogRate
      (limsup D.conclusion_solenoidal_rh_fold_strong_converse_budgetLogRate atTop -
        D.conclusion_solenoidal_rh_fold_strong_converse_threshold)

end conclusion_solenoidal_rh_fold_strong_converse_data

open conclusion_solenoidal_rh_fold_strong_converse_data

/-- Paper label: `thm:conclusion-solenoidal-rh-fold-strong-converse`. -/
theorem paper_conclusion_solenoidal_rh_fold_strong_converse
    (D : conclusion_solenoidal_rh_fold_strong_converse_data) :
    conclusion_solenoidal_rh_fold_strong_converse_claim D := by
  have hpoint :
      D.conclusion_solenoidal_rh_fold_strong_converse_pointwiseBound := by
    intro m
    rw [D.conclusion_solenoidal_rh_fold_strong_converse_success_formula]
    have hsum :
        (∑ x : Fin (D.conclusion_solenoidal_rh_fold_strong_converse_card m),
            (min
              (D.conclusion_solenoidal_rh_fold_strong_converse_fiber m x)
              (2 ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m) : ℝ)) ≤
          (D.conclusion_solenoidal_rh_fold_strong_converse_card m : ℝ) *
            (2 : ℝ) ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m := by
      calc
        (∑ x : Fin (D.conclusion_solenoidal_rh_fold_strong_converse_card m),
            (min
              (D.conclusion_solenoidal_rh_fold_strong_converse_fiber m x)
              (2 ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m) : ℝ))
            ≤ ∑ _x : Fin (D.conclusion_solenoidal_rh_fold_strong_converse_card m),
                ((2 : ℕ) ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m : ℝ) := by
              refine Finset.sum_le_sum ?_
              intro x hx
              exact_mod_cast Nat.min_le_right
                (D.conclusion_solenoidal_rh_fold_strong_converse_fiber m x)
                (2 ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m)
        _ = (D.conclusion_solenoidal_rh_fold_strong_converse_card m : ℝ) *
              (2 : ℝ) ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m := by
              norm_num
    have hnonneg : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
    calc
      ((2 : ℝ) ^ m)⁻¹ *
          (∑ x : Fin (D.conclusion_solenoidal_rh_fold_strong_converse_card m),
            (min
              (D.conclusion_solenoidal_rh_fold_strong_converse_fiber m x)
              (2 ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m) : ℝ))
          ≤
        ((2 : ℝ) ^ m)⁻¹ *
          ((D.conclusion_solenoidal_rh_fold_strong_converse_card m : ℝ) *
            (2 : ℝ) ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m) := by
            exact mul_le_mul_of_nonneg_left hsum hnonneg
      _ =
        ((2 : ℝ) ^ m)⁻¹ *
          (D.conclusion_solenoidal_rh_fold_strong_converse_card m : ℝ) *
            (2 : ℝ) ^ D.conclusion_solenoidal_rh_fold_strong_converse_budget m := by
            ring
  exact ⟨hpoint, D.conclusion_solenoidal_rh_fold_strong_converse_limsup_transfer hpoint⟩

end

end Omega.Conclusion
