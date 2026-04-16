import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Screen audit cost monotone unit drop

This file formalizes the monotonicity and unit-drop bound for an abstract audit cost on finite
screens. The cost is antitone under adding observations, and each new observation can reduce the
cost by at most one.
-/

namespace Omega.SPG.ScreenAuditCostMonotoneUnitDrop

open Finset

/-- Auxiliary induction: adjoining a finite disjoint family can lower the audit cost by at most its
cardinality.
    cor:spg-screen-audit-cost-monotone-unit-drop -/
lemma cost_insert_bound
    {α : Type*} [DecidableEq α] (S : Finset α) (cost : Finset α → ℕ)
    (hdrop : ∀ {A : Finset α} {a : α}, a ∉ A → cost A ≤ cost (insert a A) + 1) :
    ∀ U : Finset α, Disjoint S U → cost S ≤ cost (S ∪ U) + U.card := by
  intro U
  refine Finset.induction_on U ?_ ?_
  · intro _hdisj
    simp
  · intro a U ha ih hdisj
    have hdisj' : Disjoint S U := hdisj.mono_right (by
      intro x hx
      exact mem_insert_of_mem hx)
    have hnotS : a ∉ S := by
      intro has
      exact Finset.disjoint_left.mp hdisj has (mem_insert_self a U)
    have hnotSU : a ∉ S ∪ U := by
      simp [ha, hnotS]
    have hstep := hdrop (A := S ∪ U) (a := a) hnotSU
    calc
      cost S ≤ cost (S ∪ U) + U.card := ih hdisj'
      _ ≤ cost (insert a (S ∪ U)) + (U.card + 1) := by omega
      _ = cost (S ∪ insert a U) + (insert a U).card := by simp [ha]

/-- Paper seed: audit cost is monotone under adding rows, and adjoining `k` rows changes it by at
most `k`.
    cor:spg-screen-audit-cost-monotone-unit-drop -/
theorem paper_spg_screen_audit_cost_monotone_unit_drop_seeds
    {α : Type} [DecidableEq α] (S T : Finset α) (hST : S ⊆ T) (cost : Finset α → ℕ)
    (hmono : ∀ {A B : Finset α}, A ⊆ B → cost B ≤ cost A)
    (hdrop : ∀ {A : Finset α} {a : α}, a ∉ A → cost A ≤ cost (insert a A) + 1) :
    cost T ≤ cost S ∧ cost S ≤ cost T + (T \ S).card := by
  refine ⟨hmono hST, ?_⟩
  have hdisj : Disjoint S (T \ S) := disjoint_sdiff
  have hbound := cost_insert_bound S cost hdrop (T \ S) hdisj
  have hunion : S ∪ (T \ S) = T := by
    simpa [union_comm] using sdiff_union_of_subset hST
  simpa [hunion] using hbound

/-- Paper-facing package clone for the screen audit cost monotonicity/unit-drop theorem.
    cor:spg-screen-audit-cost-monotone-unit-drop -/
theorem paper_spg_screen_audit_cost_monotone_unit_drop_package
    {α : Type} [DecidableEq α] (S T : Finset α) (hST : S ⊆ T) (cost : Finset α → ℕ)
    (hmono : ∀ {A B : Finset α}, A ⊆ B → cost B ≤ cost A)
    (hdrop : ∀ {A : Finset α} {a : α}, a ∉ A → cost A ≤ cost (insert a A) + 1) :
    cost T ≤ cost S ∧ cost S ≤ cost T + (T \ S).card :=
  paper_spg_screen_audit_cost_monotone_unit_drop_seeds S T hST cost hmono hdrop

/-- Unsuffixed paper-facing theorem for the screen audit cost monotonicity/unit-drop package.
    cor:spg-screen-audit-cost-monotone-unit-drop -/
theorem paper_spg_screen_audit_cost_monotone_unit_drop
    {α : Type} [DecidableEq α] (S T : Finset α) (hST : S ⊆ T) (cost : Finset α → ℕ)
    (hmono : ∀ {A B : Finset α}, A ⊆ B → cost B ≤ cost A)
    (hdrop : ∀ {A : Finset α} {a : α}, a ∉ A → cost A ≤ cost (insert a A) + 1) :
    cost T ≤ cost S ∧ cost S ≤ cost T + (T \ S).card :=
  paper_spg_screen_audit_cost_monotone_unit_drop_package S T hST cost hmono hdrop

end Omega.SPG.ScreenAuditCostMonotoneUnitDrop
