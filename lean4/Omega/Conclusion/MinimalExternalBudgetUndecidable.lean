import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import Omega.Conclusion.SemanticEquivalenceUndecidable

namespace Omega.Conclusion

open scoped Classical

/-- A side-information budget `B` is feasible for a finite projection when every fiber admits an
injective residual index in `Fin B`. -/
def conclusion_minimal_external_budget_undecidable_budget_feasible
    {α β : Type*} [Fintype α] [DecidableEq β] (π : α → β) (B : ℕ) : Prop :=
  ∀ y : β, Nonempty ({x : α // π x = y} ↪ Fin B)

/-- The size of one concrete fiber of a finite projection. -/
def conclusion_minimal_external_budget_undecidable_fiberSize
    {α β : Type*} [Fintype α] [DecidableEq β] (π : α → β) (y : β) : ℕ :=
  Fintype.card {x : α // π x = y}

/-- The maximal finite fiber size, used as the concrete minimal external budget. -/
def conclusion_minimal_external_budget_undecidable_maxFiberSize
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (π : α → β) : ℕ :=
  Finset.univ.sup fun y => conclusion_minimal_external_budget_undecidable_fiberSize π y

/-- Minimal external budget on the finite-fiber model. -/
def conclusion_minimal_external_budget_undecidable_minimalExternalBudget
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (π : α → β) : ℕ :=
  conclusion_minimal_external_budget_undecidable_maxFiberSize π

lemma conclusion_minimal_external_budget_undecidable_budget_feasible_iff_fiber_bound
    {α β : Type*} [Fintype α] [DecidableEq β] (π : α → β) (B : ℕ) :
    conclusion_minimal_external_budget_undecidable_budget_feasible π B ↔
      ∀ y : β, conclusion_minimal_external_budget_undecidable_fiberSize π y ≤ B := by
  constructor
  · intro h y
    rcases h y with ⟨idx⟩
    simpa [conclusion_minimal_external_budget_undecidable_fiberSize, Fintype.card_fin] using
      Fintype.card_le_of_embedding idx
  · intro h y
    exact
      Function.Embedding.nonempty_of_card_le
        (by
          simpa [conclusion_minimal_external_budget_undecidable_fiberSize, Fintype.card_fin] using
            h y)

lemma conclusion_minimal_external_budget_undecidable_minimalExternalBudget_eq_maxFiberSize
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (π : α → β) :
    conclusion_minimal_external_budget_undecidable_minimalExternalBudget π =
      conclusion_minimal_external_budget_undecidable_maxFiberSize π := by
  rfl

/-- The finite-fiber projection/budget identity used by the paper-facing theorem. -/
def conclusion_minimal_external_budget_undecidable_finite_fiber_budget_identity : Prop :=
  ∀ {α β : Type} [Fintype α] [DecidableEq β] (π : α → β) (B : ℕ),
    conclusion_minimal_external_budget_undecidable_budget_feasible π B ↔
      ∀ y : β, conclusion_minimal_external_budget_undecidable_fiberSize π y ≤ B

/-- The two-branch halting family has budget `1` before any halting witness and `2` after one. -/
noncomputable def conclusion_minimal_external_budget_undecidable_halting_projection_budget
    (haltsWithin : ℕ → ℕ → Prop) (e : ℕ) : ℕ :=
  if ∃ N, haltsWithin e N then 2 else 1

lemma conclusion_minimal_external_budget_undecidable_budget_eq_one_iff_not_halting
    {haltsWithin : ℕ → ℕ → Prop} {halts : ℕ → Prop}
    (hHalts : ∀ e, halts e ↔ ∃ N, haltsWithin e N) (e : ℕ) :
    conclusion_minimal_external_budget_undecidable_halting_projection_budget haltsWithin e = 1 ↔
      ¬ halts e := by
  classical
  by_cases h : ∃ N, haltsWithin e N
  · have hh : halts e := (hHalts e).2 h
    simp [conclusion_minimal_external_budget_undecidable_halting_projection_budget, h, hh]
  · have hh : ¬ halts e := by
      intro he
      exact h ((hHalts e).1 he)
    simp [conclusion_minimal_external_budget_undecidable_halting_projection_budget, h, hh]

/-- Paper-facing statement: finite-fiber budgets are exactly maximal fiber sizes, and the
machine-indexed `1` versus `2` budget family transfers halting undecidability to the predicate
that the minimal external budget is `1`. -/
def conclusion_minimal_external_budget_undecidable_statement : Prop :=
  conclusion_minimal_external_budget_undecidable_finite_fiber_budget_identity ∧
    ∀ (haltsWithin : ℕ → ℕ → Prop) (halts : ℕ → Prop),
      RelationPointwiseDecidable haltsWithin →
      (∀ e, halts e ↔ ∃ N, haltsWithin e N) →
      (∀ e N M, haltsWithin e N → N ≤ M → haltsWithin e M) →
      ¬ PredicatePointwiseDecidable halts →
      ¬ PredicatePointwiseDecidable fun e =>
        conclusion_minimal_external_budget_undecidable_halting_projection_budget
          haltsWithin e = 1

/-- Paper label: `thm:conclusion-minimal-external-budget-undecidable`. -/
theorem paper_conclusion_minimal_external_budget_undecidable :
    conclusion_minimal_external_budget_undecidable_statement := by
  constructor
  · intro α β _ _ π B
    exact conclusion_minimal_external_budget_undecidable_budget_feasible_iff_fiber_bound π B
  · intro haltsWithin halts _hStepDec hHalts _hMono hUndecidable hBudgetDec
    rcases hBudgetDec with ⟨hBudgetDecidable⟩
    apply hUndecidable
    refine ⟨?_⟩
    intro e
    letI := hBudgetDecidable e
    by_cases hbudget :
        conclusion_minimal_external_budget_undecidable_halting_projection_budget haltsWithin e = 1
    · exact
        isFalse fun he =>
          (conclusion_minimal_external_budget_undecidable_budget_eq_one_iff_not_halting
            hHalts e).mp hbudget he
    · exact
        isTrue
          (by
            by_contra he
            exact hbudget
              ((conclusion_minimal_external_budget_undecidable_budget_eq_one_iff_not_halting
                hHalts e).mpr he))

end Omega.Conclusion
