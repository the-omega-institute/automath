import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.POM

/-- A finite injectivizing audit budget for the renewal/factor-code family `sizes` means that every
fiber `Fin (sizes n)` injects into one common finite audit alphabet `Fin B`. -/
def pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget
    (sizes : ℕ → ℕ) : Prop :=
  ∃ B : ℕ, ∀ n : ℕ, ∃ code : Fin (sizes n) → Fin B, Function.Injective code

lemma pom_finite_audit_budget_factorcode_undecidable_bounded_fibers_give_finite_audit_budget
    {sizes : ℕ → ℕ} (hbounded : ∃ B : ℕ, ∀ n : ℕ, sizes n ≤ B) :
    pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget sizes := by
  rcases hbounded with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n
  refine ⟨Fin.castLE (hB n), Fin.castLE_injective (hB n)⟩

lemma pom_finite_audit_budget_factorcode_undecidable_finite_audit_budget_gives_bounded_fibers
    {sizes : ℕ → ℕ}
    (haudit :
      pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget sizes) :
    ∃ B : ℕ, ∀ n : ℕ, sizes n ≤ B := by
  rcases haudit with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro n
  rcases hB n with ⟨code, hcode⟩
  simpa using Fintype.card_le_of_injective code hcode

lemma pom_finite_audit_budget_factorcode_undecidable_unbounded_fibers_give_no_finite_audit_budget
    {sizes : ℕ → ℕ} (hunbounded : ∀ B : ℕ, ∃ n : ℕ, B < sizes n) :
    ¬ pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget sizes := by
  intro haudit
  rcases
    pom_finite_audit_budget_factorcode_undecidable_finite_audit_budget_gives_bounded_fibers haudit
      with ⟨B, hB⟩
  rcases hunbounded B with ⟨n, hn⟩
  exact (not_lt_of_ge (hB n)) hn

/-- Paper label: `thm:pom-finite-audit-budget-factorcode-undecidable`.
The abstract renewal family `renewalFiberSize c n` packages the factor-code fiber of the
`n`-th renewal block for code `c`. Bounded fibers yield one finite audit alphabet by `Fin.castLE`,
any finite audit alphabet bounds every fiber by cardinality, and an unbounded family therefore
admits no finite injectivizing audit budget. Consequently, any halting reduction
`halts c ↔ ∃ B, ∀ n, renewalFiberSize c n ≤ B` transfers undecidability to the existence of a
finite injectivizing audit budget. -/
theorem paper_pom_finite_audit_budget_factorcode_undecidable
    {Code : Type*} (renewalFiberSize : Code → ℕ → ℕ) (halts : Code → Prop)
    (hReduction : ∀ c : Code, halts c ↔ ∃ B : ℕ, ∀ n : ℕ, renewalFiberSize c n ≤ B)
    (hUndecidable : ¬ Nonempty (∀ c : Code, Decidable (halts c))) :
    (∀ c : Code,
        (∃ B : ℕ, ∀ n : ℕ, renewalFiberSize c n ≤ B) →
          pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget
            (renewalFiberSize c)) ∧
      (∀ c : Code,
        pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget
            (renewalFiberSize c) →
          ∃ B : ℕ, ∀ n : ℕ, renewalFiberSize c n ≤ B) ∧
      (∀ c : Code,
        (∀ B : ℕ, ∃ n : ℕ, B < renewalFiberSize c n) →
          ¬ pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget
            (renewalFiberSize c)) ∧
      ¬ Nonempty
        (∀ c : Code,
          Decidable
            (pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget
              (renewalFiberSize c))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    exact pom_finite_audit_budget_factorcode_undecidable_bounded_fibers_give_finite_audit_budget
  · intro c
    exact
      pom_finite_audit_budget_factorcode_undecidable_finite_audit_budget_gives_bounded_fibers
  · intro c
    exact
      pom_finite_audit_budget_factorcode_undecidable_unbounded_fibers_give_no_finite_audit_budget
  · intro hBudgetDecidable
    apply hUndecidable
    refine ⟨?_⟩
    intro c
    have hBudgetIff :
        pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget
            (renewalFiberSize c) ↔
          ∃ B : ℕ, ∀ n : ℕ, renewalFiberSize c n ≤ B := by
      constructor
      · exact
          pom_finite_audit_budget_factorcode_undecidable_finite_audit_budget_gives_bounded_fibers
      · exact
          pom_finite_audit_budget_factorcode_undecidable_bounded_fibers_give_finite_audit_budget
    let hdec :
        Decidable
          (pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget
            (renewalFiberSize c)) :=
      Classical.choice hBudgetDecidable c
    exact decidable_of_iff
      (pom_finite_audit_budget_factorcode_undecidable_has_finite_injectivizing_audit_budget
        (renewalFiberSize c))
      ((hReduction c).trans hBudgetIff.symm).symm

end Omega.POM
