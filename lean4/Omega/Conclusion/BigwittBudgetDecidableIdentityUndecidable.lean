import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite Big--Witt budget data plus a Fredholm identity undecidability witness set. -/
structure conclusion_bigwitt_budget_decidable_identity_undecidable_data where
  conclusion_bigwitt_budget_decidable_identity_undecidable_atomCount : ℕ
  conclusion_bigwitt_budget_decidable_identity_undecidable_multiplicity :
    Fin conclusion_bigwitt_budget_decidable_identity_undecidable_atomCount → ℕ
  conclusion_bigwitt_budget_decidable_identity_undecidable_period :
    Fin conclusion_bigwitt_budget_decidable_identity_undecidable_atomCount → ℕ
  conclusion_bigwitt_budget_decidable_identity_undecidable_fredholmIdentityProblem : Set ℕ
  conclusion_bigwitt_budget_decidable_identity_undecidable_fredholmIdentityUndecidable :
    ¬ ∃ decider : ℕ → Bool,
      ∀ n,
        decider n = true ↔
          n ∈ conclusion_bigwitt_budget_decidable_identity_undecidable_fredholmIdentityProblem

/-- Closed finite formula for the exact Big--Witt realization budget. -/
def conclusion_bigwitt_budget_decidable_identity_undecidable_budget
    (D : conclusion_bigwitt_budget_decidable_identity_undecidable_data) : ℕ :=
  ∑ j,
    D.conclusion_bigwitt_budget_decidable_identity_undecidable_multiplicity j *
      D.conclusion_bigwitt_budget_decidable_identity_undecidable_period j

/-- The finite budget side is decidable because the closed formula is a natural number. -/
def conclusion_bigwitt_budget_decidable_identity_undecidable_budget_decidable
    (D : conclusion_bigwitt_budget_decidable_identity_undecidable_data) : Prop :=
  ∃ budget : ℕ,
    budget = conclusion_bigwitt_budget_decidable_identity_undecidable_budget D ∧
      Nonempty
        (Decidable (budget = conclusion_bigwitt_budget_decidable_identity_undecidable_budget D))

/-- The Fredholm identity side has no uniform Boolean decider on the recorded problem set. -/
def conclusion_bigwitt_budget_decidable_identity_undecidable_identity_undecidable
    (D : conclusion_bigwitt_budget_decidable_identity_undecidable_data) : Prop :=
  ¬ ∃ decider : ℕ → Bool,
    ∀ n,
      decider n = true ↔
        n ∈ D.conclusion_bigwitt_budget_decidable_identity_undecidable_fredholmIdentityProblem

namespace conclusion_bigwitt_budget_decidable_identity_undecidable_data

/-- The computable budget formula coexists with undecidable Fredholm identity equivalence. -/
def conclusion_bigwitt_budget_decidable_identity_undecidable_statement
    (D : conclusion_bigwitt_budget_decidable_identity_undecidable_data) : Prop :=
  conclusion_bigwitt_budget_decidable_identity_undecidable_budget_decidable D ∧
    conclusion_bigwitt_budget_decidable_identity_undecidable_identity_undecidable D

end conclusion_bigwitt_budget_decidable_identity_undecidable_data

/-- Paper label: `thm:conclusion-bigwitt-budget-decidable-identity-undecidable`. -/
theorem paper_conclusion_bigwitt_budget_decidable_identity_undecidable
    (D : conclusion_bigwitt_budget_decidable_identity_undecidable_data) :
    D.conclusion_bigwitt_budget_decidable_identity_undecidable_statement := by
  refine ⟨?_, ?_⟩
  · refine ⟨conclusion_bigwitt_budget_decidable_identity_undecidable_budget D, rfl, ?_⟩
    exact ⟨inferInstance⟩
  · exact D.conclusion_bigwitt_budget_decidable_identity_undecidable_fredholmIdentityUndecidable

end Omega.Conclusion
