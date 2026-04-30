import Omega.Conclusion.BigwittBudgetDecidableIdentityUndecidable

namespace Omega.Conclusion

/-- A finite obstruction vector has a nontrivial resonance exactly when some entry is nonzero. -/
def conclusion_resonance_decidable_fredholm_identity_undecidable_layer_local_resonance
    (obstructions : List ℕ) : Prop :=
  obstructions.any (fun n => n != 0) = true

/-- The terminating audit budget for finite obstruction data. -/
def conclusion_resonance_decidable_fredholm_identity_undecidable_layer_audit_budget
    (obstructions : List ℕ) : ℕ :=
  obstructions.length

/-- The Fredholm identity undecidability predicate reused from the Big--Witt wrapper. -/
def conclusion_resonance_decidable_fredholm_identity_undecidable_layer_fredholm_undecidable
    (D : conclusion_bigwitt_budget_decidable_identity_undecidable_data) : Prop :=
  conclusion_bigwitt_budget_decidable_identity_undecidable_identity_undecidable D

/-- Concrete logical split: finite local resonance is decidable, while Fredholm identity is not. -/
def conclusion_resonance_decidable_fredholm_identity_undecidable_layer_statement : Prop :=
  (∀ obstructions : List ℕ,
    (conclusion_resonance_decidable_fredholm_identity_undecidable_layer_local_resonance
        obstructions ↔
      obstructions.any (fun n => n != 0) = true) ∧
      Nonempty
        (Decidable
          (conclusion_resonance_decidable_fredholm_identity_undecidable_layer_local_resonance
            obstructions)) ∧
        conclusion_resonance_decidable_fredholm_identity_undecidable_layer_audit_budget
            obstructions =
          obstructions.length) ∧
    (∀ D : conclusion_bigwitt_budget_decidable_identity_undecidable_data,
      conclusion_resonance_decidable_fredholm_identity_undecidable_layer_fredholm_undecidable D)

/-- Paper label: `thm:conclusion-resonance-decidable-fredholm-identity-undecidable-layer`. -/
theorem paper_conclusion_resonance_decidable_fredholm_identity_undecidable_layer :
    conclusion_resonance_decidable_fredholm_identity_undecidable_layer_statement := by
  refine ⟨?_, ?_⟩
  · intro obstructions
    refine ⟨Iff.rfl, ?_, rfl⟩
    exact ⟨by
      unfold conclusion_resonance_decidable_fredholm_identity_undecidable_layer_local_resonance
      infer_instance⟩
  · intro D
    exact (paper_conclusion_bigwitt_budget_decidable_identity_undecidable D).2

end Omega.Conclusion
