import Mathlib.Tactic

namespace Omega.StatisticalStability.ResidueClassification

/-- prop:stable-predicate-residue-classification -/
theorem paper_stable_predicate_residue_classification_seeds
    {Ω R X : Type} (fold : Ω → X) (s : R → X) (r : Ω → R)
    (hfactor : ∀ ω, fold ω = s (r ω)) (P : Set X) (ω : Ω) :
    fold ω ∈ P ↔ r ω ∈ s ⁻¹' P := by
  simp [hfactor, Set.mem_preimage]

theorem paper_stable_predicate_residue_classification_package
    {Ω R X : Type} (fold : Ω → X) (s : R → X) (r : Ω → R)
    (hfactor : ∀ ω, fold ω = s (r ω)) (P : Set X) (ω : Ω) :
    fold ω ∈ P ↔ r ω ∈ s ⁻¹' P :=
  paper_stable_predicate_residue_classification_seeds fold s r hfactor P ω

end Omega.StatisticalStability.ResidueClassification
