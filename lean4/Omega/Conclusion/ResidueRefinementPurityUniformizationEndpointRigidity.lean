import Omega.POM.ResidueRefinementJensen
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite fiber/refinement data for the residue-refinement endpoint package. -/
structure conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data where
  conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_fiberCount : ℕ
  conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount : ℕ
  conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount_pos :
    0 < conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount
  conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts :
    Fin conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_fiberCount →
      Fin conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount → ℕ
  conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_pure_endpoint :
    ∀ x a b,
      conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a ≠ 0 →
        conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x b ≠ 0 →
          a = b
  conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_uniform_endpoint :
    ∀ x a,
      conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount *
          conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a =
        ∑ b,
          conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x b

/-- The coarse q=2 fiber moment. -/
def conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_coarseMoment
    (D : conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data) : ℕ :=
  ∑ x,
    (∑ a,
      D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a) ^ 2

/-- The residue-refined q=2 fiber moment. -/
def conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_refinedMoment
    (D : conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data) : ℕ :=
  ∑ x,
    ∑ a,
      D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a ^ 2

/-- At the purity endpoint, each fiber has support in at most one residue class. -/
def conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_purityEndpoint
    (D : conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data) : Prop :=
  ∀ x a b,
    D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a ≠ 0 →
      D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x b ≠ 0 →
        a = b

/-- At the uniform endpoint, every residue count is the same fraction of the fiber total. -/
def conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_uniformEndpoint
    (D : conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data) : Prop :=
  ∀ x a,
    D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount *
        D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a =
      ∑ b,
        D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x b

/-- Integer uniformization forces divisibility of each coarse fiber by the residue count. -/
def conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_divisibility
    (D : conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data) : Prop :=
  ∀ x,
    D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount ∣
      ∑ a,
        D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a

/-- The normalized q=2 gap bounds, in cross-multiplied finite-moment form. -/
def conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_gapBounds
    (D : conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data) : Prop :=
  conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_refinedMoment D ≤
      conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_coarseMoment D ∧
    conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_coarseMoment D ≤
      D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount *
        conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_refinedMoment D

/-- Paper-facing package for residue-refinement endpoint rigidity. -/
def conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_statement
    (D : conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data) : Prop :=
  conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_purityEndpoint D ∧
    conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_uniformEndpoint D ∧
      conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_divisibility D ∧
        conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_gapBounds D

/-- Paper label:
`thm:conclusion-residue-refinement-purity-uniformization-endpoint-rigidity`. -/
theorem paper_conclusion_residue_refinement_purity_uniformization_endpoint_rigidity
    (D : conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_data) :
    conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_pure_endpoint
  · exact D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_uniform_endpoint
  · intro x
    let a0 : Fin
        D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount :=
      ⟨0,
        D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount_pos⟩
    refine ⟨D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a0, ?_⟩
    simpa [a0] using
      (D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_uniform_endpoint x a0).symm
  · constructor
    · have hpoint :
          ∀ x,
            (∑ a,
              D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a ^ 2) ≤
            (∑ a,
              D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a) ^ 2 := by
        intro x
        have h :=
          (Omega.POM.paper_pom_residue_refinement_jensen_q2
            (fun a : Fin
                D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount =>
              (D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a :
                ℤ))
            (fun _ => by positivity)).2
        exact_mod_cast h
      simpa [conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_refinedMoment,
        conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_coarseMoment] using
        Finset.sum_le_sum (fun x _ => hpoint x)
    · have hpoint :
          ∀ x,
            (∑ a,
              D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a) ^ 2 ≤
            D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount *
              ∑ a,
                D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a ^ 2 := by
        intro x
        have h :=
          (Omega.POM.paper_pom_residue_refinement_jensen_q2
            (fun a : Fin
                D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount =>
              (D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a :
                ℤ))
            (fun _ => by positivity)).1
        exact_mod_cast h
      have hsum :
          (∑ x,
            (∑ a,
              D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a) ^ 2) ≤
          ∑ x,
            D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_residueCount *
              ∑ a,
                D.conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_counts x a ^ 2 :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      simpa [conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_refinedMoment,
        conclusion_residue_refinement_purity_uniformization_endpoint_rigidity_coarseMoment,
        Finset.mul_sum] using hsum

end Omega.Conclusion
