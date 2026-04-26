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

/-- The residue image attached to a stable predicate after factoring through the residue map. -/
def stable_predicate_residue_classification_residue_image
    {X : Type} {M : ℕ} (s : ZMod M → X) (P : Set X) : Set (ZMod M) :=
  s ⁻¹' P

/-- The periodic indicator attached to a residue set. -/
noncomputable def stable_predicate_residue_classification_periodic_indicator
    {M : ℕ} (R : Set (ZMod M)) : ℕ → ℕ :=
  by
    classical
    exact fun n => if (n : ZMod M) ∈ R then 1 else 0

/-- The indicator of a predicate as a `{0,1}`-valued function. -/
noncomputable def stable_predicate_residue_classification_indicator
    {X : Type} (P : Set X) : X → ℕ :=
  by
    classical
    exact fun x => if x ∈ P then 1 else 0

/-- prop:stable-predicate-residue-classification -/
theorem paper_stable_predicate_residue_classification
    {Ω X : Type} {M : ℕ}
    (fold : Ω → X) (s : ZMod M → X) (r : Ω → ZMod M) (N : Ω → ℕ)
    (hfactor : ∀ ω, fold ω = s (r ω))
    (hresidue : ∀ ω, ((N ω : ℕ) : ZMod M) = r ω)
    (P : Set X) :
    (∀ ω,
        stable_predicate_residue_classification_indicator P (fold ω) =
          stable_predicate_residue_classification_periodic_indicator
            (stable_predicate_residue_classification_residue_image s P) (N ω)) ∧
      ∀ n,
        stable_predicate_residue_classification_periodic_indicator
            (stable_predicate_residue_classification_residue_image s P) (n + M) =
        stable_predicate_residue_classification_periodic_indicator
            (stable_predicate_residue_classification_residue_image s P) n := by
  classical
  refine ⟨?_, ?_⟩
  · intro ω
    have hmem :
        fold ω ∈ P ↔
          ((N ω : ℕ) : ZMod M) ∈
            stable_predicate_residue_classification_residue_image s P := by
      simpa [stable_predicate_residue_classification_residue_image, hresidue ω] using
        (paper_stable_predicate_residue_classification_package fold s r hfactor P ω)
    by_cases hω : fold ω ∈ P
    · have hN :
          ((N ω : ℕ) : ZMod M) ∈
            stable_predicate_residue_classification_residue_image s P :=
        hmem.mp hω
      simp [stable_predicate_residue_classification_indicator,
        stable_predicate_residue_classification_periodic_indicator, hω, hN]
    · have hN :
          ((N ω : ℕ) : ZMod M) ∉
            stable_predicate_residue_classification_residue_image s P := by
        intro hN
        exact hω (hmem.mpr hN)
      simp [stable_predicate_residue_classification_indicator,
        stable_predicate_residue_classification_periodic_indicator, hω, hN]
  · intro n
    simp [stable_predicate_residue_classification_periodic_indicator]

end Omega.StatisticalStability.ResidueClassification
