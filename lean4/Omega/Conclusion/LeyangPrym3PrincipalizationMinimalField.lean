import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finite certificate package for the three cubic root fields and their principalizations. -/
structure conclusion_leyang_prym3_principalization_minimal_field_certificate where
  cubicRootFields : Finset ℕ
  fieldsOfDefinition : Finset ℕ
  extensionDegree : ℕ → ℕ
  nonzeroTwoTorsion : ℕ → Finset ℕ
  cubicRootFields_nonempty : cubicRootFields.Nonempty
  single_rational_nonzero_point_over_cubic :
    ∀ K ∈ cubicRootFields, (nonzeroTwoTorsion K).card = 1
  cubic_fields_define :
    ∀ {K}, K ∈ cubicRootFields → K ∈ fieldsOfDefinition
  cubic_degree :
    ∀ K ∈ cubicRootFields, extensionDegree K = 3
  every_definition_field_contains_cubic_root :
    ∀ E ∈ fieldsOfDefinition, ∃ K ∈ cubicRootFields, extensionDegree K ≤ extensionDegree E

/-- Requested data name for the Prym principalization minimal-field certificate. -/
abbrev conclusion_leyang_prym3_principalization_minimal_field_data :=
  conclusion_leyang_prym3_principalization_minimal_field_certificate

/-- Principalizations over a cubic root field are represented by rational nonzero 2-torsion
points over that field. -/
def conclusion_leyang_prym3_principalization_minimal_field_data.principalizations_over
    (D : conclusion_leyang_prym3_principalization_minimal_field_data) (K : ℕ) : Finset ℕ :=
  D.nonzeroTwoTorsion K

/-- Existence and uniqueness of the principalization over each cubic root field. -/
def conclusion_leyang_prym3_principalization_minimal_field_data.exists_unique_over_cubic_root_fields
    (D : conclusion_leyang_prym3_principalization_minimal_field_data) : Prop :=
  ∀ K ∈ D.cubicRootFields, ∃! P, P ∈ D.principalizations_over K

/-- Degrees of fields over which a principalization is defined. -/
def conclusion_leyang_prym3_principalization_minimal_field_data.definition_degrees
    (D : conclusion_leyang_prym3_principalization_minimal_field_data) : Finset ℕ :=
  D.fieldsOfDefinition.image D.extensionDegree

/-- The definition-degree set is nonempty because every cubic root field defines a
principalization. -/
def conclusion_leyang_prym3_principalization_minimal_field_data.definition_degrees_nonempty
    (D : conclusion_leyang_prym3_principalization_minimal_field_data) :
    D.definition_degrees.Nonempty := by
  rcases D.cubicRootFields_nonempty with ⟨K, hK⟩
  exact ⟨D.extensionDegree K, Finset.mem_image.mpr ⟨K, D.cubic_fields_define hK, rfl⟩⟩

/-- Minimal extension degree among fields of definition. -/
def conclusion_leyang_prym3_principalization_minimal_field_data.minimal_extension_degree
    (D : conclusion_leyang_prym3_principalization_minimal_field_data) : ℕ :=
  D.definition_degrees.min' D.definition_degrees_nonempty

/-- Paper label: `thm:conclusion-leyang-prym3-principalization-minimal-field`. -/
theorem paper_conclusion_leyang_prym3_principalization_minimal_field
    (D : conclusion_leyang_prym3_principalization_minimal_field_data) :
    D.exists_unique_over_cubic_root_fields ∧ D.minimal_extension_degree = 3 := by
  refine ⟨?_, ?_⟩
  · intro K hK
    obtain ⟨P, hP⟩ := Finset.card_eq_one.mp (D.single_rational_nonzero_point_over_cubic K hK)
    refine ⟨P, ?_, ?_⟩
    · simp [conclusion_leyang_prym3_principalization_minimal_field_data.principalizations_over,
        hP]
    · intro Q hQ
      have hQ' : Q ∈ ({P} : Finset ℕ) := by
        simpa [conclusion_leyang_prym3_principalization_minimal_field_data.principalizations_over,
          hP] using hQ
      simpa using hQ'
  · rw [conclusion_leyang_prym3_principalization_minimal_field_data.minimal_extension_degree]
    apply le_antisymm
    · rcases D.cubicRootFields_nonempty with ⟨K, hK⟩
      have hmem : 3 ∈ D.definition_degrees := by
        refine Finset.mem_image.mpr ⟨K, D.cubic_fields_define hK, ?_⟩
        exact D.cubic_degree K hK
      exact Finset.min'_le D.definition_degrees 3 hmem
    · refine Finset.le_min' D.definition_degrees
        D.definition_degrees_nonempty 3 ?_
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨E, hE, rfl⟩
      rcases D.every_definition_field_contains_cubic_root E hE with ⟨K, hK, hle⟩
      simpa [D.cubic_degree K hK] using hle

end Omega.Conclusion
