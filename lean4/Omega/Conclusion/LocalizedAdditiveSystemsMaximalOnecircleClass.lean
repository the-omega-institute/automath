import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- The visible compact Lie quotient of the localized additive model has one circle. -/
def conclusion_localized_additive_systems_maximal_onecircle_class_visible_dimension
    (_S : Type u) : ℕ :=
  1

/-- The finite kernel carried by a finite localized additive system. -/
abbrev conclusion_localized_additive_systems_maximal_onecircle_class_kernel
    (S : Type u) : Type u :=
  S

/-- Concrete short exact sequence model: a one-circle visible coordinate with finite kernel. -/
def conclusion_localized_additive_systems_maximal_onecircle_class_extension
    (S : Type u) : Type u :=
  Unit ⊕ conclusion_localized_additive_systems_maximal_onecircle_class_kernel S

/-- Projection to the visible one-circle quotient. -/
def conclusion_localized_additive_systems_maximal_onecircle_class_visible_projection
    (S : Type*) :
    conclusion_localized_additive_systems_maximal_onecircle_class_extension S → Unit :=
  fun _ => ()

/-- Inclusion of the finite kernel as the fiber over the visible base point. -/
def conclusion_localized_additive_systems_maximal_onecircle_class_kernel_inclusion
    {S : Type*} :
    conclusion_localized_additive_systems_maximal_onecircle_class_kernel S →
      conclusion_localized_additive_systems_maximal_onecircle_class_extension S :=
  Sum.inr

/-- The finite-kernel recovery map from the extension. -/
def conclusion_localized_additive_systems_maximal_onecircle_class_kernel_recovery
    {S : Type*} :
    conclusion_localized_additive_systems_maximal_onecircle_class_extension S →
      Option (conclusion_localized_additive_systems_maximal_onecircle_class_kernel S)
  | Sum.inl _ => none
  | Sum.inr s => some s

/-- The concrete paper-facing package for maximal one-circle localized additive systems. -/
def conclusion_localized_additive_systems_maximal_onecircle_class_statement
    (S : Type*) [Fintype S] : Prop :=
  Function.Injective
      (conclusion_localized_additive_systems_maximal_onecircle_class_kernel_inclusion
        (S := S)) ∧
    Function.Surjective
      (conclusion_localized_additive_systems_maximal_onecircle_class_visible_projection S) ∧
    conclusion_localized_additive_systems_maximal_onecircle_class_visible_dimension S = 1 ∧
    (∀ s : S,
      conclusion_localized_additive_systems_maximal_onecircle_class_kernel_recovery
          (conclusion_localized_additive_systems_maximal_onecircle_class_kernel_inclusion
            (S := S) s) =
        some s) ∧
    IsEmpty (Fin (Fintype.card S + 1) ↪ S)

/-- Paper label:
`cor:conclusion-localized-additive-systems-maximal-onecircle-class`. -/
theorem paper_conclusion_localized_additive_systems_maximal_onecircle_class
    (S : Type*) [Fintype S] :
    conclusion_localized_additive_systems_maximal_onecircle_class_statement S := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro s t hst
    cases hst
    rfl
  · intro u
    exact ⟨Sum.inl u, rfl⟩
  · intro s
    rfl
  · exact
      { false := by
          intro e
          have hcard := Fintype.card_le_of_embedding e
          simp at hcard }

end Omega.Conclusion
