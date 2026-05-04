import Mathlib.SetTheory.Cardinal.Continuum

namespace Omega.Conclusion

open scoped Cardinal

/-- The concrete continuum of residual slopes. -/
abbrev conclusion_tate_primitive_line_atlas_continuum_upper_bound_slope := Set ℕ

/-- A concrete residual rank-two space used for the primitive-line atlas seed. -/
abbrev conclusion_tate_primitive_line_atlas_continuum_upper_bound_residual :=
  conclusion_tate_primitive_line_atlas_continuum_upper_bound_slope ×
    conclusion_tate_primitive_line_atlas_continuum_upper_bound_slope

/-- The primitive line with slope `a`, modelled as the graph fiber with second coordinate `a`. -/
def conclusion_tate_primitive_line_atlas_continuum_upper_bound_line
    (a : conclusion_tate_primitive_line_atlas_continuum_upper_bound_slope) :
    Set conclusion_tate_primitive_line_atlas_continuum_upper_bound_residual :=
  {x | x.2 = a}

/-- The primitive-line atlas obtained from all residual slopes. -/
def conclusion_tate_primitive_line_atlas_continuum_upper_bound_atlas :
    Set (Set conclusion_tate_primitive_line_atlas_continuum_upper_bound_residual) :=
  Set.range conclusion_tate_primitive_line_atlas_continuum_upper_bound_line

lemma conclusion_tate_primitive_line_atlas_continuum_upper_bound_line_injective :
    Function.Injective
      conclusion_tate_primitive_line_atlas_continuum_upper_bound_line := by
  intro a b hline
  have hmem :
      (∅, a) ∈
        conclusion_tate_primitive_line_atlas_continuum_upper_bound_line b := by
    rw [← hline]
    rfl
  exact hmem

/-- Paper-facing concrete statement for
`prop:conclusion-tate-primitive-line-atlas-continuum-upper-bound`.

Every residual point is covered by its second-coordinate primitive line, distinct
slopes give distinct lines, and the resulting atlas has continuum cardinality. -/
def conclusion_tate_primitive_line_atlas_continuum_upper_bound_statement : Prop :=
  (∀ x : conclusion_tate_primitive_line_atlas_continuum_upper_bound_residual,
      ∃ L ∈ conclusion_tate_primitive_line_atlas_continuum_upper_bound_atlas, x ∈ L) ∧
    Function.Injective
      conclusion_tate_primitive_line_atlas_continuum_upper_bound_line ∧
    #conclusion_tate_primitive_line_atlas_continuum_upper_bound_atlas = 𝔠

/-- Paper label: `prop:conclusion-tate-primitive-line-atlas-continuum-upper-bound`. -/
theorem paper_conclusion_tate_primitive_line_atlas_continuum_upper_bound :
    conclusion_tate_primitive_line_atlas_continuum_upper_bound_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    refine ⟨conclusion_tate_primitive_line_atlas_continuum_upper_bound_line x.2, ?_, ?_⟩
    · exact ⟨x.2, rfl⟩
    · rfl
  · exact conclusion_tate_primitive_line_atlas_continuum_upper_bound_line_injective
  · calc
      #conclusion_tate_primitive_line_atlas_continuum_upper_bound_atlas =
          #(Set.range conclusion_tate_primitive_line_atlas_continuum_upper_bound_line) := rfl
      _ = #(Set ℕ) := by
        simpa using Cardinal.mk_range_eq_of_injective
          conclusion_tate_primitive_line_atlas_continuum_upper_bound_line_injective
      _ = 𝔠 := Cardinal.mk_set_nat

end Omega.Conclusion
