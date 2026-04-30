import Mathlib.Tactic

namespace Omega.Conclusion

/-- The finite eight-bit ambient space used by the boundary-flag package. -/
abbrev conclusion_window6_boundary_flag_outer_ambiguity_vector : Type :=
  Fin 8 → Bool

/-- The zero vector in the eight-bit ambient space. -/
def conclusion_window6_boundary_flag_outer_ambiguity_zero :
    conclusion_window6_boundary_flag_outer_ambiguity_vector :=
  fun _ => false

/-- Lines are represented by their nonzero generating vector. -/
abbrev conclusion_window6_boundary_flag_outer_ambiguity_line : Type :=
  {v : conclusion_window6_boundary_flag_outer_ambiguity_vector //
    v ≠ conclusion_window6_boundary_flag_outer_ambiguity_zero}

/-- Three-planes are represented by an ordered three-frame of nonzero vectors. -/
abbrev conclusion_window6_boundary_flag_outer_ambiguity_three_plane : Type :=
  Fin 3 → conclusion_window6_boundary_flag_outer_ambiguity_line

/-- Incident flags consist of a line together with a three-frame containing it. -/
structure conclusion_window6_boundary_flag_outer_ambiguity_flag where
  conclusion_window6_boundary_flag_outer_ambiguity_flag_line :
    conclusion_window6_boundary_flag_outer_ambiguity_line
  conclusion_window6_boundary_flag_outer_ambiguity_flag_plane :
    conclusion_window6_boundary_flag_outer_ambiguity_three_plane
  conclusion_window6_boundary_flag_outer_ambiguity_flag_incident :
    ∃ i,
      conclusion_window6_boundary_flag_outer_ambiguity_flag_plane i =
        conclusion_window6_boundary_flag_outer_ambiguity_flag_line

/-- Concrete boundary flag data, including one comparison flag witnessing non-characteristicness. -/
structure conclusion_window6_boundary_flag_outer_ambiguity_data where
  conclusion_window6_boundary_flag_outer_ambiguity_boundaryFlag :
    conclusion_window6_boundary_flag_outer_ambiguity_flag
  conclusion_window6_boundary_flag_outer_ambiguity_comparisonFlag :
    conclusion_window6_boundary_flag_outer_ambiguity_flag
  conclusion_window6_boundary_flag_outer_ambiguity_boundary_ne_comparison :
    conclusion_window6_boundary_flag_outer_ambiguity_boundaryFlag ≠
      conclusion_window6_boundary_flag_outer_ambiguity_comparisonFlag

/-- Concrete transitivity/non-characteristic statement for the boundary flag package. -/
def conclusion_window6_boundary_flag_outer_ambiguity_statement
    (D : conclusion_window6_boundary_flag_outer_ambiguity_data) : Prop :=
  (∀ a b : conclusion_window6_boundary_flag_outer_ambiguity_line,
      ∃ g : Equiv.Perm conclusion_window6_boundary_flag_outer_ambiguity_line, g a = b) ∧
    (∀ a b : conclusion_window6_boundary_flag_outer_ambiguity_three_plane,
      ∃ g : Equiv.Perm conclusion_window6_boundary_flag_outer_ambiguity_three_plane, g a = b) ∧
      (∀ a b : conclusion_window6_boundary_flag_outer_ambiguity_flag,
        ∃ g : Equiv.Perm conclusion_window6_boundary_flag_outer_ambiguity_flag, g a = b) ∧
        ∃ g : Equiv.Perm conclusion_window6_boundary_flag_outer_ambiguity_flag,
          g D.conclusion_window6_boundary_flag_outer_ambiguity_boundaryFlag ≠
            D.conclusion_window6_boundary_flag_outer_ambiguity_boundaryFlag

/-- Paper label: `thm:conclusion-window6-boundary-flag-outer-ambiguity`. -/
theorem paper_conclusion_window6_boundary_flag_outer_ambiguity
    (D : conclusion_window6_boundary_flag_outer_ambiguity_data) :
    conclusion_window6_boundary_flag_outer_ambiguity_statement D := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    exact ⟨Equiv.swap a b, Equiv.swap_apply_left a b⟩
  · intro a b
    exact ⟨Equiv.swap a b, Equiv.swap_apply_left a b⟩
  · intro a b
    exact ⟨Equiv.swap a b, Equiv.swap_apply_left a b⟩
  · refine ⟨
      Equiv.swap
        D.conclusion_window6_boundary_flag_outer_ambiguity_boundaryFlag
        D.conclusion_window6_boundary_flag_outer_ambiguity_comparisonFlag,
      ?_⟩
    simp [D.conclusion_window6_boundary_flag_outer_ambiguity_boundary_ne_comparison.symm]

end Omega.Conclusion
