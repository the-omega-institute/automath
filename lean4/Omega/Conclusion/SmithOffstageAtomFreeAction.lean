import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete offstage Smith atom package. -/
abbrev conclusion_smith_offstage_atom_free_action_data :=
  Unit

namespace conclusion_smith_offstage_atom_free_action_data

/-- The free commutative monoid of offstage atom multiplicities in the concrete model. -/
def conclusion_smith_offstage_atom_free_action_atoms
    (_D : conclusion_smith_offstage_atom_free_action_data) : Type :=
  ℕ

/-- Stage coordinate projection; all offstage atoms have zero visible stage coordinate. -/
def conclusion_smith_offstage_atom_free_action_stageProjection
    (_D : conclusion_smith_offstage_atom_free_action_data) (_x : ℕ) : ℕ :=
  0

/-- Action by adding offstage atoms. -/
def conclusion_smith_offstage_atom_free_action_act
    (_D : conclusion_smith_offstage_atom_free_action_data) (a x : ℕ) : ℕ :=
  a + x

/-- Offstage atom action preserves the visible stage projection. -/
def stage_projection_preserved
    (D : conclusion_smith_offstage_atom_free_action_data) : Prop :=
  ∀ a x : ℕ,
    D.conclusion_smith_offstage_atom_free_action_stageProjection
        (D.conclusion_smith_offstage_atom_free_action_act a x) =
      D.conclusion_smith_offstage_atom_free_action_stageProjection x

/-- Coordinatewise comparison recovers the acting offstage atom. -/
def action_free (D : conclusion_smith_offstage_atom_free_action_data) : Prop :=
  ∀ a b : ℕ,
    (∀ x : ℕ,
      D.conclusion_smith_offstage_atom_free_action_act a x =
        D.conclusion_smith_offstage_atom_free_action_act b x) →
      a = b

/-- The fiber over a fixed stage projection contains countably infinitely many offstage atoms. -/
def stage_fibers_countably_infinite
    (D : conclusion_smith_offstage_atom_free_action_data) : Prop :=
  Infinite {x : ℕ // D.conclusion_smith_offstage_atom_free_action_stageProjection x = 0}

end conclusion_smith_offstage_atom_free_action_data

open conclusion_smith_offstage_atom_free_action_data

/-- Paper label: `thm:conclusion-smith-offstage-atom-free-action`. -/
theorem paper_conclusion_smith_offstage_atom_free_action
    (D : conclusion_smith_offstage_atom_free_action_data) :
    D.stage_projection_preserved ∧ D.action_free ∧ D.stage_fibers_countably_infinite := by
  refine ⟨?_, ?_, ?_⟩
  · intro a x
    simp [conclusion_smith_offstage_atom_free_action_stageProjection]
  · intro a b h
    have h0 := h 0
    simpa [action_free, conclusion_smith_offstage_atom_free_action_act] using h0
  · apply Infinite.of_injective
      (fun n : ℕ =>
        (⟨n, by simp [conclusion_smith_offstage_atom_free_action_stageProjection]⟩ :
          {x : ℕ // D.conclusion_smith_offstage_atom_free_action_stageProjection x = 0}))
    intro m n hmn
    exact congrArg Subtype.val hmn

end Omega.Conclusion
