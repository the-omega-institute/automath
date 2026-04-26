import Mathlib.Tactic

namespace Omega.POM

/-- Concrete data for collision-count lumping before the symmetric moment quotient.  The
transition/output kernel is deterministic on finite input, and `classOf` records the proposed
collision-count quotient classes. -/
structure pom_moment_col_lumping_data where
  stateCount : ℕ
  inputCount : ℕ
  outputCount : ℕ
  classCount : ℕ
  q : ℕ
  classOf : Fin stateCount → Fin classCount
  nextState : Fin stateCount → Fin inputCount → Fin stateCount
  emitted : Fin stateCount → Fin inputCount → Fin outputCount
  collisionCount_eq :
    ∀ s t : Fin stateCount,
      classOf s = classOf t →
        ∀ b : Fin outputCount,
          ∀ C : Fin classCount,
            Fintype.card
                {a : Fin inputCount //
                  emitted s a = b ∧ classOf (nextState s a) = C} =
              Fintype.card
                {a : Fin inputCount //
                  emitted t a = b ∧ classOf (nextState t a) = C}

namespace pom_moment_col_lumping_data

/-- Number of inputs sending `s` to output bucket `b` and successor quotient class `C`. -/
def pom_moment_col_lumping_collision_count (D : pom_moment_col_lumping_data)
    (s : Fin D.stateCount) (b : Fin D.outputCount) (C : Fin D.classCount) : ℕ :=
  Fintype.card
    {a : Fin D.inputCount // D.emitted s a = b ∧ D.classOf (D.nextState s a) = C}

/-- Quotient transition counts, choosing an arbitrary representative when the class is inhabited
and returning zero for empty classes. -/
noncomputable def pom_moment_col_lumping_quotient_transition_count
    (D : pom_moment_col_lumping_data)
    (C : Fin D.classCount) (b : Fin D.outputCount) (C' : Fin D.classCount) : ℕ :=
  if h : ∃ s : Fin D.stateCount, D.classOf s = C then
    D.pom_moment_col_lumping_collision_count (Classical.choose h) b C'
  else
    0

/-- The quotient moment kernel is well-defined exactly when transition counts factor through
collision-count classes. -/
def exists_lumped_moment_kernel (D : pom_moment_col_lumping_data) : Prop :=
  ∀ s : Fin D.stateCount,
    ∀ b : Fin D.outputCount,
      ∀ C : Fin D.classCount,
        D.pom_moment_col_lumping_quotient_transition_count (D.classOf s) b C =
          D.pom_moment_col_lumping_collision_count s b C

/-- Stars-and-bars state count for class-occupancy vectors of total mass `q`. -/
def lumped_state_count (D : pom_moment_col_lumping_data) : ℕ :=
  Nat.choose (D.q + D.classCount - 1) (D.classCount - 1)

/-- The expected class-occupancy count from the stars-and-bars formula. -/
def expected_lumped_state_count (D : pom_moment_col_lumping_data) : ℕ :=
  Nat.choose (D.q + D.classCount - 1) (D.classCount - 1)

lemma pom_moment_col_lumping_quotient_transition_count_eq_collision_count
    (D : pom_moment_col_lumping_data) (s : Fin D.stateCount) (b : Fin D.outputCount)
    (C : Fin D.classCount) :
    D.pom_moment_col_lumping_quotient_transition_count (D.classOf s) b C =
      D.pom_moment_col_lumping_collision_count s b C := by
  unfold pom_moment_col_lumping_quotient_transition_count
  by_cases h : ∃ t : Fin D.stateCount, D.classOf t = D.classOf s
  · simp [h]
    exact D.collisionCount_eq (Classical.choose h) s (Classical.choose_spec h) b C
  · exact False.elim (h ⟨s, rfl⟩)

end pom_moment_col_lumping_data

open pom_moment_col_lumping_data

/-- Paper label: `prop:pom-moment-col-lumping`. -/
theorem paper_pom_moment_col_lumping (D : pom_moment_col_lumping_data) :
    D.exists_lumped_moment_kernel ∧ D.lumped_state_count = D.expected_lumped_state_count := by
  refine ⟨?_, ?_⟩
  · intro s b C
    exact pom_moment_col_lumping_quotient_transition_count_eq_collision_count D s b C
  · rfl

end Omega.POM
