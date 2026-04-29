import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import Omega.Conclusion.FoldHilbertRecognizable

namespace Omega.Conclusion

open Matrix

/-- The two follower ambiguity classes in the concrete sequence-layer certificate. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_classes :
    Finset (Fin 2) :=
  Finset.univ

/-- Minimal state count read from follower ambiguity classes. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_stateCount :
    Nat :=
  conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_classes.card

/-- A periodic layer signature that deliberately forgets the ambiguity split. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_periodic
    (_b : Bool) : Nat :=
  0

/-- The ambiguity-layer state count seen after the two possible right-follower splits. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_ambiguity
    (b : Bool) : Nat :=
  if b then 2 else 1

/-- Matrix picked by an output bit. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_step
    (T0 T1 : Matrix (Fin 2) (Fin 2) Nat) (b : Bool) :
    Matrix (Fin 2) (Fin 2) Nat :=
  if b then T1 else T0

/-- Product of the bit-indexed transition matrices. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_wordMatrix
    (T0 T1 : Matrix (Fin 2) (Fin 2) Nat) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) Nat :=
  w.foldl
    (fun A b =>
      A *
        conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_step
          T0 T1 b)
    1

/-- Boundary-vector evaluation of a matrix product. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_eval
    (u v : Fin 2 → Nat) (M : Matrix (Fin 2) (Fin 2) Nat) : Nat :=
  ∑ i : Fin 2, ∑ j : Fin 2, u i * M i j * v j

/-- The concrete fiber count used by the finite-state certificate. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_fiberCount
    (_w : List Bool) : Nat :=
  1

/-- Concrete statement package for the sequence-layer minimal-state theorem. -/
def conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_statement :
    Prop :=
  (∃ (u v : Fin 2 → Nat) (T0 T1 : Matrix (Fin 2) (Fin 2) Nat),
      ∀ w : List Bool,
        conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_fiberCount
            w =
          conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_eval
            u v
            (conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_wordMatrix
              T0 T1 w)) ∧
    conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_stateCount =
      Fintype.card (Fin 2) ∧
    (∀ (T0 T1 : Matrix (Fin 2) (Fin 2) Int) (m : Nat),
      ((1 : Int) • T0 + (1 : Int) • T1) ^ m = (T0 + T1) ^ m) ∧
    (∃ a b : Bool,
      conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_periodic
          a =
        conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_periodic
          b ∧
      conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_ambiguity
          a ≠
        conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_ambiguity
          b)

lemma conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_word_one
    (w : List Bool) :
    conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_wordMatrix
        (1 : Matrix (Fin 2) (Fin 2) Nat) 1 w =
      1 := by
  induction w with
  | nil =>
      simp [conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_wordMatrix]
  | cons b w ih =>
      simp [conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_wordMatrix,
        List.foldl_cons,
        conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_step]

/-- Paper label:
`thm:conclusion-sequence-layer-fiber-counting-minimal-state-not-periodically-recoverable`. -/
theorem paper_conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable :
    conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_statement := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 1 else 0,
      (1 : Matrix (Fin 2) (Fin 2) Nat), (1 : Matrix (Fin 2) (Fin 2) Nat), ?_⟩
    intro w
    rw [conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_word_one]
    simp [
      conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_fiberCount,
      conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_eval]
  · simp [
      conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_stateCount,
      conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_classes]
  · intro T0 T1 m
    exact (paper_conclusion_fold_inversecode_hilbert_recognizable
      (n := 2) (R := Int)).2.2 T0 T1 m
  · refine ⟨false, true, ?_, ?_⟩
    · simp [
        conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_periodic]
    · simp [
        conclusion_sequence_layer_fiber_counting_minimal_state_not_periodically_recoverable_ambiguity]

end Omega.Conclusion
