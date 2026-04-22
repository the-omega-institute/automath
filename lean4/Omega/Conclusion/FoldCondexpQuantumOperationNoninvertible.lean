import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldConditionalExpectation

namespace Omega.Conclusion

open Omega.OperatorAlgebra
open Omega.OperatorAlgebra.FoldConditionalExpectationData
open scoped BigOperators

/-- Concrete finite fold data together with a nontrivial fiber witness. -/
structure conclusion_fold_condexp_quantum_operation_noninvertible_data
    extends FoldConditionalExpectationData where
  collisionLeft : Ω
  collisionRight : Ω
  collision_ne : collisionLeft ≠ collisionRight
  collision_fold : fold collisionLeft = fold collisionRight

/-- The basis idempotent `P_a`. -/
def conclusion_fold_condexp_quantum_operation_noninvertible_point_mass
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) (a : D.Ω) :
    D.Ω → ℚ :=
  fun ω => if ω = a then 1 else 0

/-- The counting trace `τ(f) = ∑_ω f(ω)`. -/
def conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) (f : D.Ω → ℚ) : ℚ :=
  ∑ ω, f ω

lemma conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace_point_mass
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) (a : D.Ω) :
    conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace D
        (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D a) = 1 := by
  classical
  simp [conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace,
    conclusion_fold_condexp_quantum_operation_noninvertible_point_mass]

lemma conclusion_fold_condexp_quantum_operation_noninvertible_point_mass_sum
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) (a ω : D.Ω) :
    Finset.sum (D.toFoldConditionalExpectationData.fiber (D.fold ω))
      (fun b => conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D a b) =
        if D.fold a = D.fold ω then 1 else 0 := by
  classical
  by_cases h : D.fold a = D.fold ω
  · have ha_mem : a ∈ D.toFoldConditionalExpectationData.fiber (D.fold ω) := by
      simp [FoldConditionalExpectationData.fiber, h]
    rw [if_pos h]
    simp [conclusion_fold_condexp_quantum_operation_noninvertible_point_mass,
      FoldConditionalExpectationData.fiber, h]
  · have ha_not_mem : a ∉ D.toFoldConditionalExpectationData.fiber (D.fold ω) := by
      simp [FoldConditionalExpectationData.fiber, h]
    rw [if_neg h]
    simp [conclusion_fold_condexp_quantum_operation_noninvertible_point_mass,
      FoldConditionalExpectationData.fiber, h]

lemma conclusion_fold_condexp_quantum_operation_noninvertible_foldExpectation_point_mass
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) (a ω : D.Ω) :
    D.toFoldConditionalExpectationData.foldExpectation
        (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D a) ω =
      if D.fold ω = D.fold a then
        (1 : ℚ) / D.toFoldConditionalExpectationData.fiberCard (D.fold a)
      else 0 := by
  by_cases h : D.fold ω = D.fold a
  · have h' : D.fold a = D.fold ω := h.symm
    rw [if_pos h]
    rw [FoldConditionalExpectationData.foldExpectation,
      conclusion_fold_condexp_quantum_operation_noninvertible_point_mass_sum]
    rw [if_pos h']
    simp [h]
  · have h' : D.fold a ≠ D.fold ω := by
      intro h''
      exact h h''.symm
    rw [if_neg h]
    rw [FoldConditionalExpectationData.foldExpectation,
      conclusion_fold_condexp_quantum_operation_noninvertible_point_mass_sum]
    rw [if_neg h']
    simp

lemma conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace_foldExpectation_point_mass
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) (a : D.Ω) :
    conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace D
        (D.toFoldConditionalExpectationData.foldExpectation
          (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D a)) = 1 := by
  classical
  let F := D.toFoldConditionalExpectationData.fiber (D.fold a)
  have hcard_pos : 0 < D.toFoldConditionalExpectationData.fiberCard (D.fold a) :=
    D.toFoldConditionalExpectationData.fiberCard_pos (D.fold a)
  have hcard_ne : ((D.toFoldConditionalExpectationData.fiberCard (D.fold a) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcard_pos
  calc
    conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace D
        (D.toFoldConditionalExpectationData.foldExpectation
          (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D a))
      = Finset.sum F (fun _ => (1 : ℚ) / D.toFoldConditionalExpectationData.fiberCard (D.fold a)) := by
          calc
            conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace D
                (D.toFoldConditionalExpectationData.foldExpectation
                  (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D a))
                =
                  ∑ ω,
                    if D.fold ω = D.fold a then
                      (1 : ℚ) / D.toFoldConditionalExpectationData.fiberCard (D.fold a)
                    else 0 := by
                      refine Finset.sum_congr rfl ?_
                      intro ω hω
                      by_cases h : D.fold ω = D.fold a
                      · simp [conclusion_fold_condexp_quantum_operation_noninvertible_foldExpectation_point_mass,
                          h]
                      · simp [conclusion_fold_condexp_quantum_operation_noninvertible_foldExpectation_point_mass,
                          h]
            _ = Finset.sum F (fun _ => (1 : ℚ) / D.toFoldConditionalExpectationData.fiberCard (D.fold a)) := by
                  simpa [F, FoldConditionalExpectationData.fiber] using
                    (Finset.sum_filter (s := Finset.univ)
                      (p := fun ω : D.Ω => D.fold ω = D.fold a)
                      (f := fun _ => (1 : ℚ) / D.toFoldConditionalExpectationData.fiberCard (D.fold a))).symm
    _ = (F.card : ℚ) * ((1 : ℚ) / D.toFoldConditionalExpectationData.fiberCard (D.fold a)) := by
          simp
    _ = 1 := by
          have hcard_eq :
              (F.card : ℚ) = D.toFoldConditionalExpectationData.fiberCard (D.fold a) := by
            simp [F, FoldConditionalExpectationData.fiberCard]
          rw [hcard_eq]
          field_simp [hcard_ne]

lemma conclusion_fold_condexp_quantum_operation_noninvertible_point_mass_ne
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) :
    conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D D.collisionLeft ≠
      conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D D.collisionRight := by
  intro hEq
  have hAtLeft := congrArg (fun f => f D.collisionLeft) hEq
  simp [conclusion_fold_condexp_quantum_operation_noninvertible_point_mass, D.collision_ne] at hAtLeft

lemma conclusion_fold_condexp_quantum_operation_noninvertible_foldExpectation_collision_eq
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) :
    D.toFoldConditionalExpectationData.foldExpectation
        (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D D.collisionLeft) =
      D.toFoldConditionalExpectationData.foldExpectation
        (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D D.collisionRight) := by
  funext ω
  simp [conclusion_fold_condexp_quantum_operation_noninvertible_foldExpectation_point_mass,
    D.collision_fold]

/-- The finite fold conditional expectation is positive and unital, preserves the counting trace
on basis idempotents, and any nontrivial fiber forces noninjectivity and hence noninvertibility. -/
def conclusion_fold_condexp_quantum_operation_noninvertible_statement
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) : Prop :=
  D.toFoldConditionalExpectationData.positiveUnitalIdempotent ∧
    (∀ a : D.Ω,
      conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace D
          (D.toFoldConditionalExpectationData.foldExpectation
            (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D a)) =
        conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace D
          (conclusion_fold_condexp_quantum_operation_noninvertible_point_mass D a)) ∧
    ¬ Function.Injective D.toFoldConditionalExpectationData.foldExpectation ∧
    ¬ Function.Bijective D.toFoldConditionalExpectationData.foldExpectation

/-- Paper label: `thm:conclusion-fold-condexp-quantum-operation-noninvertible`. -/
theorem paper_conclusion_fold_condexp_quantum_operation_noninvertible
    (D : conclusion_fold_condexp_quantum_operation_noninvertible_data) :
    conclusion_fold_condexp_quantum_operation_noninvertible_statement D := by
  have hcondexp := paper_op_algebra_fold_conditional_expectation D.toFoldConditionalExpectationData
  have hnotinj : ¬ Function.Injective D.toFoldConditionalExpectationData.foldExpectation := by
    intro hinj
    apply conclusion_fold_condexp_quantum_operation_noninvertible_point_mass_ne D
    exact hinj (conclusion_fold_condexp_quantum_operation_noninvertible_foldExpectation_collision_eq D)
  refine ⟨hcondexp.1, ?_, hnotinj, ?_⟩
  · intro a
    rw [conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace_foldExpectation_point_mass,
      conclusion_fold_condexp_quantum_operation_noninvertible_counting_trace_point_mass]
  · intro hbij
    exact hnotinj hbij.1

end Omega.Conclusion
