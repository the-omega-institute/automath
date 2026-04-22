import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finite-dimensional observables in the visible block model. -/
abbrev conclusion_fold_quantum_visible_booleanization_operator (n : ℕ) :=
  Fin n → Fin n → ℂ

/-- The fold channel discards off-diagonal amplitudes and keeps the visible diagonal. -/
def conclusion_fold_quantum_visible_booleanization_foldChannel {n : ℕ}
    (A : conclusion_fold_quantum_visible_booleanization_operator n) :
    conclusion_fold_quantum_visible_booleanization_operator n :=
  fun i j => if i = j then A i i else 0

/-- The visible algebra is the diagonal subalgebra. -/
def conclusion_fold_quantum_visible_booleanization_visibleAlgebra (n : ℕ) :
    Set (conclusion_fold_quantum_visible_booleanization_operator n) :=
  {A | ∀ i j, i ≠ j → A i j = 0}

/-- The sharp event attached to a visible subset. -/
def conclusion_fold_quantum_visible_booleanization_subsetProjector {n : ℕ}
    (S : Finset (Fin n)) : conclusion_fold_quantum_visible_booleanization_operator n :=
  fun i j => if i = j then if i ∈ S then 1 else 0 else 0

/-- Visible sharp events are diagonal `0/1`-valued projectors. -/
def conclusion_fold_quantum_visible_booleanization_sharpEvent {n : ℕ}
    (P : conclusion_fold_quantum_visible_booleanization_operator n) : Prop :=
  P ∈ conclusion_fold_quantum_visible_booleanization_visibleAlgebra n ∧
    ∀ i, P i i = 0 ∨ P i i = 1

/-- Support of a visible sharp event. -/
noncomputable def conclusion_fold_quantum_visible_booleanization_eventSupport {n : ℕ}
    (P : conclusion_fold_quantum_visible_booleanization_operator n) : Finset (Fin n) :=
  Finset.univ.filter fun i => P i i = 1

lemma conclusion_fold_quantum_visible_booleanization_foldChannel_mem_visibleAlgebra {n : ℕ}
    (A : conclusion_fold_quantum_visible_booleanization_operator n) :
    conclusion_fold_quantum_visible_booleanization_foldChannel A ∈
      conclusion_fold_quantum_visible_booleanization_visibleAlgebra n := by
  intro i j hij
  simp [conclusion_fold_quantum_visible_booleanization_foldChannel, hij]

lemma conclusion_fold_quantum_visible_booleanization_foldChannel_eq_of_visible {n : ℕ}
    {A : conclusion_fold_quantum_visible_booleanization_operator n}
    (hA : A ∈ conclusion_fold_quantum_visible_booleanization_visibleAlgebra n) :
    conclusion_fold_quantum_visible_booleanization_foldChannel A = A := by
  funext i j
  by_cases hij : i = j
  · subst hij
    simp [conclusion_fold_quantum_visible_booleanization_foldChannel]
  · simp [conclusion_fold_quantum_visible_booleanization_foldChannel, hij, hA i j hij]

lemma conclusion_fold_quantum_visible_booleanization_range_foldChannel {n : ℕ} :
    Set.range (@conclusion_fold_quantum_visible_booleanization_foldChannel n) =
      conclusion_fold_quantum_visible_booleanization_visibleAlgebra n := by
  ext A
  constructor
  · rintro ⟨B, rfl⟩
    exact conclusion_fold_quantum_visible_booleanization_foldChannel_mem_visibleAlgebra B
  · intro hA
    refine ⟨A, ?_⟩
    exact conclusion_fold_quantum_visible_booleanization_foldChannel_eq_of_visible hA

lemma conclusion_fold_quantum_visible_booleanization_subsetProjector_sharpEvent {n : ℕ}
    (S : Finset (Fin n)) :
    conclusion_fold_quantum_visible_booleanization_sharpEvent
      (conclusion_fold_quantum_visible_booleanization_subsetProjector S) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    simp [conclusion_fold_quantum_visible_booleanization_subsetProjector, hij]
  · intro i
    by_cases hi : i ∈ S
    · right
      simp [conclusion_fold_quantum_visible_booleanization_subsetProjector, hi]
    · left
      simp [conclusion_fold_quantum_visible_booleanization_subsetProjector, hi]

lemma conclusion_fold_quantum_visible_booleanization_eventSupport_subsetProjector {n : ℕ}
    (S : Finset (Fin n)) :
    conclusion_fold_quantum_visible_booleanization_eventSupport
        (conclusion_fold_quantum_visible_booleanization_subsetProjector S) = S := by
  ext i
  simp [conclusion_fold_quantum_visible_booleanization_eventSupport,
    conclusion_fold_quantum_visible_booleanization_subsetProjector]

lemma conclusion_fold_quantum_visible_booleanization_sharpEvent_eq_subsetProjector_support {n : ℕ}
    {P : conclusion_fold_quantum_visible_booleanization_operator n}
    (hP : conclusion_fold_quantum_visible_booleanization_sharpEvent P) :
    P =
      conclusion_fold_quantum_visible_booleanization_subsetProjector
        (conclusion_fold_quantum_visible_booleanization_eventSupport P) := by
  funext i j
  by_cases hij : i = j
  · subst hij
    by_cases hmem : i ∈ conclusion_fold_quantum_visible_booleanization_eventSupport P
    · have hdiag : P i i = 1 := by
        simpa [conclusion_fold_quantum_visible_booleanization_eventSupport] using hmem
      simp [conclusion_fold_quantum_visible_booleanization_subsetProjector,
        conclusion_fold_quantum_visible_booleanization_eventSupport, hdiag]
    · have hnotOne : P i i ≠ 1 := by
        intro hEq
        exact hmem (by
          simpa [conclusion_fold_quantum_visible_booleanization_eventSupport] using hEq)
      rcases hP.2 i with hzero | hone
      · simp [conclusion_fold_quantum_visible_booleanization_subsetProjector,
          conclusion_fold_quantum_visible_booleanization_eventSupport, hzero]
      · exact (hnotOne hone).elim
  · have hOff : P i j = 0 := hP.1 i j hij
    simp [conclusion_fold_quantum_visible_booleanization_subsetProjector, hij, hOff]

/-- The sharp visible-event lattice is Boolean because its events are exactly subset projectors. -/
noncomputable def conclusion_fold_quantum_visible_booleanization_sharpEventEquivSubsets (n : ℕ) :
    {P : conclusion_fold_quantum_visible_booleanization_operator n //
      conclusion_fold_quantum_visible_booleanization_sharpEvent P} ≃ Finset (Fin n) where
  toFun P := conclusion_fold_quantum_visible_booleanization_eventSupport P.1
  invFun S :=
    ⟨conclusion_fold_quantum_visible_booleanization_subsetProjector S,
      conclusion_fold_quantum_visible_booleanization_subsetProjector_sharpEvent S⟩
  left_inv P := by
    apply Subtype.ext
    symm
    exact conclusion_fold_quantum_visible_booleanization_sharpEvent_eq_subsetProjector_support P.2
  right_inv S :=
    conclusion_fold_quantum_visible_booleanization_eventSupport_subsetProjector S

/-- The fold channel has exactly the diagonal visible algebra as its image, visible sharp events
are exactly subset projectors, and the finite visible-event lattice is Boolean.
    thm:conclusion-fold-quantum-visible-booleanization -/
theorem paper_conclusion_fold_quantum_visible_booleanization (n : ℕ) :
    Set.range (@conclusion_fold_quantum_visible_booleanization_foldChannel n) =
      conclusion_fold_quantum_visible_booleanization_visibleAlgebra n ∧
    (∀ P, conclusion_fold_quantum_visible_booleanization_sharpEvent P ↔
      ∃ S : Finset (Fin n),
        P = conclusion_fold_quantum_visible_booleanization_subsetProjector S) ∧
    Nonempty
      ({P : conclusion_fold_quantum_visible_booleanization_operator n //
        conclusion_fold_quantum_visible_booleanization_sharpEvent P} ≃ Finset (Fin n)) := by
  refine ⟨conclusion_fold_quantum_visible_booleanization_range_foldChannel, ?_, ?_⟩
  · intro P
    constructor
    · intro hP
      refine ⟨conclusion_fold_quantum_visible_booleanization_eventSupport P, ?_⟩
      exact conclusion_fold_quantum_visible_booleanization_sharpEvent_eq_subsetProjector_support hP
    · rintro ⟨S, rfl⟩
      exact conclusion_fold_quantum_visible_booleanization_subsetProjector_sharpEvent S
  · exact ⟨conclusion_fold_quantum_visible_booleanization_sharpEventEquivSubsets n⟩

end Omega.Conclusion
