import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

open scoped BigOperators

namespace Omega.OperatorAlgebra

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

open FoldJonesBasicConstructionDirectsum

/-- The normalized coefficient attached to a matrix unit in the averaged fiber element. -/
noncomputable def op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card
    (fold : Ω → X) (x : X) : ℂ :=
  (Fintype.card (foldFiber fold x) : ℂ)⁻¹

/-- The averaged diagonal block appearing in the weak-Hopf realization of the fold channel. -/
noncomputable def op_algebra_fold_quantum_channel_weak_hopf_groupoid_average_diagonal
    (fold : Ω → X) (x : X) : Matrix (foldFiber fold x) (foldFiber fold x) ℂ :=
  ∑ ω : foldFiber fold x,
    op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card fold x •
      fiberMatrixUnit fold x ω ω

/-- The basis-level action induced by the distinguished averaged groupoid element. -/
noncomputable def op_algebra_fold_quantum_channel_weak_hopf_groupoid_basis_action
    (fold : Ω → X) (x : X) (a b : foldFiber fold x) :
    Matrix (foldFiber fold x) (foldFiber fold x) ℂ :=
  ∑ ω : foldFiber fold x,
    ∑ ω' : foldFiber fold x,
      op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card fold x •
        (fiberMatrixUnit fold x ω ω' * fiberMatrixUnit fold x a b *
          fiberMatrixUnit fold x ω' ω)

/-- The fiberwise channel sends a matrix unit to the normalized diagonal average when the basis
vector survives the fold and to `0` otherwise. -/
noncomputable def op_algebra_fold_quantum_channel_weak_hopf_groupoid_channel_on_basis
    (fold : Ω → X) (x : X) (a b : foldFiber fold x) :
    Matrix (foldFiber fold x) (foldFiber fold x) ℂ :=
  if a = b then op_algebra_fold_quantum_channel_weak_hopf_groupoid_average_diagonal fold x else 0

omit [Fintype X] in
lemma op_algebra_fold_quantum_channel_weak_hopf_groupoid_triple_product
    (fold : Ω → X) (x : X) (ω ω' a b : foldFiber fold x) :
    fiberMatrixUnit fold x ω ω' * fiberMatrixUnit fold x a b * fiberMatrixUnit fold x ω' ω =
      if ω' = a then if a = b then fiberMatrixUnit fold x ω ω else 0 else 0 := by
  by_cases hω' : ω' = a
  · subst a
    rw [fiberMatrixUnit_mul, if_pos rfl]
    by_cases hab : ω' = b
    · subst b
      simp [fiberMatrixUnit_mul]
    · have hb' : b ≠ ω' := by
        simpa [eq_comm] using hab
      rw [fiberMatrixUnit_mul]
      simp [hab, hb']
  · simp [fiberMatrixUnit_mul, hω']

omit [Fintype X] in
lemma op_algebra_fold_quantum_channel_weak_hopf_groupoid_sum_over_middle
    (fold : Ω → X) (x : X) (ω a b : foldFiber fold x) :
    ∑ ω' : foldFiber fold x,
      op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card fold x •
        (fiberMatrixUnit fold x ω ω' * fiberMatrixUnit fold x a b *
          fiberMatrixUnit fold x ω' ω) =
      if a = b then
        op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card fold x •
          fiberMatrixUnit fold x ω ω
      else 0 := by
  by_cases hab : a = b
  · subst hab
    rw [Finset.sum_eq_single a]
    · simp [op_algebra_fold_quantum_channel_weak_hopf_groupoid_triple_product]
    · intro ω' _ hω'
      simp [op_algebra_fold_quantum_channel_weak_hopf_groupoid_triple_product, hω']
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ a))
  · have hzero :
        (∑ ω' : foldFiber fold x,
            op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card fold x •
              (fiberMatrixUnit fold x ω ω' * fiberMatrixUnit fold x a b *
                fiberMatrixUnit fold x ω' ω)) =
          (0 : Matrix (foldFiber fold x) (foldFiber fold x) ℂ) := by
      calc
        ∑ ω' : foldFiber fold x,
            op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card fold x •
              (fiberMatrixUnit fold x ω ω' * fiberMatrixUnit fold x a b *
                fiberMatrixUnit fold x ω' ω) =
          ∑ _ : foldFiber fold x, (0 : Matrix (foldFiber fold x) (foldFiber fold x) ℂ) := by
            apply Finset.sum_congr rfl
            intro ω' hω'
            simp [op_algebra_fold_quantum_channel_weak_hopf_groupoid_triple_product, hab]
        _ = 0 := by simp
    simpa [hab] using hzero

omit [Fintype X] in
lemma op_algebra_fold_quantum_channel_weak_hopf_groupoid_basis_action_eq_channel_on_basis
    (fold : Ω → X) (x : X) (a b : foldFiber fold x) :
    op_algebra_fold_quantum_channel_weak_hopf_groupoid_basis_action fold x a b =
      op_algebra_fold_quantum_channel_weak_hopf_groupoid_channel_on_basis fold x a b := by
  unfold op_algebra_fold_quantum_channel_weak_hopf_groupoid_basis_action
    op_algebra_fold_quantum_channel_weak_hopf_groupoid_channel_on_basis
    op_algebra_fold_quantum_channel_weak_hopf_groupoid_average_diagonal
  have hrewrite :
      (∑ ω : foldFiber fold x,
          ∑ ω' : foldFiber fold x,
            op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card fold x •
              (fiberMatrixUnit fold x ω ω' * fiberMatrixUnit fold x a b *
                fiberMatrixUnit fold x ω' ω)) =
        ∑ ω : foldFiber fold x,
          if a = b then
            op_algebra_fold_quantum_channel_weak_hopf_groupoid_inv_card fold x •
              fiberMatrixUnit fold x ω ω
          else 0 := by
    apply Finset.sum_congr rfl
    intro ω hω
    exact op_algebra_fold_quantum_channel_weak_hopf_groupoid_sum_over_middle fold x ω a b
  rw [hrewrite]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab]

/-- Paper label: `thm:op-algebra-fold-quantum-channel-weak-hopf-groupoid`.
The finite fold basis decomposes into fiber blocks, and on each block the distinguished averaged
groupoid element acts on matrix units exactly by the fold channel. -/
theorem paper_op_algebra_fold_quantum_channel_weak_hopf_groupoid (fold : Ω → X) :
    directsumMatrixDecomposition fold ∧
      ∀ x (a b : foldFiber fold x),
        op_algebra_fold_quantum_channel_weak_hopf_groupoid_basis_action fold x a b =
          op_algebra_fold_quantum_channel_weak_hopf_groupoid_channel_on_basis fold x a b := by
  refine ⟨paper_op_algebra_fold_jones_basic_construction_directsum fold |>.1, ?_⟩
  intro x a b
  exact op_algebra_fold_quantum_channel_weak_hopf_groupoid_basis_action_eq_channel_on_basis
    fold x a b

end

end Omega.OperatorAlgebra
