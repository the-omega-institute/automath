import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

open scoped BigOperators

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

/-- The largest rank allowed on the `x`-block under the ambient block size and the external rank
cap `L`. -/
def oracleProjectionBlockCap (fold : Ω → X) (L : ℕ) (x : X) : ℕ :=
  min (Fintype.card (foldFiber fold x)) L

/-- A blockwise rank profile is admissible when each block rank is bounded both by the block size
and by the external rank cutoff `L`. -/
def oracleProjectionAdmissible (fold : Ω → X) (L : ℕ) (r : X → ℕ) : Prop :=
  ∀ x, r x ≤ Fintype.card (foldFiber fold x) ∧ r x ≤ L

/-- The continuous capacity curve evaluated at the integer cutoff `L`. -/
def oracleProjectionVariationalCapacity (fold : Ω → X) (L : ℕ) : ℕ :=
  ∑ x, oracleProjectionBlockCap fold L x

/-- The fiberwise maximizing rank profile: on each block one takes the largest admissible rank. -/
def oracleProjectionMaximizer (fold : Ω → X) (L : ℕ) : X → ℕ :=
  oracleProjectionBlockCap fold L

omit [DecidableEq Ω] [Fintype X] in
lemma oracleProjectionAdmissible_le_blockCap (fold : Ω → X) (L : ℕ) {r : X → ℕ}
    (hr : oracleProjectionAdmissible fold L r) (x : X) :
    r x ≤ oracleProjectionBlockCap fold L x := by
  exact le_min (hr x).1 (hr x).2

/-- Paper label: `thm:op-algebra-oracle-projection-variational-capacity`.
In the direct-sum Jones model, maximizing the total projected rank under the per-block cutoff `L`
amounts to taking the rank `min(d_x, L)` in each block, so the maximal value is the sum of these
blockwise minima, and equality occurs exactly for that maximizing rank profile. -/
theorem paper_op_algebra_oracle_projection_variational_capacity
    (fold : Ω → X) (L : ℕ) :
    FoldJonesBasicConstructionDirectsum.directsumMatrixDecomposition fold ∧
      oracleProjectionAdmissible fold L (oracleProjectionMaximizer fold L) ∧
      (∀ r, oracleProjectionAdmissible fold L r →
        (∑ x, r x) ≤ oracleProjectionVariationalCapacity fold L) ∧
      (∀ r, oracleProjectionAdmissible fold L r →
        ((∑ x, r x) = oracleProjectionVariationalCapacity fold L ↔
          ∀ x, r x = oracleProjectionMaximizer fold L x)) := by
  refine ⟨(paper_op_algebra_fold_jones_basic_construction_directsum fold).1, ?_, ?_, ?_⟩
  · intro x
    exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩
  · intro r hr
    refine Finset.sum_le_sum ?_
    intro x hx
    exact oracleProjectionAdmissible_le_blockCap fold L hr x
  · intro r hr
    constructor
    · intro hsum x
      have hle : ∀ y ∈ (Finset.univ : Finset X), r y ≤ oracleProjectionMaximizer fold L y := by
        intro y hy
        exact oracleProjectionAdmissible_le_blockCap fold L hr y
      have hzero :
          ∑ y, (oracleProjectionMaximizer fold L y - r y) = 0 := by
        have hsumCap : ∑ y, oracleProjectionMaximizer fold L y =
            oracleProjectionVariationalCapacity fold L := by
          simp [oracleProjectionVariationalCapacity, oracleProjectionMaximizer]
        calc
          ∑ y, (oracleProjectionMaximizer fold L y - r y)
              = ∑ y, oracleProjectionMaximizer fold L y - ∑ y, r y := by
                  simpa using (Finset.sum_tsub_distrib (s := Finset.univ) hle)
          _ = oracleProjectionVariationalCapacity fold L - ∑ y, r y := by rw [hsumCap]
          _ = 0 := by rw [← hsum]; simp
      have hterms :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun y hy => Nat.zero_le _) ).1 hzero
      exact le_antisymm
        (hle x (by simp))
        (Nat.sub_eq_zero_iff_le.mp (hterms x (by simp)))
    · intro hmax
      calc
        (∑ x, r x) = ∑ x, oracleProjectionMaximizer fold L x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact hmax x
        _ = oracleProjectionVariationalCapacity fold L := by
          simp [oracleProjectionVariationalCapacity, oracleProjectionMaximizer]

end

end Omega.OperatorAlgebra
