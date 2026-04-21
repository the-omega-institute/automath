import Mathlib.Data.Real.Sqrt
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

/-- The blockwise square-root index field `x ↦ sqrt(d_x)`. -/
noncomputable def foldSqrtIndexField (fold : Ω → X) (x : X) : ℝ :=
  Real.sqrt (foldWatataniIndexElement fold x)

/-- The maximal fiber cardinality. -/
def foldSqrtIndexFieldMaxFiber (fold : Ω → X) : ℕ :=
  Finset.univ.sup fun x => Fintype.card (foldFiber fold x)

/-- The finite `ℓ∞` norm of the square-root index field. -/
noncomputable def foldSqrtIndexFieldNorm (fold : Ω → X) : ℝ :=
  Real.sqrt (foldSqrtIndexFieldMaxFiber fold)

/-- Basic identities for the blockwise square-root index field. -/
def FoldSqrtIndexFieldBasic (fold : Ω → X) : Prop :=
  (∀ x, foldSqrtIndexField fold x ^ 2 = (Fintype.card (foldFiber fold x) : ℝ)) ∧
    foldSqrtIndexFieldNorm fold = Real.sqrt (foldSqrtIndexFieldMaxFiber fold) ∧
    foldSqrtIndexFieldNorm fold ^ 2 = (foldSqrtIndexFieldMaxFiber fold : ℝ)

/-- Paper label: `prop:op-algebra-fold-sqrt-index-field-basic`. -/
theorem paper_op_algebra_fold_sqrt_index_field_basic {Ω X : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype X] [DecidableEq X] (fold : Ω → X) : FoldSqrtIndexFieldBasic fold := by
  have hMult := paper_op_algebra_fold_watatani_index_equals_multiplicity_field fold
  refine ⟨?_, rfl, ?_⟩
  · intro x
    unfold foldSqrtIndexField
    rw [Real.sq_sqrt]
    exact_mod_cast hMult.2.2 x
    positivity
  · unfold foldSqrtIndexFieldNorm
    rw [Real.sq_sqrt]
    positivity

end

end Omega.OperatorAlgebra
