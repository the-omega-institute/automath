import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldIndexExtremalEntropyLossMaxfiber
import Omega.OperatorAlgebra.FoldSqrtIndexFieldBasic

namespace Omega.DerivedConsequences

/-- Paper label: `thm:derived-sqrt-index-field-triple-extremum`. The squared norm of the
square-root index field, the supremum of the Watatani index field, and the explicit max-fiber
quantity all identify the same largest-fiber cardinality. -/
theorem paper_derived_sqrt_index_field_triple_extremum {OmegaTy XTy : Type*}
    [Fintype OmegaTy] [DecidableEq OmegaTy] [Nonempty OmegaTy] [Fintype XTy] [DecidableEq XTy]
    (fold : OmegaTy → XTy) (hfold : Function.Surjective fold) :
    Omega.OperatorAlgebra.foldSqrtIndexFieldNorm fold ^ 2 =
      (Omega.OperatorAlgebra.foldLargestFiberCard fold : ℝ) ∧
    ((Finset.univ.sup fun x => Omega.OperatorAlgebra.foldWatataniIndexElement fold x : ℕ) : ℝ) =
      (Omega.OperatorAlgebra.foldLargestFiberCard fold : ℝ) ∧
    (Omega.OperatorAlgebra.foldSqrtIndexFieldMaxFiber fold : ℝ) =
      (Omega.OperatorAlgebra.foldLargestFiberCard fold : ℝ) := by
  have hsqrt := Omega.OperatorAlgebra.paper_op_algebra_fold_sqrt_index_field_basic fold
  have hmax := Omega.OperatorAlgebra.paper_op_algebra_index_extremal_entropy_loss_maxfiber fold hfold
  refine ⟨?_, ?_, by rfl⟩
  · simpa [Omega.OperatorAlgebra.foldSqrtIndexFieldMaxFiber,
      Omega.OperatorAlgebra.foldLargestFiberCard] using hsqrt.2.2
  · exact_mod_cast hmax.1

end Omega.DerivedConsequences
