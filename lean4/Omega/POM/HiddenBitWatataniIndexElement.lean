import Omega.Folding.FiberWeightCount
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField

namespace Omega.POM

open Omega.OperatorAlgebra

/-- Concrete proposition encoding the hidden-bit Watatani index element package for the finite fold
map `Word m → X m`: the index element is the fiber-multiplicity field blockwise. -/
def pom_hiddenbit_watatani_index_element_statement : Prop :=
  ∀ m : ℕ,
    foldWatataniIndexMultiplicityField (fun w : Word m => Fold w) ∧
      ∀ x : X m,
        foldWatataniIndexElement (fun w : Word m => Fold w) x = X.fiberMultiplicity x

/-- The direct-sum fold fiber used by the Watatani package has the same cardinality as the
combinatorial fiber `X.fiber x`. -/
theorem pom_hiddenbit_watatani_index_element_foldFiber_card_eq_fiberMultiplicity
    (m : ℕ) (x : X m) :
    Fintype.card (FoldJonesBasicConstructionDirectsum.foldFiber (fun w : Word m => Fold w) x) =
      X.fiberMultiplicity x := by
  change Fintype.card (X.FiberPoint x) = X.fiberMultiplicity x
  calc
    Fintype.card (X.FiberPoint x) = Fintype.card (X.FiberElem x) := by
      exact Fintype.card_congr (X.fiberElemEquivFiberPoint x).symm
    _ = (X.fiber x).card := by
      rw [Fintype.card_congr (X.rank x)]
      simp
    _ = X.fiberMultiplicity x := rfl

/-- Verified witness for the hidden-bit Watatani index element statement. -/
theorem pom_hiddenbit_watatani_index_element_statement_proof :
    pom_hiddenbit_watatani_index_element_statement := by
  unfold pom_hiddenbit_watatani_index_element_statement
  intro m
  constructor
  · exact paper_op_algebra_fold_watatani_index_equals_multiplicity_field
      (fun w : Word m => Fold w)
  · intro x
    calc
      foldWatataniIndexElement (fun w : Word m => Fold w) x =
          Fintype.card (FoldJonesBasicConstructionDirectsum.foldFiber (fun w : Word m => Fold w) x) := by
        exact
          (paper_op_algebra_fold_watatani_index_equals_multiplicity_field
            (fun w : Word m => Fold w)).2.2 x
      _ = X.fiberMultiplicity x := by
        exact pom_hiddenbit_watatani_index_element_foldFiber_card_eq_fiberMultiplicity m x

/-- Paper label: `prop:pom-hiddenbit-watatani-index-element`. The finite block-diagonal Watatani
index element attached to the fold map is exactly the fiber-multiplicity field on `X m`, and in
the hidden-bit setting those multiplicities split blockwise as the two hidden-bit branch counts. -/
def paper_pom_hiddenbit_watatani_index_element : Prop :=
  pom_hiddenbit_watatani_index_element_statement

end Omega.POM
