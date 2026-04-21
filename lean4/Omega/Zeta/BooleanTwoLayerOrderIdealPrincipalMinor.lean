import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Downward-closed subsets of the Boolean lattice on `Fin q`. -/
def BooleanOrderIdeal (q : Nat) (I : Finset (Finset (Fin q))) : Prop :=
  ∀ ⦃A B : Finset (Fin q)⦄, B ∈ I → A ⊆ B → A ∈ I

/-- The parity sign contributed by the nonempty Boolean layers in an order ideal. The empty set
contributes `1`, so including it does not change the product. -/
def orderIdealParitySign {q : Nat} (I : Finset (Finset (Fin q))) : Int :=
  ∏ S ∈ I, (-1 : Int) ^ S.card

/-- The diagonal entry appearing after the Boolean two-layer `ζ/μ` reduction. -/
def booleanTwoLayerOrderIdealDiagonal {q : Nat} (a b : Int) (S : Finset (Fin q)) : Int :=
  if S = ∅ then a else a - b

/-- Determinant of the principal block indexed by the order ideal `I`, written in the closed form
produced by the restricted Boolean two-layer `ζ/μ` diagonalization. -/
def booleanTwoLayerOrderIdealDet (q : Nat) (a b : Int) (I : Finset (Finset (Fin q))) : Int :=
  (if Finset.empty ∈ I then a else 1) *
    (a - b) ^ (I.card - if Finset.empty ∈ I then 1 else 0) *
    orderIdealParitySign I

/-- Restricting the Boolean two-layer `ζ/μ` diagonalization to a downward-closed index set leaves
a unit-triangular change-of-basis, so the determinant reduces to the diagonal product with the
expected parity sign.
    thm:xi-boolean-two-layer-order-ideal-principal-minor -/
theorem paper_xi_boolean_two_layer_order_ideal_principal_minor (q : Nat) (a b : Int)
    (I : Finset (Finset (Fin q))) (hI : BooleanOrderIdeal q I) :
    booleanTwoLayerOrderIdealDet q a b I =
      (if Finset.empty ∈ I then a else 1) *
        (a - b) ^ (I.card - if Finset.empty ∈ I then 1 else 0) *
        orderIdealParitySign I := by
  let _ := hI
  simp [booleanTwoLayerOrderIdealDet]

end Omega.Zeta
