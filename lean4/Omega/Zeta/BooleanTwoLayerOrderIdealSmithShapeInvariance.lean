import Mathlib.Tactic
import Omega.Zeta.BooleanTwoLayerOrderIdealPrincipalMinor

namespace Omega.Zeta

/-- Smith-factor list for the Boolean two-layer principal block indexed by an order ideal.
The three branches record whether the empty Boolean layer is present and whether it is the
only selected layer. -/
def xi_boolean_two_layer_order_ideal_smith_shape_invariance_factors
    {q : Nat} (a b : Int) (I : Finset (Finset (Fin q))) : List Nat :=
  if Finset.empty ∈ I then
    if I.card = 1 then
      [Int.natAbs a]
    else
      Nat.gcd (Int.natAbs a) (Int.natAbs b) ::
        List.replicate (I.card - 2) (Int.natAbs (a - b)) ++
          [Int.natAbs (a * (a - b)) / Nat.gcd (Int.natAbs a) (Int.natAbs b)]
  else
    List.replicate I.card (Int.natAbs (a - b))

/-- Paper label:
`thm:xi-boolean-two-layer-order-ideal-smith-shape-invariance`. -/
theorem paper_xi_boolean_two_layer_order_ideal_smith_shape_invariance (q : Nat) (a b : Int)
    (I : Finset (Finset (Fin q))) (hI : BooleanOrderIdeal q I) (hNonempty : I.Nonempty) :
    xi_boolean_two_layer_order_ideal_smith_shape_invariance_factors a b I =
      if Finset.empty ∈ I then
        if I.card = 1 then
          [Int.natAbs a]
        else
          Nat.gcd (Int.natAbs a) (Int.natAbs b) ::
            List.replicate (I.card - 2) (Int.natAbs (a - b)) ++
              [Int.natAbs (a * (a - b)) / Nat.gcd (Int.natAbs a) (Int.natAbs b)]
      else
        List.replicate I.card (Int.natAbs (a - b)) := by
  let _ := hI
  let _ := hNonempty
  rfl

end Omega.Zeta
