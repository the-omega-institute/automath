import Omega.Zeta.BooleanTwoLayerSmithNormalForm

namespace Omega.Zeta

/-- Paper-facing quotient-Smith package obtained by normalizing the integer parameters to natural
data and reordering the Smith diagonal into endpoint-plus-middle-layer form. -/
def XiBooleanTwoLayerSymmetricQuotientSmithStatement (q : Nat) (a b : Int) : Prop :=
  let layerCount := q - 1
  let a0 := Int.natAbs a
  let b0 := Int.natAbs b
  let d := a0 - b0
  let g := Nat.gcd a0 d
  List.Perm (booleanTwoLayerSmithDiagonal a0 b0 layerCount)
    (g :: (List.replicate layerCount d ++ [Nat.lcm a0 d]))

/-- Thin wrapper around the existing Boolean two-layer Smith reduction, with the diagonal entries
presented in the paper's endpoint-plus-middle-layer order.
    thm:xi-boolean-two-layer-symmetric-quotient-smith -/
theorem paper_xi_boolean_two_layer_symmetric_quotient_smith
    (q : Nat) (a b : Int) : XiBooleanTwoLayerSymmetricQuotientSmithStatement q a b := by
  dsimp [XiBooleanTwoLayerSymmetricQuotientSmithStatement]
  let layerCount := q - 1
  let a0 := Int.natAbs a
  let b0 := Int.natAbs b
  let d := a0 - b0
  let g := Nat.gcd a0 d
  obtain ⟨_, _, _, hdiag, _⟩ := paper_xi_boolean_two_layer_smith_normal_form a0 b0 layerCount
  rw [hdiag]
  have hperm : List.Perm (Nat.lcm a0 d :: List.replicate layerCount d)
      (List.replicate layerCount d ++ [Nat.lcm a0 d]) := by
    simpa using
      (List.perm_middle (a := Nat.lcm a0 d) (l₁ := List.replicate layerCount d)
        (l₂ := ([] : List Nat))).symm
  simpa [g, d, layerCount, a0, b0] using List.Perm.cons g hperm

end Omega.Zeta
