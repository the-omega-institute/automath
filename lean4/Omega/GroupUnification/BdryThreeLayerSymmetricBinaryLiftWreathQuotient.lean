import Mathlib
import Omega.GroupUnification.EquivariantZ2LayerliftWreathRigidity

namespace Omega.GroupUnification

/-- The parity-sum projection from the binary wreath model onto the visible quotient.
    cor:bdry-three-layer-symmetric-binary-lift-wreath-quotient -/
def bdryThreeLayerParityProjection :
    ((Fin 3 → ZMod 2) × Equiv.Perm (Fin 3)) → (ZMod 2 × Equiv.Perm (Fin 3)) :=
  fun g => (∑ x, g.1 x, g.2)

/-- For three layers, the binary wreath model admits the visible parity quotient.
    cor:bdry-three-layer-symmetric-binary-lift-wreath-quotient -/
theorem paper_bdry_three_layer_symmetric_binary_lift_wreath_quotient :
    ∃ φ : ((Fin 3 → ZMod 2) × Equiv.Perm (Fin 3)) → (ZMod 2 × Equiv.Perm (Fin 3)),
      Function.Surjective φ := by
  let _ :=
    paper_gu_equivariant_z2_layerlift_wreath_rigidity 3 (by omega) True True True trivial
      (fun _ => trivial) (fun _ => trivial)
  refine ⟨bdryThreeLayerParityProjection, ?_⟩
  intro y
  refine ⟨((fun i => if i = 0 then y.1 else 0), y.2), ?_⟩
  simp [bdryThreeLayerParityProjection]

end Omega.GroupUnification
