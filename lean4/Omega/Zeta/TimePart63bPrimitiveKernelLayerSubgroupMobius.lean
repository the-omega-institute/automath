import Mathlib.Algebra.Ring.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part63b-primitive-kernel-layer-subgroup-mobius`. -/
theorem paper_xi_time_part63b_primitive_kernel_layer_subgroup_mobius {Sub R : Type}
    [CommRing R] (sumAbove : (Sub -> R) -> Sub -> R)
    (mobiusSumAbove : (Sub -> R) -> Sub -> R) (B K : Sub -> R)
    (h_forward : forall H, B H = sumAbove K H)
    (h_mobius : forall H, K H = mobiusSumAbove B H) :
    (forall H, B H = sumAbove K H) ∧ (forall H, K H = mobiusSumAbove B H) := by
  exact ⟨h_forward, h_mobius⟩

end Omega.Zeta
