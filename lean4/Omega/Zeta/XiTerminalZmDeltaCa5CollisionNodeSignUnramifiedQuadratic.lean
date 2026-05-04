import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-terminal-zm-delta-ca5-collision-node-sign-unramified-quadratic`. -/
theorem paper_xi_terminal_zm_delta_ca5_collision_node_sign_unramified_quadratic :
    (∃ a : ZMod 3739, a ^ 2 = (3694 : ZMod 3739) * ((-140267 : ZMod 3739)⁻¹)) ∧
      (∃ a : ZMod 7333, a ^ 2 = (6699 : ZMod 7333) * ((-140267 : ZMod 7333)⁻¹)) := by
  constructor
  · exact ⟨1146, by native_decide⟩
  · exact ⟨1746, by native_decide⟩

end Omega.Zeta
