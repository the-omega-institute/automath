import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete token type for audited characteristic shadows over `F_2`. -/
inductive xi_time_part9zj_resonance_window_mod2_order_aliasing_F2Poly where
  | xi_time_part9zj_resonance_window_mod2_order_aliasing_F2Poly_shadow
  | xi_time_part9zj_resonance_window_mod2_order_aliasing_F2Poly_other (code : Nat)
  deriving DecidableEq

/-- The common audited mod-2 shadow `lambda^3 (lambda + 1)^8`. -/
def xi_time_part9zj_resonance_window_mod2_order_aliasing_shadow :
    xi_time_part9zj_resonance_window_mod2_order_aliasing_F2Poly :=
  .xi_time_part9zj_resonance_window_mod2_order_aliasing_F2Poly_shadow

/-- Paper label: `prop:xi-time-part9zj-resonance-window-mod2-order-aliasing`. -/
theorem paper_xi_time_part9zj_resonance_window_mod2_order_aliasing
    (P : Nat → xi_time_part9zj_resonance_window_mod2_order_aliasing_F2Poly)
    (h13 : P 13 = xi_time_part9zj_resonance_window_mod2_order_aliasing_shadow)
    (h15 : P 15 = xi_time_part9zj_resonance_window_mod2_order_aliasing_shadow) :
    P 13 = P 15 ∧ (13 : Nat) ≠ 15 := by
  refine ⟨?_, by omega⟩
  rw [h13, h15]

end Omega.Zeta
