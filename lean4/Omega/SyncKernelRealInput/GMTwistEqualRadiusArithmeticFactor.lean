import Mathlib.Data.ZMod.Basic

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:gm-twist-equal-radius-arithmetic-factor`. -/
theorem paper_gm_twist_equal_radius_arithmetic_factor {State : Type*} (q : Nat)
    (shift : State → State) (val : State → ZMod q) (equalRadius : Prop)
    (hWielandt :
      equalRadius →
        ∃ pi g : State → ZMod q,
          (∃ x y, pi x ≠ pi y) ∧ ∀ x, val x = g x - g (shift x))
    (heq : equalRadius) :
    ∃ pi g : State → ZMod q,
      (∃ x y, pi x ≠ pi y) ∧ ∀ x, val x = g x - g (shift x) := by
  exact hWielandt heq

end Omega.SyncKernelRealInput
