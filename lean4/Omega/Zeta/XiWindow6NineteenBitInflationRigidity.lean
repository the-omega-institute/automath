import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-window6-nineteen-bit-inflation-rigidity`. -/
theorem paper_xi_window6_nineteen_bit_inflation_rigidity :
    (21 : Nat) - 2 = 19 ∧ (2 : Nat) ^ 21 / (2 : Nat) ^ 2 = (2 : Nat) ^ 19 := by
  norm_num

end Omega.Zeta
