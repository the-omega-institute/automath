import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-real-input40-primitive-two-step-exact-count`.  The peeling identity
and the audited total count force the two-step primitive core count. -/
theorem paper_xi_real_input40_primitive_two_step_exact_count
    (p2 p2_core : Nat) (hpeel : p2 = 1 + p2_core) (haudit : p2 = 7) :
    p2 = 7 ∧ p2_core = 6 := by
  constructor
  · exact haudit
  · omega

end Omega.Zeta
