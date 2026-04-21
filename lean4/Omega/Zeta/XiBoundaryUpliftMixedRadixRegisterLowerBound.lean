import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-boundary-uplift-mixed-radix-register-lower-bound`.  Independent binary
and ternary boundary choices contribute `2 ^ b2 * 3 ^ b3` global states, so any injective register
encoding needs at least that many targets. -/
theorem paper_xi_boundary_uplift_mixed_radix_register_lower_bound
    (b2 b3 R : ℕ) (encode : Fin (2 ^ b2 * 3 ^ b3) → Fin R)
    (hinj : Function.Injective encode) : 2 ^ b2 * 3 ^ b3 ≤ R := by
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective encode hinj

/-- Window-`6` boundary uplift specialization: three independent binary choices already require
at least eight register states. -/
theorem xi_boundary_uplift_window6_register_lower_bound
    (R : ℕ) (encode : Fin 8 → Fin R) (hinj : Function.Injective encode) : 8 ≤ R := by
  simpa using
    paper_xi_boundary_uplift_mixed_radix_register_lower_bound 3 0 R encode hinj

/-- Window-`7` boundary uplift specialization: five ternary choices require at least `3^5 = 243`
register states. -/
theorem xi_boundary_uplift_window7_register_lower_bound
    (R : ℕ) (encode : Fin 243 → Fin R) (hinj : Function.Injective encode) : 243 ≤ R := by
  simpa using
    paper_xi_boundary_uplift_mixed_radix_register_lower_bound 0 5 R encode hinj

/-- Window-`8` boundary uplift specialization: eight ternary choices require at least
`3^8 = 6561` register states. -/
theorem xi_boundary_uplift_window8_register_lower_bound
    (R : ℕ) (encode : Fin 6561 → Fin R) (hinj : Function.Injective encode) : 6561 ≤ R := by
  simpa using
    paper_xi_boundary_uplift_mixed_radix_register_lower_bound 0 8 R encode hinj

end Omega.Zeta
