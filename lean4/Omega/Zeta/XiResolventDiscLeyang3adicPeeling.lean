import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-resolvent-disc-leyang-3adic-peeling`.
The cubic discriminant of `256*y^3 + 411*y^2 + 165*y + 32` factors as
`-3^9 * 31^2 * 37`, and peeling the `3^9` factor leaves `31^2 * 37`. -/
theorem paper_xi_resolvent_disc_leyang_3adic_peeling :
    (let disc : ℤ :=
      411^2 * 165^2 - 4 * 256 * 165^3 - 4 * 411^3 * 32 - 27 * 256^2 * 32^2 +
        18 * 256 * 411 * 165 * 32
    disc = - (3 : ℤ)^9 * 31^2 * 37 ∧ -disc / (3 : ℤ)^9 = 31^2 * 37) := by
  norm_num

end Omega.Zeta
