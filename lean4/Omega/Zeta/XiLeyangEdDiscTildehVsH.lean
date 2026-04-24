import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-leyang-ed-disc-tildeh-vs-h`.
The two Lee--Yang discriminant factorizations differ only by a factor of `2^4`. -/
theorem paper_xi_leyang_ed_disc_tildeh_vs_h (disc_h disc_tildeh : ℤ)
    (hdisc_h : disc_h = -((2^2) * 3^3 * 31^2 * 37 : ℤ))
    (hdisc_tildeh : disc_tildeh = -((2^6) * 3^3 * 31^2 * 37 : ℤ)) :
    disc_tildeh = (2^4 : ℤ) * disc_h := by
  rw [hdisc_h, hdisc_tildeh]
  ring

end Omega.Zeta
