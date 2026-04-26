import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-pick-poisson-three-set-mobius-identity`. -/
theorem paper_xi_pick_poisson_three_set_mobius_identity
    (singleA singleB singleC internalA internalB internalC crossAB crossAC crossBC
      phiABC phiAB phiBC phiB : ℝ)
    (hABC :
      phiABC =
        singleA + singleB + singleC + internalA + internalB + internalC +
          crossAB + crossAC + crossBC)
    (hAB : phiAB = singleA + singleB + internalA + internalB + crossAB)
    (hBC : phiBC = singleB + singleC + internalB + internalC + crossBC)
    (hB : phiB = singleB + internalB) :
    phiABC - phiAB - phiBC + phiB = crossAC := by
  rw [hABC, hAB, hBC, hB]
  ring

end Omega.Zeta
