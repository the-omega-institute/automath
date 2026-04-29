import Omega.Zeta.XiCdimKolmResidualGap

namespace Omega.Zeta

/-- Paper label: `cor:xi-cdim-kolm-single-phase`. -/
theorem paper_xi_cdim_kolm_single_phase
    (r b torsionCard shortCodeCount t : ℕ)
    (hr : 2 ≤ r)
    (hshort : shortCodeCount * 2 ^ t ≤ (2 ^ b) ^ (r - 1) * torsionCard) :
    let W := xiCdimWindowCard r b torsionCard
    let P := xiCdimVisiblePhaseCard 1 b
    P * shortCodeCount * 2 ^ t ≤ W ∧
      W = P * ((2 ^ b) ^ (r - 1) * torsionCard) := by
  have hphase : 1 ≤ r := by omega
  exact paper_xi_cdim_kolm_residual_gap r 1 b torsionCard shortCodeCount t hphase hshort

end Omega.Zeta
