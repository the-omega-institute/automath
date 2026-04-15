import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the survivor Renyi pressure spectrum theorem.
    thm:survivor-renyi-pressure -/
theorem paper_scan_projection_address_survivor_renyi_pressure
    (s PY PYHphi PYHs gammaH ambientLimit conditionedLimit h2H chiH PYH2phi : ℝ)
    (hAmbient : ambientLimit = s * PY - PYHs)
    (hGap : gammaH = PY - PYHphi)
    (hConditioned : conditionedLimit = ambientLimit - s * gammaH)
    (h2 : h2H = 2 * PYHphi - PYH2phi)
    (hChi : chiH = 2 * PY - PYH2phi) :
    conditionedLimit = s * PYHphi - PYHs ∧
      chiH = 2 * gammaH + h2H := by
  constructor
  · rw [hConditioned, hAmbient, hGap]
    ring
  · rw [hChi, hGap, h2]
    ring

end Omega.SPG
