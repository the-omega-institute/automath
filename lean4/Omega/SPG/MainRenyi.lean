import Omega.SPG.SurvivorRenyiPressure

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Introduction-level wrapper for the survivor R\'enyi pressure spectrum theorem.
    thm:main-renyi -/
theorem paper_scan_projection_address_main_renyi
    (s PY PYHphi PYHs gammaH ambientLimit conditionedLimit h2H chiH PYH2phi : ℝ)
    (hAmbient : ambientLimit = s * PY - PYHs)
    (hGap : gammaH = PY - PYHphi)
    (hConditioned : conditionedLimit = ambientLimit - s * gammaH)
    (h2 : h2H = 2 * PYHphi - PYH2phi)
    (hChi : chiH = 2 * PY - PYH2phi) :
    conditionedLimit = s * PYHphi - PYHs ∧
      h2H = 2 * PYHphi - PYH2phi ∧
      chiH = 2 * gammaH + h2H := by
  have hCore :=
    paper_scan_projection_address_survivor_renyi_pressure
      s PY PYHphi PYHs gammaH ambientLimit conditionedLimit h2H chiH PYH2phi
      hAmbient hGap hConditioned h2 hChi
  exact ⟨hCore.1, h2, hCore.2⟩

end Omega.SPG
