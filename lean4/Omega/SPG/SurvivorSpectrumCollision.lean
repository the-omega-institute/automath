import Omega.SPG.SurvivorRenyiPressure

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the collision consequences of the survivor spectrum.
    cor:survivor-spectrum-collision -/
theorem paper_scan_projection_address_survivor_spectrum_collision
    (s PY PYHphi PYHs gammaH ambientLimit conditionedLimit h2H chiH PYH2phi : ℝ)
    (collisionSecondMoment collisionThirdMoment poissonCollision birthdayThreshold : Prop)
    (hAmbient : ambientLimit = s * PY - PYHs)
    (hGap : gammaH = PY - PYHphi)
    (hConditioned : conditionedLimit = ambientLimit - s * gammaH)
    (h2 : h2H = 2 * PYHphi - PYH2phi)
    (hChi : chiH = 2 * PY - PYH2phi)
    (hSecond : collisionSecondMoment)
    (hThird : collisionThirdMoment)
    (hPoisson : collisionSecondMoment → collisionThirdMoment → poissonCollision)
    (hThreshold : collisionSecondMoment → birthdayThreshold) :
    conditionedLimit = s * PYHphi - PYHs ∧
      chiH = 2 * gammaH + h2H ∧
      poissonCollision ∧
      birthdayThreshold := by
  have hPressure :
      conditionedLimit = s * PYHphi - PYHs ∧
        chiH = 2 * gammaH + h2H :=
    paper_scan_projection_address_survivor_renyi_pressure
      s PY PYHphi PYHs gammaH ambientLimit conditionedLimit h2H chiH PYH2phi
      hAmbient hGap hConditioned h2 hChi
  rcases hPressure with ⟨hConditioned', hCollision'⟩
  exact ⟨hConditioned', hCollision', hPoisson hSecond hThird, hThreshold hSecond⟩

end Omega.SPG
