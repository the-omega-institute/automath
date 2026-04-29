import Mathlib.Tactic

namespace Omega.Zeta

/-- Three-way equivalence loop between major-arc resonance, additive-energy distortion, and the
    cyclotomic obstruction witness.
    thm:gm-majorarc-energy-obstruction-loop -/
theorem paper_gm_majorarc_energy_obstruction_loop
    (majorArcResonance energyDistortion resonantObstruction : Prop)
    (h12 : majorArcResonance → energyDistortion)
    (h21 : energyDistortion → majorArcResonance)
    (h13 : majorArcResonance → resonantObstruction)
    (h31 : resonantObstruction → majorArcResonance) :
    (majorArcResonance ↔ energyDistortion) ∧
      (majorArcResonance ↔ resonantObstruction) ∧
      (energyDistortion ↔ resonantObstruction) := by
  refine ⟨⟨h12, h21⟩, ⟨h13, h31⟩, ⟨?_, ?_⟩⟩
  · intro hEnergy
    exact h13 (h21 hEnergy)
  · intro hObstruction
    exact h12 (h31 hObstruction)

end Omega.Zeta
