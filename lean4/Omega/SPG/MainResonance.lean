import Mathlib.Tactic

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the cyclotomic resonance lift theorem in the
    scan-projection ETDS introduction.
    thm:main-resonance -/
theorem paper_scan_projection_address_main_resonance
    (residueTwistedKilledResolvent polesInKilledCyclotomicLift
      positiveRealPoleLeastModulus blockRecodingResolvent
      polesInOpenCyclotomicLift leadingResonanceSimple
      leadingResonanceIsolated residueNondegeneracy asymptoticExpansion : Prop)
    (zH reciprocalEscapeFactor : ℝ)
    (hResolvent : residueTwistedKilledResolvent)
    (hPoleLift : residueTwistedKilledResolvent → polesInKilledCyclotomicLift)
    (hLeastPole : residueTwistedKilledResolvent → positiveRealPoleLeastModulus)
    (hzH : zH = reciprocalEscapeFactor)
    (hBlock : blockRecodingResolvent)
    (hOpenPoleLift : blockRecodingResolvent → polesInOpenCyclotomicLift)
    (hAsymptotic :
      blockRecodingResolvent →
        leadingResonanceSimple →
          leadingResonanceIsolated →
            residueNondegeneracy →
              asymptoticExpansion) :
    residueTwistedKilledResolvent ∧
      polesInKilledCyclotomicLift ∧
      positiveRealPoleLeastModulus ∧
      zH = reciprocalEscapeFactor ∧
      blockRecodingResolvent ∧
      polesInOpenCyclotomicLift ∧
      (leadingResonanceSimple →
        leadingResonanceIsolated →
          residueNondegeneracy →
            asymptoticExpansion) := by
  refine ⟨hResolvent, hPoleLift hResolvent, hLeastPole hResolvent, hzH,
    hBlock, hOpenPoleLift hBlock, ?_⟩
  intro hSimple hIsolated hNondeg
  exact hAsymptotic hBlock hSimple hIsolated hNondeg

end Omega.SPG
