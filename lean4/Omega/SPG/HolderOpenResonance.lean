import Omega.SPG.MainResonance

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Holder block-recoding lift of the open
    resonance package.
    thm:holder-open-resonance -/
theorem paper_scan_projection_address_holder_open_resonance
    (exactBlockTransfer backwardGMeasure openBackwardOperator
      residueTwistedKilledResolvent polesInKilledCyclotomicLift
      positiveRealPoleLeastModulus blockRecodingResolvent
      polesInOpenCyclotomicLift leadingResonanceSimple
      leadingResonanceIsolated residueNondegeneracy asymptoticExpansion : Prop)
    (zH reciprocalEscapeFactor : ℝ)
    (hTransfer : exactBlockTransfer)
    (hBackward : backwardGMeasure)
    (hOpenBackward : backwardGMeasure → openBackwardOperator)
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
    exactBlockTransfer ∧
      backwardGMeasure ∧
      openBackwardOperator ∧
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
  have hMain :=
    paper_scan_projection_address_main_resonance
      residueTwistedKilledResolvent
      polesInKilledCyclotomicLift
      positiveRealPoleLeastModulus
      blockRecodingResolvent
      polesInOpenCyclotomicLift
      leadingResonanceSimple
      leadingResonanceIsolated
      residueNondegeneracy
      asymptoticExpansion
      zH
      reciprocalEscapeFactor
      hResolvent
      hPoleLift
      hLeastPole
      hzH
      hBlock
      hOpenPoleLift
      hAsymptotic
  exact
    ⟨hTransfer, hBackward, hOpenBackward hBackward, hMain.1, hMain.2.1,
      hMain.2.2.1, hMain.2.2.2.1, hMain.2.2.2.2.1, hMain.2.2.2.2.2.1,
      hMain.2.2.2.2.2.2⟩

end Omega.SPG
