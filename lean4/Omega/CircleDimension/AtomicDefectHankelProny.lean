import Mathlib.Tactic
import Omega.CircleDimension.AtomicDefectProny2KappaRecovery

namespace Omega.CircleDimension

/-- Paper-facing wrapper for the single-frequency atomic-defect Hankel--Prony identifiability
package.
    prop:cdim-atomic-defect-hankel-prony -/
theorem paper_cdim_atomic_defect_hankel_prony
    (singleFrequencyLowRankModel depthRecoveryByHankel phaseRecovery overallIdentifiability :
      Prop)
    (hModel : singleFrequencyLowRankModel)
    (hDepth : singleFrequencyLowRankModel -> depthRecoveryByHankel)
    (hPhase : depthRecoveryByHankel -> phaseRecovery)
    (hId : depthRecoveryByHankel -> phaseRecovery -> overallIdentifiability) :
    overallIdentifiability := by
  have hDepthRecovery : depthRecoveryByHankel := hDepth hModel
  have hPhaseRecovery : phaseRecovery := hPhase hDepthRecovery
  exact hId hDepthRecovery hPhaseRecovery

end Omega.CircleDimension
