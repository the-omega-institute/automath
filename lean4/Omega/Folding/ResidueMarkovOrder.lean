import Omega.Folding.BitRecoveryFromLocalCongruenceData
import Omega.Folding.RandomResidueDistribution

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact Markov order of the local residue process in
    `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt`.
    thm:residue-markov-order -/
theorem paper_resolution_folding_residue_markov_order
    (windowBitRecovery oneSidedDecodingRule memoryThresholdOptimality
      realizableSupport uniquePreimage bernoulliWeight residueStepMarkov
      uniformHalfCase transitionKernelFormula noShorterMemory : Prop)
    (hRecovery : windowBitRecovery)
    (hOneSided : windowBitRecovery → oneSidedDecodingRule)
    (hOptimal : windowBitRecovery → memoryThresholdOptimality)
    (hSupport : realizableSupport)
    (hLift : realizableSupport → uniquePreimage)
    (hWeight : uniquePreimage → bernoulliWeight)
    (hUniform : bernoulliWeight → uniformHalfCase)
    (hMarkov : oneSidedDecodingRule → bernoulliWeight → residueStepMarkov)
    (hKernel : residueStepMarkov → transitionKernelFormula)
    (hMinimal : memoryThresholdOptimality → residueStepMarkov → noShorterMemory) :
    realizableSupport ∧ residueStepMarkov ∧ transitionKernelFormula ∧ noShorterMemory := by
  obtain ⟨_, hOneSidedRule, hOptimality⟩ :=
    paper_resolution_folding_bit_recovery_from_local_congruence_data
      windowBitRecovery oneSidedDecodingRule memoryThresholdOptimality hRecovery hOneSided hOptimal
  obtain ⟨hSupportRealizable, hUniquePreimage, hBernoulliWeight, _⟩ :=
    paper_resolution_folding_random_residue_distribution
      realizableSupport uniquePreimage bernoulliWeight uniformHalfCase
      hSupport hLift hWeight hUniform
  have hStepMarkov : residueStepMarkov := hMarkov hOneSidedRule hBernoulliWeight
  have hTransitionKernel : transitionKernelFormula := hKernel hStepMarkov
  exact
    ⟨hSupportRealizable, hStepMarkov, hTransitionKernel, hMinimal hOptimality hStepMarkov⟩

end Omega.Folding
