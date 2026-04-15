namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for bit recovery from local congruence data in
    `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt`.
    thm:bit-recovery-residues -/
theorem paper_resolution_folding_bit_recovery_from_local_congruence_data
    (windowBitRecovery oneSidedDecodingRule memoryThresholdOptimality : Prop)
    (hRecovery : windowBitRecovery)
    (hOneSided : windowBitRecovery → oneSidedDecodingRule)
    (hOptimal : windowBitRecovery → memoryThresholdOptimality) :
    windowBitRecovery ∧ oneSidedDecodingRule ∧ memoryThresholdOptimality := by
  exact ⟨hRecovery, hOneSided hRecovery, hOptimal hRecovery⟩

end Omega.Folding
