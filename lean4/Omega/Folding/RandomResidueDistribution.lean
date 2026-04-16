namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact distribution theorem of random
    local residues in `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt`.
    thm:random-residue-distribution -/
theorem paper_resolution_folding_random_residue_distribution
    (realizableSupport uniquePreimage bernoulliWeight uniformHalfCase : Prop)
    (hSupport : realizableSupport)
    (hLift : realizableSupport → uniquePreimage)
    (hWeight : uniquePreimage → bernoulliWeight)
    (hUniform : bernoulliWeight → uniformHalfCase) :
    realizableSupport ∧ uniquePreimage ∧ bernoulliWeight ∧ uniformHalfCase := by
  have hPreimage : uniquePreimage := hLift hSupport
  have hBernoulli : bernoulliWeight := hWeight hPreimage
  exact ⟨hSupport, hPreimage, hBernoulli, hUniform hBernoulli⟩

end Omega.Folding
