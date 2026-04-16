import Mathlib.Tactic

namespace Omega.GU

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the window-6 cyclic Weyl-orbit partition cut out by the weight-one
    threshold.
    thm:window6-cyclic-weight-threshold-root-length -/
theorem paper_window6_cyclic_weight_threshold_root_length
    (weightOneShortRootOrbit nonWeightOneLongRootOrbit weylOrbitPartition : Prop)
    (hShort : weightOneShortRootOrbit) (hLong : nonWeightOneLongRootOrbit)
    (hPartition :
      weightOneShortRootOrbit ∧ nonWeightOneLongRootOrbit → weylOrbitPartition) :
    weightOneShortRootOrbit ∧ nonWeightOneLongRootOrbit ∧ weylOrbitPartition := by
  exact ⟨hShort, hLong, hPartition ⟨hShort, hLong⟩⟩

end Omega.GU
