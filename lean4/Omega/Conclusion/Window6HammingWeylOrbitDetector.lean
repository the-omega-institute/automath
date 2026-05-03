import Omega.GU.Window6CyclicWeightThresholdRootLength

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-hamming-weyl-orbit-detector`.
This conclusion corollary is the GU window-6 cyclic weight threshold theorem repackaged under
the conclusion namespace. -/
theorem paper_conclusion_window6_hamming_weyl_orbit_detector
    (weightOneShortRootOrbit nonWeightOneLongRootOrbit weylOrbitPartition : Prop)
    (hShort : weightOneShortRootOrbit) (hLong : nonWeightOneLongRootOrbit)
    (hPartition : weightOneShortRootOrbit ∧ nonWeightOneLongRootOrbit → weylOrbitPartition) :
    weightOneShortRootOrbit ∧ nonWeightOneLongRootOrbit ∧ weylOrbitPartition := by
  exact Omega.GU.paper_window6_cyclic_weight_threshold_root_length
    weightOneShortRootOrbit nonWeightOneLongRootOrbit weylOrbitPartition hShort hLong hPartition

end Omega.Conclusion
