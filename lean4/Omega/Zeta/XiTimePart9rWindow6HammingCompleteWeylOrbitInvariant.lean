import Omega.Zeta.XiTimePart62deaWindow6WeightDeterminesWeylOrbits

namespace Omega.Zeta

/-- Paper label:
`thm:xi-time-part9r-window6-hamming-complete-weyl-orbit-invariant`. -/
theorem paper_xi_time_part9r_window6_hamming_complete_weyl_orbit_invariant
    (weightOneShortRootOrbit nonWeightOneLongRootOrbit weylOrbitPartition : Prop)
    (hShort : weightOneShortRootOrbit) (hLong : nonWeightOneLongRootOrbit)
    (hPartition : weightOneShortRootOrbit ∧ nonWeightOneLongRootOrbit → weylOrbitPartition) :
    weightOneShortRootOrbit ∧ nonWeightOneLongRootOrbit ∧ weylOrbitPartition := by
  exact ⟨hShort, hLong, hPartition ⟨hShort, hLong⟩⟩

end Omega.Zeta
