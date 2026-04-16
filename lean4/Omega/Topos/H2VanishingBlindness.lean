namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the `H_2`-vanishing blindness corollary.
    cor:h2-vanishing-blindness -/
theorem paper_gluing_failure_h2_vanishing_blindness
    (H2Zero evZero kernelZero visibleAll blind : Prop)
    (hcollapse : H2Zero → evZero ∧ kernelZero ∧ visibleAll)
    (hblind : evZero → blind) :
    H2Zero → evZero ∧ kernelZero ∧ visibleAll ∧ blind := by
  intro hH2
  obtain ⟨hev, hker, hvis⟩ := hcollapse hH2
  exact ⟨hev, hker, hvis, hblind hev⟩

end Omega.Topos
