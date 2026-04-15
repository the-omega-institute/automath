namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the conjugacy-invariants corollary in
    `submitted_2026_resolution_folding_core_symbolic_dynamics_jnt`.
    cor:Y-m-conjugacy-collapse -/
theorem paper_resolution_folding_y_m_conjugacy_collapse
    (topologicalConjugacy entropyReadout fixedPointCounts zetaClosedForm : Prop)
    (hConj : topologicalConjugacy)
    (hEntropy : topologicalConjugacy → entropyReadout)
    (hFixed : topologicalConjugacy → fixedPointCounts)
    (hZeta : fixedPointCounts → zetaClosedForm) :
    entropyReadout ∧ fixedPointCounts ∧ zetaClosedForm := by
  have hEntropyReadout : entropyReadout := hEntropy hConj
  have hFixedCounts : fixedPointCounts := hFixed hConj
  exact ⟨hEntropyReadout, hFixedCounts, hZeta hFixedCounts⟩

end Omega.Folding
