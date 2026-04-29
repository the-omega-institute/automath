import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-godel-leyang-two-phase-coexistence-window`. -/
theorem paper_xi_godel_leyang_two_phase_coexistence_window
    (twoPhaseDominance normalizedPartitionConvergence zeroCondensation nearestZeroAsymptotic : Prop)
    (hDom : twoPhaseDominance)
    (hConv : twoPhaseDominance → normalizedPartitionConvergence)
    (hZeros : normalizedPartitionConvergence → zeroCondensation)
    (hNearest : zeroCondensation → nearestZeroAsymptotic) :
    twoPhaseDominance ∧ normalizedPartitionConvergence ∧ zeroCondensation ∧
      nearestZeroAsymptotic := by
  exact ⟨hDom, hConv hDom, hZeros (hConv hDom), hNearest (hZeros (hConv hDom))⟩

end Omega.Zeta
