import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-boundary-parity-never-anomaly-complete`. -/
theorem paper_conclusion_window6_boundary_parity_never_anomaly_complete
    (completeAnomalySignatureDim boundaryParityDim extensionCount : ℕ)
    (boundaryParityComplete : Prop)
    (hCompleteDim : completeAnomalySignatureDim = 21)
    (hBoundaryDim : boundaryParityDim = 3)
    (hExtensions : extensionCount = 2 ^ 18)
    (hCompleteRequires : boundaryParityComplete → completeAnomalySignatureDim ≤ boundaryParityDim) :
    ¬ boundaryParityComplete ∧ extensionCount = 2 ^ 18 := by
  constructor
  · intro hcomplete
    have hle := hCompleteRequires hcomplete
    omega
  · exact hExtensions

end Omega.Conclusion
