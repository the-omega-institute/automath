import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-inversion-anomaly-strict-separation`. -/
theorem paper_conclusion_window6_inversion_anomaly_strict_separation
    (B anomalyDim : Nat) (hB : B = 2) (hA : anomalyDim = 21) :
    B = 2 ∧ anomalyDim = 21 ∧ B < anomalyDim := by
  subst B
  subst anomalyDim
  norm_num

end Omega.Conclusion
