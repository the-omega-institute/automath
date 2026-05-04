import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-synchronization-entropy-kl-anomaly-identity`. -/
theorem paper_conclusion_window6_synchronization_entropy_kl_anomaly_identity
    (syncCost kappa kl : ℝ) (hsync : syncCost = Real.log 64 - kappa)
    (hkl : kl = kappa - (Real.log 64 - Real.log 21)) : syncCost = Real.log 21 - kl := by
  rw [hsync, hkl]
  ring

end Omega.Conclusion
