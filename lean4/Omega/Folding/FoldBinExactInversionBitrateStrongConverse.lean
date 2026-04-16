import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing wrapper for the bin-fold exact inversion bitrate threshold and strong converse:
the exact threshold closed form and critical rate limit are taken as inputs, and the strong
converse is recorded as the implication from a subcritical budget bound to exponential success
decay.
    thm:fold-bin-exact-inversion-bitrate-strong-converse -/
theorem paper_fold_bin_exact_inversion_bitrate_strong_converse
    (exactThresholdClosedForm : Prop) (criticalRateLimit : Prop) (subcriticalBudgetBound : Prop)
    (exponentialSuccessDecay : Prop) (hThreshold : exactThresholdClosedForm)
    (hRate : criticalRateLimit) (hStrong : subcriticalBudgetBound -> exponentialSuccessDecay) :
    exactThresholdClosedForm ∧
      criticalRateLimit ∧ (subcriticalBudgetBound -> exponentialSuccessDecay) := by
  exact ⟨hThreshold, hRate, hStrong⟩

end Omega.Folding
