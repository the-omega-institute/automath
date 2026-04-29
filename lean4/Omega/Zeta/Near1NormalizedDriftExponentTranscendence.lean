import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:near1-normalized-drift-exponent-transcendence`. -/
theorem paper_near1_normalized_drift_exponent_transcendence
    (Trans : ℝ → Prop) (log2_logPhi c1_over_logPhi : ℝ)
    (hTrans : Trans log2_logPhi)
    (hShift : ∀ x : ℝ, Trans x → Trans (x - 1))
    (h : c1_over_logPhi = log2_logPhi - 1) :
    Trans c1_over_logPhi := by
  rw [h]
  exact hShift log2_logPhi hTrans

end Omega.Zeta
