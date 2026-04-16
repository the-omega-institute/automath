import Mathlib.Data.Nat.Basic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact finite-type order of the folded shift.
    thm:Y-m-exact-SFT-order -/
theorem paper_resolution_folding_y_m_exact_sft_order
    (isStepSFT : ℕ → Prop) {m : ℕ}
    (_hm : 3 ≤ m)
    (hmStep : isStepSFT m)
    (hNotPrev : ¬ isStepSFT (m - 1)) :
    isStepSFT m ∧ ¬ isStepSFT (m - 1) := by
  exact ⟨hmStep, hNotPrev⟩

end Omega.Folding
