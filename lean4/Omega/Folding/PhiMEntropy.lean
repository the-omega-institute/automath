import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the entropy corollary of the folded image shift.
    cor:Phi-m-entropy -/
theorem paper_resolution_folding_phi_m_entropy
    (hTop : ℕ → ℝ)
    (hUpper : ∀ {m : ℕ}, 2 ≤ m → hTop m ≤ Real.log 2)
    (hLower : ∀ {m : ℕ}, 2 ≤ m → Real.log 2 ≤ hTop m) :
    ∀ {m : ℕ}, 2 ≤ m → hTop m = Real.log 2 := by
  intro m hm
  linarith [hUpper hm, hLower hm]

end Omega.Folding
