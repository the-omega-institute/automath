import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exact synchronizing-length threshold in
    the rigidity reconstruction section.
    cor:uniform-synchronizing-length -/
theorem paper_resolution_folding_uniform_synchronizing_length
    (allSynchronizing : ℕ → Prop) {m : ℕ}
    (hmono : Monotone allSynchronizing)
    (hm : allSynchronizing m)
    (hprev : ¬ allSynchronizing (m - 1)) :
    allSynchronizing m ∧ ∀ n < m, ¬ allSynchronizing n := by
  refine ⟨hm, ?_⟩
  intro n hn hnSync
  exact hprev (hmono (Nat.le_pred_of_lt hn) hnSync)

end Omega.Folding
