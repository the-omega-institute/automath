import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exponential synchronization-tail package.
    thm:Ym-sync-tail -/
theorem paper_Ym_sync_tail
    (cylinderUpperBound unsyncPrefixExponentialCount syncTailExponentialBound
      finiteExpectedSyncTime syncBudget : Prop)
    (hCyl : cylinderUpperBound)
    (hUnsync : unsyncPrefixExponentialCount)
    (hTail : cylinderUpperBound → unsyncPrefixExponentialCount → syncTailExponentialBound)
    (hExp : syncTailExponentialBound → finiteExpectedSyncTime)
    (hBudget : syncTailExponentialBound → syncBudget) :
    syncTailExponentialBound ∧ finiteExpectedSyncTime ∧ syncBudget := by
  have hSync : syncTailExponentialBound := hTail hCyl hUnsync
  exact ⟨hSync, hExp hSync, hBudget hSync⟩

end Omega.Folding
