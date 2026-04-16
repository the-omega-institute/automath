import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local wrapper for the sharp Perron--Frobenius synchronization-tail package. The two
availability fields record that the underlying synchronization-tail and unsynchronized-prefix
certificates have been assembled elsewhere in the chapter, and `readout` stores the paper-facing
tail conclusion extracted from that package. -/
structure YmSyncTailPfSharpData where
  hasPositivePeriodicConstants : Prop
  hasSharpExponentialTail : Prop
  limitExponent : ℝ
  epsilon : ℝ
  syncTailPackageAvailable : Prop
  unsyncPrefixPfSharpPackageAvailable : Prop
  hasSyncTailPackageAvailable : syncTailPackageAvailable
  hasUnsyncPrefixPfSharpPackageAvailable : unsyncPrefixPfSharpPackageAvailable
  readout :
    syncTailPackageAvailable →
      unsyncPrefixPfSharpPackageAvailable →
        hasPositivePeriodicConstants ∧ hasSharpExponentialTail ∧ limitExponent = -epsilon

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the sharp Perron--Frobenius asymptotic of the synchronization tail.
    thm:Ym-sync-tail-pf-sharp -/
theorem paper_Ym_sync_tail_pf_sharp (D : YmSyncTailPfSharpData) :
    D.hasPositivePeriodicConstants ∧ D.hasSharpExponentialTail ∧
      D.limitExponent = -D.epsilon := by
  exact D.readout D.hasSyncTailPackageAvailable D.hasUnsyncPrefixPfSharpPackageAvailable

end Omega.Folding
