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

set_option maxHeartbeats 400000 in
/-- Paper-facing dichotomy between finite-delay synchronization and nontrivial spectral tails.
    cor:Ym-finite-delay-spectral-tail -/
theorem paper_Ym_finite_delay_spectral_tail (rhoAmb : ℝ) (acyclic finiteDelay spectralTail : Prop)
    (hAcyclic : acyclic ↔ rhoAmb = 0) (hFinite : acyclic → finiteDelay)
    (hTail : ¬ acyclic → spectralTail) : (rhoAmb = 0 → finiteDelay) ∧ (rhoAmb ≠ 0 → spectralTail) := by
  refine ⟨?_, ?_⟩
  · intro hZero
    exact hFinite ((hAcyclic).2 hZero)
  · intro hNeZero
    exact hTail (mt (hAcyclic).1 hNeZero)

end Omega.Folding
