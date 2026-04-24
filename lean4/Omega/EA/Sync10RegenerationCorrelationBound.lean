import Mathlib.Tactic
import Omega.EA.Sync10Regeneration
import Omega.EA.Sync10ResetWaitingTime

namespace Omega.EA

/-- Paper label: `cor:sync10-regeneration-correlation-bound`.
The deterministic reset block `00000` couples all start states after it appears, and the same
block inherits the existing IID waiting-time tail and expectation bounds. -/
theorem paper_sync10_regeneration_correlation_bound (q : ℚ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∀ s t : Sync10State, ∀ suffix : List (Fin 3),
      sync10Run s (sync10ResetBlock ++ suffix) = sync10Run t (sync10ResetBlock ++ suffix)) ∧
      (∀ n : ℕ, Omega.Zeta.syncKernelResetWordBlockTail (sync10ResetBlockHitProbability q) n =
        (1 - sync10ResetBlockHitProbability q) ^ n) ∧
      (∀ N : ℕ, Omega.Zeta.syncKernelResetWordPartialWaitingTime 5
        (sync10ResetBlockHitProbability q) N ≤ 5 / sync10ResetBlockHitProbability q) := by
  rcases paper_sync10_reset_waitingtime_iid_bound q hq0 hq1 with ⟨_, hTail, hWait⟩
  refine ⟨?_, hTail, hWait⟩
  intro s t suffix
  calc
    sync10Run s (sync10ResetBlock ++ suffix) = sync10Run Sync10State.q000 suffix := by
      simpa using (paper_sync10_regeneration s [] suffix)
    _ = sync10Run t (sync10ResetBlock ++ suffix) := by
      symm
      simpa using (paper_sync10_regeneration t [] suffix)

end Omega.EA
