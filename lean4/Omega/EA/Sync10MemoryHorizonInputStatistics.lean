import Omega.EA.Sync10ResetWaitingTime

namespace Omega.EA

/-- Specializing the general IID reset-word estimate to the explicit reset block `00000` yields
the advertised geometric tail and partial waiting-time bound.
    cor:sync10-memory-horizon-input-statistics -/
theorem paper_sync10_memory_horizon_input_statistics (q : ℚ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    sync10ResetBlockHitProbability q = q ^ 5 ∧
      (∀ n : ℕ, Omega.Zeta.syncKernelResetWordBlockTail (sync10ResetBlockHitProbability q) n =
        (1 - q ^ 5) ^ n) ∧
      (∀ N : ℕ, Omega.Zeta.syncKernelResetWordPartialWaitingTime 5
        (sync10ResetBlockHitProbability q) N ≤ 5 / q ^ 5) := by
  rcases paper_sync10_reset_waitingtime_iid_bound q hq0 hq1 with ⟨_, hTail, hWait⟩
  refine ⟨rfl, ?_, ?_⟩
  · intro n
    simpa [sync10ResetBlockHitProbability] using hTail n
  · intro N
    simpa [sync10ResetBlockHitProbability] using hWait N

end Omega.EA
