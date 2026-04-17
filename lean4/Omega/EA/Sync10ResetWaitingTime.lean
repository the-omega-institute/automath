import Mathlib.Tactic
import Omega.EA.Sync10Regeneration
import Omega.Zeta.SyncKernelResetWordWaitingTimeGeneralIid

namespace Omega.EA

/-- The `00000` reset-block hit probability under an IID input law with `P(D₀ = 0) = q`. -/
def sync10ResetBlockHitProbability (q : ℚ) : ℚ :=
  q ^ 5

/-- The explicit `00000` reset block gives the advertised IID geometric tail and expectation
bound after specializing the general reset-word waiting-time estimate to `L = 5` and `π₀ = q^5`.
    prop:sync10-reset-waitingtime-iid-bound -/
theorem paper_sync10_reset_waitingtime_iid_bound
    (q : ℚ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    sync10ResetBlock.length = 5 ∧
      (∀ n : ℕ,
        Omega.Zeta.syncKernelResetWordBlockTail (sync10ResetBlockHitProbability q) n =
          (1 - sync10ResetBlockHitProbability q) ^ n) ∧
      (∀ N : ℕ,
        Omega.Zeta.syncKernelResetWordPartialWaitingTime 5 (sync10ResetBlockHitProbability q) N ≤
          5 / sync10ResetBlockHitProbability q) := by
  have hpi0_pos : 0 < sync10ResetBlockHitProbability q := by
    simpa [sync10ResetBlockHitProbability] using pow_pos hq0 5
  have hpi0_le_one : sync10ResetBlockHitProbability q ≤ 1 := by
    simpa [sync10ResetBlockHitProbability] using pow_le_one₀ hq0.le hq1
  have hbound :
      ∀ N : ℕ,
        Omega.Zeta.syncKernelResetWordPartialWaitingTime 5 (sync10ResetBlockHitProbability q) N ≤
          Omega.Zeta.syncKernelResetWordWaitingTimeBound 5 (sync10ResetBlockHitProbability q) :=
    Omega.Zeta.paper_sync_kernel_reset_word_waiting_time_general_iid
      (L := 5) (pi0 := sync10ResetBlockHitProbability q) (hL := by positivity) (hpi0 := hpi0_pos)
      (hpi1 := hpi0_le_one)
  refine ⟨by simp [sync10ResetBlock], ?_, ?_⟩
  · intro n
    rfl
  · intro N
    simpa [Omega.Zeta.syncKernelResetWordWaitingTimeBound] using hbound N

end Omega.EA
