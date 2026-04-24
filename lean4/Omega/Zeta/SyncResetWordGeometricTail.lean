import Mathlib.Tactic
import Omega.Zeta.SyncKernelResetWordWaitingTimeGeneralIid

namespace Omega.Zeta

/-- The geometric tail formula is definitional, and the waiting-time estimate is exactly the IID
reset-word bound already proved for synchronizing words. -/
theorem paper_sync_reset_word_geometric_tail
    (L pi0 : ℚ) (hL : 0 ≤ L) (hpi0 : 0 < pi0) (hpi1 : pi0 ≤ 1) :
    (∀ n : ℕ, Omega.Zeta.syncKernelResetWordBlockTail pi0 n = (1 - pi0) ^ n) ∧
      (∀ N : ℕ,
        Omega.Zeta.syncKernelResetWordPartialWaitingTime L pi0 N ≤
          Omega.Zeta.syncKernelResetWordWaitingTimeBound L pi0) := by
  refine ⟨?_, Omega.Zeta.paper_sync_kernel_reset_word_waiting_time_general_iid
    (L := L) (pi0 := pi0) hL hpi0 hpi1⟩
  intro n
  rfl

end Omega.Zeta
