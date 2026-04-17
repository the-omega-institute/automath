import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import Omega.Zeta.SyncKernelMixingRate

namespace Omega.Zeta

/-- Block tail bound for a synchronizing word hit probability `pi0`. -/
def syncKernelResetWordBlockTail (pi0 : ℚ) (n : ℕ) : ℚ :=
  (1 - pi0) ^ n

/-- Truncated block-based waiting-time estimate for a synchronizing word of length `L`. -/
def syncKernelResetWordPartialWaitingTime (L pi0 : ℚ) (N : ℕ) : ℚ :=
  L * ∑ k ∈ Finset.range N, syncKernelResetWordBlockTail pi0 k

/-- Geometric upper bound on the expected waiting time. -/
def syncKernelResetWordWaitingTimeBound (L pi0 : ℚ) : ℚ :=
  L / pi0

/-- For an IID source with synchronizing-word hit probability `pi0`, the block tail is geometric,
so every truncated block waiting-time estimate is bounded by `L / pi0`.
    cor:sync-kernel-reset-word-waiting-time-general-iid -/
theorem paper_sync_kernel_reset_word_waiting_time_general_iid
    (L pi0 : ℚ) (hL : 0 ≤ L) (hpi0 : 0 < pi0) (hpi1 : pi0 ≤ 1) :
    ∀ N : ℕ,
      syncKernelResetWordPartialWaitingTime L pi0 N ≤
        syncKernelResetWordWaitingTimeBound L pi0 := by
  intro N
  set q : ℚ := 1 - pi0
  set S : ℚ := ∑ k ∈ Finset.range N, q ^ k
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    linarith
  have hq_le_one : q ≤ 1 := by
    dsimp [q]
    linarith
  have hpi0_ne : pi0 ≠ 0 := by
    linarith
  have hq_def : 1 - q = pi0 := by
    dsimp [q]
    ring
  have hgeom' : S * (1 - q) = 1 - q ^ N := by
    simpa [S] using (geom_sum_mul_of_le_one hq_le_one N)
  have hgeom : S * pi0 = 1 - q ^ N := by
    calc
      S * pi0 = S * (1 - q) := by rw [hq_def.symm]
      _ = 1 - q ^ N := hgeom'
  have hS_eq : S = (1 - q ^ N) / pi0 := by
    exact (eq_div_iff hpi0_ne).2 hgeom
  have hq_pow_nonneg : 0 ≤ q ^ N := pow_nonneg hq_nonneg N
  have hnum_le : 1 - q ^ N ≤ 1 := by
    linarith
  have hS_le : S ≤ 1 / pi0 := by
    rw [hS_eq]
    exact div_le_div_of_nonneg_right hnum_le hpi0.le
  have hmul := mul_le_mul_of_nonneg_left hS_le hL
  simpa [syncKernelResetWordPartialWaitingTime, syncKernelResetWordWaitingTimeBound,
    syncKernelResetWordBlockTail, S, q, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hmul

end Omega.Zeta
