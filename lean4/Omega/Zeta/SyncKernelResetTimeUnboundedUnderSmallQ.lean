import Mathlib.Tactic
import Omega.Zeta.SyncKernelMixingRate

namespace Omega.Zeta

/-- For every prescribed threshold `B`, one can choose a sufficiently small positive rational
`q` so that the toy reset-time bound `5 / q^5` exceeds `B`.
    cor:sync-kernel-reset-time-unbounded-under-small-q -/
theorem paper_sync_kernel_reset_time_unbounded_under_small_q :
    ∀ B : ℚ, ∃ q : ℚ, 0 < q ∧ B ≤ 5 / (q ^ 5) := by
  intro B
  let N : ℕ := Nat.ceil B + 1
  let q : ℚ := 1 / N
  have hNpos_nat : 0 < N := by
    dsimp [N]
    omega
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  refine ⟨q, hqpos, ?_⟩
  have hB_le_N : B ≤ N := by
    refine le_trans (Nat.le_ceil B) ?_
    dsimp [N]
    exact_mod_cast Nat.le_succ (Nat.ceil B)
  have hN_le_bound_nat : N ≤ 5 * N ^ 5 := by
    have hpowpos : 0 < N ^ 4 := pow_pos hNpos_nat 4
    have hpow_le : N ^ 4 ≤ 5 * N ^ 4 := by
      simpa [one_mul] using Nat.mul_le_mul_right (N ^ 4) (show 1 ≤ 5 by decide)
    have hfac : 1 ≤ 5 * N ^ 4 := le_trans (Nat.succ_le_of_lt hpowpos) hpow_le
    calc
      N = 1 * N := by simp
      _ ≤ (5 * N ^ 4) * N := Nat.mul_le_mul_right N hfac
      _ = 5 * (N ^ 4 * N) := by ring
      _ = 5 * N ^ 5 := by simp [pow_succ, mul_assoc]
  have hN_le_bound : (N : ℚ) ≤ 5 * N ^ 5 := by
    exact_mod_cast hN_le_bound_nat
  have hbound_eq : (5 : ℚ) / (q ^ 5) = 5 * N ^ 5 := by
    dsimp [q]
    field_simp
  calc
    B ≤ N := hB_le_N
    _ ≤ 5 * N ^ 5 := hN_le_bound
    _ = 5 / (q ^ 5) := hbound_eq.symm

end Omega.Zeta
