import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmEllipticWeightNCorrespondenceBidegreeDelta

namespace Omega.Zeta

private lemma xi_terminal_zm_elliptic_weight_2k_delta_ledger_pow_sq (k : ℕ) :
    (2 ^ k : ℕ) ^ 2 = 4 ^ k := by
  calc
    (2 ^ k : ℕ) ^ 2 = 2 ^ (k * 2) := by rw [pow_mul]
    _ = 2 ^ (2 * k) := by rw [Nat.mul_comm]
    _ = (2 ^ 2) ^ k := by rw [← pow_mul]
    _ = 4 ^ k := by norm_num

/-- Paper label: `cor:xi-terminal-zm-elliptic-weight-2k-delta-ledger`. Specializing the
weight-`n` correspondence formula to `n = 2^k` gives the closed bidegree and the equivalent
closed forms `12 * 4^k - 4 = 3 * 4^(k+1) - 4` for the total `δ`-invariant. -/
theorem paper_xi_terminal_zm_elliptic_weight_2k_delta_ledger (k : ℕ) :
    xiTerminalBidegree (2 ^ k) = (4 ^ (k + 1), 4) ∧
      xiTerminalTotalDelta (2 ^ k) = 12 * 4 ^ k - 4 ∧
      xiTerminalTotalDelta (2 ^ k) = 3 * 4 ^ (k + 1) - 4 := by
  rcases paper_xi_terminal_zm_elliptic_weight_n_correspondence_bidegree_delta (2 ^ k) with
    ⟨_, _, _, hdelta⟩
  have hpow := xi_terminal_zm_elliptic_weight_2k_delta_ledger_pow_sq k
  have hbidegree :
      xiTerminalBidegree (2 ^ k) = (4 ^ (k + 1), 4) := by
    calc
      xiTerminalBidegree (2 ^ k) = (4 * (2 ^ k) ^ 2, 4) := by rfl
      _ = (4 * 4 ^ k, 4) := by rw [hpow]
      _ = (4 ^ (k + 1), 4) := by
        simp [pow_succ, Nat.mul_comm]
  have hdelta₁ : xiTerminalTotalDelta (2 ^ k) = 12 * 4 ^ k - 4 := by
    calc
      xiTerminalTotalDelta (2 ^ k) = 12 * (2 ^ k) ^ 2 - 4 := hdelta
      _ = 12 * 4 ^ k - 4 := by rw [hpow]
  have hdelta₂ : xiTerminalTotalDelta (2 ^ k) = 3 * 4 ^ (k + 1) - 4 := by
    calc
      xiTerminalTotalDelta (2 ^ k) = 12 * 4 ^ k - 4 := hdelta₁
      _ = 3 * 4 ^ (k + 1) - 4 := by
        rw [pow_succ]
        omega
  exact ⟨hbidegree, hdelta₁, hdelta₂⟩

end Omega.Zeta
