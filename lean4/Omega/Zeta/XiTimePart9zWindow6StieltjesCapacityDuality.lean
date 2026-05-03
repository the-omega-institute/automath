import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9z-window6-stieltjes-capacity-duality`. -/
theorem paper_xi_time_part9z_window6_stieltjes_capacity_duality (B : ℕ) :
    8 * min (2 ^ B) 2 + 4 * min (2 ^ B) 3 + 9 * min (2 ^ B) 4 =
      (if B = 0 then 21 else if B = 1 then 42 else 64) := by
  rcases B with _ | B
  · norm_num
  · rcases B with _ | B
    · norm_num
    · have hB : 2 ≤ Nat.succ (Nat.succ B) :=
        Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le B))
      have hpow : 4 ≤ 2 ^ Nat.succ (Nat.succ B) := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ Nat.succ (Nat.succ B) :=
            pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) hB
      rw [min_eq_right (Nat.le_trans (by norm_num : 2 ≤ 4) hpow),
        min_eq_right (Nat.le_trans (by norm_num : 3 ≤ 4) hpow), min_eq_right hpow]
      norm_num

end Omega.Zeta
