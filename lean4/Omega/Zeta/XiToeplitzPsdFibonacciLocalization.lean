import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

open scoped goldenRatio

private theorem xi_toeplitz_psd_fibonacci_localization_fib_succ_ge_index :
    ∀ n : ℕ, n ≤ Nat.fib (n + 1)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      have ih : n + 1 ≤ Nat.fib (n + 2) :=
        xi_toeplitz_psd_fibonacci_localization_fib_succ_ge_index (n + 1)
      have hrec : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.fib_add_two (n := n + 1))
      have hpos : 1 ≤ Nat.fib (n + 1) := Nat.succ_le_of_lt (Nat.fib_pos.mpr (by omega))
      calc
        n + 2 ≤ Nat.fib (n + 2) + Nat.fib (n + 1) := by omega
        _ = Nat.fib (n + 3) := by simpa [add_comm] using hrec.symm

private theorem xi_toeplitz_psd_fibonacci_localization_goldenConj_pow_lt_one
    {k : ℕ} (hk : 0 < k) :
    Real.goldenConj ^ k < 1 := by
  have hψ : |Real.goldenConj| < 1 := by
    rw [abs_lt]
    exact ⟨by linarith [Real.neg_one_lt_goldenConj], by linarith [Real.goldenConj_neg]⟩
  have hpow_abs_lt : |Real.goldenConj ^ k| < 1 := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk) with ⟨n, rfl⟩
    rw [abs_pow, pow_succ]
    have hbase : |Real.goldenConj| ^ n ≤ 1 := by
      exact pow_le_one₀ (abs_nonneg _) hψ.le
    have hmul : |Real.goldenConj| ^ n * |Real.goldenConj| ≤ 1 * |Real.goldenConj| := by
      exact mul_le_mul_of_nonneg_right hbase (abs_nonneg _)
    have hle : |Real.goldenConj| ^ n * |Real.goldenConj| ≤ |Real.goldenConj| := by
      simpa using hmul
    exact lt_of_le_of_lt hle hψ
  exact lt_of_le_of_lt (le_abs_self _) hpow_abs_lt

/-- Paper label: `prop:xi-toeplitz-psd-fibonacci-localization`. Once Toeplitz failure is upward
closed from the first bad index `N₀`, every larger truncation also fails. Choosing the least
Fibonacci stage above `N₀` localizes the obstruction to a Fibonacci scale whose size is still
strictly below `φ · N₀`. -/
theorem paper_xi_toeplitz_psd_fibonacci_localization
    (fails : ℕ → Prop) (N0 : ℕ)
    (hN0 : 1 ≤ N0)
    (hbad : fails N0)
    (hmono : ∀ {m n : ℕ}, m ≤ n → fails m → fails n) :
    (∀ M : ℕ, N0 ≤ M → fails M) ∧
      ∃ k : ℕ,
        Nat.fib k < N0 ∧
          N0 ≤ Nat.fib (k + 1) ∧
          fails (Nat.fib (k + 1)) ∧
          ((Nat.fib (k + 1) : ℝ) < Real.goldenRatio * N0) := by
  have htail : ∀ M : ℕ, N0 ≤ M → fails M := by
    intro M hM
    exact hmono hM hbad
  have hexists : ∃ k : ℕ, N0 ≤ Nat.fib (k + 1) := by
    refine ⟨N0, ?_⟩
    exact xi_toeplitz_psd_fibonacci_localization_fib_succ_ge_index N0
  refine ⟨htail, ?_⟩
  let k := Nat.find hexists
  have hk_ge : N0 ≤ Nat.fib (k + 1) := Nat.find_spec hexists
  have hk_prev : Nat.fib k < N0 := by
    by_cases hk0 : k = 0
    · have hpos : (0 : ℕ) < N0 := by omega
      simpa [hk0] using hpos
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      by_contra hk_not_lt
      have hk_prev_ge : N0 ≤ Nat.fib k := Nat.le_of_not_gt hk_not_lt
      have hk_prev_witness : N0 ≤ Nat.fib ((k - 1) + 1) := by
        have hk_eq : k - 1 + 1 = k := Nat.sub_add_cancel (show 1 ≤ k by omega)
        exact hk_eq ▸ hk_prev_ge
      have hk_min : k ≤ k - 1 := Nat.find_min' hexists hk_prev_witness
      omega
  have hk_fail : fails (Nat.fib (k + 1)) := htail _ hk_ge
  have hk_step :
      (Nat.fib (k + 1) : ℝ) < Real.goldenRatio * (((Nat.fib k : ℕ) + 1 : ℕ) : ℝ) := by
    by_cases hk0 : k = 0
    · have hk1 : Nat.fib (k + 1) = 1 := by simp [hk0]
      have hN0_eq : N0 = 1 := by
        have hleft : N0 ≤ 1 := by simpa [hk0, hk1] using hk_ge
        omega
      simpa [hk0, hk1, hN0_eq] using Real.one_lt_goldenRatio
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have hk_error :
          (Nat.fib (k + 1) : ℝ) - (Nat.fib k : ℝ) * Real.goldenRatio < 1 := by
        calc
          (Nat.fib (k + 1) : ℝ) - (Nat.fib k : ℝ) * Real.goldenRatio
              = Real.goldenConj ^ k := by
                simpa [mul_comm] using Real.fib_succ_sub_goldenRatio_mul_fib k
          _ < 1 := xi_toeplitz_psd_fibonacci_localization_goldenConj_pow_lt_one hk_pos
      have htmp : (Nat.fib (k + 1) : ℝ) < (Nat.fib k : ℝ) * Real.goldenRatio + 1 := by
        linarith
      have hcast :
          ((((Nat.fib k : ℕ) + 1 : ℕ) : ℝ)) = (Nat.fib k : ℝ) + 1 := by
        norm_num
      calc
        (Nat.fib (k + 1) : ℝ) < (Nat.fib k : ℝ) * Real.goldenRatio + 1 := htmp
        _ ≤ (Nat.fib k : ℝ) * Real.goldenRatio + Real.goldenRatio := by
            nlinarith [Real.one_lt_goldenRatio]
        _ = ((Nat.fib k : ℝ) + 1) * Real.goldenRatio := by
            ring
        _ = ((((Nat.fib k : ℕ) + 1 : ℕ) : ℝ)) * Real.goldenRatio := by
            rw [hcast]
        _ = Real.goldenRatio * (((Nat.fib k : ℕ) + 1 : ℕ) : ℝ) := by
            ring
  have hk_step_le :
      Real.goldenRatio * (((Nat.fib k : ℕ) + 1 : ℕ) : ℝ) ≤ Real.goldenRatio * N0 := by
    have hk_succ_le : Nat.fib k + 1 ≤ N0 := Nat.succ_le_of_lt hk_prev
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk_succ_le) (le_of_lt Real.goldenRatio_pos)
  refine ⟨k, hk_prev, hk_ge, hk_fail, lt_of_lt_of_le hk_step hk_step_le⟩

end Omega.Zeta
