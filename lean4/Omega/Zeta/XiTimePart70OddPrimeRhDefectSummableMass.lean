import Mathlib

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part70-odd-prime-rh-defect-summable-mass`. -/
theorem paper_xi_time_part70_odd_prime_rh_defect_summable_mass
    (isOddPrime : ℕ → Prop) [DecidablePred isOddPrime]
    (δ : ℕ → ℝ) (p0 : ℕ) (C : ℝ)
    (hp0 : 1 ≤ p0) (hC : 0 ≤ C)
    (hδ_nonneg : ∀ n, isOddPrime n → p0 ≤ n → 0 ≤ δ n)
    (hδ_bound : ∀ n, isOddPrime n → p0 ≤ n → δ n ≤ C / (n : ℝ)^2) :
    Summable (fun n => if isOddPrime n then δ n else 0) := by
  have hbase :
      Summable (fun n : ℕ => C * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ))) := by
    exact
      ((summable_nat_add_iff 1).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))).mul_left C
  have htail_major :
      Summable (fun n : ℕ => C / ((n + p0 : ℕ) : ℝ) ^ (2 : ℕ)) := by
    refine hbase.of_nonneg_of_le ?_ ?_
    · intro n
      positivity
    · intro n
      have hden_pos : 0 < ((n + p0 : ℕ) : ℝ) ^ (2 : ℕ) := by
        have hn_pos : (0 : ℝ) < (n + p0 : ℕ) := by
          exact_mod_cast Nat.add_pos_right n (Nat.succ_le_iff.mp hp0)
        positivity
      have hden_one_pos : 0 < ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by positivity
      have hden_le : ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((n + p0 : ℕ) : ℝ) ^ (2 : ℕ) := by
        gcongr
      have hinv_le :
          1 / ((n + p0 : ℕ) : ℝ) ^ (2 : ℕ) ≤
            1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) :=
        one_div_le_one_div_of_le hden_one_pos hden_le
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv_le hC
  have htail :
      Summable (fun n : ℕ => if isOddPrime (n + p0) then δ (n + p0) else 0) := by
    refine htail_major.of_nonneg_of_le ?_ ?_
    · intro n
      by_cases hprime : isOddPrime (n + p0)
      · simpa [hprime] using hδ_nonneg (n + p0) hprime (Nat.le_add_left p0 n)
      · simp [hprime]
    · intro n
      by_cases hprime : isOddPrime (n + p0)
      · simpa [hprime] using hδ_bound (n + p0) hprime (Nat.le_add_left p0 n)
      · simp [hprime]
        exact div_nonneg hC (sq_nonneg _)
  exact (summable_nat_add_iff p0).1 htail

end Omega.Zeta
