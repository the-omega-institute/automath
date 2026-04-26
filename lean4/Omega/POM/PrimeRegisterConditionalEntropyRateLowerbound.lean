import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

theorem paper_pom_prime_register_conditional_entropy_rate_lowerbound (p : ℕ) (N fiberSize : ℕ → ℕ)
    (hmu : ℝ) (hp : Nat.Prime p) (hreadable : ∀ n, fiberSize (n + 1) ≤ p ^ N (n + 1))
    (hentropy : ∀ ε : ℝ, 0 < ε →
      ∃ n0 : ℕ, ∀ n ≥ n0, ((n + 1 : ℝ) * (hmu - ε) ≤ Real.log (fiberSize (n + 1) : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ∃ n0 : ℕ, ∀ n ≥ n0, hmu / Real.log p - ε ≤ (N (n + 1) : ℝ) / (n + 1) := by
  intro ε hε
  have hp_two : 2 ≤ p := hp.two_le
  have hp_real_pos : 0 < (p : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) hp_two
  have hlogp_pos : 0 < Real.log p := by
    refine Real.log_pos ?_
    exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hp_two
  have hδ_pos : 0 < ε * Real.log p := mul_pos hε hlogp_pos
  rcases hentropy (ε * Real.log p) hδ_pos with ⟨n0, hn0⟩
  refine ⟨n0, ?_⟩
  intro n hn
  have hpow_nat_pos : 0 < p ^ N (n + 1) := pow_pos hp.pos _
  have hpow_nat_one : 1 ≤ p ^ N (n + 1) := Nat.succ_le_of_lt hpow_nat_pos
  have hpow_log_nonneg : 0 ≤ Real.log (((p ^ N (n + 1) : ℕ) : ℝ)) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hpow_nat_one
  have hread_real : (fiberSize (n + 1) : ℝ) ≤ ((p ^ N (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hreadable n
  have hlog_upper :
      Real.log (fiberSize (n + 1) : ℝ) ≤ Real.log (((p ^ N (n + 1) : ℕ) : ℝ)) := by
    by_cases hzero : fiberSize (n + 1) = 0
    · simp [hzero]
      exact mul_nonneg (by positivity) (le_of_lt hlogp_pos)
    · have hfiber_pos : 0 < (fiberSize (n + 1) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      exact Real.log_le_log hfiber_pos hread_real
  have hlog_pow :
      Real.log (((p ^ N (n + 1) : ℕ) : ℝ)) = (N (n + 1) : ℝ) * Real.log p := by
    rw [show (((p ^ N (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ N (n + 1)) by norm_num]
    rw [show ((p : ℝ) ^ N (n + 1) = (p : ℝ) ^ (N (n + 1) : ℝ)) by rw [Real.rpow_natCast]]
    rw [Real.log_rpow hp_real_pos]
  have hmain :
      (n + 1 : ℝ) * (hmu - ε * Real.log p) ≤ (N (n + 1) : ℝ) * Real.log p := by
    exact le_trans (hn0 n hn) (by simpa [hlog_pow] using hlog_upper)
  have hn1_pos : 0 < (n + 1 : ℝ) := by positivity
  have hdiv_n :
      hmu - ε * Real.log p ≤ ((N (n + 1) : ℝ) * Real.log p) / (n + 1) := by
    refine (le_div_iff₀ hn1_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
  have hdiv_log :
      (hmu - ε * Real.log p) / Real.log p
        ≤ (((N (n + 1) : ℝ) * Real.log p) / (n + 1)) / Real.log p := by
    exact div_le_div_of_nonneg_right hdiv_n (le_of_lt hlogp_pos)
  have hlogp_ne : Real.log p ≠ 0 := ne_of_gt hlogp_pos
  have hleft :
      (hmu - ε * Real.log p) / Real.log p = hmu / Real.log p - ε := by
    field_simp [hlogp_ne]
  have hright :
      (((N (n + 1) : ℝ) * Real.log p) / (n + 1)) / Real.log p = (N (n + 1) : ℝ) / (n + 1) := by
    field_simp [hlogp_ne]
  simpa [hleft, hright] using hdiv_log

end Omega.POM
