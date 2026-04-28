import Mathlib

open scoped BigOperators

/-- Paper label: `cor:xi-hankel-padics-global-budget-detH0`. -/
theorem paper_xi_hankel_padics_global_budget_deth0
    (badPrimes : Finset ℕ) (N s : ℕ -> ℕ) (hne : badPrimes.Nonempty)
    (hlog : ∀ p ∈ badPrimes, 0 < Real.log p)
    (hstrict : ∀ p ∈ badPrimes, s p < N p) :
    (∑ p ∈ badPrimes, (s p : ℝ) * Real.log p) <
      ∑ p ∈ badPrimes, (N p : ℝ) * Real.log p := by
  classical
  have hterm_lt :
      ∀ p ∈ badPrimes, (s p : ℝ) * Real.log p < (N p : ℝ) * Real.log p := by
    intro p hp
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hstrict p hp) (hlog p hp)
  rcases hne with ⟨p0, hp0⟩
  exact Finset.sum_lt_sum (fun p hp => le_of_lt (hterm_lt p hp)) ⟨p0, hp0, hterm_lt p0 hp0⟩
