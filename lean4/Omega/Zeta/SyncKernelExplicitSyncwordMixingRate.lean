import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:sync-kernel-explicit-syncword-mixing-rate`. -/
theorem paper_sync_kernel_explicit_syncword_mixing_rate
    (blockFail tail tv : ℕ → ℝ) (lam : ℝ) (hLam : 0 ≤ lam) (h0 : blockFail 0 ≤ 1)
    (hstep : ∀ k : ℕ, blockFail (k + 1) ≤ lam * blockFail k)
    (htail : ∀ k : ℕ, tail (5 * k) ≤ blockFail k)
    (htv : ∀ n : ℕ, 5 ≤ n → tv n ≤ tail (5 * ((n - 5) / 5))) :
    (∀ k : ℕ, tail (5 * k) ≤ lam ^ k) ∧
      ∀ n : ℕ, 5 ≤ n → tv n ≤ lam ^ ((n - 5) / 5) := by
  have hblock : ∀ k : ℕ, blockFail k ≤ lam ^ k := by
    intro k
    induction k with
    | zero =>
        simpa using h0
    | succ k ih =>
        calc
          blockFail (k + 1) ≤ lam * blockFail k := hstep k
          _ ≤ lam * lam ^ k := mul_le_mul_of_nonneg_left ih hLam
          _ = lam ^ (k + 1) := by
            simp [pow_succ, mul_comm]
  have htail_pow : ∀ k : ℕ, tail (5 * k) ≤ lam ^ k := by
    intro k
    exact le_trans (htail k) (hblock k)
  refine ⟨htail_pow, ?_⟩
  intro n hn
  exact le_trans (htv n hn) (htail_pow ((n - 5) / 5))

end Omega.Zeta
