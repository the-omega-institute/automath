import Mathlib.Tactic

namespace Omega.POM

/-- Pointwise finite Markov bound used for the prime-register `q`-quota family. -/
lemma pom_prime_register_q_quota_family_pointwise {q : ℕ} {B y : ℝ} (hq : 2 ≤ q)
    (hB : 0 < B) (hy : 0 ≤ y) (hBy : B ≤ y) :
    y * B ^ (q - 1) ≤ y ^ q := by
  have hpow : B ^ (q - 1) ≤ y ^ (q - 1) :=
    pow_le_pow_left₀ hB.le hBy (q - 1)
  calc
    y * B ^ (q - 1) ≤ y * y ^ (q - 1) := by
      exact mul_le_mul_of_nonneg_left hpow hy
    _ = y ^ q := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q)]

/-- Paper label: `cor:pom-prime-register-q-quota-family`. -/
theorem paper_pom_prime_register_q_quota_family {X : Type*} [Fintype X] (m q : ℕ) (B : ℝ)
    (d : X → ℝ) (hq : 2 ≤ q) (hB : 0 < B) (hd : ∀ x, 0 ≤ d x) :
    (∑ x, if B ≤ d x then d x / (2 : ℝ) ^ m else 0) * B ^ (q - 1) ≤
      (∑ x, d x ^ q) / (2 : ℝ) ^ m := by
  have hden_pos : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) m
  calc
    (∑ x, if B ≤ d x then d x / (2 : ℝ) ^ m else 0) * B ^ (q - 1)
        = ∑ x, (if B ≤ d x then d x / (2 : ℝ) ^ m else 0) * B ^ (q - 1) := by
          rw [Finset.sum_mul]
    _ ≤ ∑ x, d x ^ q / (2 : ℝ) ^ m := by
          refine Finset.sum_le_sum ?_
          intro x hx
          by_cases hBy : B ≤ d x
          · simp only [hBy, ↓reduceIte]
            have hpoint :
                d x * B ^ (q - 1) / (2 : ℝ) ^ m ≤ d x ^ q / (2 : ℝ) ^ m :=
              (div_le_div_iff_of_pos_right hden_pos).2
                (pom_prime_register_q_quota_family_pointwise hq hB (hd x) hBy)
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpoint
          · simp only [hBy, ↓reduceIte, zero_mul]
            exact div_nonneg (pow_nonneg (hd x) q) hden_pos.le
    _ = (∑ x, d x ^ q) / (2 : ℝ) ^ m := by
          rw [Finset.sum_div]

end Omega.POM
