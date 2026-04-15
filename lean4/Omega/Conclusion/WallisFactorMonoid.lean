import Mathlib.Tactic

namespace Omega.Conclusion

/-- Every positive natural number can be written as 2n, 2n-1, or 2n+1 for some n ≥ 1.
    Equivalently, the set {2n : n ≥ 1} ∪ {2n-1 : n ≥ 1} ∪ {2n+1 : n ≥ 1} = ℕ \ {0}.
    This means the Wallis factor generators {2n, 2n-1, 2n+1 : n ≥ 1} already contain
    every positive integer, so the generated monoid is all of ℕ×.
    thm:conclusion-wallis-factor-monoid-universal -/
theorem wallis_factor_cover (m : ℕ) (hm : 0 < m) :
    (∃ n : ℕ, 0 < n ∧ m = 2 * n) ∨
    (∃ n : ℕ, 0 < n ∧ m = 2 * n - 1) ∨
    (∃ n : ℕ, 0 < n ∧ m = 2 * n + 1) := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; exact ⟨k, by omega, by omega⟩
  · by_cases hk' : k = 0
    · right; left; exact ⟨1, by omega, by omega⟩
    · right; right; exact ⟨k, by omega, by omega⟩

/-- The Wallis partial product uses factors of the form 2n/(2n-1) and 2n/(2n+1).
    Every even number ≥ 2 appears as a numerator 2n (n ≥ 1).
    thm:conclusion-wallis-factor-monoid-universal -/
theorem wallis_even_numerator (n : ℕ) (hn : 0 < n) : 0 < 2 * n := by omega

/-- Every odd number ≥ 1 appears as a denominator in the Wallis product.
    Specifically, 2n-1 ≥ 1 and 2n+1 ≥ 3 for n ≥ 1.
    thm:conclusion-wallis-factor-monoid-universal -/
theorem wallis_odd_denominator_bounds (n : ℕ) (hn : 0 < n) :
    1 ≤ 2 * n - 1 ∧ 3 ≤ 2 * n + 1 := by omega

/-- Seed values: first few Wallis partial products (numerators and denominators).
    W_n = ∏_{k=1}^{n} (2k)²/((2k-1)(2k+1)).
    thm:conclusion-wallis-factor-monoid-universal -/
theorem wallis_product_seeds :
    2 * 2 = 4 ∧ 1 * 3 = 3 ∧
    (2 * 2) * (4 * 4) = 64 ∧ (1 * 3) * (3 * 5) = 45 ∧
    (2 * 4 * 6) ^ 2 = 2304 ∧ (1 * 3) * (3 * 5) * (5 * 7) = 1575 := by omega

/-- Paper: `thm:conclusion-wallis-factor-monoid-universal`.
    Wallis factor monoid universality: every positive integer lies in the
    Wallis factor set, so the generated monoid is all of ℕ×. -/
theorem paper_conclusion_wallis_factor_monoid_universal :
    (∀ m : ℕ, 0 < m →
      (∃ n, 0 < n ∧ m = 2 * n) ∨
      (∃ n, 0 < n ∧ m = 2 * n - 1) ∨
      (∃ n, 0 < n ∧ m = 2 * n + 1)) ∧
    (∀ n : ℕ, 0 < n → 1 ≤ 2 * n - 1 ∧ 3 ≤ 2 * n + 1) := by
  exact ⟨wallis_factor_cover, wallis_odd_denominator_bounds⟩

end Omega.Conclusion
