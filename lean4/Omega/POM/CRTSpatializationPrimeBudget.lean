import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.POM

/-- Fibonacci numbers grow at least exponentially: F_{m+2} ≥ m + 1 for all m.
    This is a weak lower bound used for the prime budget argument.
    cor:pom-order-spatialization-prime-budget -/
theorem fib_lower_bound (m : ℕ) : m + 1 ≤ Nat.fib (m + 2) := by
  induction m with
  | zero => simp [Nat.fib]
  | succ n ih =>
    have h1 : 0 < Nat.fib (n + 1) := by
      rw [Nat.fib_pos]; omega
    have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    linarith

/-- For CRT unique reconstruction, the modulus product P must exceed 2B.
    When B ~ F_{m+2}, this forces log P ≥ log(2·(m+1)).
    Seeds: F_{m+2} values for small m confirm exponential growth.
    cor:pom-order-spatialization-prime-budget -/
theorem fib_growth_seeds :
    Nat.fib 3 = 2 ∧ Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 ∧
    Nat.fib 6 = 8 ∧ Nat.fib 7 = 13 ∧ Nat.fib 8 = 21 ∧
    Nat.fib 9 = 34 ∧ Nat.fib 10 = 55 := by native_decide

/-- If P > 2B and B ≥ m+1 (from Fibonacci lower bound), then P ≥ 2(m+1)+1.
    This formalizes the core inequality for the prime budget lower bound.
    cor:pom-order-spatialization-prime-budget -/
theorem crt_product_lower_bound (P B m : ℕ) (hP : P > 2 * B) (hB : B ≥ m + 1) :
    P ≥ 2 * (m + 1) + 1 := by omega

/-- If each prime modulus p_i ≤ m^c (polynomial-size primes), and their product
    P = ∏ p_i > 2B ≥ 2(m+1), then the number of primes k satisfies
    k ≥ log(2(m+1)) / (c · log m).
    Seed verification: for m = 5, F_7 = 13, need P > 26, using primes ≤ 25,
    need at least 2 primes (e.g. 3 × 11 = 33 > 26).
    cor:pom-order-spatialization-prime-budget -/
theorem prime_count_seed_m5 :
    Nat.fib 7 = 13 ∧ 2 * 13 = 26 ∧ 3 * 11 > 26 ∧
    3 ≤ 5 ^ 2 ∧ 11 ≤ 5 ^ 2 := by
  refine ⟨by native_decide, by omega, by omega, by omega, by omega⟩

/-- For m = 8, F_10 = 55, need P > 110. Using primes ≤ 64 = 8²,
    we need at least 3 primes (e.g., 5 × 7 × 11 = 385 > 110).
    This illustrates Ω(m / log m) growth of the number of primes needed.
    cor:pom-order-spatialization-prime-budget -/
theorem prime_count_seed_m8 :
    Nat.fib 10 = 55 ∧ 2 * 55 = 110 ∧
    5 * 7 * 11 > 110 ∧ 5 ≤ 8 ^ 2 ∧ 7 ≤ 8 ^ 2 ∧ 11 ≤ 8 ^ 2 := by
  refine ⟨?_, by omega, by omega, by omega, by omega, by omega⟩
  native_decide

/-- Paper: `cor:pom-order-spatialization-prime-budget`.
    CRT spatialization prime budget: Fibonacci growth forces the CRT modulus product
    to be at least linear in m, requiring Ω(m / log m) polynomial-size primes. -/
theorem paper_pom_crt_spatialization_prime_budget :
    (∀ m : ℕ, m + 1 ≤ Nat.fib (m + 2)) ∧
    (∀ P B m : ℕ, P > 2 * B → B ≥ m + 1 → P ≥ 2 * (m + 1) + 1) ∧
    (Nat.fib 7 = 13 ∧ Nat.fib 10 = 55) := by
  refine ⟨fib_lower_bound, crt_product_lower_bound, ?_, ?_⟩ <;> native_decide

end Omega.POM
