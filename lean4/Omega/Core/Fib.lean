import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Defs

/-! ### Convenience lemmas for `Nat.fib`

The project uses `Nat.fib` directly with the standard convention F₀ = 0, F₁ = 1.
The previous `paperFib k` indirection layer has been removed: all references now
use `Nat.fib (k + 1)` directly.

Mathlib's `Nat.fib_add_two` has the *small* term first:
  `Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1)`.
Many project proofs need the *large* term first, so we provide `fib_succ_succ`. -/

namespace Omega

-- ══════════════════════════════════════════════════════════════════
-- New canonical lemmas (Nat.fib based, in Omega namespace)
-- ══════════════════════════════════════════════════════════════════

/-- Fibonacci recurrence with large term first: F(n+2) = F(n+1) + F(n). -/
theorem fib_succ_succ' (n : Nat) : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  have := Nat.fib_add_two (n := n); omega

/-- F(n+1) > 0 for all n. -/
theorem fib_succ_pos (n : Nat) : 0 < Nat.fib (n + 1) :=
  Nat.fib_pos.mpr (by omega)

/-- F(n+1) ≥ 1 for all n. -/
theorem one_le_fib_succ (n : Nat) : 1 ≤ Nat.fib (n + 1) :=
  fib_succ_pos n

/-- Fibonacci recurrence, additive form: F(m+2) + F(m+1) = F(m+3). -/
theorem fib_add_succ (m : Nat) : Nat.fib (m + 2) + Nat.fib (m + 1) = Nat.fib (m + 3) := by
  have h := fib_succ_succ' (m + 1)
  rw [show m + 1 + 2 = m + 3 from by omega, show m + 1 + 1 = m + 2 from by omega] at h
  omega

/-- Fibonacci subtraction: F(m+3) - F(m+2) = F(m+1). -/
theorem fib_sub_succ (m : Nat) : Nat.fib (m + 3) - Nat.fib (m + 2) = Nat.fib (m + 1) := by
  have h := fib_succ_succ' (m + 1)
  rw [show m + 1 + 2 = m + 3 from by omega, show m + 1 + 1 = m + 2 from by omega] at h
  omega

/-- Carry modular identity: (F(m+2) + F(m+1)) % F(m+3) = 0. -/
theorem fib_mod_sum' (m : Nat) :
    (Nat.fib (m + 2) + Nat.fib (m + 1)) % Nat.fib (m + 3) = 0 := by
  rw [fib_add_succ, Nat.mod_self]

/-- Strict monotonicity: F(m+2) < F(m+3). -/
theorem fib_lt_fib_succ (m : Nat) : Nat.fib (m + 2) < Nat.fib (m + 3) := by
  have h := fib_succ_succ' (m + 1)
  rw [show m + 1 + 2 = m + 3 from by omega, show m + 1 + 1 = m + 2 from by omega] at h
  have := fib_succ_pos m; omega

/-- Resolution-crossing identity: F(m+4) mod F(m+3) = F(m+2). -/
theorem fib_succ_mod' (m : Nat) :
    Nat.fib (m + 4) % Nat.fib (m + 3) = Nat.fib (m + 2) := by
  have : Nat.fib (m + 4) = Nat.fib (m + 3) + Nat.fib (m + 2) := by
    rw [show m + 4 = (m + 2) + 2 from by omega]; exact fib_succ_succ' (m + 2)
  rw [this, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (fib_lt_fib_succ m)]

/-- F(m+2) > 1 for m ≥ 1. -/
theorem fib_gt_one_of_ge_two (hm : 1 ≤ m) : 1 < Nat.fib (m + 2) := by
  calc 1 < 2 := by omega
    _ = Nat.fib 3 := by native_decide
    _ ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)

/-- Upper bound: F(m+2) ≤ 2^(m+1) for all m.
    fib-growth-upper-bound
    fib-growth-upper-bound -/
theorem fib_le_pow_two : ∀ m : Nat, Nat.fib (m + 2) ≤ 2 ^ (m + 1)
  | 0 => by simp
  | 1 => by native_decide
  | m + 2 => by
    calc Nat.fib (m + 2 + 2)
        = Nat.fib (m + 2 + 1) + Nat.fib (m + 2) := fib_succ_succ' (m + 2)
      _ ≤ 2 ^ (m + 1 + 1) + 2 ^ (m + 1) :=
          Nat.add_le_add (fib_le_pow_two (m + 1)) (fib_le_pow_two m)
      _ ≤ 2 ^ (m + 1 + 1) + 2 ^ (m + 1 + 1) :=
          Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) (by omega)) _
      _ = 2 ^ (m + 2 + 1) := by ring

/-- Fibonacci doubling bound: 2 · F(n) ≤ F(n+2) for n ≥ 1.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem fib_double_le (n : Nat) (_hn : 1 ≤ n) :
    2 * Nat.fib n ≤ Nat.fib (n + 2) := by
  rw [Nat.fib_add_two]
  linarith [Nat.fib_mono (show n ≤ n + 1 by omega)]

/-- Fibonacci exponential growth: F(n+2k) ≥ 2^k · F(n) for n ≥ 1.
    subsec:conclusion-bounded-prime-register-godel-scaling -/
theorem fib_exponential_growth (n k : Nat) (hn : 1 ≤ n) :
    2 ^ k * Nat.fib n ≤ Nat.fib (n + 2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc 2 ^ (k + 1) * Nat.fib n
        = 2 * (2 ^ k * Nat.fib n) := by ring
      _ ≤ 2 * Nat.fib (n + 2 * k) := by linarith
      _ ≤ Nat.fib (n + 2 * k + 2) := fib_double_le (n + 2 * k) (by omega)
      _ = Nat.fib (n + 2 * (k + 1)) := by ring_nf

/-- gcd(F_m, F_n) = F_{gcd(m,n)} (strong divisibility).
    fib-gcd
    lem:fib-divisibility-iff -/
theorem fib_gcd (m n : Nat) : Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) :=
  (Nat.fib_gcd m n).symm

/-- F_m and F_{m+1} are coprime.
    fib-coprime-succ
    fib-coprime-succ -/
theorem fib_coprime_succ (m : Nat) : Nat.Coprime (Nat.fib m) (Nat.fib (m + 1)) :=
  Nat.fib_coprime_fib_succ m

/-- F_m divides F_{k*m}.
    fib-dvd-mul
    lem:fib-divisibility-chain -/
theorem fib_dvd_mul (m k : Nat) : Nat.fib m ∣ Nat.fib (k * m) :=
  Nat.fib_dvd m (k * m) ⟨k, (Nat.mul_comm m k).symm⟩

/-- F_m divides F_{m*k} (argument-order convenience wrapper).
    infra:fib-divisibility -/
theorem fib_dvd_fib_mul (m k : ℕ) : Nat.fib m ∣ Nat.fib (m * k) := by
  rw [Nat.mul_comm]; exact fib_dvd_mul m k

/-- fib(6) | fib(12).
    infra:fib-divisibility -/
theorem fib_six_dvd_fib_twelve : Nat.fib 6 ∣ Nat.fib 12 :=
  fib_dvd_fib_mul 6 2

-- ══════════════════════════════════════════════════════════════
-- Phase R143: Fibonacci divisibility paper wrappers
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci divisibility: m | n → F(m) | F(n).
    cor:discussion-horizon-boundarylayer-phi-scaling -/
theorem paper_fib_dvd (m n : Nat) (h : m ∣ n) : Nat.fib m ∣ Nat.fib n :=
  Nat.fib_dvd m n h

/-- Fibonacci GCD = Fibonacci of GCD.
    cor:discussion-horizon-boundarylayer-phi-scaling -/
theorem paper_fib_gcd (m n : Nat) :
    Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) :=
  fib_gcd m n

/-- Concrete: F(6)=8 divides F(12)=144.
    cor:discussion-horizon-boundarylayer-phi-scaling -/
theorem paper_fib_6_dvd_fib_12 : Nat.fib 6 ∣ Nat.fib 12 :=
  fib_six_dvd_fib_twelve

/-- F_{2n} = F_n · (2·F_{n+1} - F_n).
    prop:fib-double-formula -/
theorem fib_double (n : Nat) :
    Nat.fib (2 * n) = Nat.fib n * (2 * Nat.fib (n + 1) - Nat.fib n) :=
  Nat.fib_two_mul n

/-- F_{2n+1} = F_{n+1}² + F_n².
    prop:fib-double-plus-one-formula -/
theorem fib_double_plus_one (n : Nat) :
    Nat.fib (2 * n + 1) = Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 :=
  Nat.fib_two_mul_add_one n

/-- F_n² + F_{n+1}² = F_{2n+1}.
    prop:fib-sq-add-sq -/
theorem fib_sq_add_sq (n : Nat) :
    Nat.fib n ^ 2 + Nat.fib (n + 1) ^ 2 = Nat.fib (2 * n + 1) := by
  rw [Nat.add_comm]; exact (Nat.fib_two_mul_add_one n).symm

-- ══════════════════════════════════════════════════════════════
-- Fibonacci parity / Pisano period mod 2
-- ══════════════════════════════════════════════════════════════

/-- 3|n → 2|F_n.
    thm:fib-even-of-three-dvd -/
theorem fib_even_of_three_dvd (n : Nat) (h : 3 ∣ n) : 2 ∣ Nat.fib n := by
  exact dvd_trans (show (2 : Nat) ∣ Nat.fib 3 from by decide) (Nat.fib_dvd 3 n h)

/-- 2|F_n → 3|n.
    thm:three-dvd-of-fib-even -/
theorem three_dvd_of_fib_even (n : Nat) (h : 2 ∣ Nat.fib n) : 3 ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact dvd_zero 3
    | 1 => exfalso; simp [Nat.fib] at h
    | 2 => exfalso; simp [Nat.fib] at h
    | n + 3 =>
      -- F(n+3) = F(n+2) + F(n+1). If F(n+3) even, then F(n+2) and F(n+1) have same parity.
      have hfib : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
      -- If both even: 3|(n+1) and 3|(n+2), impossible (consecutive)
      -- If both odd: F(n) = F(n+2) - F(n+1) is even → 3|n by IH → 3|(n+3)
      by_cases h1 : 2 ∣ Nat.fib (n + 1)
      · -- F(n+1) even → 3|(n+1). Also F(n+2) even (same parity) → 3|(n+2). Contradiction.
        have h2 : 2 ∣ Nat.fib (n + 2) := by rwa [hfib, Nat.dvd_add_right h1] at h
        have := ih (n + 1) (by omega) h1
        have := ih (n + 2) (by omega) h2
        omega
      · -- F(n+1) odd → F(n+2) odd (same parity) → F(n) = F(n+2)-F(n+1) even
        have h2 : ¬ (2 ∣ Nat.fib (n + 2)) := by
          intro h2; exact h1 (by rwa [hfib, Nat.dvd_add_left h2] at h)
        -- F(n) = F(n+2) - F(n+1)
        have hfn : Nat.fib n = Nat.fib (n + 2) - Nat.fib (n + 1) := by
          have := Nat.fib_add_two (n := n); omega
        -- F(n+1) odd and F(n+2) odd → F(n+1) % 2 = 1, F(n+2) % 2 = 1
        -- F(n) = F(n+2) - F(n+1), both odd → difference even
        have heven : 2 ∣ Nat.fib n := by
          rw [hfn]
          -- Both F(n+1) and F(n+2) are odd, so their difference is even
          have hr1 : Nat.fib (n + 1) % 2 = 1 := by omega
          have hr2 : Nat.fib (n + 2) % 2 = 1 := by omega
          omega
        have := ih n (by omega) heven
        omega

/-- F_n is even iff 3|n.
    thm:fib-even-iff-three-dvd -/
theorem fib_even_iff_three_dvd (n : Nat) : 2 ∣ Nat.fib n ↔ 3 ∣ n :=
  ⟨three_dvd_of_fib_even n, fib_even_of_three_dvd n⟩

/-- F_n % 2 = F_{n%3} % 2.
    thm:fib-mod-two-period -/
theorem fib_mod_two_period (n : Nat) :
    Nat.fib n % 2 = Nat.fib (n % 3) % 2 := by
  by_cases h : 3 ∣ n
  · -- 3|n → F_n even → F_n % 2 = 0. Also n%3=0 → F_0=0 → F_0 % 2 = 0
    have heven := (fib_even_iff_three_dvd n).mpr h
    have hmod : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [hmod]; simp only [Nat.fib_zero, Nat.zero_mod]; omega
  · -- 3∤n → F_n odd → F_n % 2 = 1. n%3 ∈ {1,2} → F_{n%3} ∈ {F_1, F_2} = {1,1} → % 2 = 1
    have hodd := mt (three_dvd_of_fib_even n) h
    have hmod : n % 3 = 1 ∨ n % 3 = 2 := by omega
    have : Nat.fib n % 2 = 1 := by omega
    rcases hmod with hm | hm <;> rw [hm] <;> simp only [Nat.fib_one, Nat.fib_two] <;> omega

/-- F_n is odd iff 3∤n.
    thm:fib-odd-iff-not-three-dvd -/
theorem fib_odd_iff_not_three_dvd (n : Nat) : ¬ (2 ∣ Nat.fib n) ↔ ¬ (3 ∣ n) := by
  rw [fib_even_iff_three_dvd]

-- ══════════════════════════════════════════════════════════════
-- Fibonacci summation identities
-- ══════════════════════════════════════════════════════════════

/-- Σ_{k<n} F_{k+1} = F_{n+2} - 1.
    thm:fib-partial-sum -/
theorem fib_partial_sum (n : Nat) :
    ∑ k ∈ Finset.range n, Nat.fib (k + 1) = Nat.fib (n + 2) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : Nat.fib (n + 1 + 1) = Nat.fib (n + 2) := rfl
    have h2 : Nat.fib (n + 1 + 2) = Nat.fib (n + 3) := rfl
    rw [h1, h2]
    have := Nat.fib_add_two (n := n + 1)
    rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at this
    have := fib_succ_pos n; have := fib_succ_pos (n + 1)
    omega

/-- Σ_{k<n} F_{k+2} = F_{n+3} - 2.
    thm:fib-partial-sum-from-two -/
theorem fib_partial_sum_from_two (n : Nat) :
    ∑ k ∈ Finset.range n, Nat.fib (k + 2) = Nat.fib (n + 3) - 2 := by
  induction n with
  | zero => simp [Nat.fib]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : Nat.fib (n + 1 + 2) = Nat.fib (n + 3) := rfl
    have h2 : Nat.fib (n + 1 + 3) = Nat.fib (n + 4) := rfl
    rw [h1, h2]
    have := Nat.fib_add_two (n := n + 2)
    rw [show n + 2 + 2 = n + 4 from rfl, show n + 2 + 1 = n + 3 from rfl] at this
    have : 0 < Nat.fib (n + 2) := fib_succ_pos (n + 1)
    have : 0 < Nat.fib (n + 3) := fib_succ_pos (n + 2)
    have hfib3 := Nat.fib_add_two (n := n + 1)
    rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at hfib3
    have : 0 < Nat.fib (n + 1) := fib_succ_pos n
    have : 2 ≤ Nat.fib (n + 4) := by omega
    omega

/-- Σ_{k<n} F_{k+1}² = F_n · F_{n+1}.
    thm:fib-sq-sum -/
theorem fib_sq_sum (n : Nat) :
    ∑ k ∈ Finset.range n, Nat.fib (k + 1) ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hfib := Nat.fib_add_two (n := n)
    -- F_n*F_{n+1} + F_{n+1}^2 = F_{n+1}*(F_n+F_{n+1}) = F_{n+1}*F_{n+2}
    rw [show Nat.fib (n + 1) ^ 2 = Nat.fib (n + 1) * Nat.fib (n + 1) from sq _, hfib]
    ring

/-- Σ_{k<n} F_{2(k+1)} = F_{2n+1} - 1.
    thm:fib-even-sum -/
theorem fib_even_sum (n : Nat) :
    ∑ k ∈ Finset.range n, Nat.fib (2 * (k + 1)) = Nat.fib (2 * n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    -- Normalize: 2*(n+1) = 2*n+2, 2*(n+1)+1 = 2*n+3, 2*(n+1+1) = 2*n+4
    -- But these may not match syntactically. Use conv/show.
    -- Goal: F(2n+1)-1 + F(2*(n+1)) = F(2*(n+1)+1)-1
    -- = F(2n+1)-1 + F(2n+2) = F(2n+3)-1
    -- F(2n+3) = F(2n+1) + F(2n+2)
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
        show 2 * n + 2 + 1 = 2 * n + 3 from by ring]
    have := Nat.fib_add_two (n := 2 * n + 1)
    rw [show 2 * n + 1 + 2 = 2 * n + 3 from rfl, show 2 * n + 1 + 1 = 2 * n + 2 from rfl] at this
    have : 0 < Nat.fib (2 * n + 1) := fib_succ_pos (2 * n)
    have : 0 < Nat.fib (2 * n + 2) := fib_succ_pos (2 * n + 1)
    omega

/-- Adding F_2=1 to the alternating pattern value gives F_{m+1}.
    thm:zeckendorf-parallel-propagation-lower-bound -/
theorem fib_even_sum_add_one (n : Nat) (_hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, Nat.fib (2 * (k + 1)) + 1 = Nat.fib (2 * n + 1) := by
  rw [fib_even_sum]
  have : 0 < Nat.fib (2 * n + 1) := fib_succ_pos (2 * n)
  omega

/-- The parallel propagation value pair certificate:
    Val(x^(m)) = F_{m+1}-1 and Val(x^(m)) + F_2 = F_{m+1}.
    thm:zeckendorf-parallel-propagation-lower-bound -/
theorem parallel_propagation_value_pair (n : Nat) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, Nat.fib (2 * (k + 1)) = Nat.fib (2 * n + 1) - 1) ∧
    (∑ k ∈ Finset.range n, Nat.fib (2 * (k + 1)) + Nat.fib 2 = Nat.fib (2 * n + 1)) := by
  exact ⟨fib_even_sum n, by simp [Nat.fib]; exact fib_even_sum_add_one n hn⟩

/-- Paper: thm:zeckendorf-parallel-propagation-lower-bound -/
theorem paper_parallel_propagation_value_pair (n : Nat) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range n, Nat.fib (2 * (k + 1)) = Nat.fib (2 * n + 1) - 1) ∧
    (∑ k ∈ Finset.range n, Nat.fib (2 * (k + 1)) + Nat.fib 2 = Nat.fib (2 * n + 1)) :=
  parallel_propagation_value_pair n hn

/-- Σ_{k<n} F_{2k+1} = F_{2n}.
    thm:fib-odd-sum -/
theorem fib_odd_sum (n : Nat) :
    ∑ k ∈ Finset.range n, Nat.fib (2 * k + 1) = Nat.fib (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [h1]
    have := Nat.fib_add_two (n := 2 * n)
    rw [show 2 * n + 2 = 2 * n + 2 from rfl] at this
    omega

-- ══════════════════════════════════════════════════════════════
-- Advanced Fibonacci identities
-- ══════════════════════════════════════════════════════════════

/-- 3 ∣ F(n) ↔ 4 ∣ n.
    thm:pom-fib-div-three-iff -/
theorem fib_div_three_iff (n : Nat) : 3 ∣ Nat.fib n ↔ 4 ∣ n := by
  constructor
  · -- 3|F(n) → 4|n: by strong induction + Pisano period
    intro h
    induction n using Nat.strongRecOn with
    | _ n ih =>
      match n with
      | 0 => exact dvd_zero 4
      | 1 => simp [Nat.fib] at h
      | 2 => simp [Nat.fib] at h
      | 3 => simp [Nat.fib] at h
      | n + 4 =>
        -- F(n+4) = F(n+3)+F(n+2) = (F(n+2)+F(n+1))+F(n+2) = 2F(n+2)+F(n+1)
        -- F(n+2) = F(n+1)+F(n)
        -- F(n+4) = 2(F(n+1)+F(n))+F(n+1) = 3F(n+1)+2F(n)
        -- If 3|F(n+4): 3|3F(n+1)+2F(n) → 3|2F(n) → 3|F(n) (since gcd(3,2)=1)
        have hfib2 := Nat.fib_add_two (n := n)
        have hfib3 := Nat.fib_add_two (n := n + 1)
        have hfib4 := Nat.fib_add_two (n := n + 2)
        rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at hfib3
        rw [show n + 2 + 2 = n + 4 from rfl, show n + 2 + 1 = n + 3 from rfl] at hfib4
        have h3fn : 3 ∣ Nat.fib n := by
          have : Nat.fib (n + 4) = 3 * Nat.fib (n + 1) + 2 * Nat.fib n := by
            rw [hfib4, hfib3, hfib2]; ring
          rw [this] at h
          have h2fn : 3 ∣ 2 * Nat.fib n := by omega
          have : 3 ∣ Nat.fib n * 2 := by rwa [Nat.mul_comm] at h2fn
          exact (Nat.Coprime.dvd_of_dvd_mul_right (by decide : Nat.Coprime 3 2) this)
        have := ih n (by omega) h3fn
        omega
  · -- 4|n → 3|F(n): F_4=3 divides F_{4k}
    intro ⟨k, hk⟩; rw [hk]
    exact dvd_trans (show (3 : Nat) ∣ Nat.fib 4 from by decide) (Nat.fib_dvd 4 (4 * k) ⟨k, rfl⟩)

/-- F(n+1) ≤ 2·F(n) for n ≥ 1.
    bridge:fib-ratio-bound -/
theorem fib_succ_le_double (n : Nat) (hn : 1 ≤ n) :
    Nat.fib (n + 1) ≤ 2 * Nat.fib n := by
  -- F(n+1) = F(n-1) + F(n) ≤ F(n) + F(n) = 2F(n)
  have hrec := Nat.fib_add_two (n := n - 1)
  rw [show n - 1 + 2 = n + 1 from by omega, show n - 1 + 1 = n from by omega] at hrec
  have hmono : Nat.fib (n - 1) ≤ Nat.fib n := Nat.fib_mono (by omega)
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 170
-- ══════════════════════════════════════════════════════════════

/-- F_{m+2} < 2^m for m ≥ 2. -/
theorem fib_lt_pow_two_of_ge_two (m : Nat) (hm : 2 ≤ m) :
    Nat.fib (m + 2) < 2 ^ m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 => omega
    | 2 => native_decide
    | 3 => native_decide
    | m + 4 =>
      have hfib := fib_succ_succ' (m + 4)
      rw [show m + 4 + 2 = m + 6 from by omega,
          show m + 4 + 1 = m + 5 from by omega] at hfib
      have ih3 := ih (m + 3) (by omega) (by omega)
      have ih2 := ih (m + 2) (by omega) (by omega)
      rw [hfib]
      calc Nat.fib (m + 5) + Nat.fib (m + 4)
          < 2 ^ (m + 3) + 2 ^ (m + 2) := Nat.add_lt_add ih3 ih2
        _ ≤ 2 ^ (m + 3) + 2 ^ (m + 3) :=
            Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) (by omega)) _
        _ = 2 ^ (m + 4) := by ring

-- ══════════════════════════════════════════════════════════════
-- Phase 173
-- ══════════════════════════════════════════════════════════════

/-- The fence determinant recursion: D(k+2) = 3·D(k+1) - D(k), D(0)=1, D(1)=2.
    def:pom-fence-det -/
def fenceDet : Nat → Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => 3 * fenceDet (n + 1) - fenceDet n

/-- Fibonacci identity: F_{2n+5} = 3·F_{2n+3} - F_{2n+1}. -/
theorem fib_odd_recurrence (n : Nat) :
    Nat.fib (2 * n + 5) = 3 * Nat.fib (2 * n + 3) - Nat.fib (2 * n + 1) := by
  -- F_{2n+5} = F_{2n+4} + F_{2n+3}
  have h5 := Nat.fib_add_two (n := 2 * n + 3)
  -- F_{2n+4} = F_{2n+3} + F_{2n+2}
  have h4 := Nat.fib_add_two (n := 2 * n + 2)
  -- F_{2n+3} = F_{2n+2} + F_{2n+1}
  have h3 := Nat.fib_add_two (n := 2 * n + 1)
  -- From h3: F_{2n+2} = F_{2n+3} - F_{2n+1}
  -- F_{2n+5} = 2·F_{2n+3} + F_{2n+2} = 2·F_{2n+3} + (F_{2n+3} - F_{2n+1}) = 3·F_{2n+3} - F_{2n+1}
  have hpos : Nat.fib (2 * n + 1) ≤ Nat.fib (2 * n + 3) := Nat.fib_mono (by omega)
  rw [show 2 * n + 3 + 2 = 2 * n + 5 from by omega,
      show 2 * n + 3 + 1 = 2 * n + 4 from by omega] at h5
  rw [show 2 * n + 2 + 2 = 2 * n + 4 from by omega,
      show 2 * n + 2 + 1 = 2 * n + 3 from by omega] at h4
  rw [show 2 * n + 1 + 2 = 2 * n + 3 from by omega,
      show 2 * n + 1 + 1 = 2 * n + 2 from by omega] at h3
  omega

/-- The fence determinant equals the odd-indexed Fibonacci number: det(L_k + I) = F_{2k+1}.
    cor:pom-Lk-t1-fibonacci-det-green. -/
theorem fenceDet_eq_fib (k : Nat) : fenceDet k = Nat.fib (2 * k + 1) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => simp [fenceDet]
    | 1 => simp [fenceDet]; native_decide
    | k + 2 =>
      rw [fenceDet, ih (k + 1) (by omega), ih k (by omega)]
      rw [show 2 * (k + 2) + 1 = 2 * k + 5 from by ring,
          show 2 * (k + 1) + 1 = 2 * k + 3 from by ring,
          show 2 * k + 1 = 2 * k + 1 from rfl]
      exact (fib_odd_recurrence k).symm

-- ══════════════════════════════════════════════════════════════
-- Phase 177: Cassini identity
-- ══════════════════════════════════════════════════════════════

/-- Cassini identity (even case): F_n · F_{n+2} + 1 = F_{n+1}² for even n. -/
theorem fib_cassini_even (n : Nat) (heven : Even n) :
    Nat.fib n * Nat.fib (n + 2) + 1 = Nat.fib (n + 1) ^ 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [Nat.fib]
    | 1 => exact absurd heven (by decide)
    | n + 2 =>
      have hn_even : Even n := by
        rcases heven with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
      have ih_n := ih n (by omega) hn_even
      have h1 := Nat.fib_add_two (n := n)
      have h2 := Nat.fib_add_two (n := n + 1)
      have h3 := Nat.fib_add_two (n := n + 2)
      rw [show n + 1 + 2 = n + 3 from by omega, show n + 1 + 1 = n + 2 from by omega] at h2
      rw [show n + 2 + 2 = n + 4 from by omega, show n + 2 + 1 = n + 3 from by omega] at h3
      nlinarith [sq_nonneg (Nat.fib n), sq_nonneg (Nat.fib (n + 1))]

/-- Cassini identity (odd case): F_n · F_{n+2} = F_{n+1}² + 1 for odd n. -/
theorem fib_cassini_odd (n : Nat) (hodd : ¬ Even n) :
    Nat.fib n * Nat.fib (n + 2) = Nat.fib (n + 1) ^ 2 + 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact absurd ⟨0, rfl⟩ hodd
    | 1 => simp [Nat.fib]
    | n + 2 =>
      have hn_odd : ¬ Even n := by intro ⟨k, hk⟩; exact hodd ⟨k + 1, by omega⟩
      have ih_n := ih n (by omega) hn_odd
      have h1 := Nat.fib_add_two (n := n)
      have h2 := Nat.fib_add_two (n := n + 1)
      have h3 := Nat.fib_add_two (n := n + 2)
      rw [show n + 1 + 2 = n + 3 from by omega, show n + 1 + 1 = n + 2 from by omega] at h2
      rw [show n + 2 + 2 = n + 4 from by omega, show n + 2 + 1 = n + 3 from by omega] at h3
      nlinarith [sq_nonneg (Nat.fib n), sq_nonneg (Nat.fib (n + 1))]

-- ══════════════════════════════════════════════════════════════
-- Phase R139: Indexed Cassini identities
-- ══════════════════════════════════════════════════════════════

/-- Cassini even case indexed by k: F(2k+1)² = F(2k)·F(2k+2) + 1.
    cor:discussion-horizon-boundarylayer-phi-scaling -/
theorem fib_cassini_even_indexed (k : Nat) :
    Nat.fib (2 * k + 1) ^ 2 = Nat.fib (2 * k) * Nat.fib (2 * k + 2) + 1 := by
  have := fib_cassini_even (2 * k) (even_two_mul k)
  omega

/-- Cassini odd case indexed by k: F(2k+2)² + 1 = F(2k+1)·F(2k+3).
    cor:discussion-horizon-boundarylayer-phi-scaling -/
theorem fib_cassini_odd_indexed (k : Nat) :
    Nat.fib (2 * k + 2) ^ 2 + 1 = Nat.fib (2 * k + 1) * Nat.fib (2 * k + 3) := by
  have := fib_cassini_odd (2 * k + 1) (by intro ⟨j, hj⟩; omega)
  -- this : F(2k+1) * F(2k+3) = F(2k+2)^2 + 1
  linarith

/-- Paper: cor:discussion-horizon-boundarylayer-phi-scaling (Cassini) -/
theorem paper_fib_cassini_even_indexed (k : Nat) :
    Nat.fib (2 * k + 1) ^ 2 = Nat.fib (2 * k) * Nat.fib (2 * k + 2) + 1 :=
  fib_cassini_even_indexed k

theorem paper_fib_cassini_odd_indexed (k : Nat) :
    Nat.fib (2 * k + 2) ^ 2 + 1 = Nat.fib (2 * k + 1) * Nat.fib (2 * k + 3) :=
  fib_cassini_odd_indexed k

-- ══════════════════════════════════════════════════════════════
-- Phase 178
-- ══════════════════════════════════════════════════════════════

/-- Total Fibonacci weight sum (range form): Σ_{i<m} F_{i+2} = F_{m+3} - 2. -/
theorem fib_weight_sum_range (m : Nat) :
    ∑ i ∈ Finset.range m, Nat.fib (i + 2) = Nat.fib (m + 3) - 2 :=
  fib_partial_sum_from_two m

-- ══════════════════════════════════════════════════════════════
-- Phase 182
-- ══════════════════════════════════════════════════════════════

/-- 5 ∣ F_n → 5 ∣ n (by strong induction, Pisano period 5). -/
private theorem five_dvd_of_fib_five_dvd (n : Nat) (h : 5 ∣ Nat.fib n) : 5 ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact dvd_zero 5
    | 1 => simp [Nat.fib] at h
    | 2 => simp [Nat.fib] at h
    | 3 => simp [Nat.fib] at h
    | 4 => simp [Nat.fib] at h
    | n + 5 =>
      -- F(n+5) = 5F(n+3) + 3F(n+2) = ... use F(n+5) = 5F(n+1) + 8F(n) + ... too complex
      -- Simpler: F(n+5) ≡ F(n) (mod 5) by Pisano period
      -- F(n+5) = F(n+4) + F(n+3)
      --        = (F(n+3)+F(n+2)) + F(n+3) = 2F(n+3) + F(n+2)
      --        = 2(F(n+2)+F(n+1)) + F(n+2) = 3F(n+2) + 2F(n+1)
      --        = 3(F(n+1)+F(n)) + 2F(n+1) = 5F(n+1) + 3F(n)
      -- So F(n+5) = 5F(n+1) + 3F(n), hence F(n+5) % 5 = 3F(n) % 5
      -- If 5|F(n+5) then 5|3F(n), and gcd(5,3)=1 so 5|F(n), then by IH 5|n, hence 5|(n+5).
      have hfib2 := Nat.fib_add_two (n := n)
      have hfib3 := Nat.fib_add_two (n := n + 1)
      have hfib4 := Nat.fib_add_two (n := n + 2)
      have hfib5 := Nat.fib_add_two (n := n + 3)
      rw [show n + 1 + 2 = n + 3 from by omega, show n + 1 + 1 = n + 2 from by omega] at hfib3
      rw [show n + 2 + 2 = n + 4 from by omega, show n + 2 + 1 = n + 3 from by omega] at hfib4
      rw [show n + 3 + 2 = n + 5 from by omega, show n + 3 + 1 = n + 4 from by omega] at hfib5
      have hkey : Nat.fib (n + 5) = 5 * Nat.fib (n + 1) + 3 * Nat.fib n := by linarith
      rw [hkey] at h
      have h3fn : 5 ∣ 3 * Nat.fib n := by omega
      have hfn : 5 ∣ Nat.fib n :=
        (Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 5 3) h3fn)
      have := ih n (by omega) hfn
      omega

/-- 5 ∣ n → 5 ∣ F_n. -/
private theorem fib_five_dvd_of_five_dvd (n : Nat) (h : 5 ∣ n) : 5 ∣ Nat.fib n := by
  obtain ⟨k, rfl⟩ := h
  exact dvd_trans (show (5 : Nat) ∣ Nat.fib 5 from by native_decide) (Nat.fib_dvd 5 (5 * k) ⟨k, rfl⟩)

/-- Pisano period mod 5: 5 | F_n ↔ 5 | n. -/
theorem fib_five_dvd_iff (n : Nat) : 5 ∣ Nat.fib n ↔ 5 ∣ n :=
  ⟨five_dvd_of_fib_five_dvd n, fib_five_dvd_of_five_dvd n⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 183
-- ══════════════════════════════════════════════════════════════

/-- 7 ∣ F_n → 8 ∣ n (by strong induction, Pisano entry point 8). -/
private theorem eight_dvd_of_fib_seven_dvd (n : Nat) (h : 7 ∣ Nat.fib n) : 8 ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact dvd_zero 8
    | 1 => simp [Nat.fib] at h
    | 2 => simp [Nat.fib] at h
    | 3 => simp [Nat.fib] at h
    | 4 => simp [Nat.fib] at h
    | 5 => simp [Nat.fib] at h
    | 6 => simp [Nat.fib] at h
    | 7 => simp [Nat.fib] at h
    | n + 8 =>
      -- F(n+8) = 21*F(n+1) + 13*F(n), so 7|F(n+8) → 7|13*F(n) → 7|F(n)
      have h2 := Nat.fib_add_two (n := n)
      have h3 := Nat.fib_add_two (n := n + 1)
      have h4 := Nat.fib_add_two (n := n + 2)
      have h5 := Nat.fib_add_two (n := n + 3)
      have h6 := Nat.fib_add_two (n := n + 4)
      have h7 := Nat.fib_add_two (n := n + 5)
      have h8 := Nat.fib_add_two (n := n + 6)
      rw [show n + 1 + 2 = n + 3 from by omega, show n + 1 + 1 = n + 2 from by omega] at h3
      rw [show n + 2 + 2 = n + 4 from by omega, show n + 2 + 1 = n + 3 from by omega] at h4
      rw [show n + 3 + 2 = n + 5 from by omega, show n + 3 + 1 = n + 4 from by omega] at h5
      rw [show n + 4 + 2 = n + 6 from by omega, show n + 4 + 1 = n + 5 from by omega] at h6
      rw [show n + 5 + 2 = n + 7 from by omega, show n + 5 + 1 = n + 6 from by omega] at h7
      rw [show n + 6 + 2 = n + 8 from by omega, show n + 6 + 1 = n + 7 from by omega] at h8
      have hkey : Nat.fib (n + 8) = 21 * Nat.fib (n + 1) + 13 * Nat.fib n := by linarith
      rw [hkey] at h
      have h13fn : 7 ∣ 13 * Nat.fib n := by omega
      have hfn : 7 ∣ Nat.fib n :=
        Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 7 13) h13fn
      have := ih n (by omega) hfn
      omega

/-- 8 ∣ n → 7 ∣ F_n. -/
private theorem fib_seven_dvd_of_eight_dvd (n : Nat) (h : 8 ∣ n) : 7 ∣ Nat.fib n := by
  obtain ⟨k, rfl⟩ := h
  exact dvd_trans (show (7 : Nat) ∣ Nat.fib 8 from by native_decide)
    (Nat.fib_dvd 8 (8 * k) ⟨k, rfl⟩)

/-- Pisano entry point mod 7 is 8: 7 | F_n ↔ 8 | n. -/
theorem fib_seven_dvd_iff (n : Nat) : 7 ∣ Nat.fib n ↔ 8 ∣ n :=
  ⟨eight_dvd_of_fib_seven_dvd n, fib_seven_dvd_of_eight_dvd n⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 184
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci addition formula: F_{m+n+1} = F_{m+1}·F_{n+1} + F_m·F_n. -/
theorem fib_add_formula (m n : Nat) :
    Nat.fib (m + n + 1) = Nat.fib (m + 1) * Nat.fib (n + 1) + Nat.fib m * Nat.fib n := by
  rw [Nat.fib_add m n, Nat.add_comm]

-- ══════════════════════════════════════════════════════════════
-- Phase 185
-- ══════════════════════════════════════════════════════════════

/-- F_{n+1}² - F_n² = F_{n-1} · F_{n+2} for n ≥ 1. -/
theorem fib_sq_sub_sq (n : Nat) (hn : 1 ≤ n) :
    Nat.fib (n + 1) ^ 2 - Nat.fib n ^ 2 = Nat.fib (n - 1) * Nat.fib (n + 2) := by
  -- F_{n+2} = F_{n+1} + F_n, F_{n+1} = F_n + F_{n-1}
  have h_add2 := Nat.fib_add_two (n := n)
  rw [show n + 2 = n + 2 from rfl, show n + 1 = n + 1 from rfl] at h_add2
  have h_add1 := Nat.fib_add_two (n := n - 1)
  rw [show n - 1 + 2 = n + 1 from by omega, show n - 1 + 1 = n from by omega] at h_add1
  -- F_{n+1} = F_{n-1} + F_n, so F_{n+1}^2 - F_n^2 = F_{n-1}*(F_{n-1}+2*F_n)
  -- F_{n+2} = F_n + F_{n+1} = F_{n-1} + 2*F_n, so RHS = F_{n-1}*(F_{n-1}+2*F_n)
  -- Rewrite as equality with addition (no subtraction)
  suffices Nat.fib (n + 1) ^ 2 =
      Nat.fib n ^ 2 + Nat.fib (n - 1) * Nat.fib (n + 2) by omega
  -- F_{n+1} = F_{n-1} + F_n, F_{n+2} = F_n + F_{n+1} = F_n + F_{n-1} + F_n = 2F_n + F_{n-1}
  have h_n2 : Nat.fib (n + 2) = 2 * Nat.fib n + Nat.fib (n - 1) := by linarith
  rw [h_add1, h_n2]; ring

-- ══════════════════════════════════════════════════════════════
-- Phase 187
-- ══════════════════════════════════════════════════════════════

/-- F_{n+2} - F_{n+1} = F_n. -/
theorem fib_succ_sub (n : Nat) :
    Nat.fib (n + 2) - Nat.fib (n + 1) = Nat.fib n := by
  have h := Nat.fib_add_two (n := n); omega

-- ══════════════════════════════════════════════════════════════
-- Phase 188
-- ══════════════════════════════════════════════════════════════

/-- Σ_{k<n} F_{k+2}² = F_{n+1}·F_{n+2} - 1. -/
theorem fib_sq_sum_shifted (n : Nat) :
    ∑ k ∈ Finset.range n, Nat.fib (k + 2) ^ 2 = Nat.fib (n + 1) * Nat.fib (n + 2) - 1 := by
  -- Σ_{k<n} F_{k+2}^2 = Σ_{j=1}^{n} F_{j+1}^2 = (Σ_{j<n+1} F_{j+1}^2) - F_1^2
  have hsq : ∑ k ∈ Finset.range (n + 1), Nat.fib (k + 1) ^ 2 =
      Nat.fib (n + 1) * Nat.fib (n + 2) := fib_sq_sum (n + 1)
  have hshift : ∑ k ∈ Finset.range n, Nat.fib (k + 2) ^ 2 =
      ∑ k ∈ Finset.range (n + 1), Nat.fib (k + 1) ^ 2 - Nat.fib 1 ^ 2 := by
    rw [Finset.sum_range_succ' (f := fun k => Nat.fib (k + 1) ^ 2)]
    simp [Nat.fib]
  rw [hshift, hsq]
  simp [Nat.fib]

-- ══════════════════════════════════════════════════════════════
-- Phase 189
-- ══════════════════════════════════════════════════════════════

/-- F_n < F_{n+1} for n ≥ 2. -/
theorem fib_strict_mono (n : Nat) (hn : 2 ≤ n) : Nat.fib n < Nat.fib (n + 1) := by
  have h := Nat.fib_add_two (n := n - 1)
  rw [show n - 1 + 2 = n + 1 from by omega, show n - 1 + 1 = n from by omega] at h
  have := fib_succ_pos (n - 2)
  rw [show n - 2 + 1 = n - 1 from by omega] at this
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase 190
-- ══════════════════════════════════════════════════════════════

/-- Cassini-Pell for fenceDet: D_{k+1}·D_{k-1} = D_k² + 1.
    prop:pom-Lk-det-cassini-pell at t=1. -/
theorem fenceDet_cassini (k : Nat) (hk : 1 ≤ k) :
    fenceDet (k + 1) * fenceDet (k - 1) = fenceDet k ^ 2 + 1 := by
  -- Equivalent addition form: D(k)^2 + 1 = D(k+1)*D(k-1)
  suffices h : fenceDet k ^ 2 + 1 = fenceDet (k + 1) * fenceDet (k - 1) by omega
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  -- Goal: D(k+1)^2 + 1 = D(k+2)*D(k)
  induction k with
  | zero => simp [fenceDet]
  | succ k ih =>
    -- IH: D(k+1)^2 + 1 = D(k+2)*D(k)
    -- Goal: D(k+2)^2 + 1 = D(k+3)*D(k+1)
    -- Strategy: show both sides equal 3*D(k+2)*D(k+1) - D(k+1)^2
    -- where D(k+1)^2 = D(k+2)*D(k) - 1 (from IH)
    -- and D(k+3) = 3*D(k+2) - D(k+1), D(k+2) = 3*D(k+1) - D(k)
    have hrec_add : fenceDet (k + 3) + fenceDet (k + 1) = 3 * fenceDet (k + 2) := by
      show 3 * fenceDet (k + 2) - fenceDet (k + 1) + fenceDet (k + 1) = 3 * fenceDet (k + 2)
      have : fenceDet (k + 1) ≤ fenceDet (k + 2) := by
        simp only [fenceDet_eq_fib]; exact Nat.fib_mono (by omega)
      omega
    have hrec2_add : fenceDet (k + 2) + fenceDet k = 3 * fenceDet (k + 1) := by
      show 3 * fenceDet (k + 1) - fenceDet k + fenceDet k = 3 * fenceDet (k + 1)
      have : fenceDet k ≤ fenceDet (k + 1) := by
        simp only [fenceDet_eq_fib]; exact Nat.fib_mono (by omega)
      omega
    -- Prove: D(k+2)^2 + D(k+2)*D(k) = 3*D(k+1)*D(k+2)
    -- Because D(k+2) + D(k) = 3*D(k+1), so D(k+2)*(D(k+2)+D(k)) = 3*D(k+1)*D(k+2)
    have hlhs : fenceDet (k + 2) ^ 2 + fenceDet (k + 2) * fenceDet k =
        3 * fenceDet (k + 1) * fenceDet (k + 2) := by nlinarith
    -- Prove: D(k+3)*D(k+1) + D(k+1)^2 = 3*D(k+1)*D(k+2)
    -- Because D(k+3)+D(k+1) = 3*D(k+2), so D(k+1)*(D(k+3)+D(k+1)) = 3*D(k+1)*D(k+2)
    have hrhs : fenceDet (k + 3) * fenceDet (k + 1) + fenceDet (k + 1) ^ 2 =
        3 * fenceDet (k + 1) * fenceDet (k + 2) := by nlinarith
    -- So D(k+2)^2 + D(k+2)*D(k) = D(k+3)*D(k+1) + D(k+1)^2
    -- And D(k+1)^2 + 1 = D(k+2)*D(k) (IH), so D(k+2)*D(k) = D(k+1)^2 + 1
    -- D(k+2)^2 + (D(k+1)^2+1) = D(k+3)*D(k+1) + D(k+1)^2
    -- D(k+2)^2 + 1 = D(k+3)*D(k+1). ✓
    rw [show k + 1 + 1 = k + 2 from by omega, show k + 1 - 1 = k from by omega] at ih
    have hih := ih (by omega)
    -- From hlhs = hrhs and hih:
    -- D(k+2)^2 + D(k+2)*D(k) = D(k+3)*D(k+1) + D(k+1)^2
    -- D(k+2)*D(k) = D(k+1)^2 + 1
    -- → D(k+2)^2 + D(k+1)^2 + 1 = D(k+3)*D(k+1) + D(k+1)^2
    -- → D(k+2)^2 + 1 = D(k+3)*D(k+1)
    show fenceDet (k + 2) ^ 2 + 1 = fenceDet (k + 3) * fenceDet k.succ
    linarith

/-- CRT minimum depth: 30|F_n ↔ 60|n.
    prop:crt-235-min-depth -/
theorem crt_235_min_depth :
    (30 ∣ Nat.fib 60) ∧ (∀ n, 0 < n → n < 60 → ¬(30 ∣ Nat.fib n)) := by
  constructor
  · -- 30 = 2*3*5. 2|F_60 (3|60), 3|F_60 (4|60), 5|F_60 (5|60)
    have h2 : 2 ∣ Nat.fib 60 := fib_even_of_three_dvd 60 ⟨20, by omega⟩
    have h3 : 3 ∣ Nat.fib 60 := (fib_div_three_iff 60).mpr ⟨15, by omega⟩
    have h5 : 5 ∣ Nat.fib 60 := (fib_five_dvd_iff 60).mpr ⟨12, by omega⟩
    -- 30 = 2*3*5 with pairwise coprime factors
    have : 6 ∣ Nat.fib 60 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h2 h3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) this h5
  · -- 30|F_n → 2|F_n ∧ 3|F_n ∧ 5|F_n → 3|n ∧ 4|n ∧ 5|n → 60|n
    intro n hn hlt h30
    have h2 : 2 ∣ Nat.fib n := dvd_trans ⟨15, by omega⟩ h30
    have h3 : 3 ∣ Nat.fib n := dvd_trans ⟨10, by omega⟩ h30
    have h5 : 5 ∣ Nat.fib n := dvd_trans ⟨6, by omega⟩ h30
    have hn3 : 3 ∣ n := (fib_even_iff_three_dvd n).mp h2
    have hn4 : 4 ∣ n := (fib_div_three_iff n).mp h3
    have hn5 : 5 ∣ n := (fib_five_dvd_iff n).mp h5
    -- 3|n, 4|n, 5|n → lcm(3,4,5) = 60 | n
    have h12 : 12 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) hn3 hn4
    have h60 : 60 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h12 hn5
    omega

-- ══════════════════════════════════════════════════════════════
-- Phase 191
-- ══════════════════════════════════════════════════════════════

/-- The fence det polynomial at t=0. prop:pom-Lk-det-coeff-binomial (endpoint). -/
def fenceDetZero : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * fenceDetZero (n + 1) - fenceDetZero n

/-- prop:pom-Lk-det-coeff-binomial -/
theorem fenceDetZero_eq_one (k : Nat) : fenceDetZero k = 1 := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 => simp [fenceDetZero, ih (k + 1) (by omega), ih k (by omega)]

/-- Strict log-convexity: D_k² < D_{k-1}·D_{k+1} for k ≥ 1.
    /-- cor:pom-Lk-det-logconvex-ratio -/
    cor:pom-Lk-det-logconvex-ratio. -/
theorem fenceDet_log_convex (k : Nat) (hk : 1 ≤ k) :
    fenceDet k ^ 2 < fenceDet (k - 1) * fenceDet (k + 1) := by
  have h := fenceDet_cassini k hk
  rw [mul_comm]; omega

/-- fenceDet k ≥ 1 for all k. prop:pom-Lk-det-coeff-binomial (positivity). -/
theorem fenceDet_pos (k : Nat) : 1 ≤ fenceDet k := by
  rw [fenceDet_eq_fib]; exact Nat.fib_pos.mpr (by omega)

-- ══════════════════════════════════════════════════════════════
-- Phase 193 — POM 500 milestone
-- ══════════════════════════════════════════════════════════════

/-- fenceDet is monotone: D_k ≤ D_{k+1}. -/
private theorem fenceDet_mono (k : Nat) : fenceDet k ≤ fenceDet (k + 1) := by
  simp only [fenceDet_eq_fib]; exact Nat.fib_mono (by omega)

/-- fenceDet growth: D_{k+1} ≥ 2·D_k for k ≥ 1. cor:pom-Lk-surface-free-energy. -/
theorem fenceDet_double_lower (k : Nat) (hk : 1 ≤ k) :
    2 * fenceDet k ≤ fenceDet (k + 1) := by
  -- D(k+1) = 3·D(k) - D(k-1) ≥ 3·D(k) - D(k) = 2·D(k)
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hrec : fenceDet (k + 2) + fenceDet k = 3 * fenceDet (k + 1) := by
    show 3 * fenceDet (k + 1) - fenceDet k + fenceDet k = 3 * fenceDet (k + 1)
    have := fenceDet_mono k; omega
  have hmono := fenceDet_mono k
  linarith

/-- F_6 and F_8 are coprime. prop:crt-235-min-depth framework. -/
theorem fib_six_eight_coprime : Nat.Coprime (Nat.fib 6) (Nat.fib 8) := by
  rw [Nat.Coprime, fib_gcd]; native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase 194
-- ══════════════════════════════════════════════════════════════

/-- fenceDet strictly increasing: D_k < D_{k+1} for k ≥ 1.
    cor:pom-Lk-surface-free-energy -/
theorem fenceDet_strict_mono (k : Nat) (hk : 1 ≤ k) :
    fenceDet k < fenceDet (k + 1) := by
  have h := fenceDet_double_lower k hk
  have hp := fenceDet_pos k
  linarith

/-- 8 ∣ F_n → 6 ∣ n (Pisano entry point mod 8 is 6). -/
private theorem six_dvd_of_fib_eight_dvd (n : Nat) (h : 8 ∣ Nat.fib n) : 6 ∣ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => exact dvd_zero 6
    | 1 => simp [Nat.fib] at h
    | 2 => simp [Nat.fib] at h
    | 3 => simp [Nat.fib] at h
    | 4 => simp [Nat.fib] at h
    | 5 => simp [Nat.fib] at h
    | n + 6 =>
      -- F(n+6) = 8*F(n+1) + 5*F(n)
      have h2 := Nat.fib_add_two (n := n)
      have h3 := Nat.fib_add_two (n := n + 1)
      have h4 := Nat.fib_add_two (n := n + 2)
      have h5 := Nat.fib_add_two (n := n + 3)
      have h6 := Nat.fib_add_two (n := n + 4)
      rw [show n + 1 + 2 = n + 3 from by omega, show n + 1 + 1 = n + 2 from by omega] at h3
      rw [show n + 2 + 2 = n + 4 from by omega, show n + 2 + 1 = n + 3 from by omega] at h4
      rw [show n + 3 + 2 = n + 5 from by omega, show n + 3 + 1 = n + 4 from by omega] at h5
      rw [show n + 4 + 2 = n + 6 from by omega, show n + 4 + 1 = n + 5 from by omega] at h6
      have hkey : Nat.fib (n + 6) = 8 * Nat.fib (n + 1) + 5 * Nat.fib n := by linarith
      rw [hkey] at h
      have h5fn : 8 ∣ 5 * Nat.fib n := by omega
      have hfn : 8 ∣ Nat.fib n :=
        Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 8 5) h5fn
      have := ih n (by omega) hfn
      omega

/-- 6 ∣ n → 8 ∣ F_n. -/
private theorem fib_eight_dvd_of_six_dvd (n : Nat) (h : 6 ∣ n) : 8 ∣ Nat.fib n := by
  obtain ⟨k, rfl⟩ := h
  exact dvd_trans (show (8 : Nat) ∣ Nat.fib 6 from by native_decide)
    (Nat.fib_dvd 6 (6 * k) ⟨k, rfl⟩)

/-- Pisano entry point mod 8 is 6: 8 | F_n ↔ 6 | n. -/
theorem fib_eight_dvd_iff (n : Nat) : 8 ∣ Nat.fib n ↔ 6 ∣ n :=
  ⟨six_dvd_of_fib_eight_dvd n, fib_eight_dvd_of_six_dvd n⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 195
-- ══════════════════════════════════════════════════════════════

/-- D_k ≤ 3^k. cor:pom-Lk-surface-free-energy (upper bound). -/
theorem fenceDet_le_pow_three (k : Nat) : fenceDet k ≤ 3 ^ k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => simp [fenceDet]
    | 1 => simp [fenceDet]
    | k + 2 =>
      have ih1 := ih (k + 1) (by omega)
      calc fenceDet (k + 2)
          ≤ 3 * fenceDet (k + 1) := by
            have : fenceDet (k + 2) = 3 * fenceDet (k + 1) - fenceDet k := rfl
            have := fenceDet_mono k; omega
        _ ≤ 3 * 3 ^ (k + 1) := Nat.mul_le_mul_left 3 ih1
        _ = 3 ^ (k + 2) := by ring

/-- F_a | F_b ↔ a | b for a ≥ 3 (where F_a ≥ 2 ensures injectivity).
    prop:crt-235-min-depth -/
theorem fib_dvd_iff (a b : Nat) (ha : 3 ≤ a) : Nat.fib a ∣ Nat.fib b ↔ a ∣ b := by
  constructor
  · intro hdvd
    have hgcd_fib : Nat.fib (Nat.gcd a b) = Nat.fib a := by
      rw [← fib_gcd]; exact Nat.gcd_eq_left hdvd
    have hgcd_le : Nat.gcd a b ≤ a := Nat.gcd_le_left b (by omega)
    -- gcd(a,b) = a by Fibonacci strict monotonicity (a ≥ 3 → F injective)
    have heq : Nat.gcd a b = a := by
      by_contra hne
      have hlt : Nat.gcd a b < a := Nat.lt_of_le_of_ne hgcd_le hne
      have : Nat.fib (Nat.gcd a b) < Nat.fib a := by
        calc Nat.fib (Nat.gcd a b) ≤ Nat.fib (a - 1) := Nat.fib_mono (by omega)
          _ < Nat.fib a := by
              rw [show a = (a - 1) + 1 from by omega]
              exact fib_strict_mono (a - 1) (by omega)
      omega
    exact heq ▸ Nat.gcd_dvd_right a b
  · exact Nat.fib_dvd a b

-- ══════════════════════════════════════════════════════════════
-- Phase 196
-- ══════════════════════════════════════════════════════════════

/-- 2^k ≤ D_k for k ≥ 1. Completes 2^k ≤ D_k ≤ 3^k sandwich.
    cor:pom-Lk-surface-free-energy -/
theorem fenceDet_ge_pow_two (k : Nat) (hk : 1 ≤ k) : 2 ^ k ≤ fenceDet k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [fenceDet]
    | succ k =>
      calc 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
        _ ≤ 2 * fenceDet (k + 1) := Nat.mul_le_mul_left 2 (ih (by omega))
        _ ≤ fenceDet (k + 2) := fenceDet_double_lower (k + 1) (by omega)

/-- Unified Pisano entry point table for p=2,3,5,7,8.
    prop:crt-235-min-depth -/
theorem pisano_entry_point_table :
    (∀ n, 2 ∣ Nat.fib n ↔ 3 ∣ n) ∧
    (∀ n, 3 ∣ Nat.fib n ↔ 4 ∣ n) ∧
    (∀ n, 5 ∣ Nat.fib n ↔ 5 ∣ n) ∧
    (∀ n, 7 ∣ Nat.fib n ↔ 8 ∣ n) ∧
    (∀ n, 8 ∣ Nat.fib n ↔ 6 ∣ n) :=
  ⟨fib_even_iff_three_dvd, fib_div_three_iff, fib_five_dvd_iff,
   fib_seven_dvd_iff, fib_eight_dvd_iff⟩

-- ══════════════════════════════════════════════════════════════
-- Phase 197
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci Pell quadratic form: F_{k+1}² - F_{k+1}·F_k - F_k² = (-1)^k.
    prop:pom-fib-pell-quadratic-characterization (direction 1⇒2). -/
theorem fib_pell_quadratic (k : Nat) (hk : 1 ≤ k) :
    (Nat.fib (k + 1) : ℤ) ^ 2 - (Nat.fib (k + 1) : ℤ) * Nat.fib k -
    (Nat.fib k : ℤ) ^ 2 = (-1 : ℤ) ^ k := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  induction k with
  | zero => simp [Nat.fib]
  | succ k ih =>
    have ih' := ih (by omega)
    -- F_{k+3} = F_{k+1} + F_{k+2}
    have h1 := Nat.fib_add_two (n := k + 1)
    rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl] at h1
    have hcast : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      exact_mod_cast h1
    -- Goal: F_{k+3}² - F_{k+3}·F_{k+2} - F_{k+2}² = (-1)^(k+2)
    -- = (F_{k+1}+F_{k+2})² - (F_{k+1}+F_{k+2})·F_{k+2} - F_{k+2}²
    -- = F_{k+1}² + F_{k+1}·F_{k+2} - F_{k+2}²
    -- = -(F_{k+2}² - F_{k+2}·F_{k+1} - F_{k+1}²) = -(-1)^(k+1) = (-1)^(k+2)
    rw [show k + 1 + 1 + 1 = k + 3 from by omega, show k + 1 + 1 = k + 2 from by omega]
    rw [hcast]
    have hpow : (-1 : ℤ) ^ (k + 2) = -(-1) ^ (k + 1) := by ring
    rw [hpow]; linarith

/-- Fibonacci Pell scaled: (2·F_{k+1})² - (2·F_{k+1})·(2·F_k) - (2·F_k)² = 4·(-1)^k.
    prop:pom-fib-pell-quadratic-characterization (scaling corollary). -/
theorem fib_pell_quadratic_scaled (k : Nat) (hk : 1 ≤ k) :
    (2 * Nat.fib (k + 1) : ℤ) ^ 2 - (2 * Nat.fib (k + 1) : ℤ) * (2 * Nat.fib k) -
    (2 * Nat.fib k : ℤ) ^ 2 = 4 * (-1 : ℤ) ^ k := by
  have h := fib_pell_quadratic k hk
  nlinarith

/-- Fibonacci cross-product identity: F_{k+1}·F_{k-1} + F_k·F_{k+1} = F_{k+1}².
    Auxiliary for Pell-Fibonacci bridge.
    bridge:fib-cross-product -/
theorem fib_cross_product (k : Nat) (hk : 1 ≤ k) :
    (Nat.fib (k + 1) : ℤ) * Nat.fib (k - 1) + (Nat.fib k : ℤ) * Nat.fib (k + 1) =
    (Nat.fib (k + 1) : ℤ) ^ 2 := by
  -- F_{k-1} = F_{k+1} - F_k, so LHS = F_{k+1}·(F_{k+1} - F_k) + F_k·F_{k+1} = F_{k+1}²
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [show j + 1 - 1 = j from by omega, show j + 1 + 1 = j + 2 from by omega]
  have h := Nat.fib_add_two (n := j)
  -- F_{j+2} = F_j + F_{j+1}, so F_j = F_{j+2} - F_{j+1}
  have hfj : (Nat.fib j : ℤ) = Nat.fib (j + 2) - Nat.fib (j + 1) := by omega
  rw [hfj]; ring

-- ══════════════════════════════════════════════════════════════
-- Phase 201: Fibonacci tail matrix determinant
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci tail matrix G_m has det = 1 when m is even:
    F(m+3)^2 = F(m+2)*F(m+4) + 1.
    prop:fib-tail-reversibility -/
theorem fib_tail_matrix_det_even (m : Nat) (hm : Even m) :
    Nat.fib (m + 3) ^ 2 = Nat.fib (m + 2) * Nat.fib (m + 4) + 1 := by
  -- Cassini even: F(n)*F(n+2) + 1 = F(n+1)^2 for even n.
  -- Apply with n = m+2 (even since m is even): F(m+2)*F(m+4) + 1 = F(m+3)^2.
  have heven : Even (m + 2) := by obtain ⟨k, rfl⟩ := hm; exact ⟨k + 1, by omega⟩
  exact (fib_cassini_even (m + 2) heven).symm

/-- Fibonacci tail matrix G_m has det = -1 when m is odd:
    F(m+2)*F(m+4) = F(m+3)^2 + 1.
    prop:fib-tail-reversibility -/
theorem fib_tail_matrix_det_odd (m : Nat) (hm : ¬ Even m) :
    Nat.fib (m + 2) * Nat.fib (m + 4) = Nat.fib (m + 3) ^ 2 + 1 := by
  -- Cassini odd: F(n)*F(n+2) = F(n+1)^2 + 1 for odd n.
  -- Apply with n = m+2 (odd since m is odd).
  have hodd : ¬ Even (m + 2) := by intro ⟨k, hk⟩; exact hm ⟨k - 1, by omega⟩
  exact fib_cassini_odd (m + 2) hodd

-- ══════════════════════════════════════════════════════════════
-- Phase 203: Fibonacci subtraction + coprimality
-- ══════════════════════════════════════════════════════════════

/-- F(n+2) - F(n+1) = F(n), the Fibonacci subtraction identity.
    thm:bdry-uplift-second-difference-residual-law -/
theorem fib_sub_consecutive (n : Nat) :
    Nat.fib (n + 2) - Nat.fib (n + 1) = Nat.fib n := by
  have h := Nat.fib_add_two (n := n); omega

/-- F(11) - F(10) = F(9) = 34.
    thm:bdry-uplift-second-difference-residual-law (m=7) -/
theorem bdry_uplift_second_diff_m7 :
    Nat.fib 11 - Nat.fib 10 = Nat.fib 9 :=
  fib_sub_consecutive 9

/-- F(12) - F(11) = F(10) = 55.
    thm:bdry-uplift-second-difference-residual-law (m=8) -/
theorem bdry_uplift_second_diff_m8 :
    Nat.fib 12 - Nat.fib 11 = Nat.fib 10 :=
  fib_sub_consecutive 10

/-- Consecutive Fibonacci numbers are coprime: gcd(F(n), F(n+1)) = 1.
    bridge:fib-coprime-consecutive -/
theorem fib_coprime_consecutive_general (n : Nat) :
    Nat.gcd (Nat.fib n) (Nat.fib (n + 1)) = 1 :=
  fib_coprime_succ n

-- ══════════════════════════════════════════════════════════════
-- Phase 204: Fibonacci alternating skip sum
-- ══════════════════════════════════════════════════════════════

/-- Σ_{k < ⌊(n+1)/2⌋} F(n+1-2k) = F(n+2) - 1, the alternating skip Fibonacci sum.
    prop:fold-endpoint-Mm-minus-one-unique -/
theorem fib_alternating_skip_sum (n : Nat) :
    ∑ k ∈ Finset.range ((n + 1) / 2), Nat.fib (n + 1 - 2 * k) = Nat.fib (n + 2) - 1 := by
  -- Prove the "+1" version: ∑ + 1 = F(n+2), avoiding Nat subtraction on the RHS
  suffices h : ∑ k ∈ Finset.range ((n + 1) / 2), Nat.fib (n + 1 - 2 * k) + 1 = Nat.fib (n + 2) by
    omega
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => simp
  | 1 => simp []; rfl
  | n + 2 =>
    -- (n+3)/2 = (n+1)/2 + 1
    rw [show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 from by omega, Finset.sum_range_succ]
    -- Shift remaining terms: F(n+3-2k) = F((n+1-2k)+2) for k < (n+1)/2
    have hshift : ∀ k ∈ Finset.range ((n + 1) / 2),
        Nat.fib (n + 2 + 1 - 2 * k) = Nat.fib ((n + 1 - 2 * k) + 2) := by
      intro k hk; congr 1; have := Finset.mem_range.mp hk; omega
    rw [Finset.sum_congr rfl hshift]
    -- Expand F(a+2) = F(a) + F(a+1)
    have hexp : ∀ k ∈ Finset.range ((n + 1) / 2),
        Nat.fib ((n + 1 - 2 * k) + 2) =
          Nat.fib (n + 1 - 2 * k) + Nat.fib ((n + 1 - 2 * k) + 1) := by
      intro k _; exact Nat.fib_add_two
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib]
    -- First sub-sum = F(n+2) - 1 by IH(n)
    have ih_n := ih n (by omega)
    -- Second sub-sum: ∑_{k<(n+1)/2} F(n+1+1-2k)
    -- Shift to match IH(n+1): F((n+1-2k)+1) = F(n+1+1-2k) for k < (n+1)/2
    have hshift2 : ∀ k ∈ Finset.range ((n + 1) / 2),
        Nat.fib ((n + 1 - 2 * k) + 1) = Nat.fib (n + 1 + 1 - 2 * k) := by
      intro k hk; congr 1; have := Finset.mem_range.mp hk; omega
    rw [Finset.sum_congr rfl hshift2]
    -- IH(n+1): ∑_{k<(n+2)/2} F(n+2-2k) + 1 = F(n+3)
    have ih_n1 := ih (n + 1) (by omega)
    -- Normalize Fib indices to canonical form
    have hfib_n4 : Nat.fib (n + 2 + 2) = Nat.fib (n + 4) := by congr 1
    have hfib_n3a : Nat.fib (n + 2 + 1) = Nat.fib (n + 3) := by congr 1
    have hfib_n3b : Nat.fib (n + 1 + 2) = Nat.fib (n + 3) := by congr 1
    rw [hfib_n4]
    -- Relate our ∑_{k<(n+1)/2} F(n+2-2k) to ih_n1's ∑_{k<(n+2)/2} F(n+2-2k)
    rw [hfib_n3b] at ih_n1
    by_cases hpar : (n + 1 + 1) / 2 = (n + 1) / 2
    · -- odd n case: (n+2)/2 = (n+1)/2, ranges match directly
      rw [hpar] at ih_n1
      have htail : Nat.fib (n + 2 + 1 - 2 * ((n + 1) / 2)) = 1 := by
        have : n + 2 + 1 - 2 * ((n + 1) / 2) = 2 := by omega
        rw [this]; rfl
      rw [htail]
      have hfib : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
        have := Nat.fib_add_two (n := n + 2)
        rw [hfib_n4, hfib_n3a] at this; exact this
      omega
    · -- even n case: (n+2)/2 = (n+1)/2 + 1
      have hrng : (n + 1 + 1) / 2 = (n + 1) / 2 + 1 := by omega
      rw [hrng, Finset.sum_range_succ] at ih_n1
      have hextra : n + 1 + 1 - 2 * ((n + 1) / 2) = 2 := by omega
      rw [hextra] at ih_n1
      have hfib2 : Nat.fib 2 = 1 := rfl
      rw [hfib2] at ih_n1
      have htail : Nat.fib (n + 2 + 1 - 2 * ((n + 1) / 2)) = 2 := by
        have : n + 2 + 1 - 2 * ((n + 1) / 2) = 3 := by omega
        rw [this]; rfl
      rw [htail]
      have hfib : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
        have := Nat.fib_add_two (n := n + 2)
        rw [hfib_n4, hfib_n3a] at this; exact this
      omega

-- ══════════════════════════════════════════════════════════════
-- Phase 215: FenceDet additive recurrence and ratio bound
-- ══════════════════════════════════════════════════════════════

/-- FenceDet additive recurrence: D(k+1) + D(k-1) = 3*D(k).
    cor:pom-Lk-golden-coupling-unique -/
theorem fenceDet_additive (k : Nat) (hk : 1 ≤ k) :
    fenceDet (k + 1) + fenceDet (k - 1) = 3 * fenceDet k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [show j + 1 - 1 = j from by omega]
  -- fenceDet(j+2) = 3*fenceDet(j+1) - fenceDet(j) by definition
  -- So fenceDet(j+2) + fenceDet(j) = 3*fenceDet(j+1)
  show fenceDet (j + 2) + fenceDet j = 3 * fenceDet (j + 1)
  have hrec : fenceDet (j + 2) = 3 * fenceDet (j + 1) - fenceDet j := rfl
  have hmono : fenceDet j ≤ fenceDet (j + 1) := fenceDet_mono j
  omega

/-- FenceDet ratio bound: D(k+1) < 3*D(k).
    cor:pom-Lk-golden-coupling-unique -/
theorem fenceDet_succ_lt_triple (k : Nat) (hk : 1 ≤ k) :
    fenceDet (k + 1) < 3 * fenceDet k := by
  have hadd := fenceDet_additive k hk
  have hpos := fenceDet_pos (k - 1)
  omega

-- ══════════════════════════════════════════════════════════════
-- Phase R29: Fibonacci product convolution sum
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci convolution: 5·Σ_{i<n} F(i+1)·F(n-i) = n·F(n+1) + 2·(n+1)·F(n).
    prop:pom-fib-product-convolution -/
theorem fib_product_sum : ∀ n : Nat,
    5 * (Finset.range n).sum (fun i => Nat.fib (i + 1) * Nat.fib (n - i)) =
    n * Nat.fib (n + 1) + 2 * (n + 1) * Nat.fib n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    -- Key decomposition: S(n+2) = F(n+2) + Sn1_shifted + Sn
    -- where Sn1_shifted = Σ_{i<n+1} F(i+1)·F(n+1-i) = S(n+1)
    -- and Sn = Σ_{i<n} F(i+1)·F(n-i) = part of S(n)
    -- Step 1: peel off the last term i=n+1
    have hpeel : (Finset.range (n + 2)).sum (fun i => Nat.fib (i + 1) * Nat.fib (n + 2 - i)) =
        (Finset.range (n + 1)).sum (fun i => Nat.fib (i + 1) * Nat.fib (n + 2 - i)) +
        Nat.fib (n + 2) := by
      rw [Finset.sum_range_succ]; congr 1; simp [show n + 2 - (n + 1) = 1 from by omega]
    -- Step 2: for i < n+1, F(n+2-i) = F(n+1-i) + F(n-i) when n+2-i ≥ 2, i.e. i ≤ n
    -- But i < n+1 means i ≤ n, so n+2-i ≥ 2 always holds.
    have hfib_split : ∀ i ∈ Finset.range (n + 1),
        Nat.fib (i + 1) * Nat.fib (n + 2 - i) =
        Nat.fib (i + 1) * Nat.fib (n + 1 - i) + Nat.fib (i + 1) * Nat.fib (n - i) := by
      intro i hi
      have hiLt : i ≤ n := by have := Finset.mem_range.mp hi; omega
      rw [show n + 2 - i = (n - i) + 2 from by omega, Nat.fib_add_two,
        show n + 1 - i = (n - i) + 1 from by omega]; ring
    rw [hpeel, Finset.sum_congr rfl hfib_split, Finset.sum_add_distrib]
    -- Now goal: 5*(S(n+1) + S'(n) + F(n+2)) = ...
    -- S'(n) = Σ_{i<n+1} F(i+1)·F(n-i) = S(n) + F(n+1)·F(0) = S(n) + 0 = S(n)
    have hSn_eq : (Finset.range (n + 1)).sum (fun i => Nat.fib (i + 1) * Nat.fib (n - i)) =
        (Finset.range n).sum (fun i => Nat.fib (i + 1) * Nat.fib (n - i)) := by
      rw [Finset.sum_range_succ]
      simp
    rw [hSn_eq]
    -- IH
    have ih1 := fib_product_sum (n + 1)
    have ih0 := fib_product_sum n
    -- Fibonacci recurrence
    have hfib_n2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have hfib_n3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      have := Nat.fib_add_two (n := n + 1); rwa [show n + 1 + 2 = n + 3 from by omega] at this
    nlinarith

-- ══════════════════════════════════════════════════════════════
-- Phase R62
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci numbers at distance 2 are coprime: gcd(F_n, F_{n+2}) = 1.
    prop:pom-fib-coprime-triple -/
theorem fib_coprime_triple (n : Nat) :
    Nat.Coprime (Nat.fib n) (Nat.fib (n + 2)) := by
  rw [Nat.fib_add_two, Nat.Coprime, Nat.add_comm]
  rw [Nat.gcd_add_self_right]
  exact fib_coprime_succ n

/-- F_n + F_{n+1} = F_{n+2}, the Fibonacci recurrence in additive form.
    prop:pom-fib-add-fib-eq-fib-succ -/
theorem fib_add_fib_eq_fib_succ (n : Nat) :
    Nat.fib n + Nat.fib (n + 1) = Nat.fib (n + 2) :=
  (Nat.fib_add_two (n := n)).symm

-- ══════════════════════════════════════════════════════════════
-- Phase R101
-- ══════════════════════════════════════════════════════════════

/-- F(n+4) < F(n)² for n ≥ 6. Used for square residual rigidity.
    prop:pom-fib-sq-gt-fib-shift -/
theorem fib_sq_gt_fib_shift (n : Nat) (hn : 6 ≤ n) :
    Nat.fib (n + 4) < Nat.fib n ^ 2 := by
  -- Write n = 6 + k and induct on k
  obtain ⟨k, rfl⟩ : ∃ k, n = 6 + k := ⟨n - 6, by omega⟩
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => native_decide  -- F(10) = 55 < 64 = 8²
    | 1 => native_decide  -- F(11) = 89 < 169 = 13²
    | k + 2 =>
      -- IH at k and k+1: F(k+10) < F(k+6)² and F(k+11) < F(k+7)²
      have ih1 := ih k (by omega) (by omega)
      have ih2 := ih (k + 1) (by omega) (by omega)
      -- F(k+12) = F(k+11) + F(k+10)
      have hrec : Nat.fib (6 + (k + 2) + 4) = Nat.fib (6 + (k + 1) + 4) + Nat.fib (6 + k + 4) := by
        have := Nat.fib_add_two (n := 6 + k + 4)
        rw [show 6 + k + 4 + 2 = 6 + (k + 2) + 4 from by omega,
            show 6 + k + 4 + 1 = 6 + (k + 1) + 4 from by omega] at this
        linarith
      -- F(k+8) = F(k+7) + F(k+6)
      have hrec_n : Nat.fib (6 + (k + 2)) = Nat.fib (6 + (k + 1)) + Nat.fib (6 + k) := by
        have := Nat.fib_add_two (n := 6 + k)
        rw [show 6 + k + 2 = 6 + (k + 2) from by omega,
            show 6 + k + 1 = 6 + (k + 1) from by omega] at this
        linarith
      rw [hrec, hrec_n]
      nlinarith

/-- Vajda's identity: F(n+i)·F(n+j) - F(n)·F(n+i+j) = (-1)^n · F(i)·F(j).
    bridge:fibonacci-vajda-identity -/
theorem fib_vajda (n i j : Nat) :
    (Nat.fib (n + i) : ℤ) * Nat.fib (n + j) -
    (Nat.fib n : ℤ) * Nat.fib (n + i + j) =
    (-1) ^ n * (Nat.fib i : ℤ) * Nat.fib j := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Key identity: F(i)*F(j+1) + F(i+1)*F(j) - F(i+j) = F(i)*F(j)
    have hgZ : (Nat.fib (i + j) : ℤ) =
        Nat.fib i * Nat.fib (j + 1) + Nat.fib (i + 1) * Nat.fib j - Nat.fib i * Nat.fib j := by
      have h1 : Nat.fib (i + j + 2) = Nat.fib (i + j) + Nat.fib (i + j + 1) := Nat.fib_add_two
      have h2 : Nat.fib (i + j + 1) = Nat.fib i * Nat.fib j + Nat.fib (i + 1) * Nat.fib (j + 1) := Nat.fib_add i j
      have h3 := Nat.fib_add i (j + 1)
      rw [show i + (j + 1) + 1 = i + j + 2 from by omega, show j + 1 + 1 = j + 2 from by omega] at h3
      have h4 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
      -- h3: F(i+j+2) = F(i)*F(j+1) + F(i+1)*F(j+2)
      -- = F(i)*F(j+1) + F(i+1)*(F(j)+F(j+1))
      -- h1+h2: F(i+j+2) = F(i+j) + F(i)*F(j) + F(i+1)*F(j+1)
      -- Equating: F(i+j) + F(i)*F(j) + F(i+1)*F(j+1) = F(i)*F(j+1) + F(i+1)*F(j) + F(i+1)*F(j+1)
      -- F(i+j) = F(i)*F(j+1) + F(i+1)*F(j) - F(i)*F(j)
      nlinarith [h1, h2, h3, h4]
    -- Cassini at n
    have hcassini : (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 1) -
        (Nat.fib n : ℤ) ^ 2 = (-1) ^ n := by
      have hfn2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      by_cases heven : Even n
      · have hcas := fib_cassini_even n heven
        have : (-1 : ℤ) ^ n = 1 := Even.neg_one_pow heven
        nlinarith [hcas, hfn2]
      · have hcas := fib_cassini_odd n heven
        have : (-1 : ℤ) ^ n = -1 := Odd.neg_one_pow (Nat.not_even_iff_odd.mp heven)
        nlinarith [hcas, hfn2]
    -- Rewrite indices
    rw [show n + 1 + i = n + i + 1 from by omega,
        show n + 1 + j = n + j + 1 from by omega,
        show n + i + 1 + j = n + (i + j) + 1 from by omega]
    -- Use fib_add decompositions
    have ha := Nat.fib_add n i
    have hb := Nat.fib_add n j
    have hc' := Nat.fib_add n (i + j)
    have : (-1 : ℤ) ^ (n + 1) = -((-1) ^ n) := by ring
    -- Cast fib_add identities to ℤ
    have haZ : (Nat.fib (n + i + 1) : ℤ) = Nat.fib n * Nat.fib i +
        Nat.fib (n + 1) * Nat.fib (i + 1) := by linarith [ha]
    have hbZ : (Nat.fib (n + j + 1) : ℤ) = Nat.fib n * Nat.fib j +
        Nat.fib (n + 1) * Nat.fib (j + 1) := by linarith [hb]
    have hcZ : (Nat.fib (n + (i + j) + 1) : ℤ) = Nat.fib n * Nat.fib (i + j) +
        Nat.fib (n + 1) * Nat.fib (i + j + 1) := by linarith [hc']
    have hijZ : (Nat.fib (i + j + 1) : ℤ) = Nat.fib i * Nat.fib j +
        Nat.fib (i + 1) * Nat.fib (j + 1) := by linarith [Nat.fib_add i j]
    -- Step 1: algebraic identity (ring)
    have halg : (Nat.fib (n + i + 1) : ℤ) * Nat.fib (n + j + 1) -
        Nat.fib (n + 1) * Nat.fib (n + (i + j) + 1) =
        -((Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 1) -
        (Nat.fib n : ℤ) ^ 2) * Nat.fib i * Nat.fib j := by
      rw [haZ, hbZ, hcZ, hgZ, hijZ]; ring
    -- Step 2: substitute Cassini
    rw [this, halg, hcassini]

/-- F(n+5) = 5*F(n+1) + 3*F(n).
    bridge:fib-shift-5 -/
theorem fib_shift5 (n : Nat) : Nat.fib (n + 5) = 5 * Nat.fib (n + 1) + 3 * Nat.fib n := by
  -- F(n+2) = F(n)+F(n+1), F(n+3) = F(n+1)+F(n+2) = 2F(n+1)+F(n),
  -- F(n+4) = 3F(n+1)+2F(n), F(n+5) = 5F(n+1)+3F(n)
  have h2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have h3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  have h4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
  have h5 : Nat.fib (n + 5) = Nat.fib (n + 3) + Nat.fib (n + 4) := Nat.fib_add_two
  linarith

theorem fib_fourteen_eq : Nat.fib 14 = 377 := by native_decide

-- ══════════════════════════════════════════════════════════════
-- Phase R135: 2^m > F(m+2) for m >= 4
-- ══════════════════════════════════════════════════════════════

/-- 2^m > F(m+2) for m ≥ 4: full binary tree strictly exceeds golden-mean count.
    cor:discussion-horizon-boundarylayer-phi-scaling -/
theorem two_pow_gt_fib (m : Nat) (hm : 4 ≤ m) :
    Nat.fib (m + 2) < 2 ^ m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m, hm with
    | 4, _ => native_decide
    | 5, _ => native_decide
    | m + 6, _ =>
      have h1 := ih (m + 5) (by omega) (by omega)
      have h2 := ih (m + 4) (by omega) (by omega)
      have hfib : Nat.fib ((m + 6) + 2) = Nat.fib (m + 6) + Nat.fib ((m + 6) + 1) :=
        Nat.fib_add_two
      rw [show (m + 6) + 2 = m + 8 from by omega, show (m + 6) + 1 = m + 7 from by omega] at hfib
      have hpow : 2 ^ (m + 6) = 2 ^ (m + 5) + 2 ^ (m + 5) := by ring
      have hle : 2 ^ (m + 4) ≤ 2 ^ (m + 5) := Nat.pow_le_pow_right (by omega) (by omega)
      linarith

/-- Paper: cor:discussion-horizon-boundarylayer-phi-scaling -/
theorem paper_two_pow_gt_fib (m : Nat) (hm : 4 ≤ m) :
    Nat.fib (m + 2) < 2 ^ m :=
  two_pow_gt_fib m hm

-- ══════════════════════════════════════════════════════════════
-- Phase R140: Hidden bit count parity
-- ══════════════════════════════════════════════════════════════

/-- Parity of ⌊2^m/3⌋ for m=2..12: odd when m is even, even when m is odd.
    thm:pom-hidden-bit-count -/
theorem floor_pow_div3_parity_bounded (m : Nat) (hm1 : 2 ≤ m) (hm2 : m ≤ 12) :
    (2 ^ m / 3) % 2 = if Even m then 1 else 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm1
  have hk : k ≤ 10 := by omega
  -- Enumerate k = 0..10, m = 2..12
  match k, hk with
  | 0, _ => native_decide  | 1, _ => native_decide  | 2, _ => native_decide
  | 3, _ => native_decide  | 4, _ => native_decide  | 5, _ => native_decide
  | 6, _ => native_decide  | 7, _ => native_decide  | 8, _ => native_decide
  | 9, _ => native_decide  | 10, _ => native_decide
  | k + 11, hk => omega

/-- Paper: thm:pom-hidden-bit-count -/
theorem paper_floor_pow_div3_parity_bounded (m : Nat) (hm1 : 2 ≤ m) (hm2 : m ≤ 12) :
    (2 ^ m / 3) % 2 = if Even m then 1 else 0 :=
  floor_pow_div3_parity_bounded m hm1 hm2

-- ══════════════════════════════════════════════════════════════
-- Phase R148: Fibonacci mod 3 period
-- ══════════════════════════════════════════════════════════════

/-- Fibonacci numbers mod 3 have Pisano period 8: F(n+8) % 3 = F(n) % 3.
    def:pom-pisano-period-3 -/
theorem fib_mod3_period_eight (n : Nat) :
    Nat.fib (n + 8) % 3 = Nat.fib n % 3 := by
  -- F(n+8) = 21·F(n+1) + 13·F(n), so F(n+8) ≡ F(n) (mod 3)
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n + 1)
  have h3 := Nat.fib_add_two (n := n + 2)
  have h4 := Nat.fib_add_two (n := n + 3)
  have h5 := Nat.fib_add_two (n := n + 4)
  have h6 := Nat.fib_add_two (n := n + 5)
  have h7 := Nat.fib_add_two (n := n + 6)
  -- F(n+8) = 21·F(n+1) + 13·F(n)
  have hexp : Nat.fib (n + 8) = 21 * Nat.fib (n + 1) + 13 * Nat.fib n := by linarith
  rw [hexp]
  -- 21 = 7*3, 13 = 4*3 + 1
  have : 21 * Nat.fib (n + 1) + 13 * Nat.fib n =
    3 * (7 * Nat.fib (n + 1) + 4 * Nat.fib n) + Nat.fib n := by ring
  rw [this, Nat.mul_add_mod]

/-- Fibonacci mod 5 has Pisano period 20: F(n+20) % 5 = F(n) % 5.
    def:pom-pisano-period-5 -/
theorem fib_mod5_period_twenty (n : Nat) :
    Nat.fib (n + 20) % 5 = Nat.fib n % 5 := by
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n + 1)
  have h3 := Nat.fib_add_two (n := n + 2)
  have h4 := Nat.fib_add_two (n := n + 3)
  have h5 := Nat.fib_add_two (n := n + 4)
  have h6 := Nat.fib_add_two (n := n + 5)
  have h7 := Nat.fib_add_two (n := n + 6)
  have h8 := Nat.fib_add_two (n := n + 7)
  have h9 := Nat.fib_add_two (n := n + 8)
  have h10 := Nat.fib_add_two (n := n + 9)
  have h11 := Nat.fib_add_two (n := n + 10)
  have h12 := Nat.fib_add_two (n := n + 11)
  have h13 := Nat.fib_add_two (n := n + 12)
  have h14 := Nat.fib_add_two (n := n + 13)
  have h15 := Nat.fib_add_two (n := n + 14)
  have h16 := Nat.fib_add_two (n := n + 15)
  have h17 := Nat.fib_add_two (n := n + 16)
  have h18 := Nat.fib_add_two (n := n + 17)
  have h19 := Nat.fib_add_two (n := n + 18)
  have hexp : Nat.fib (n + 20) = 6765 * Nat.fib (n + 1) + 4181 * Nat.fib n := by linarith
  rw [hexp]
  have : 6765 * Nat.fib (n + 1) + 4181 * Nat.fib n =
    5 * (1353 * Nat.fib (n + 1) + 836 * Nat.fib n) + Nat.fib n := by ring
  rw [this, Nat.mul_add_mod]

/-- Fibonacci mod 7 has Pisano period 16: F(n+16) % 7 = F(n) % 7.
    def:pom-pisano-period-7 -/
theorem fib_mod7_period_sixteen (n : Nat) :
    Nat.fib (n + 16) % 7 = Nat.fib n % 7 := by
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n + 1)
  have h3 := Nat.fib_add_two (n := n + 2)
  have h4 := Nat.fib_add_two (n := n + 3)
  have h5 := Nat.fib_add_two (n := n + 4)
  have h6 := Nat.fib_add_two (n := n + 5)
  have h7 := Nat.fib_add_two (n := n + 6)
  have h8 := Nat.fib_add_two (n := n + 7)
  have h9 := Nat.fib_add_two (n := n + 8)
  have h10 := Nat.fib_add_two (n := n + 9)
  have h11 := Nat.fib_add_two (n := n + 10)
  have h12 := Nat.fib_add_two (n := n + 11)
  have h13 := Nat.fib_add_two (n := n + 12)
  have h14 := Nat.fib_add_two (n := n + 13)
  have h15 := Nat.fib_add_two (n := n + 14)
  -- F(n+16) = 987*F(n+1) + 610*F(n). 987 = 141*7, 610 = 87*7 + 1
  have hexp : Nat.fib (n + 16) = 987 * Nat.fib (n + 1) + 610 * Nat.fib n := by linarith
  rw [hexp]
  have : 987 * Nat.fib (n + 1) + 610 * Nat.fib n =
    7 * (141 * Nat.fib (n + 1) + 87 * Nat.fib n) + Nat.fib n := by ring
  rw [this, Nat.mul_add_mod]

/-- Fibonacci mod 4 has period 6: F(n+6) % 4 = F(n) % 4.
    def:pom-pisano-period-2 -/
theorem fib_mod4_period_six (n : Nat) :
    Nat.fib (n + 6) % 4 = Nat.fib n % 4 := by
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n + 1)
  have h3 := Nat.fib_add_two (n := n + 2)
  have h4 := Nat.fib_add_two (n := n + 3)
  have h5 := Nat.fib_add_two (n := n + 4)
  have hexp : Nat.fib (n + 6) = 8 * Nat.fib (n + 1) + 5 * Nat.fib n := by linarith
  rw [hexp]
  have : 8 * Nat.fib (n + 1) + 5 * Nat.fib n =
    4 * (2 * Nat.fib (n + 1) + Nat.fib n) + Nat.fib n := by ring
  rw [this, Nat.mul_add_mod]

/-- Fibonacci mod 8 has period 12: F(n+12) % 8 = F(n) % 8.
    def:pom-pisano-period-2 -/
theorem fib_mod8_period_twelve (n : Nat) :
    Nat.fib (n + 12) % 8 = Nat.fib n % 8 := by
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n + 1)
  have h3 := Nat.fib_add_two (n := n + 2)
  have h4 := Nat.fib_add_two (n := n + 3)
  have h5 := Nat.fib_add_two (n := n + 4)
  have h6 := Nat.fib_add_two (n := n + 5)
  have h7 := Nat.fib_add_two (n := n + 6)
  have h8 := Nat.fib_add_two (n := n + 7)
  have h9 := Nat.fib_add_two (n := n + 8)
  have h10 := Nat.fib_add_two (n := n + 9)
  have h11 := Nat.fib_add_two (n := n + 10)
  have hexp : Nat.fib (n + 12) = 144 * Nat.fib (n + 1) + 89 * Nat.fib n := by linarith
  rw [hexp]
  have : 144 * Nat.fib (n + 1) + 89 * Nat.fib n =
    8 * (18 * Nat.fib (n + 1) + 11 * Nat.fib n) + Nat.fib n := by ring
  rw [this, Nat.mul_add_mod]

/-- Fibonacci mod 9 has period 24: F(n+24) % 9 = F(n) % 9.
    def:pom-pisano-period-2 -/
theorem fib_mod9_period_twentyfour (n : Nat) :
    Nat.fib (n + 24) % 9 = Nat.fib n % 9 := by
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n + 1)
  have h3 := Nat.fib_add_two (n := n + 2)
  have h4 := Nat.fib_add_two (n := n + 3)
  have h5 := Nat.fib_add_two (n := n + 4)
  have h6 := Nat.fib_add_two (n := n + 5)
  have h7 := Nat.fib_add_two (n := n + 6)
  have h8 := Nat.fib_add_two (n := n + 7)
  have h9 := Nat.fib_add_two (n := n + 8)
  have h10 := Nat.fib_add_two (n := n + 9)
  have h11 := Nat.fib_add_two (n := n + 10)
  have h12 := Nat.fib_add_two (n := n + 11)
  have h13 := Nat.fib_add_two (n := n + 12)
  have h14 := Nat.fib_add_two (n := n + 13)
  have h15 := Nat.fib_add_two (n := n + 14)
  have h16 := Nat.fib_add_two (n := n + 15)
  have h17 := Nat.fib_add_two (n := n + 16)
  have h18 := Nat.fib_add_two (n := n + 17)
  have h19 := Nat.fib_add_two (n := n + 18)
  have h20 := Nat.fib_add_two (n := n + 19)
  have h21 := Nat.fib_add_two (n := n + 20)
  have h22 := Nat.fib_add_two (n := n + 21)
  have h23 := Nat.fib_add_two (n := n + 22)
  have hexp : Nat.fib (n + 24) = 46368 * Nat.fib (n + 1) + 28657 * Nat.fib n := by linarith
  rw [hexp]
  have : 46368 * Nat.fib (n + 1) + 28657 * Nat.fib n =
    9 * (5152 * Nat.fib (n + 1) + 3184 * Nat.fib n) + Nat.fib n := by ring
  rw [this, Nat.mul_add_mod]

/-- Fibonacci mod 11 has period 10: F(n+10) % 11 = F(n) % 11.
    def:pom-pisano-period-2 -/
theorem fib_mod11_period_ten (n : Nat) :
    Nat.fib (n + 10) % 11 = Nat.fib n % 11 := by
  have h1 := Nat.fib_add_two (n := n)
  have h2 := Nat.fib_add_two (n := n + 1)
  have h3 := Nat.fib_add_two (n := n + 2)
  have h4 := Nat.fib_add_two (n := n + 3)
  have h5 := Nat.fib_add_two (n := n + 4)
  have h6 := Nat.fib_add_two (n := n + 5)
  have h7 := Nat.fib_add_two (n := n + 6)
  have h8 := Nat.fib_add_two (n := n + 7)
  have h9 := Nat.fib_add_two (n := n + 8)
  have hexp : Nat.fib (n + 10) = 55 * Nat.fib (n + 1) + 34 * Nat.fib n := by linarith
  rw [hexp]
  have : 55 * Nat.fib (n + 1) + 34 * Nat.fib n =
    11 * (5 * Nat.fib (n + 1) + 3 * Nat.fib n) + Nat.fib n := by ring
  rw [this, Nat.mul_add_mod]

-- ══════════════════════════════════════════════════════════════
-- Phase R147: Fibonacci prime entry point
-- ══════════════════════════════════════════════════════════════

/-- For prime p dividing F(k), p divides F(n) iff k divides n.
    thm:conclusion-valuation-fib-gcd-instances -/
theorem fib_prime_entry_point (p k n : Nat) (_hp : Nat.Prime p) (hk : 1 ≤ k)
    (hentry : p ∣ Nat.fib k) (hmin : ∀ j, 1 ≤ j → j < k → ¬ (p ∣ Nat.fib j)) :
    p ∣ Nat.fib n ↔ k ∣ n := by
  constructor
  · -- (→) p | F(n) → k | n
    intro hpn
    -- p | gcd(F(k), F(n)) = F(gcd(k,n))
    have hgcd_dvd : p ∣ Nat.fib (Nat.gcd k n) := by
      rw [← fib_gcd]
      exact Nat.dvd_gcd hentry hpn
    -- gcd(k,n) ≤ k
    by_cases hn0 : n = 0
    · subst hn0; simp
    · have hgcd_pos : 0 < Nat.gcd k n := Nat.pos_of_ne_zero (by
        intro h; exact hn0 (Nat.eq_zero_of_gcd_eq_zero_right h))
      -- If gcd(k,n) < k, then by minimality, p ∤ F(gcd(k,n)), contradiction
      by_contra hndvd
      have hgcd_lt : Nat.gcd k n < k := by
        have hle := Nat.gcd_le_left n (by omega : 0 < k)
        exact Nat.lt_of_le_of_ne hle (fun h => hndvd (h ▸ Nat.gcd_dvd_right k n))
      exact hmin (Nat.gcd k n) (by omega) hgcd_lt hgcd_dvd
  · -- (←) k | n → p | F(n)
    intro hkn
    exact dvd_trans hentry (Nat.fib_dvd k n hkn)

end Omega
