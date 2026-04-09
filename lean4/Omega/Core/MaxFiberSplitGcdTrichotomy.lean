import Mathlib.Tactic

namespace Omega.POM

/-- `gcd(fib(k+1), fib k) = 1`: consecutive Fibonacci numbers are coprime.
    cor:pom-max-fiber-achievers-bsplit-gcd-trichotomy -/
theorem fib_gcd_succ_eq_one (k : ℕ) :
    Nat.gcd (Nat.fib (k + 1)) (Nat.fib k) = 1 := by
  have h : Nat.Coprime (Nat.fib k) (Nat.fib (k + 1)) := Nat.fib_coprime_fib_succ k
  exact h.symm

/-- `gcd(fib(k+1), fib(k+1)) = fib(k+1)`.
    cor:pom-max-fiber-achievers-bsplit-gcd-trichotomy -/
theorem fib_gcd_self (k : ℕ) :
    Nat.gcd (Nat.fib (k + 1)) (Nat.fib (k + 1)) = Nat.fib (k + 1) :=
  Nat.gcd_self _

/-- Biased split: `gcd(2·fib(k-1), 2·fib k) = 2` for `k ≥ 1`.
    cor:pom-max-fiber-achievers-bsplit-gcd-trichotomy -/
theorem fib_biased_gcd (k : ℕ) (hk : 1 ≤ k) :
    Nat.gcd (2 * Nat.fib (k - 1)) (2 * Nat.fib k) = 2 := by
  rw [Nat.gcd_mul_left]
  have hcop : Nat.gcd (Nat.fib (k - 1)) (Nat.fib k) = 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact Nat.fib_coprime_fib_succ j
  rw [hcop]

/-- Balanced split: `fib(k+1) + fib(k+1) = 2·fib(k+1)`.
    cor:pom-max-fiber-achievers-bsplit-gcd-trichotomy -/
theorem fib_balanced_sum (k : ℕ) :
    Nat.fib (k + 1) + Nat.fib (k + 1) = 2 * Nat.fib (k + 1) := by ring

/-- Even-length decomposition: `fib(k+1) + fib k = fib(k+2)`.
    cor:pom-max-fiber-achievers-bsplit-gcd-trichotomy -/
theorem D_even_eq_fib (k : ℕ) :
    Nat.fib (k + 1) + Nat.fib k = Nat.fib (k + 2) := by
  rw [Nat.fib_add_two, Nat.add_comm]

/-- Paper package: POM max-fiber achievers b-split gcd trichotomy.
    cor:pom-max-fiber-achievers-bsplit-gcd-trichotomy -/
theorem paper_pom_max_fiber_achievers_bsplit_gcd_trichotomy :
    (∀ k : ℕ, Nat.gcd (Nat.fib (k + 1)) (Nat.fib k) = 1) ∧
    (∀ k : ℕ, Nat.gcd (Nat.fib (k + 1)) (Nat.fib (k + 1)) = Nat.fib (k + 1)) ∧
    (∀ k : ℕ, 1 ≤ k → Nat.gcd (2 * Nat.fib (k - 1)) (2 * Nat.fib k) = 2) ∧
    (∀ k : ℕ, Nat.fib (k + 1) + Nat.fib (k + 1) = 2 * Nat.fib (k + 1)) ∧
    (∀ k : ℕ, Nat.fib (k + 1) + Nat.fib k = Nat.fib (k + 2)) ∧
    (Nat.gcd (Nat.fib 4) (Nat.fib 3) = 1) :=
  ⟨fib_gcd_succ_eq_one,
   fib_gcd_self,
   fib_biased_gcd,
   fib_balanced_sum,
   D_even_eq_fib,
   fib_gcd_succ_eq_one 3⟩

end Omega.POM
