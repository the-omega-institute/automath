import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.EA.FibAdicTower

open Nat

/-- Tower indices: `n_k = 2^k`.
    def:fib-adic-ring -/
def n_k (k : ℕ) : ℕ := 2 ^ k

/-- Fibonacci tower moduli: `M_k = F_{2^k}`.
    def:fib-adic-ring -/
def M_k (k : ℕ) : ℕ := Nat.fib (n_k k)

/-- `2^k ∣ 2^(k+1)`.
    def:fib-adic-ring -/
theorem two_pow_dvd_succ (k : ℕ) : 2 ^ k ∣ 2 ^ (k + 1) :=
  pow_dvd_pow 2 (Nat.le_succ k)

/-- `n_k ∣ n_{k+1}`.
    def:fib-adic-ring -/
theorem n_k_dvd_succ (k : ℕ) : n_k k ∣ n_k (k + 1) := by
  unfold n_k
  exact two_pow_dvd_succ k

/-- `M_k ∣ M_{k+1}` (Fibonacci tower divisibility).
    def:fib-adic-ring -/
theorem M_k_dvd_succ (k : ℕ) : M_k k ∣ M_k (k + 1) := by
  unfold M_k
  exact Nat.fib_dvd _ _ (n_k_dvd_succ k)

/-- General divisibility along the tower: `k ≤ ℓ → M_k ∣ M_ℓ`.
    def:fib-adic-ring -/
theorem M_k_dvd_of_le (k ℓ : ℕ) (hkl : k ≤ ℓ) : M_k k ∣ M_k ℓ := by
  unfold M_k
  exact Nat.fib_dvd _ _ (pow_dvd_pow 2 hkl)

/-- Paper package: Fib-adic ring tower divisibility.
    def:fib-adic-ring -/
theorem paper_def_fib_adic_ring_divisibility (k : ℕ) : M_k k ∣ M_k (k + 1) :=
  M_k_dvd_succ k

end Omega.EA.FibAdicTower
