import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Omega.Zeta.KilloSmithLossSpectrum

namespace Omega.Zeta

/-- Kernel-size closed form for a Smith diagonal with invariant factors `dᵢ` modulo `b`. -/
def killoKernelSizeGeneralModulus (n m b : ℕ) (invariantFactors : List ℕ) : ℕ :=
  b ^ (n - m) * (invariantFactors.map (Nat.gcd b)).prod

private lemma list_prod_gcd_prime_powers (p k : ℕ) :
    ∀ exponents : List ℕ,
      (exponents.map (fun e => Nat.gcd (p ^ k) (p ^ e))).prod =
        p ^ ((exponents.map fun e => min e k).sum)
  | [] => by simp
  | e :: es => by
      have hgcd : Nat.gcd (p ^ k) (p ^ e) = p ^ min e k := by
        by_cases hek : e ≤ k
        · rw [Nat.min_eq_left hek, Nat.gcd_eq_right (pow_dvd_pow p hek)]
        · have hke : k ≤ e := Nat.le_of_not_ge hek
          rw [Nat.min_eq_right hke, Nat.gcd_eq_left (pow_dvd_pow p hke)]
      rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, hgcd,
        list_prod_gcd_prime_powers p k es, Nat.pow_add]

/-- Paper label: `cor:killo-kernel-size-general-modulus`.
For the prime-power Smith spectrum coming from `paper_killo_smith_loss_spectrum`, the local
kernel size modulo `p^k` matches the Smith-spectrum count, and for an arbitrary modulus `b`
the kernel size is the free-variable factor `b^(n-m)` times the product of the coordinatewise
`gcd` contributions of the invariant factors. -/
theorem paper_killo_kernel_size_general_modulus (p n m : ℕ) (exponents : List ℕ) :
    (∀ k : ℕ,
      killoKernelSizeGeneralModulus n m (p ^ k) (exponents.map fun e => p ^ e) =
        smithFiberCardinality p n m k (exponents : Multiset ℕ)) ∧
    (∀ b : ℕ,
      killoKernelSizeGeneralModulus n m b (exponents.map fun e => p ^ e) =
        b ^ (n - m) * ((exponents.map fun e => Nat.gcd b (p ^ e)).prod)) := by
  refine ⟨?_, ?_⟩
  · intro k
    unfold killoKernelSizeGeneralModulus
    rw [List.map_map]
    have hmap :
        List.map ((Nat.gcd (p ^ k)) ∘ fun e => p ^ e) exponents =
          List.map (fun e => Nat.gcd (p ^ k) (p ^ e)) exponents := by
      simp [Function.comp]
    rw [hmap]
    calc
      (p ^ k) ^ (n - m) * (List.map (fun e => Nat.gcd (p ^ k) (p ^ e)) exponents).prod
          = p ^ (k * (n - m)) * p ^ ((exponents.map fun e => min e k).sum) := by
            rw [Nat.pow_mul, list_prod_gcd_prime_powers]
      _ = p ^ (k * (n - m) + (exponents.map fun e => min e k).sum) := by
            rw [← Nat.pow_add]
      _ = p ^ (k * (n - m) + smithEntropy (exponents : Multiset ℕ) k) := by
            simp [smithEntropy]
      _ = smithFiberCardinality p n m k (exponents : Multiset ℕ) := by
            symm
            simpa [smithFiberCardinality] using
              (paper_killo_smith_loss_spectrum p n m (exponents : Multiset ℕ)).1 k
  · intro b
    unfold killoKernelSizeGeneralModulus
    rw [List.map_map]
    have hmap :
        List.map (Nat.gcd b ∘ fun e => p ^ e) exponents =
          List.map (fun e => Nat.gcd b (p ^ e)) exponents := by
      simp [Function.comp]
    rw [hmap]

end Omega.Zeta
