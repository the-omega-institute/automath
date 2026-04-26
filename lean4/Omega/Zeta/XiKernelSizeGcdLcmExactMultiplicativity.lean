import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private lemma xi_kernel_size_gcd_lcm_exact_multiplicativity_min_min_max
    (a b c : ℕ) :
    min a (min b c) + min a (max b c) = min a b + min a c := by
  by_cases hbc : b ≤ c
  · simp [min_eq_left hbc, max_eq_right hbc]
  · have hcb : c ≤ b := le_of_not_ge hbc
    simp [min_eq_right hcb, max_eq_left hcb, add_comm]

private lemma xi_kernel_size_gcd_lcm_exact_multiplicativity_gcd_lcm_factor
    (a b c : ℕ) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.gcd a (Nat.gcd b c) * Nat.gcd a (Nat.lcm b c) =
      Nat.gcd a b * Nat.gcd a c := by
  by_cases ha : a = 0
  · subst ha
    simp [Nat.gcd_mul_lcm]
  · have hbc_gcd : Nat.gcd b c ≠ 0 := Nat.gcd_ne_zero_left hb
    have hbc_lcm : Nat.lcm b c ≠ 0 := Nat.lcm_ne_zero hb hc
    refine Nat.eq_of_factorization_eq ?_ ?_ fun p => ?_
    · exact mul_ne_zero (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left ha)
    · exact mul_ne_zero (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left ha)
    · rw [Nat.factorization_mul (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left ha),
        Nat.factorization_mul (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left ha),
        Nat.factorization_gcd ha hbc_gcd, Nat.factorization_gcd ha hbc_lcm,
        Nat.factorization_gcd ha hb, Nat.factorization_gcd ha hc,
        Nat.factorization_gcd hb hc, Nat.factorization_lcm hb hc]
      exact xi_kernel_size_gcd_lcm_exact_multiplicativity_min_min_max
        (a.factorization p) (b.factorization p) (c.factorization p)

/-- Paper label: `cor:xi-kernel-size-gcd-lcm-exact-multiplicativity`. -/
theorem paper_xi_kernel_size_gcd_lcm_exact_multiplicativity {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (r : ℕ) (κ : ℕ → ℕ)
    (hκ : ∀ b, κ b = b ^ r * ∏ i, Nat.gcd (d i) b) :
    ∀ b c, 1 ≤ b → 1 ≤ c →
      κ (Nat.gcd b c) * κ (Nat.lcm b c) = κ b * κ c := by
  intro b c hb hc
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hpow :
      (Nat.gcd b c) ^ r * (Nat.lcm b c) ^ r = b ^ r * c ^ r := by
    rw [← mul_pow, Nat.gcd_mul_lcm, mul_pow]
  have hprod :
      (∏ i, Nat.gcd (d i) (Nat.gcd b c)) *
          (∏ i, Nat.gcd (d i) (Nat.lcm b c)) =
        (∏ i, Nat.gcd (d i) b) * (∏ i, Nat.gcd (d i) c) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i _
    exact xi_kernel_size_gcd_lcm_exact_multiplicativity_gcd_lcm_factor (d i) b c hb0 hc0
  rw [hκ (Nat.gcd b c), hκ (Nat.lcm b c), hκ b, hκ c]
  calc
    ((Nat.gcd b c) ^ r * ∏ i, Nat.gcd (d i) (Nat.gcd b c)) *
        ((Nat.lcm b c) ^ r * ∏ i, Nat.gcd (d i) (Nat.lcm b c)) =
        ((Nat.gcd b c) ^ r * (Nat.lcm b c) ^ r) *
          ((∏ i, Nat.gcd (d i) (Nat.gcd b c)) *
            (∏ i, Nat.gcd (d i) (Nat.lcm b c))) := by
      ring
    _ = (b ^ r * c ^ r) * ((∏ i, Nat.gcd (d i) b) * (∏ i, Nat.gcd (d i) c)) := by
      rw [hpow, hprod]
    _ = (b ^ r * ∏ i, Nat.gcd (d i) b) * (c ^ r * ∏ i, Nat.gcd (d i) c) := by
      ring

end Omega.Zeta
