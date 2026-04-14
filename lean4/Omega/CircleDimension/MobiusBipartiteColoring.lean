import Mathlib.Tactic
import Mathlib.Data.Nat.PrimeFin

namespace Omega.CircleDimension.MobiusBipartiteColoring

open Finset

/-- Number of distinct prime factors.
    cor:cdim-mobius-bipartite-coloring -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- Mobius sign: `(-1)^ω(n)`.
    cor:cdim-mobius-bipartite-coloring -/
def mobiusSign (n : ℕ) : ℤ := (-1) ^ omega n

/-- `(-1)^(n+1) = -(-1)^n`.
    cor:cdim-mobius-bipartite-coloring -/
theorem neg_one_pow_succ (n : ℕ) : (-1 : ℤ) ^ (n + 1) = - (-1) ^ n := by
  rw [pow_succ]; ring

/-- `ω(a·p) = ω(a) + 1` when `p` is prime and `p ∉ a.primeFactors`.
    cor:cdim-mobius-bipartite-coloring -/
theorem omega_mul_prime_of_not_dvd {a p : ℕ} (hp : p.Prime) (ha : a ≠ 0)
    (hpa : p ∉ a.primeFactors) :
    omega (a * p) = omega a + 1 := by
  unfold omega
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Nat.primeFactors_mul ha hp0]
  rw [Nat.Prime.primeFactors hp]
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_singleton_right]
    exact hpa)]
  simp

/-- Single prime flip inverts the Mobius sign.
    cor:cdim-mobius-bipartite-coloring -/
theorem paper_cdim_mobius_bipartite_coloring {a p : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hpa : p ∉ a.primeFactors) :
    mobiusSign (a * p) = - mobiusSign a := by
  unfold mobiusSign
  rw [omega_mul_prime_of_not_dvd hp ha hpa, neg_one_pow_succ]

-- Phase R611: Omega and Mobius sign seeds
-- ══════════════════════════════════════════════════════════════

/-- ω(1) = 0: 1 has no prime factors.
    cor:cdim-mobius-bipartite-coloring -/
theorem omega_one : omega 1 = 0 := by native_decide

/-- ω(p) = 1 for prime p.
    cor:cdim-mobius-bipartite-coloring -/
theorem omega_prime (p : ℕ) (hp : p.Prime) : omega p = 1 := by
  unfold omega; rw [Nat.Prime.primeFactors hp]; simp

/-- Omega seeds at small values.
    cor:cdim-mobius-bipartite-coloring -/
theorem omega_seeds :
    omega 1 = 0 ∧ omega 2 = 1 ∧ omega 3 = 1 ∧
    omega 6 = 2 ∧ omega 30 = 3 ∧ omega 210 = 4 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Mobius sign seeds.
    cor:cdim-mobius-bipartite-coloring -/
theorem mobiusSign_seeds :
    mobiusSign 1 = 1 ∧ mobiusSign 2 = -1 ∧ mobiusSign 3 = -1 ∧
    mobiusSign 6 = 1 ∧ mobiusSign 30 = -1 ∧ mobiusSign 210 = 1 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

/-- Double prime flip preserves Mobius sign: μ(a·p·q) = μ(a) when p,q are new primes.
    cor:cdim-mobius-bipartite-coloring -/
theorem mobiusSign_double_prime {a p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (ha : a ≠ 0) (hpa : p ∉ a.primeFactors) (hqa : q ∉ (a * p).primeFactors)
    (_hpq : p ≠ q) :
    mobiusSign (a * p * q) = mobiusSign a := by
  have hap : a * p ≠ 0 := Nat.mul_ne_zero ha hp.ne_zero
  unfold mobiusSign
  rw [omega_mul_prime_of_not_dvd hq hap hqa,
      omega_mul_prime_of_not_dvd hp ha hpa]
  simp [pow_succ]

/-- Paper package: Mobius bipartite coloring extended.
    cor:cdim-mobius-bipartite-coloring -/
theorem paper_cdim_mobius_bipartite_extended :
    (omega 1 = 0 ∧ omega 6 = 2 ∧ omega 30 = 3) ∧
    (mobiusSign 1 = 1 ∧ mobiusSign 6 = 1 ∧ mobiusSign 30 = -1) ∧
    (2 * 3 * 5 * 7 = 210 ∧ omega 210 = 4) := by
  refine ⟨⟨by native_decide, by native_decide, by native_decide⟩,
          ⟨by native_decide, by native_decide, by native_decide⟩,
          ⟨by omega, by native_decide⟩⟩

end Omega.CircleDimension.MobiusBipartiteColoring
