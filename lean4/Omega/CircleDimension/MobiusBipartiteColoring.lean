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

end Omega.CircleDimension.MobiusBipartiteColoring
