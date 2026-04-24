import Mathlib.Tactic

/-!
# Cyclic lift gcd-lcm factorization seeds

This file registers the paper-facing seed/package wrapper for
`prop:finite-part-cyclic-lift-gcd-lcm`.
-/

namespace Omega.Zeta.CyclicLiftGcdLcm

/-- Paper seed for the cyclic-lift gcd/lcm factorization.
    This packages the arithmetic identity `m * n = gcd(m,n) * lcm(m,n)`,
    which matches the orbit-count-times-orbit-length decomposition of the
    diagonal action on `ZMod m × ZMod n`.
    prop:finite-part-cyclic-lift-gcd-lcm -/
theorem paper_finite_part_cyclic_lift_gcd_lcm_seeds (m n : ℕ) :
    m * n = Nat.gcd m n * Nat.lcm m n := by
  exact (Nat.gcd_mul_lcm m n).symm

/-- Packaged form of the cyclic-lift gcd/lcm factorization seeds.
    prop:finite-part-cyclic-lift-gcd-lcm -/
theorem paper_finite_part_cyclic_lift_gcd_lcm_package (m n : ℕ) :
    m * n = Nat.gcd m n * Nat.lcm m n :=
  paper_finite_part_cyclic_lift_gcd_lcm_seeds m n

/-- Paper-facing cardinality form of the cyclic-lift gcd/lcm factorization: the product
`Fin m × Fin n` has the same cardinality as `gcd(m,n)` cycles of length `lcm(m,n)`.
    prop:finite-part-cyclic-lift-gcd-lcm -/
theorem paper_finite_part_cyclic_lift_gcd_lcm (m n : ℕ) :
    Fintype.card (Fin (Nat.gcd m n) × Fin (Nat.lcm m n)) = Fintype.card (Fin m × Fin n) := by
  rw [Fintype.card_prod, Fintype.card_prod]
  simpa using (paper_finite_part_cyclic_lift_gcd_lcm_package m n).symm

end Omega.Zeta.CyclicLiftGcdLcm
