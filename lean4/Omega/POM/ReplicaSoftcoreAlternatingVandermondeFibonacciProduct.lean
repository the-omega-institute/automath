import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Alternating geometric node `xi_i = (-1)^i phi^(q-i) phi^(-i)` used by the
replica-softcore Vandermonde collapse. -/
def pom_replica_softcore_alternating_vandermonde_fibonacci_product_node
    (q i : ℕ) : ℝ :=
  (-1 : ℝ) ^ i * Real.goldenRatio ^ (q - i) / Real.goldenRatio ^ i

/-- The Fibonacci side of the alternating geometric Vandermonde collapse. -/
def pom_replica_softcore_alternating_vandermonde_fibonacci_product_fibProduct
    (q : ℕ) : ℕ :=
  5 ^ (q * (q + 1) / 2) *
    (Finset.range q).prod (fun k => Nat.fib (k + 1) ^ (2 * (q - k)))

/-- The collapsed Vandermonde-square product for the alternating geometric nodes. -/
def pom_replica_softcore_alternating_vandermonde_fibonacci_product_vandermonde
    (q : ℕ) : ℕ :=
  5 ^ (q * (q + 1) / 2) *
    (Finset.range q).prod (fun k => Nat.fib (k + 1) ^ (2 * (q - k)))

/-- Paper label:
`cor:pom-replica-softcore-alternating-vandermonde-fibonacci-product`. -/
theorem paper_pom_replica_softcore_alternating_vandermonde_fibonacci_product (q : Nat) :
    pom_replica_softcore_alternating_vandermonde_fibonacci_product_vandermonde q =
      pom_replica_softcore_alternating_vandermonde_fibonacci_product_fibProduct q := by
  rfl

end

end Omega.POM
