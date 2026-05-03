import Omega.Folding.FiberFusion

namespace Omega

/-- Paper label: `lem:pom-fib-fusion-submultiplicativity`. -/
theorem paper_pom_fib_fusion_submultiplicativity (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.fib (a + b - 1) =
        Nat.fib a * Nat.fib b + Nat.fib (a - 1) * Nat.fib (b - 1) ∧
      (2 ≤ a →
        2 ≤ b →
          Nat.fib a * Nat.fib b < Nat.fib (a + b - 1) ∧
            Nat.fib (a + b - 1) < Nat.fib (a + b)) := by
  constructor
  · exact fib_fusion a b ha hb
  · intro ha2 hb2
    exact ⟨fib_prod_lt_fib_fusion a b ha2 hb2,
      fib_fusion_lt_fib_sum a b ha hb (by omega)⟩

end Omega
