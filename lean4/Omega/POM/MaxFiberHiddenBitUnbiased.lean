import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.FiberWeightCount

namespace Omega.POM

/-- Paper label: `cor:pom-max-fiber-hidden-bit-unbiased`. -/
theorem paper_pom_max_fiber_hidden_bit_unbiased
    (k : ℕ) (x₁ x₂ : Omega.X (2 * k)) :
    Omega.fiberHiddenBitCount 0 x₁ = Nat.fib (k + 1) →
      Omega.fiberHiddenBitCount 1 x₁ = Nat.fib k →
      Omega.fiberHiddenBitCount 0 x₂ = Nat.fib k →
      Omega.fiberHiddenBitCount 1 x₂ = Nat.fib (k + 1) →
      Omega.fiberHiddenBitCount 0 x₁ + Omega.fiberHiddenBitCount 0 x₂ = Nat.fib (k + 2) ∧
        Omega.fiberHiddenBitCount 1 x₁ + Omega.fiberHiddenBitCount 1 x₂ = Nat.fib (k + 2) := by
  intro h₀₁ h₁₁ h₀₂ h₁₂
  have hfib : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := by
    simpa [add_comm] using (Nat.fib_add_two (n := k))
  constructor <;> omega

end Omega.POM
