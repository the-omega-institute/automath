import Mathlib.Tactic
import Omega.Folding.FiberFusion

namespace Omega.POM

/-- Paper-facing Fibonacci component-fusion gain. Merging two positive path components raises the
    Fibonacci count strictly, and the exact gap is the product of the shifted tails, hence at least
    the shorter-tail contribution.
    cor:pom-fib-component-fusion-gain -/
theorem paper_pom_fib_component_fusion_gain (ℓ ℓ' : ℕ) (hℓ : 1 ≤ ℓ) (hℓ' : 1 ≤ ℓ') :
    Nat.fib (ℓ + 2) * Nat.fib (ℓ' + 2) < Nat.fib (ℓ + ℓ' + 3) ∧
      Nat.fib (ℓ + ℓ' + 3) - Nat.fib (ℓ + 2) * Nat.fib (ℓ' + 2) =
        Nat.fib (ℓ + 1) * Nat.fib (ℓ' + 1) ∧
      Nat.fib (min ℓ ℓ' + 1) ≤
        Nat.fib (ℓ + ℓ' + 3) - Nat.fib (ℓ + 2) * Nat.fib (ℓ' + 2) := by
  refine ⟨Omega.fib_component_fusion_lt ℓ ℓ' hℓ hℓ', ?_, ?_⟩
  · exact Omega.fib_component_fusion_gain ℓ ℓ' hℓ hℓ'
  · exact Omega.fib_component_fusion_gain_ge ℓ ℓ' hℓ hℓ'

end Omega.POM
