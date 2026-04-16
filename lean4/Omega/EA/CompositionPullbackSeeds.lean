import Omega.EA.CompositionPullback

namespace Omega.EA.CompositionPullbackSeeds

open Omega X

/-- Paper-facing seeds for addition and multiplication pullback through `X.ofNat`.
    cor:composition-pullback -/
theorem paper_composition_pullback_seeds (m a b : ℕ)
    (ha : a + b < Nat.fib (m + 2)) (hmul : a * b < Nat.fib (m + 2)) :
    X.stableAdd (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a + b) ∧
    X.stableMul (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a * b) := by
  exact ⟨Omega.EA.compositionPullback_add m a b ha, Omega.EA.compositionPullback_mul m a b hmul⟩

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_composition_pullback_package (m a b : ℕ)
    (ha : a + b < Nat.fib (m + 2)) (hmul : a * b < Nat.fib (m + 2)) :
    X.stableAdd (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a + b) ∧
    X.stableMul (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a * b) :=
  paper_composition_pullback_seeds m a b ha hmul

end Omega.EA.CompositionPullbackSeeds
