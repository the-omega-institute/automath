import Omega.EA.CompositionPullback
import Omega.EA.CompositionTwoLayer
import Omega.EA.MulNoNewPrimitive

namespace Omega.EA.ArithComposition

open Omega

/-- Paper-facing composition package for additive and multiplicative stable readouts.
    The theorem itself follows the round placeholder signature and returns the packaged proposition.
    thm:arith-composition -/
theorem arithCompositionPackage {A : Type _} (g : A → A) (m : Nat) :
    (∀ n k : ℕ,
      Omega.EA.CompositionTwoLayer.iota0 g (n + k) =
        Omega.EA.CompositionTwoLayer.iota0 g n ∘ Omega.EA.CompositionTwoLayer.iota0 g k) ∧
    (∀ a b : ℕ, a + b < Nat.fib (m + 2) →
      X.stableAdd (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a + b)) ∧
    (∀ a b : ℕ, a * b < Nat.fib (m + 2) →
      X.stableMul (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a * b)) ∧
    (1 ≤ m → ∀ x y : X m, X.stableMul y x = X.iteratedStableAdd x (stableValue y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Omega.EA.CompositionTwoLayer.paper_ea_composition_two_layer_package g
  · exact (Omega.EA.paper_composition_pullback m).1
  · exact (Omega.EA.paper_composition_pullback m).2
  · intro hm x y
    exact Omega.EA.MulNoNewPrimitive.paper_mul_no_new_primitive hm x y

/-- Paper-facing wrapper with the requested placeholder signature.
    Lean does not allow this header as a theorem because it is not itself a proposition,
    so the round placeholder is realized as a definition.
    thm:arith-composition -/
def paper_arith_composition {A : Type _} (g : A -> A) (m : Nat) : Prop :=
  (∀ n k : ℕ,
    Omega.EA.CompositionTwoLayer.iota0 g (n + k) =
      Omega.EA.CompositionTwoLayer.iota0 g n ∘ Omega.EA.CompositionTwoLayer.iota0 g k) ∧
  (∀ a b : ℕ, a + b < Nat.fib (m + 2) →
    X.stableAdd (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a + b)) ∧
  (∀ a b : ℕ, a * b < Nat.fib (m + 2) →
    X.stableMul (X.ofNat m a) (X.ofNat m b) = X.ofNat m (a * b)) ∧
  (1 ≤ m → ∀ x y : X m, X.stableMul y x = X.iteratedStableAdd x (stableValue y))

end Omega.EA.ArithComposition
