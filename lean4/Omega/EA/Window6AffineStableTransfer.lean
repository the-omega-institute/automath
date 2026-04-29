import Omega.Folding.FiberRing

namespace Omega.EA

open Omega

noncomputable section

/-- Paper-facing statement for the affine magma transfer bridge across stable values.

For six-variable binary magma terms, the affine operation
`x ⋄ y = a * x + b * y` on `X m` satisfies an equation exactly when the same
equation is satisfied after transporting coefficients and variables through
`X.stableValueRingEquiv m` to `ZMod (Nat.fib (m + 2))`.
-/
def window6_affine_stable_transfer_statement (m a b : ℕ) : Prop :=
  ∀ lhs rhs : X.AffineMagmaTerm (Fin 6),
    X.AffineMagmaTerm.SatisfiesX m (X.ofNat m a) (X.ofNat m b) lhs rhs ↔
      X.AffineMagmaTerm.SatisfiesZ m
        (X.stableValueRingEquiv m (X.ofNat m a))
        (X.stableValueRingEquiv m (X.ofNat m b)) lhs rhs

/-- Paper label: `lem:window6-affine-stable-transfer`. -/
theorem paper_window6_affine_stable_transfer (m a b : ℕ) :
    window6_affine_stable_transfer_statement m a b := by
  intro lhs rhs
  exact X.stableValueRingEquiv_preserves_magma_satisfaction m
    (X.ofNat m a) (X.ofNat m b) lhs rhs

end

end Omega.EA
