import Mathlib.Data.ZMod.Basic
import Omega.Folding.FiberRing

namespace Omega.EA

/-- Paper label: `thm:add-definitional`. The stable-value map identifies stable addition on
`X m` with addition modulo `fib (m + 2)`, and the existing commutative-ring structure transports
both the additive monoid structure and the additive equivalence to `ZMod`. -/
theorem paper_add_definitional (m : ℕ) :
    (∀ x y : Omega.X m,
        Omega.stableValue (Omega.X.stableAdd x y) =
          (Omega.stableValue x + Omega.stableValue y) % Nat.fib (m + 2)) ∧
      Nonempty (AddCommMonoid (Omega.X m)) ∧
      Nonempty (Omega.X m ≃+ ZMod (Nat.fib (m + 2))) := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact Omega.X.stableValue_stableAdd_eq x y
  · refine ⟨⟨show AddCommMonoid (Omega.X m) from inferInstance⟩, ?_⟩
    exact ⟨(Omega.X.stableValueRingEquiv m).toAddEquiv⟩

end Omega.EA
