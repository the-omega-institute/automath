import Mathlib.Data.ZMod.Basic
import Omega.Folding.FiberRing

namespace Omega.EA

/-- Concrete CRT factorization statement transported across the stable-value ring equivalence:
`X m` is isomorphic to `ZMod (F_{m+2})`, and every coprime factorization of `F_{m+2}` yields the
corresponding Chinese-remainder product decomposition. -/
def CrtFactorizationStatement (m : ℕ) : Prop :=
  Nonempty (Omega.X m ≃+* ZMod (Nat.fib (m + 2))) ∧
    ∀ p q : ℕ, Nat.fib (m + 2) = p * q → Nat.Coprime p q →
      Nonempty (Omega.X m ≃+* ZMod p × ZMod q)

/-- Paper label: `cor:crt-factorization`. The stable-value map already identifies `X m` with
`ZMod (F_{m+2})`, and the existing CRT equivalence transports any coprime factorization of
`F_{m+2}` to a product decomposition of the folded ring. -/
theorem paper_crt_factorization (m : ℕ) : CrtFactorizationStatement m := by
  refine ⟨⟨Omega.X.stableValueRingEquiv m⟩, ?_⟩
  intro p q hpq hcop
  exact ⟨Omega.X.crtDecomposition m p q hpq hcop⟩

end Omega.EA
