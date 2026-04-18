import Mathlib.Data.ZMod.Basic
import Omega.Folding.FiberArithmeticProperties

namespace Omega

noncomputable section

/-- The fold quotient inherits its commutative semiring structure by transport along the existing
equivalence with the stable-value model `X m`. -/
noncomputable instance instFoldQuotientCommSemiring (m : Nat) :
    CommSemiring (Quotient (foldSetoid m)) :=
  Equiv.commSemiring (foldQuotientEquiv m)

/-- The fold quotient is semiring-isomorphic to the stable-value model `X m`. -/
noncomputable def foldQuotientSemiringEquiv (m : Nat) :
    Quotient (foldSetoid m) ≃+* X m := by
  let e := foldQuotientEquiv m
  exact
    { toEquiv := e
      map_mul' := by
        intro a b
        change e (e.symm (e a * e b)) = e a * e b
        simp
      map_add' := by
        intro a b
        change e (e.symm (e a + e b)) = e a + e b
        simp }

/-- The fold congruence quotient is a commutative semiring, and the quotient map identifies it
with the Fibonacci modulus `ZMod (Nat.fib (m + 2))`.
    thm:fold-congruence-mod-semirings -/
theorem paper_fold_congruence_mod_semirings (m : Nat) :
    Nonempty (CommSemiring (Quotient (foldSetoid m))) ∧
      Nonempty (Quotient (foldSetoid m) ≃+* ZMod (Nat.fib (m + 2))) := by
  refine ⟨?_, ?_⟩
  · exact ⟨inferInstance⟩
  · exact ⟨(foldQuotientSemiringEquiv m).trans (X.stableValueRingEquiv m)⟩

end

end Omega
