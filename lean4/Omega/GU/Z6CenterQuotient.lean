import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas

namespace Omega.GU.Z6CenterQuotient

open Fintype ZMod

/-- Card of Z₂ × Z₃ is 6.
    cor:bdry-global-z6-quotient -/
theorem z2_times_z3_card :
    Fintype.card (ZMod 2 × ZMod 3) = 6 := by
  simp [Fintype.card_prod, ZMod.card]

/-- 2 and 3 are coprime.
    cor:bdry-global-z6-quotient -/
theorem two_coprime_three : Nat.Coprime 2 3 := by decide

/-- Z₂ × Z₃ ≅ Z₆ as rings via CRT.
    cor:bdry-global-z6-quotient -/
theorem z2_times_z3_ringEquiv_z6 :
    Nonempty (ZMod 2 × ZMod 3 ≃+* ZMod 6) :=
  ⟨(ZMod.chineseRemainder two_coprime_three).symm⟩

/-- Paper package: card = 6, coprimality, and CRT isomorphism.
    cor:bdry-global-z6-quotient -/
theorem paper_bdry_global_z6_quotient :
    Fintype.card (ZMod 2 × ZMod 3) = 6 ∧
    Nat.Coprime 2 3 ∧
    Nonempty (ZMod 2 × ZMod 3 ≃+* ZMod 6) :=
  ⟨z2_times_z3_card, two_coprime_three, z2_times_z3_ringEquiv_z6⟩

end Omega.GU.Z6CenterQuotient
