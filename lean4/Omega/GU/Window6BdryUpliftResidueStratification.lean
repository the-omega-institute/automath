import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace Omega.GU

instance factPrime571Window6BdryUpliftResidueStratification : Fact (Nat.Prime 571) := by
  exact ⟨by native_decide⟩

private def unit34 : (ZMod 571)ˣ :=
  Units.mk0 (34 : ZMod 571) (by native_decide)

private def unit144 : (ZMod 571)ˣ :=
  Units.mk0 (144 : ZMod 571) (by native_decide)

private def unit55 : (ZMod 571)ˣ :=
  Units.mk0 (55 : ZMod 571) (by native_decide)

private def unit89 : (ZMod 571)ˣ :=
  Units.mk0 (89 : ZMod 571) (by native_decide)

private theorem prime_dvd_285 {p : ℕ} (hp : Nat.Prime p) (hpdvd : p ∣ 285) :
    p = 3 ∨ p = 5 ∨ p = 19 := by
  have hmul : p ∣ 3 * (5 * 19) := by
    simpa [Nat.mul_assoc] using hpdvd
  rcases hp.dvd_mul.mp hmul with h3 | hrest
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3)
  · rcases hp.dvd_mul.mp hrest with h5 | h19
    · exact Or.inr <| Or.inl <| (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h5
    · exact Or.inr <| Or.inr <|
        (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)).mp h19

private theorem prime_dvd_570 {p : ℕ} (hp : Nat.Prime p) (hpdvd : p ∣ 570) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 19 := by
  have hmul : p ∣ 2 * (3 * (5 * 19)) := by
    simpa [Nat.mul_assoc] using hpdvd
  rcases hp.dvd_mul.mp hmul with h2 | hrest
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h2)
  · rcases hp.dvd_mul.mp hrest with h3 | hrest'
    · exact Or.inr <|
        Or.inl <| (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3
    · rcases hp.dvd_mul.mp hrest' with h5 | h19
      · exact Or.inr <| Or.inr <| Or.inl <|
          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h5
      · exact Or.inr <| Or.inr <| Or.inr <|
          (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)).mp h19

private theorem order_unit34 : orderOf unit34 = 285 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := unit34) (n := 285) (by decide) ?_ ?_
  · native_decide
  · intro p hp hpdvd
    rcases prime_dvd_285 hp hpdvd with rfl | rfl | rfl <;> native_decide

private theorem order_unit144 : orderOf unit144 = 285 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := unit144) (n := 285) (by decide) ?_ ?_
  · native_decide
  · intro p hp hpdvd
    rcases prime_dvd_285 hp hpdvd with rfl | rfl | rfl <;> native_decide

private theorem order_unit55 : orderOf unit55 = 19 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := unit55) (n := 19) (by decide) ?_ ?_
  · native_decide
  · intro p hp hpdvd
    have hp19 : p = 19 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)).mp hpdvd
    subst hp19
    native_decide

private theorem order_unit89 : orderOf unit89 = 570 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := unit89) (n := 570) (by decide) ?_ ?_
  · native_decide
  · intro p hp hpdvd
    rcases prime_dvd_570 hp hpdvd with rfl | rfl | rfl | rfl <;> native_decide

private theorem order_zmod34 : orderOf (34 : ZMod 571) = 285 := by
  change orderOf (unit34 : ZMod 571) = 285
  rw [orderOf_units]
  exact order_unit34

private theorem order_zmod144 : orderOf (144 : ZMod 571) = 285 := by
  change orderOf (unit144 : ZMod 571) = 285
  rw [orderOf_units]
  exact order_unit144

private theorem order_zmod55 : orderOf (55 : ZMod 571) = 19 := by
  change orderOf (unit55 : ZMod 571) = 19
  rw [orderOf_units]
  exact order_unit55

private theorem order_zmod89 : orderOf (89 : ZMod 571) = 570 := by
  change orderOf (unit89 : ZMod 571) = 570
  rw [orderOf_units]
  exact order_unit89

/-- Audited residue-stratification orders for the window-6 boundary uplift modulo `571`.
    prop:window6-bdry-uplift-residue-stratification -/
theorem paper_window6_bdry_uplift_residue_stratification :
    orderOf (34 : ZMod 571) = 285 ∧
      orderOf (144 : ZMod 571) = 285 ∧
      orderOf (55 : ZMod 571) = 19 ∧
      orderOf (89 : ZMod 571) = 570 := by
  exact ⟨order_zmod34, order_zmod144, order_zmod55, order_zmod89⟩

end Omega.GU
