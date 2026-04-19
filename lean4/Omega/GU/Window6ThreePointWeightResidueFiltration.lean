import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic
import Omega.GU.Window6BdryUpliftResidueStratification

namespace Omega.GU

private def unit21 : (ZMod 571)ˣ :=
  Units.mk0 (21 : ZMod 571) (by native_decide)

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

private theorem order_unit21 : orderOf unit21 = 285 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := unit21) (n := 285) (by decide) ?_ ?_
  · native_decide
  · intro p hp hpdvd
    rcases prime_dvd_285 hp hpdvd with rfl | rfl | rfl <;> native_decide

private theorem order_zmod21 : orderOf (21 : ZMod 571) = 285 := by
  change orderOf (unit21 : ZMod 571) = 285
  rw [orderOf_units]
  exact order_unit21

/-- The three audited window-6 weights lie in the same residue filtration modulo `571`, with the
    two explicit power relations linking the short orbit to the order-`285` generators.
    cor:window6-three-point-weight-residue-filtration -/
theorem paper_window6_three_point_weight_residue_filtration :
    orderOf (21 : ZMod 571) = 285 ∧
      orderOf (34 : ZMod 571) = 285 ∧
      orderOf (55 : ZMod 571) = 19 ∧
      (55 : ZMod 571) = (34 : ZMod 571) ^ 15 ∧
      (55 : ZMod 571) = (21 : ZMod 571) ^ 30 := by
  rcases paper_window6_bdry_uplift_residue_stratification with ⟨h34, _, h55, _⟩
  refine ⟨order_zmod21, h34, h55, by native_decide, by native_decide⟩

end Omega.GU
