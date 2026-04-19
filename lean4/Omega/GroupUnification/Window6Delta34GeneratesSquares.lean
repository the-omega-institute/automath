import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace Omega.GroupUnification

instance : Fact (Nat.Prime 571) := ⟨by native_decide⟩

/-- The window-6 boundary uplift `δ = 34` viewed as a unit of `ZMod 571`. -/
def delta34Unit571 : (ZMod 571)ˣ :=
  Units.mk0 (34 : ZMod 571) (by native_decide)

/-- An explicit square root of `34` modulo `571`. -/
def delta34Sqrt571 : (ZMod 571)ˣ :=
  Units.mk0 (264 : ZMod 571) (by native_decide)

/-- The subgroup of squares inside `(ZMod 571)ˣ`. -/
def squareUnitsSubgroup571 : Subgroup (ZMod 571)ˣ where
  carrier := {u | ∃ v : (ZMod 571)ˣ, v ^ (2 : ℕ) = u}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x * y, by simp [pow_two, mul_comm, mul_left_comm]⟩
  inv_mem' := by
    rintro a ⟨x, rfl⟩
    refine ⟨x⁻¹, by simp [pow_two]⟩

private theorem delta34Sqrt571_sq :
    delta34Sqrt571 ^ (2 : ℕ) = delta34Unit571 := by
  ext
  native_decide

private theorem order_delta34Unit571 :
    orderOf delta34Unit571 = 285 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := delta34Unit571) (n := 285) (by decide) ?_ ?_
  · native_decide
  · intro p hp hpdvd
    have hp_ge : 2 ≤ p := hp.two_le
    have hp_le : p ≤ 285 := Nat.le_of_dvd (by decide : 0 < 285) hpdvd
    interval_cases p <;> native_decide

private theorem delta34_power_is_square (n : ℕ) :
    ∃ u : (ZMod 571)ˣ, u ^ (2 : ℕ) = delta34Unit571 ^ n := by
  refine ⟨delta34Sqrt571 ^ n, ?_⟩
  calc
    (delta34Sqrt571 ^ n) ^ (2 : ℕ) = delta34Sqrt571 ^ (n * 2) := by rw [pow_mul]
    _ = delta34Sqrt571 ^ (2 * n) := by rw [Nat.mul_comm]
    _ = (delta34Sqrt571 ^ (2 : ℕ)) ^ n := by rw [pow_mul]
    _ = delta34Unit571 ^ n := by rw [delta34Sqrt571_sq]

/-- The window-6 uplift step `δ = 34` has exact order `285 = (571 - 1) / 2`, so its cyclic
subgroup has index two in `(ZMod 571)ˣ`. Since `34 = 264² (mod 571)`, every power of `34`
is a square, matching the paper's square-subgroup certificate.
    prop:window6-delta34-generates-squares -/
theorem paper_window6_delta34_generates_squares :
    orderOf delta34Unit571 = 285 ∧
    Fintype.card (Subgroup.zpowers delta34Unit571) = 285 ∧
    Fintype.card (Subgroup.zpowers delta34Unit571) * 2 = Fintype.card (ZMod 571)ˣ ∧
    delta34Unit571 ∈ squareUnitsSubgroup571 ∧
    (∀ n : ℕ, delta34Unit571 ^ n ∈ squareUnitsSubgroup571) := by
  refine ⟨order_delta34Unit571, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_zpowers, order_delta34Unit571]
  · rw [Fintype.card_zpowers, order_delta34Unit571]
    native_decide
  · exact ⟨delta34Sqrt571, delta34Sqrt571_sq⟩
  · intro n
    exact delta34_power_is_square n

end Omega.GroupUnification
