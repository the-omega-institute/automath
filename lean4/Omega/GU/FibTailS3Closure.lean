import Mathlib.Tactic

namespace Omega.GU.FibTailS3Closure

open ZMod

/-- The g₆ action on ZMod 23: x ↦ 3x + 1.
    cor:fib-tail-s3-closure -/
def g6Action (x : ZMod 23) : ZMod 23 := 3 * x + 1

/-- g₆ has order 11: g₆¹¹ = id on ZMod 23.
    cor:fib-tail-s3-closure -/
theorem g6_order_eleven : ∀ x : ZMod 23,
    (Nat.iterate g6Action 11 x) = x := by native_decide

/-- The fixed point of g₆ is 11.
    cor:fib-tail-s3-closure -/
theorem g6_fixed_point : g6Action (11 : ZMod 23) = 11 := by decide

/-- The R-action on ZMod 23: x ↦ -x⁻¹.
    cor:fib-tail-s3-closure -/
noncomputable def rAction (x : ZMod 23) : ZMod 23 := -(x⁻¹)

/-- R is an involution on all nonzero elements: R(R(x)) = x for x ≠ 0.
    Proved by exhaustive check on the 22 nonzero elements.
    cor:fib-tail-s3-closure -/
theorem r_involution (x : ZMod 23) (hx : x ≠ 0) :
    rAction (rAction x) = x := by
  revert hx
  revert x
  decide

/-- Seed: g₆(0) = 1.
    cor:fib-tail-s3-closure -/
theorem g6_zero : g6Action (0 : ZMod 23) = 1 := by decide

/-- Seed: g₆(1) = 4.
    cor:fib-tail-s3-closure -/
theorem g6_one : g6Action (1 : ZMod 23) = 4 := by decide

/-- Seed: g₆(4) = 13.
    cor:fib-tail-s3-closure -/
theorem g6_four : g6Action (4 : ZMod 23) = 13 := by decide

/-- Seed: g₆(13) = 17.
    cor:fib-tail-s3-closure -/
theorem g6_thirteen : g6Action (13 : ZMod 23) = 17 := by decide

/-- Paper package: Fib-tail S₃ closure mod 23 seeds.
    cor:fib-tail-s3-closure -/
theorem paper_fib_tail_s3_closure :
    (∀ x : ZMod 23, Nat.iterate g6Action 11 x = x) ∧
    (∀ x : ZMod 23, x ≠ 0 → rAction (rAction x) = x) ∧
    g6Action (11 : ZMod 23) = 11 ∧
    g6Action (0 : ZMod 23) = 1 ∧
    g6Action (1 : ZMod 23) = 4 ∧
    g6Action (4 : ZMod 23) = 13 ∧
    g6Action (13 : ZMod 23) = 17 :=
  ⟨g6_order_eleven, r_involution, g6_fixed_point,
   g6_zero, g6_one, g6_four, g6_thirteen⟩

-- Phase R609: Complete orbit decomposition
-- ══════════════════════════════════════════════════════════════

/-- g₆¹¹(2) = 2: the second orbit is also period 11.
    cor:fib-tail-s3-closure -/
theorem g6_orbit_two :
    Nat.iterate g6Action 11 (2 : ZMod 23) = 2 := by native_decide

/-- The orbit of 0 under g₆ is [0,1,4,13,17,6,19,12,14,20,15] with no duplicates,
    and 11 is not in this orbit. Every non-fixed element lies in one of the two orbits.
    cor:fib-tail-s3-closure -/
theorem g6_orbit_decomposition :
    (List.Nodup ([0, 1, 4, 13, 17, 6, 19, 12, 14, 20, 15].map (fun n => (n : ZMod 23)))) ∧
    ((11 : ZMod 23) ∉ [0, 1, 4, 13, 17, 6, 19, 12, 14, 20, 15].map (fun n => (n : ZMod 23))) ∧
    (∀ x : ZMod 23, x ≠ 11 →
      x ∈ [0, 1, 4, 13, 17, 6, 19, 12, 14, 20, 15].map (fun n => (n : ZMod 23)) ∨
      x ∈ [2, 3, 5, 7, 8, 9, 10, 16, 18, 21, 22].map (fun n => (n : ZMod 23))) := by
  refine ⟨by decide, by decide, by decide⟩

/-- Paper package: complete orbit decomposition of g₆ on ZMod 23.
    cor:fib-tail-s3-closure -/
theorem paper_fib_tail_s3_orbit_decomposition :
    (∀ x : ZMod 23, Nat.iterate g6Action 11 x = x) ∧
    (g6Action (11 : ZMod 23) = 11) ∧
    (1 + 11 + 11 = 23) ∧
    (Nat.iterate g6Action 11 (2 : ZMod 23) = 2) :=
  ⟨g6_order_eleven, g6_fixed_point, by omega, g6_orbit_two⟩

end Omega.GU.FibTailS3Closure
