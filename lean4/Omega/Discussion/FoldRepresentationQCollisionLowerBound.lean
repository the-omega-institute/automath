import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Discussion

open Finset
open scoped BigOperators

section

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Fiberwise absolute-mass pushforward on a finite type. -/
def pushforward (p : X → ℚ) (g : X → Y) : Y → ℚ :=
  fun y => Finset.sum (univ.filter (fun x => g x = y)) (fun x => |p x|)

/-- The q-collision functional attached to absolute masses on a finite type. -/
def collisionProb (q : ℕ) (p : X → ℚ) : ℚ :=
  ∑ x, |p x| ^ q

omit [DecidableEq X] in
private lemma sum_over_fibers (g : X → Y) (a : X → ℚ) :
    ∑ y, Finset.sum (univ.filter (fun x => g x = y)) a = ∑ x, a x := by
  calc
    ∑ y, Finset.sum (univ.filter (fun x => g x = y)) a
      = ∑ y, ∑ x, if g x = y then a x else 0 := by
          refine sum_congr rfl ?_
          intro y hy
          rw [sum_filter]
    _ = ∑ x, ∑ y, if g x = y then a x else 0 := by
          rw [sum_comm]
    _ = ∑ x, a x := by
          refine sum_congr rfl ?_
          intro x hx
          rw [sum_eq_single (g x)]
          · simp
          · intro y hy hyx
            have hxy : g x ≠ y := by
              simpa [eq_comm] using hyx
            simp [hxy]
          · intro hmem
            simp at hmem

private lemma sum_pow_le_pow_sum {α : Type} [DecidableEq α] (s : Finset α) (a : α → ℚ)
    {q : ℕ} (hq : 1 ≤ q) (ha : ∀ x, 0 ≤ a x) :
    Finset.sum s (fun x => (a x) ^ q) ≤ (Finset.sum s a) ^ q := by
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert x s hx ih =>
      rw [sum_insert hx, sum_insert hx]
      have hs_nonneg : 0 ≤ Finset.sum s a := by
        exact sum_nonneg (fun y hy => ha y)
      have hstep : a x ^ q + Finset.sum s (fun y => a y ^ q) ≤ a x ^ q + (Finset.sum s a) ^ q := by
        gcongr
      calc
        a x ^ q + Finset.sum s (fun y => a y ^ q) ≤ a x ^ q + (Finset.sum s a) ^ q := hstep
        _ ≤ (a x + Finset.sum s a) ^ q := by
              exact pow_add_pow_le (ha x) hs_nonneg (Nat.one_le_iff_ne_zero.mp hq)

/-- Folding a finite representation through any quotient map can only increase the q-collision
rate, because equal inputs always remain equal after applying the representation. The proof is
the finite-fiber power-sum monotonicity induced by collecting absolute mass on each fiber.
    prop:discussion-fold-representation-qcollision-lower-bound -/
theorem paper_discussion_fold_representation_qcollision_lower_bound {X Y : Type} [Fintype X]
    [Fintype Y] [DecidableEq X] [DecidableEq Y] (p : X → ℚ) (g : X → Y) (q : ℕ) (hq : 2 ≤ q) :
    collisionProb q (pushforward p g) ≥ collisionProb q p := by
  have hq' : 1 ≤ q := by
    omega
  calc
    collisionProb q p
      = ∑ y, Finset.sum (univ.filter (fun x => g x = y)) (fun x => |p x| ^ q) := by
          symm
          exact sum_over_fibers g (fun x => |p x| ^ q)
    _ ≤ ∑ y, (Finset.sum (univ.filter (fun x => g x = y)) (fun x => |p x|)) ^ q := by
          refine sum_le_sum ?_
          intro y hy
          exact sum_pow_le_pow_sum _ _ hq' (fun x => abs_nonneg (p x))
    _ = ∑ y, |pushforward p g y| ^ q := by
          refine sum_congr rfl ?_
          intro y hy
          rw [pushforward]
          rw [abs_of_nonneg]
          exact sum_nonneg (fun x hx => abs_nonneg (p x))
    _ = collisionProb q (pushforward p g) := by
          rfl

end

end Omega.Discussion
