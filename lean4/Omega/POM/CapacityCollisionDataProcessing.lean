import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.POM

open Finset
open scoped BigOperators

variable {Omega X Y : Type*} [Fintype Omega] [Fintype X] [Fintype Y]
variable [DecidableEq X] [DecidableEq Y]

/-- Cardinality of the `x`-fiber of a finite map. -/
def fiberCard (f : Omega → X) (x : X) : ℕ :=
  ∑ ω, if f ω = x then 1 else 0

/-- Saturated capacity curve obtained by truncating each fiber size at level `T`. -/
def capacityCurve (f : Omega → X) (T : ℕ) : ℕ :=
  ∑ x, min (fiberCard f x) T

/-- Collision moment given by the `q`-th power sum of the fiber sizes. -/
def collisionMoment (f : Omega → X) (q : ℕ) : ℕ :=
  ∑ x, (fiberCard f x) ^ q

private lemma fiberCard_comp (f : Omega → X) (g : X → Y) (y : Y) :
    fiberCard (g ∘ f) y = Finset.sum (univ.filter (fun x => g x = y)) (fiberCard f) := by
  classical
  unfold fiberCard
  calc
    ∑ ω, (if (g ∘ f) ω = y then (1 : ℕ) else 0)
      =
        ∑ ω, Finset.sum (univ.filter (fun x => g x = y)) (fun x => if f ω = x then (1 : ℕ) else 0) := by
          refine sum_congr rfl ?_
          intro ω hω
          by_cases hgy : g (f ω) = y
          · rw [sum_eq_single (f ω)]
            · simp [hgy]
            · intro x hx hxf
              have hfx : f ω ≠ x := by
                exact fun h => hxf h.symm
              simp [hfx]
            · intro hmem
              simp [hgy] at hmem
          · have hzero :
                ∀ x ∈ univ.filter (fun x => g x = y), (if f ω = x then (1 : ℕ) else 0) = 0 := by
                intro x hx
                by_cases hfx : f ω = x
                · subst hfx
                  simp [hgy] at hx
                · simp [hfx]
            simpa [hgy] using Finset.sum_eq_zero hzero
    _ = Finset.sum (univ.filter (fun x => g x = y)) (fun x => ∑ ω, if f ω = x then (1 : ℕ) else 0) := by
          rw [sum_comm]
    _ = Finset.sum (univ.filter (fun x => g x = y)) (fiberCard f) := by
          simp [fiberCard]

private lemma sum_over_fibers (g : X → Y) (a : X → ℕ) :
    ∑ y, Finset.sum (univ.filter (fun x => g x = y)) a = ∑ x, a x := by
  classical
  calc
    ∑ y, Finset.sum (univ.filter (fun x => g x = y)) a
      = ∑ y, ∑ x, if g x = y then a x else 0 := by
          refine sum_congr rfl ?_
          intro y hy
          rw [sum_filter]
    _ = ∑ x, ∑ y, if g x = y then a x else 0 := by rw [sum_comm]
    _ = ∑ x, a x := by
          refine sum_congr rfl ?_
          intro x hx
          rw [sum_eq_single (g x)]
          · simp
          · intro y hy hyx
            have hxy : g x ≠ y := by simpa [eq_comm] using hyx
            simp [hxy]
          · intro hmem
            simp at hmem

private lemma min_add_le_add_min (a b T : ℕ) : min (a + b) T ≤ min a T + min b T := by
  by_cases ha : T ≤ a
  · rw [Nat.min_eq_right ha]
    omega
  · have ha' : a < T := lt_of_not_ge ha
    rw [Nat.min_eq_left ha'.le]
    by_cases hab : T ≤ a + b
    · have hsub : T - a ≤ min b T := by
        refine le_min ?_ (Nat.sub_le _ _)
        omega
      omega
    · have hab' : a + b < T := lt_of_not_ge hab
      rw [Nat.min_eq_left hab'.le]
      omega

private lemma min_sum_le_sum_min {α : Type*} [DecidableEq α] (s : Finset α) (a : α → ℕ) (T : ℕ) :
    min (Finset.sum s a) T ≤ Finset.sum s (fun x => min (a x) T) := by
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert x s hx ih =>
      rw [sum_insert hx, sum_insert hx]
      have hstep : min (a x) T + min (Finset.sum s a) T ≤
          min (a x) T + Finset.sum s (fun y => min (a y) T) := by
        gcongr
      exact (min_add_le_add_min (a x) (Finset.sum s a) T).trans hstep

private lemma sum_pow_le_pow_sum {α : Type*} [DecidableEq α] (s : Finset α) (a : α → ℕ)
    {q : ℕ} (hq : 1 ≤ q) :
    Finset.sum s (fun x => (a x) ^ q) ≤ (Finset.sum s a) ^ q := by
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert x s hx ih =>
      rw [sum_insert hx, sum_insert hx]
      have hstep : a x ^ q + Finset.sum s (fun y => a y ^ q) ≤ a x ^ q + (Finset.sum s a) ^ q := by
        gcongr
      calc
        a x ^ q + Finset.sum s (fun y => a y ^ q) ≤ a x ^ q + (Finset.sum s a) ^ q := hstep
        _ ≤ (a x + Finset.sum s a) ^ q := by
          exact
            pow_add_pow_le (Nat.zero_le _) (sum_nonneg fun _ _ => Nat.zero_le _)
              (Nat.one_le_iff_ne_zero.mp hq)

theorem paper_pom_capacity_collision_data_processing {Omega X Y : Type*} [Fintype Omega]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] (f : Omega → X) (g : X → Y) (T q : ℕ)
    (hT : 0 < T) (hq : 1 ≤ q) :
    capacityCurve (g ∘ f) T ≤ capacityCurve f T ∧
      collisionMoment (g ∘ f) q ≥ collisionMoment f q := by
  constructor
  · unfold capacityCurve
    calc
      ∑ y, min (fiberCard (g ∘ f) y) T
        = ∑ y, min (Finset.sum (univ.filter (fun x => g x = y)) (fiberCard f)) T := by
            refine sum_congr rfl ?_
            intro y hy
            rw [fiberCard_comp]
      _ ≤ ∑ y, Finset.sum (univ.filter (fun x => g x = y)) (fun x => min (fiberCard f x) T) := by
            refine sum_le_sum ?_
            intro y hy
            exact min_sum_le_sum_min _ _ _
      _ = ∑ x, min (fiberCard f x) T := by
            simpa using sum_over_fibers g (fun x => min (fiberCard f x) T)
  · have hmoment :
        collisionMoment f q ≤ collisionMoment (g ∘ f) q := by
      unfold collisionMoment
      calc
        ∑ x, fiberCard f x ^ q
          = ∑ y, Finset.sum (univ.filter (fun x => g x = y)) (fun x => fiberCard f x ^ q) := by
              symm
              simpa using sum_over_fibers g (fun x => fiberCard f x ^ q)
        _ ≤ ∑ y, (Finset.sum (univ.filter (fun x => g x = y)) (fiberCard f)) ^ q := by
              refine sum_le_sum ?_
              intro y hy
              exact sum_pow_le_pow_sum _ _ hq
        _ = ∑ y, fiberCard (g ∘ f) y ^ q := by
              refine sum_congr rfl ?_
              intro y hy
              rw [fiberCard_comp]
    exact hmoment

end Omega.POM
