import Omega.Core.Word
import Mathlib.Tactic

namespace Omega.Core

open scoped BigOperators

def flipBit (i : Fin n) (w : Word n) : Word n :=
  Function.update w i (!(w i))

def deltaBit (i : Fin n) (f : Word n → ℤ) (w : Word n) : ℤ :=
  f w - f (flipBit i w)

theorem walshStokes_singleton (i : Fin n) (f : Word n → ℤ) :
    Finset.sum (Finset.univ.filter fun w : Word n => w i = false) (deltaBit i f)
      =
    ∑ w : Word n, (if w i = false then 1 else -1) * f w := by
  classical
  unfold deltaBit
  rw [Finset.sum_sub_distrib]
  have hbij :
      Finset.sum (Finset.univ.filter fun w : Word n => w i = false) (fun w => f (flipBit i w))
        =
      Finset.sum (Finset.univ.filter fun w : Word n => w i = true) f := by
    refine Finset.sum_bij (fun w _ => flipBit i w) ?_ ?_ ?_ ?_
    · intro w hw
      simp [flipBit] at hw ⊢
      exact hw
    · intro w hw
      simp [flipBit]
    · intro w1 hw1 w2 hw2 hEq
      have := congrFun hEq i
      simp [flipBit] at this
      exact funext_iff.mp (by
        apply funext
        intro j
        by_cases hji : j = i <;> simp [flipBit, Function.update, hji] )
    · intro w hw
      refine ⟨flipBit i w, ?_, ?_⟩
      · simp [flipBit] at hw ⊢
        exact hw
      · simp [flipBit]
  rw [hbij]
  have hsplit :
      ∑ w : Word n, (if w i = false then 1 else -1) * f w
        =
      Finset.sum (Finset.univ.filter fun w : Word n => w i = false) f
        -
      Finset.sum (Finset.univ.filter fun w : Word n => w i = true) f := by
    classical
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Word n))) (p := fun w => w i = false)]
    simp
  linarith [hsplit]

theorem walshStokes_singleton_const (i : Fin n) (c : ℤ) :
    Finset.sum (Finset.univ.filter fun w : Word n => w i = false) (deltaBit i (fun _ => c)) = 0 := by
  simp [deltaBit]

end Omega.Core
