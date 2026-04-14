import Omega.Core.Word
import Mathlib.Tactic

namespace Omega.Core

open scoped BigOperators

def flipBit (i : Fin n) (w : Word n) : Word n :=
  Function.update w i (!(w i))

def deltaBit (i : Fin n) (f : Word n → ℤ) (w : Word n) : ℤ :=
  f w - f (flipBit i w)

@[simp] theorem flipBit_apply_same (i : Fin n) (w : Word n) :
    flipBit i w i = !(w i) := by
  simp [flipBit]

@[simp] theorem flipBit_apply_ne (i : Fin n) (w : Word n) {j : Fin n} (h : j ≠ i) :
    flipBit i w j = w j := by
  simp [flipBit, Function.update, h]

@[simp] theorem flipBit_involutive (i : Fin n) (w : Word n) : flipBit i (flipBit i w) = w := by
  funext j
  by_cases h : j = i
  · subst h
    simp [flipBit]
  · simp [flipBit, Function.update, h]

theorem walshStokes_singleton (i : Fin n) (f : Word n → ℤ) :
    Finset.sum (Finset.univ.filter fun w : Word n => w i = false) (deltaBit i f)
      =
    ∑ w : Word n, (if w i = false then 1 else -1) * f w := by
  classical
  unfold deltaBit
  rw [Finset.sum_sub_distrib]
  have hbijective : Function.Bijective (flipBit i : Word n → Word n) := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have := congrArg (flipBit i) hab
      simpa [flipBit_involutive] using this
    · intro w
      exact ⟨flipBit i w, by simp [flipBit_involutive]⟩
  have hbij :
      Finset.sum (Finset.univ.filter fun w : Word n => w i = false) (fun w => f (flipBit i w))
        =
      Finset.sum (Finset.univ.filter fun w : Word n => w i = true) f := by
    refine Finset.sum_bijective (flipBit i) hbijective ?_ ?_
    · intro w
      simp [flipBit]
    · intro w hw
      rfl
  rw [hbij]
  have hfalse :
      Finset.sum (Finset.univ.filter fun w : Word n => w i = false)
        (fun w => (if w i = false then 1 else -1) * f w)
        = Finset.sum (Finset.univ.filter fun w : Word n => w i = false) f := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    have hwi : w i = false := by simpa using hw
    simp [hwi]
  have htrue :
      Finset.sum (Finset.univ.filter fun w : Word n => ¬ w i = false)
        (fun w => (if w i = false then 1 else -1) * f w)
        = -Finset.sum (Finset.univ.filter fun w : Word n => w i = true) f := by
    rw [show (Finset.filter (fun w : Word n => ¬ w i = false) Finset.univ) =
          Finset.filter (fun w : Word n => w i = true) Finset.univ by
          ext w
          simp]
    calc
      Finset.sum (Finset.univ.filter fun w : Word n => w i = true)
          (fun w => (if w i = false then 1 else -1) * f w)
          = Finset.sum (Finset.univ.filter fun w : Word n => w i = true) (fun w => -f w) := by
              refine Finset.sum_congr rfl ?_
              intro w hw
              have hwi : w i = true := by simpa using hw
              simp [hwi]
      _ = -Finset.sum (Finset.univ.filter fun w : Word n => w i = true) f := by
            rw [← Finset.sum_neg_distrib]
  have hsplit :
      ∑ w : Word n, (if w i = false then 1 else -1) * f w
        =
      Finset.sum (Finset.univ.filter fun w : Word n => w i = false) f
        -
      Finset.sum (Finset.univ.filter fun w : Word n => w i = true) f := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Word n)))
      (p := fun w => w i = false)]
    rw [hfalse, htrue, sub_eq_add_neg]
  linarith [hsplit]

theorem walshStokes_singleton_const (i : Fin n) (c : ℤ) :
    Finset.sum (Finset.univ.filter fun w : Word n => w i = false) (deltaBit i (fun _ => c)) = 0 := by
  simp [deltaBit]

end Omega.Core
