import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

namespace Omega.GU

/-- A window-`6` word, indexed by the six coordinate directions. -/
abbrev Window6Word := Fin 6 → Bool

/-- Toggle the `i`-th coordinate of a window-`6` word. -/
def window6Toggle (i : Fin 6) (ω : Window6Word) : Window6Word :=
  fun j => if j = i then !(ω j) else ω j

@[simp] theorem window6Toggle_involutive (i : Fin 6) :
    Function.Involutive (window6Toggle i) := by
  intro ω
  funext j
  by_cases h : j = i
  · subst h
    simp [window6Toggle]
  · simp [window6Toggle, h]

/-- The concrete toggle matrix whose `(u,v)`-entry records whether `v` is obtained from `u`
by flipping the `i`-th bit. -/
def window6ToggleMatrix (i : Fin 6) : Matrix Window6Word Window6Word ℤ :=
  fun u v => if v = window6Toggle i u then 1 else 0

private theorem window6Toggle_eq_swap_iff (i : Fin 6) (u v : Window6Word) :
    v = window6Toggle i u ↔ u = window6Toggle i v := by
  constructor
  · intro huv
    calc
      u = window6Toggle i (window6Toggle i u) := by
            simpa using (window6Toggle_involutive i u).symm
      _ = window6Toggle i v := by rw [huv]
  · intro hvu
    calc
      v = window6Toggle i (window6Toggle i v) := by
            simpa using (window6Toggle_involutive i v).symm
      _ = window6Toggle i u := by rw [hvu]

private theorem window6ToggleMatrix_entry_swap (i : Fin 6) (u v : Window6Word) :
    window6ToggleMatrix i u v = window6ToggleMatrix i v u := by
  by_cases huv : v = window6Toggle i u
  · have hvu : u = window6Toggle i v := (window6Toggle_eq_swap_iff i u v).mp huv
    rw [window6ToggleMatrix, if_pos huv, window6ToggleMatrix, if_pos hvu]
  · have hvu : u ≠ window6Toggle i v := by
      intro h
      exact huv ((window6Toggle_eq_swap_iff i u v).mpr h)
    rw [window6ToggleMatrix, if_neg huv, window6ToggleMatrix, if_neg hvu]

/-- The window-`6` Lie generators are symmetric: the involution `ω ↦ ω ⊕ e_i` pairs each witness
for `(u,v)` with a witness for `(v,u)`.
    lem:window6-li-symmetric -/
theorem paper_window6_li_symmetric :
    ∀ i : Fin 6, (window6ToggleMatrix i).IsSymm := by
  intro i
  ext u v
  exact window6ToggleMatrix_entry_swap i v u

end Omega.GU
