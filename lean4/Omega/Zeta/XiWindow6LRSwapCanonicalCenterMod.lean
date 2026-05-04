import Mathlib.Tactic

namespace Omega.Zeta

/-- The canonical window-`6` center, written in the basis `(a,b,c)`. -/
abbrev xi_window6_lr_swap_canonical_center_mod_center :=
  Fin 3 → ZMod 2

/-- The left--right swap fixes `a` and exchanges `b` with `c`. -/
def xi_window6_lr_swap_canonical_center_mod_swap
    (x : xi_window6_lr_swap_canonical_center_mod_center) :
    xi_window6_lr_swap_canonical_center_mod_center :=
  ![x 0, x 2, x 1]

/-- The projection detecting the exchanged left/right channel. -/
def xi_window6_lr_swap_canonical_center_mod_projection
    (x : xi_window6_lr_swap_canonical_center_mod_center) : ZMod 2 :=
  x 1 + x 2

/-- Kernel of the LR projection. -/
def xi_window6_lr_swap_canonical_center_mod_kernel :
    Set xi_window6_lr_swap_canonical_center_mod_center :=
  {x | xi_window6_lr_swap_canonical_center_mod_projection x = 0}

/-- Fixed points of the LR swap. -/
def xi_window6_lr_swap_canonical_center_mod_fixed :
    Set xi_window6_lr_swap_canonical_center_mod_center :=
  {x | xi_window6_lr_swap_canonical_center_mod_swap x = x}

/-- Coordinate equality in `ZMod 2`: `b+c=0` iff `b=c`. -/
theorem xi_window6_lr_swap_canonical_center_mod_add_eq_zero_iff_eq
    (b c : ZMod 2) : b + c = 0 ↔ b = c := by
  constructor
  · intro h
    rw [add_eq_zero_iff_eq_neg] at h
    simpa [ZMod.neg_eq_self_mod_two] using h
  · intro h
    rw [h]
    exact CharTwo.add_self_eq_zero c

/-- The LR projection kernel is exactly the LR-swap fixed locus. -/
def xi_window6_lr_swap_canonical_center_mod_kernel_eq_fixed : Prop :=
  xi_window6_lr_swap_canonical_center_mod_kernel =
    xi_window6_lr_swap_canonical_center_mod_fixed

/-- The LR projection kernel is exactly the LR-swap fixed locus. -/
theorem xi_window6_lr_swap_canonical_center_mod_kernel_eq_fixed_proof :
    xi_window6_lr_swap_canonical_center_mod_kernel_eq_fixed := by
  ext x
  constructor
  · intro hx
    have hcoord : x 1 = x 2 := by
      exact (xi_window6_lr_swap_canonical_center_mod_add_eq_zero_iff_eq (x 1) (x 2)).mp
        (by simpa [xi_window6_lr_swap_canonical_center_mod_kernel,
          xi_window6_lr_swap_canonical_center_mod_projection] using hx)
    ext i
    fin_cases i
    · simp [xi_window6_lr_swap_canonical_center_mod_swap]
    · simpa [xi_window6_lr_swap_canonical_center_mod_swap] using hcoord.symm
    · simpa [xi_window6_lr_swap_canonical_center_mod_swap] using hcoord
  · intro hx
    have hcoord : x 2 = x 1 := by
      have hraw := congrArg (fun f : xi_window6_lr_swap_canonical_center_mod_center => f 1) hx
      simpa [xi_window6_lr_swap_canonical_center_mod_swap] using hraw
    simpa [xi_window6_lr_swap_canonical_center_mod_kernel,
      xi_window6_lr_swap_canonical_center_mod_projection,
      xi_window6_lr_swap_canonical_center_mod_add_eq_zero_iff_eq] using hcoord.symm

/-- The fixed locus has the two free coordinates `(a,b)`. -/
def xi_window6_lr_swap_canonical_center_mod_fixed_equiv :
    {x : xi_window6_lr_swap_canonical_center_mod_center //
      xi_window6_lr_swap_canonical_center_mod_swap x = x} ≃ ZMod 2 × ZMod 2 where
  toFun x := (x.1 0, x.1 1)
  invFun ab :=
    ⟨![ab.1, ab.2, ab.2], by
      ext i
      fin_cases i <;> simp [xi_window6_lr_swap_canonical_center_mod_swap]⟩
  left_inv x := by
    ext i
    fin_cases i
    · simp
    · simp
    · have hcoord :
          xi_window6_lr_swap_canonical_center_mod_swap x.1 2 = x.1 2 := by
        exact congrArg (fun f : xi_window6_lr_swap_canonical_center_mod_center => f 2)
          x.2
      simpa [xi_window6_lr_swap_canonical_center_mod_swap] using hcoord
  right_inv ab := by
    cases ab
    rfl

/-- The fixed locus has cardinality `4`. -/
def xi_window6_lr_swap_canonical_center_mod_card_fixed : ℕ :=
  Fintype.card
    {x : xi_window6_lr_swap_canonical_center_mod_center //
      xi_window6_lr_swap_canonical_center_mod_swap x = x}

/-- Paper label: `thm:xi-window6-lr-swap-canonical-center-mod`. -/
theorem paper_xi_window6_lr_swap_canonical_center_mod :
    xi_window6_lr_swap_canonical_center_mod_kernel_eq_fixed ∧
      xi_window6_lr_swap_canonical_center_mod_card_fixed = 4 := by
  constructor
  · exact xi_window6_lr_swap_canonical_center_mod_kernel_eq_fixed_proof
  · unfold xi_window6_lr_swap_canonical_center_mod_card_fixed
    rw [Fintype.card_congr xi_window6_lr_swap_canonical_center_mod_fixed_equiv]
    simp [Fintype.card_prod, ZMod.card]

end Omega.Zeta
