import Mathlib

namespace Omega.GU

open scoped BigOperators

/-- The prefixed finite `𝔽₂` boundary parity module on the three boundary axes. -/
abbrev xi_window6_boundary_parity_c3_module_splitting_module :=
  Fin 3 → ZMod 2

/-- The cyclic generator on the three boundary axes, written on coordinates. -/
def xi_window6_boundary_parity_c3_module_splitting_shift
    (v : xi_window6_boundary_parity_c3_module_splitting_module) :
    xi_window6_boundary_parity_c3_module_splitting_module :=
  fun i =>
    if i = (0 : Fin 3) then v 2
    else if i = (1 : Fin 3) then v 0
    else v 1

/-- The constant-vector line in the boundary parity module. -/
def xi_window6_boundary_parity_c3_module_splitting_const (c : ZMod 2) :
    xi_window6_boundary_parity_c3_module_splitting_module :=
  fun _ => c

/-- The augmentation functional cutting out the two-dimensional complementary cycle module. -/
def xi_window6_boundary_parity_c3_module_splitting_aug
    (v : xi_window6_boundary_parity_c3_module_splitting_module) : ZMod 2 :=
  v 0 + v 1 + v 2

/-- Concrete finite model for the window-6 boundary parity `C₃`-module splitting. It records the
three-dimensional permutation module, the order-three cyclic action, the unique fixed line of
constant vectors, and the invariant two-dimensional augmentation kernel. -/
def xi_window6_boundary_parity_c3_module_splitting_spec : Prop :=
  Fintype.card xi_window6_boundary_parity_c3_module_splitting_module = 8 ∧
    (∀ v : xi_window6_boundary_parity_c3_module_splitting_module,
      (xi_window6_boundary_parity_c3_module_splitting_shift^[3]) v = v) ∧
    (∀ v : xi_window6_boundary_parity_c3_module_splitting_module,
      xi_window6_boundary_parity_c3_module_splitting_shift v = v ↔
        ∃ c : ZMod 2, v = xi_window6_boundary_parity_c3_module_splitting_const c) ∧
    (∀ v : xi_window6_boundary_parity_c3_module_splitting_module,
      xi_window6_boundary_parity_c3_module_splitting_aug
          (xi_window6_boundary_parity_c3_module_splitting_shift v) =
        xi_window6_boundary_parity_c3_module_splitting_aug v) ∧
    (∀ v : xi_window6_boundary_parity_c3_module_splitting_module,
      xi_window6_boundary_parity_c3_module_splitting_aug v = 0 ↔
        v = 0 ∨
          v = (fun i => if i = (0 : Fin 3) then 1 else if i = (1 : Fin 3) then 1 else 0) ∨
          v = (fun i => if i = (0 : Fin 3) then 1 else if i = (2 : Fin 3) then 1 else 0) ∨
          v = (fun i => if i = (1 : Fin 3) then 1 else if i = (2 : Fin 3) then 1 else 0)) ∧
    (∀ v :
        {v : xi_window6_boundary_parity_c3_module_splitting_module //
          xi_window6_boundary_parity_c3_module_splitting_aug v = 0},
      xi_window6_boundary_parity_c3_module_splitting_shift v.1 = v.1 → v.1 = 0)

/-- Paper label: `thm:xi-window6-boundary-parity-c3-module-splitting`. -/
theorem paper_xi_window6_boundary_parity_c3_module_splitting :
    xi_window6_boundary_parity_c3_module_splitting_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_fun]
    norm_num [Fintype.card_fin]
  · intro v
    ext i
    fin_cases i <;> simp [xi_window6_boundary_parity_c3_module_splitting_shift]
  · intro v
    constructor
    · intro hfix
      refine ⟨v 0, ?_⟩
      ext i
      fin_cases i
      · rfl
      · have h := congrArg (fun w : xi_window6_boundary_parity_c3_module_splitting_module =>
            w 1) hfix
        simpa [xi_window6_boundary_parity_c3_module_splitting_shift] using h.symm
      · have h := congrArg (fun w : xi_window6_boundary_parity_c3_module_splitting_module =>
            w 0) hfix
        simpa [xi_window6_boundary_parity_c3_module_splitting_shift] using h
    · rintro ⟨c, rfl⟩
      ext i
      fin_cases i <;>
        simp [xi_window6_boundary_parity_c3_module_splitting_shift,
          xi_window6_boundary_parity_c3_module_splitting_const]
  · intro v
    simp [xi_window6_boundary_parity_c3_module_splitting_aug,
      xi_window6_boundary_parity_c3_module_splitting_shift, add_assoc, add_left_comm, add_comm]
  · decide
  · intro v hfix
    rcases v with ⟨v, hv⟩
    have hvals : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have h10 : v 1 = v 0 := by
      have h := congrArg (fun w : xi_window6_boundary_parity_c3_module_splitting_module =>
        w 1) hfix
      simpa [xi_window6_boundary_parity_c3_module_splitting_shift] using h.symm
    have h20 : v 2 = v 0 := by
      have h := congrArg (fun w : xi_window6_boundary_parity_c3_module_splitting_module =>
        w 0) hfix
      simpa [xi_window6_boundary_parity_c3_module_splitting_shift] using h
    have h0zero : v 0 = 0 := by
      rcases hvals (v 0) with h0 | h0
      · exact h0
      · have htriple : v 0 + v 0 + v 0 = 0 := by
          simpa [xi_window6_boundary_parity_c3_module_splitting_aug, h10, h20] using hv
        have hbad : (1 : ZMod 2) + 1 + 1 = 0 := by
          simpa [h0] using htriple
        exact False.elim ((by decide : ¬ ((1 : ZMod 2) + 1 + 1 = 0)) hbad)
    ext i
    fin_cases i
    · exact h0zero
    · exact h10.trans h0zero
    · exact h20.trans h0zero

end Omega.GU
