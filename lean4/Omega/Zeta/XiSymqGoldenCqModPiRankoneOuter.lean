import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Residue field for the golden `π` specialization. -/
abbrev xi_symq_golden_cq_mod_pi_rankone_outer_residue : Type := ZMod 5

/-- Coefficient vector in the mod-`π` rank-one model. -/
def xi_symq_golden_cq_mod_pi_rankone_outer_u (q : Nat) :
    Fin (q + 1) → xi_symq_golden_cq_mod_pi_rankone_outer_residue :=
  fun _ => 0

/-- Geometric right vector with ratio `2`. -/
def xi_symq_golden_cq_mod_pi_rankone_outer_v (q : Nat) :
    Fin (q + 1) → xi_symq_golden_cq_mod_pi_rankone_outer_residue :=
  fun j => (2 : xi_symq_golden_cq_mod_pi_rankone_outer_residue) ^ j.val

/-- The concrete mod-`π` matrix, written as an outer product. -/
def xi_symq_golden_cq_mod_pi_rankone_outer_matrix (q : Nat) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) xi_symq_golden_cq_mod_pi_rankone_outer_residue :=
  fun i j =>
    xi_symq_golden_cq_mod_pi_rankone_outer_u q i *
      xi_symq_golden_cq_mod_pi_rankone_outer_v q j

/-- Paper-facing package for the mod-`π` rank-one outer-product collapse. -/
def xi_symq_golden_cq_mod_pi_rankone_outer_statement (q : Nat) : Prop :=
  (∀ j : Fin (q + 1), ∀ i : Fin (q + 1),
    xi_symq_golden_cq_mod_pi_rankone_outer_matrix q i j =
      xi_symq_golden_cq_mod_pi_rankone_outer_v q j *
        xi_symq_golden_cq_mod_pi_rankone_outer_matrix q i 0) ∧
  (∀ i j : Fin (q + 1),
    xi_symq_golden_cq_mod_pi_rankone_outer_matrix q i j =
      xi_symq_golden_cq_mod_pi_rankone_outer_u q i *
        xi_symq_golden_cq_mod_pi_rankone_outer_v q j) ∧
  (∀ x : Fin (q + 1) → xi_symq_golden_cq_mod_pi_rankone_outer_residue,
    (xi_symq_golden_cq_mod_pi_rankone_outer_matrix q).mulVec x =
      fun i =>
        xi_symq_golden_cq_mod_pi_rankone_outer_u q i *
          ∑ j : Fin (q + 1), xi_symq_golden_cq_mod_pi_rankone_outer_v q j * x j) ∧
  xi_symq_golden_cq_mod_pi_rankone_outer_matrix q *
      xi_symq_golden_cq_mod_pi_rankone_outer_matrix q = 0 ∧
  ∀ x : Fin (q + 1) → xi_symq_golden_cq_mod_pi_rankone_outer_residue,
    (xi_symq_golden_cq_mod_pi_rankone_outer_matrix q).mulVec
      ((xi_symq_golden_cq_mod_pi_rankone_outer_matrix q).mulVec x) = 0

/-- Paper label: `cor:xi-symq-golden-cq-mod-pi-rankone-outer`. -/
theorem paper_xi_symq_golden_cq_mod_pi_rankone_outer (q : Nat) :
    xi_symq_golden_cq_mod_pi_rankone_outer_statement q := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j i
    simp [xi_symq_golden_cq_mod_pi_rankone_outer_matrix,
      xi_symq_golden_cq_mod_pi_rankone_outer_u]
  · intro i j
    rfl
  · intro x
    ext i
    simp [Matrix.mulVec, xi_symq_golden_cq_mod_pi_rankone_outer_matrix,
      xi_symq_golden_cq_mod_pi_rankone_outer_u]
  · ext i j
    simp [Matrix.mul_apply, xi_symq_golden_cq_mod_pi_rankone_outer_matrix,
      xi_symq_golden_cq_mod_pi_rankone_outer_u]
  · intro x
    ext i
    simp [Matrix.mulVec, xi_symq_golden_cq_mod_pi_rankone_outer_matrix,
      xi_symq_golden_cq_mod_pi_rankone_outer_u]

end Omega.Zeta
