import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- Concrete two-coordinate affine centralizer data.  The scalar `lambda` has no fixed
translation vector, which is the abstract 2-adic input used to force the affine translation
part to vanish. -/
structure xi_time_part69d_godel_tate_affine_centralizer_complete_data where
  R : Type u
  inst : CommRing R
  lambda : R
  dilation_fixed_zero : ∀ t : R × R, t = lambda • t → t = 0

abbrev xi_time_part69d_godel_tate_affine_centralizer_complete_module
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data) : Type u :=
  D.R × D.R

abbrev xi_time_part69d_godel_tate_affine_centralizer_complete_linear
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data) : Type u := by
  letI := D.inst
  exact
    xi_time_part69d_godel_tate_affine_centralizer_complete_module D →ₗ[D.R]
      xi_time_part69d_godel_tate_affine_centralizer_complete_module D

structure xi_time_part69d_godel_tate_affine_centralizer_complete_affine
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data) where
  linear : xi_time_part69d_godel_tate_affine_centralizer_complete_linear D
  trans : xi_time_part69d_godel_tate_affine_centralizer_complete_module D

def xi_time_part69d_godel_tate_affine_centralizer_complete_eval
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data)
    (F : xi_time_part69d_godel_tate_affine_centralizer_complete_affine D)
    (x : xi_time_part69d_godel_tate_affine_centralizer_complete_module D) :
    xi_time_part69d_godel_tate_affine_centralizer_complete_module D := by
  letI := D.inst
  exact F.linear x + F.trans

def xi_time_part69d_godel_tate_affine_centralizer_complete_line
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data) (a : D.R) :
    xi_time_part69d_godel_tate_affine_centralizer_complete_module D := by
  letI := D.inst
  exact (a, 0)

def xi_time_part69d_godel_tate_affine_centralizer_complete_commutes_translations
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data)
    (F : xi_time_part69d_godel_tate_affine_centralizer_complete_affine D) : Prop := by
  letI := D.inst
  exact ∀ a x,
    xi_time_part69d_godel_tate_affine_centralizer_complete_eval D F
        (x + xi_time_part69d_godel_tate_affine_centralizer_complete_line D a) =
      xi_time_part69d_godel_tate_affine_centralizer_complete_eval D F x +
        xi_time_part69d_godel_tate_affine_centralizer_complete_line D a

def xi_time_part69d_godel_tate_affine_centralizer_complete_commutes_dilation
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data)
    (F : xi_time_part69d_godel_tate_affine_centralizer_complete_affine D) : Prop := by
  letI := D.inst
  exact ∀ x,
    xi_time_part69d_godel_tate_affine_centralizer_complete_eval D F (D.lambda • x) =
      D.lambda • xi_time_part69d_godel_tate_affine_centralizer_complete_eval D F x

def xi_time_part69d_godel_tate_affine_centralizer_complete_upper_triangular_fixed_first
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data)
    (A : xi_time_part69d_godel_tate_affine_centralizer_complete_linear D) : Prop := by
  letI := D.inst
  exact ∃ b d : D.R, ∀ x : xi_time_part69d_godel_tate_affine_centralizer_complete_module D,
    A x = (x.1 + b * x.2, d * x.2)

def xi_time_part69d_godel_tate_affine_centralizer_complete_statement
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data) : Prop := by
  letI := D.inst
  exact ∀ F : xi_time_part69d_godel_tate_affine_centralizer_complete_affine D,
    xi_time_part69d_godel_tate_affine_centralizer_complete_commutes_translations D F →
      xi_time_part69d_godel_tate_affine_centralizer_complete_commutes_dilation D F →
        F.trans = 0 ∧
          (∀ a : D.R,
            F.linear (xi_time_part69d_godel_tate_affine_centralizer_complete_line D a) =
              xi_time_part69d_godel_tate_affine_centralizer_complete_line D a) ∧
          xi_time_part69d_godel_tate_affine_centralizer_complete_upper_triangular_fixed_first
            D F.linear

lemma xi_time_part69d_godel_tate_affine_centralizer_complete_linear_pair
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data)
    (A : xi_time_part69d_godel_tate_affine_centralizer_complete_linear D)
    (hA : ∀ a : D.R,
      A (xi_time_part69d_godel_tate_affine_centralizer_complete_line D a) =
        xi_time_part69d_godel_tate_affine_centralizer_complete_line D a) :
    xi_time_part69d_godel_tate_affine_centralizer_complete_upper_triangular_fixed_first D A := by
  letI := D.inst
  refine ⟨(A (0, 1)).1, (A (0, 1)).2, ?_⟩
  intro x
  have hx :
      x = x.1 • (1, 0) + x.2 • (0, 1) := by
    ext <;> simp
  have hA_one : A (1, 0) = (1, 0) := by
    simpa [xi_time_part69d_godel_tate_affine_centralizer_complete_line] using hA 1
  rw [hx, map_add, map_smul, map_smul, hA_one]
  ext <;> simp [mul_comm]

/-- Paper label:
`thm:xi-time-part69d-godel-tate-affine-centralizer-complete`.  An affine map on the
two-coordinate module that commutes with all translations along the closed first-coordinate
line and with a dilation whose only fixed translation is zero has zero translation part and a
linear part represented, in the chosen basis, by an upper-triangular matrix with fixed first
column. -/
theorem paper_xi_time_part69d_godel_tate_affine_centralizer_complete
    (D : xi_time_part69d_godel_tate_affine_centralizer_complete_data) :
    xi_time_part69d_godel_tate_affine_centralizer_complete_statement D := by
  letI := D.inst
  intro F htrans hdil
  have htrans_eq_dil : F.trans = D.lambda • F.trans := by
    simpa [xi_time_part69d_godel_tate_affine_centralizer_complete_eval] using hdil 0
  have htrans_zero : F.trans = 0 := D.dilation_fixed_zero F.trans htrans_eq_dil
  have hline :
      ∀ a : D.R,
        F.linear (xi_time_part69d_godel_tate_affine_centralizer_complete_line D a) =
          xi_time_part69d_godel_tate_affine_centralizer_complete_line D a := by
    intro a
    have h := htrans a 0
    simpa [xi_time_part69d_godel_tate_affine_centralizer_complete_eval, htrans_zero]
      using h
  exact
    ⟨htrans_zero, hline,
      xi_time_part69d_godel_tate_affine_centralizer_complete_linear_pair D F.linear hline⟩

end Omega.Zeta
