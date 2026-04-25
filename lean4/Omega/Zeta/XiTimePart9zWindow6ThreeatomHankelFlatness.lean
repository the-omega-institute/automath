import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The window-`6` moment sequence attached to the three-atom measure
`8 δ₂ + 4 δ₃ + 9 δ₄`. -/
def xi_time_part9z_window6_threeatom_hankel_flatness_moment (n : ℕ) : ℚ :=
  8 * 2 ^ n + 4 * 3 ^ n + 9 * 4 ^ n

/-- The `3 × 3` Hankel block `H₂`. -/
def xi_time_part9z_window6_threeatom_hankel_flatness_H2 : Matrix (Fin 3) (Fin 3) ℚ :=
  fun i j => xi_time_part9z_window6_threeatom_hankel_flatness_moment (i.1 + j.1)

/-- The `4 × 4` Hankel block `H₃`. -/
def xi_time_part9z_window6_threeatom_hankel_flatness_H3 : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => xi_time_part9z_window6_threeatom_hankel_flatness_moment (i.1 + j.1)

/-- The square Vandermonde block for the support points `2,3,4`. -/
def xi_time_part9z_window6_threeatom_hankel_flatness_V2 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1 : ℚ), 1, 1;
     2, 3, 4;
     4, 9, 16]

/-- The rectangular Vandermonde block for the support points `2,3,4`. -/
def xi_time_part9z_window6_threeatom_hankel_flatness_V3 : Matrix (Fin 4) (Fin 3) ℚ :=
  !![(1 : ℚ), 1, 1;
     2, 3, 4;
     4, 9, 16;
     8, 27, 64]

/-- The diagonal weight matrix `diag(8,4,9)`. -/
def xi_time_part9z_window6_threeatom_hankel_flatness_D : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(8 : ℚ), 0, 0;
     0, 4, 0;
     0, 0, 9]

private lemma xi_time_part9z_window6_threeatom_hankel_flatness_H2_factor :
    xi_time_part9z_window6_threeatom_hankel_flatness_H2 =
      xi_time_part9z_window6_threeatom_hankel_flatness_V2 *
        xi_time_part9z_window6_threeatom_hankel_flatness_D *
          xi_time_part9z_window6_threeatom_hankel_flatness_V2.transpose := by
  native_decide

private lemma xi_time_part9z_window6_threeatom_hankel_flatness_H3_factor :
    xi_time_part9z_window6_threeatom_hankel_flatness_H3 =
      xi_time_part9z_window6_threeatom_hankel_flatness_V3 *
        xi_time_part9z_window6_threeatom_hankel_flatness_D *
          xi_time_part9z_window6_threeatom_hankel_flatness_V3.transpose := by
  native_decide

/-- Paper label: `thm:xi-time-part9z-window6-threeatom-hankel-flatness`. The window-`6`
three-atom moment Hankel blocks factor through the Vandermonde matrix at the support points
`2,3,4`; the `3 × 3` block has determinant `1152`, while the `4 × 4` block has rank at most `3`
and therefore determinant `0`. -/
theorem paper_xi_time_part9z_window6_threeatom_hankel_flatness :
    xi_time_part9z_window6_threeatom_hankel_flatness_H2 =
        xi_time_part9z_window6_threeatom_hankel_flatness_V2 *
          xi_time_part9z_window6_threeatom_hankel_flatness_D *
            xi_time_part9z_window6_threeatom_hankel_flatness_V2.transpose ∧
      xi_time_part9z_window6_threeatom_hankel_flatness_H3 =
        xi_time_part9z_window6_threeatom_hankel_flatness_V3 *
          xi_time_part9z_window6_threeatom_hankel_flatness_D *
            xi_time_part9z_window6_threeatom_hankel_flatness_V3.transpose ∧
      xi_time_part9z_window6_threeatom_hankel_flatness_H2.rank = 3 ∧
      xi_time_part9z_window6_threeatom_hankel_flatness_H3.rank ≤ 3 ∧
      Matrix.det xi_time_part9z_window6_threeatom_hankel_flatness_H2 = 1152 ∧
      Matrix.det xi_time_part9z_window6_threeatom_hankel_flatness_H3 = 0 := by
  refine ⟨xi_time_part9z_window6_threeatom_hankel_flatness_H2_factor,
    xi_time_part9z_window6_threeatom_hankel_flatness_H3_factor, ?_, ?_, ?_, ?_⟩
  · have hdet :
        Matrix.det xi_time_part9z_window6_threeatom_hankel_flatness_H2 = 1152 := by
      norm_num [xi_time_part9z_window6_threeatom_hankel_flatness_H2,
        xi_time_part9z_window6_threeatom_hankel_flatness_moment, Matrix.det_fin_three]
    have hdet_ne :
        Matrix.det xi_time_part9z_window6_threeatom_hankel_flatness_H2 ≠ 0 := by
      rw [hdet]
      norm_num
    have hunit :
        IsUnit xi_time_part9z_window6_threeatom_hankel_flatness_H2 := by
      exact
          (Matrix.isUnit_iff_isUnit_det
            (A := xi_time_part9z_window6_threeatom_hankel_flatness_H2)).2
            (isUnit_iff_ne_zero.mpr hdet_ne)
    simpa using Matrix.rank_of_isUnit xi_time_part9z_window6_threeatom_hankel_flatness_H2 hunit
  · calc
      xi_time_part9z_window6_threeatom_hankel_flatness_H3.rank
          = (xi_time_part9z_window6_threeatom_hankel_flatness_V3 *
              xi_time_part9z_window6_threeatom_hankel_flatness_D *
                xi_time_part9z_window6_threeatom_hankel_flatness_V3.transpose).rank := by
              rw [xi_time_part9z_window6_threeatom_hankel_flatness_H3_factor]
      _ ≤ (xi_time_part9z_window6_threeatom_hankel_flatness_V3 *
            xi_time_part9z_window6_threeatom_hankel_flatness_D).rank := by
            exact Matrix.rank_mul_le_left _ _
      _ ≤ xi_time_part9z_window6_threeatom_hankel_flatness_D.rank := by
            exact Matrix.rank_mul_le_right _ _
      _ ≤ 3 := by
            simpa using
              (Matrix.rank_le_card_height
                xi_time_part9z_window6_threeatom_hankel_flatness_D)
  · norm_num [xi_time_part9z_window6_threeatom_hankel_flatness_H2,
      xi_time_part9z_window6_threeatom_hankel_flatness_moment, Matrix.det_fin_three]
  · have hrank :
        xi_time_part9z_window6_threeatom_hankel_flatness_H3.rank ≤ 3 := by
      calc
        xi_time_part9z_window6_threeatom_hankel_flatness_H3.rank
            = (xi_time_part9z_window6_threeatom_hankel_flatness_V3 *
                xi_time_part9z_window6_threeatom_hankel_flatness_D *
                  xi_time_part9z_window6_threeatom_hankel_flatness_V3.transpose).rank := by
                rw [xi_time_part9z_window6_threeatom_hankel_flatness_H3_factor]
        _ ≤ (xi_time_part9z_window6_threeatom_hankel_flatness_V3 *
              xi_time_part9z_window6_threeatom_hankel_flatness_D).rank := by
              exact Matrix.rank_mul_le_left _ _
        _ ≤ xi_time_part9z_window6_threeatom_hankel_flatness_D.rank := by
              exact Matrix.rank_mul_le_right _ _
        _ ≤ 3 := by
              simpa using
                (Matrix.rank_le_card_height
                  xi_time_part9z_window6_threeatom_hankel_flatness_D)
    by_contra hdet
    have hunit :
        IsUnit xi_time_part9z_window6_threeatom_hankel_flatness_H3 := by
      exact
        (Matrix.isUnit_iff_isUnit_det
          (A := xi_time_part9z_window6_threeatom_hankel_flatness_H3)).2
          (isUnit_iff_ne_zero.mpr hdet)
    have hfull :
        xi_time_part9z_window6_threeatom_hankel_flatness_H3.rank = 4 := by
      simpa using Matrix.rank_of_isUnit xi_time_part9z_window6_threeatom_hankel_flatness_H3 hunit
    omega

end Omega.Zeta
