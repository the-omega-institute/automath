import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zcWindow6OrthogonalPolynomialsCubicTermination

set_option linter.unnecessarySeqFocus false

namespace Omega.Zeta

open Matrix

/-- The explicit Cartan-to-Lanczos change-of-basis matrix. -/
noncomputable def xi_time_part9zc_window6_cartan_lanczos_conjugacy_U :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![(1 / 2 : ℝ), Real.sqrt 3 / 4, 3 / 4;
    -7 * Real.sqrt 183 / 122, -5 * Real.sqrt 61 / 244, 11 * Real.sqrt 183 / 244;
    3 * Real.sqrt 61 / 61, -4 * Real.sqrt 183 / 61, 2 * Real.sqrt 61 / 61]

/-- The spin-1 Cartan observable `diag(2,3,4)`. -/
def xi_time_part9zc_window6_cartan_lanczos_conjugacy_C :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![(2 : ℝ), 0, 0;
    0, 3, 0;
    0, 0, 4]

/-- The Jacobi--Lanczos Hamiltonian for the three-atom window-6 law. -/
noncomputable def xi_time_part9zc_window6_cartan_lanczos_conjugacy_J :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![(53 / 16 : ℝ), Real.sqrt 183 / 16, 0;
    Real.sqrt 183 / 16, 2703 / 976, 16 * Real.sqrt 3 / 61;
    0, 16 * Real.sqrt 3 / 61, 178 / 61]

/-- Concrete statement for `thm:xi-time-part9zc-window6-cartan-lanczos-conjugacy`. -/
def xi_time_part9zc_window6_cartan_lanczos_conjugacy_statement : Prop :=
  xi_time_part9zc_window6_cartan_lanczos_conjugacy_U *
      xi_time_part9zc_window6_cartan_lanczos_conjugacy_U.transpose =
    (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
    xi_time_part9zc_window6_cartan_lanczos_conjugacy_U.det = 1 ∧
    xi_time_part9zc_window6_cartan_lanczos_conjugacy_U *
        xi_time_part9zc_window6_cartan_lanczos_conjugacy_C *
        xi_time_part9zc_window6_cartan_lanczos_conjugacy_U.transpose =
      xi_time_part9zc_window6_cartan_lanczos_conjugacy_J

/-- Paper label: `thm:xi-time-part9zc-window6-cartan-lanczos-conjugacy`. -/
theorem paper_xi_time_part9zc_window6_cartan_lanczos_conjugacy :
    xi_time_part9zc_window6_cartan_lanczos_conjugacy_statement := by
  have h61sq : (Real.sqrt (61 : ℝ)) ^ 2 = 61 := by
    rw [Real.sq_sqrt (by norm_num)]
  have h183sq : (Real.sqrt (183 : ℝ)) ^ 2 = 183 := by
    rw [Real.sq_sqrt (by norm_num)]
  have h3sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
    rw [Real.sq_sqrt (by norm_num)]
  have h18361 :
      Real.sqrt (183 : ℝ) * Real.sqrt (61 : ℝ) = 61 * Real.sqrt (3 : ℝ) := by
    calc
      Real.sqrt (183 : ℝ) * Real.sqrt (61 : ℝ) = Real.sqrt ((183 : ℝ) * 61) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 183)]
      _ = Real.sqrt ((61 : ℝ) * 61 * 3) := by norm_num
      _ = Real.sqrt ((61 : ℝ) * 61) * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 61 * 61)]
      _ = 61 * Real.sqrt 3 := by
        rw [Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 61)]
  have h61183 :
      Real.sqrt (61 : ℝ) * Real.sqrt (183 : ℝ) = 61 * Real.sqrt (3 : ℝ) := by
    rw [mul_comm, h18361]
  have h361 : Real.sqrt (3 : ℝ) * Real.sqrt (61 : ℝ) = Real.sqrt (183 : ℝ) := by
    calc
      Real.sqrt (3 : ℝ) * Real.sqrt (61 : ℝ) = Real.sqrt ((3 : ℝ) * 61) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ = Real.sqrt (183 : ℝ) := by norm_num
  have h613 : Real.sqrt (61 : ℝ) * Real.sqrt (3 : ℝ) = Real.sqrt (183 : ℝ) := by
    rw [mul_comm, h361]
  have h3183 :
      Real.sqrt (3 : ℝ) * Real.sqrt (183 : ℝ) = 3 * Real.sqrt (61 : ℝ) := by
    calc
      Real.sqrt (3 : ℝ) * Real.sqrt (183 : ℝ) = Real.sqrt ((3 : ℝ) * 183) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ = Real.sqrt ((3 : ℝ) * 3 * 61) := by norm_num
      _ = Real.sqrt ((3 : ℝ) * 3) * Real.sqrt 61 := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 * 3)]
      _ = 3 * Real.sqrt 61 := by
        rw [Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 3)]
  have h1833 :
      Real.sqrt (183 : ℝ) * Real.sqrt (3 : ℝ) = 3 * Real.sqrt (61 : ℝ) := by
    rw [mul_comm, h3183]
  unfold xi_time_part9zc_window6_cartan_lanczos_conjugacy_statement
  refine ⟨?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [xi_time_part9zc_window6_cartan_lanczos_conjugacy_U, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_three] <;>
      ring_nf <;>
      simp only [h61sq, h183sq, h3sq, h361, h613, h3183, h1833] <;>
      ring_nf
  · rw [Matrix.det_fin_three]
    simp [xi_time_part9zc_window6_cartan_lanczos_conjugacy_U]
    ring_nf
    rw [h61183, h61sq, h183sq]
    ring_nf
    rw [h3sq]
    norm_num
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [xi_time_part9zc_window6_cartan_lanczos_conjugacy_U,
        xi_time_part9zc_window6_cartan_lanczos_conjugacy_C,
        xi_time_part9zc_window6_cartan_lanczos_conjugacy_J, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_three] <;>
      ring_nf <;>
      simp only [h61sq, h183sq, h3sq, h18361, h61183, h361, h613, h3183, h1833] <;>
      ring_nf

end Omega.Zeta
