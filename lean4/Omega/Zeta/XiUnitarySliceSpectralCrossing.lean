import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

noncomputable section

/-- Concrete completed-section and determinant data on a finite unitary slice. -/
structure xi_unitary_slice_spectral_crossing_data where
  xi_unitary_slice_spectral_crossing_size : ℕ
  xi_unitary_slice_spectral_crossing_xi : ℂ → ℂ
  xi_unitary_slice_spectral_crossing_prefactor : ℝ → ℂ
  xi_unitary_slice_spectral_crossing_prefactor_ne :
    ∀ t, xi_unitary_slice_spectral_crossing_prefactor t ≠ 0
  xi_unitary_slice_spectral_crossing_uL : ℝ → ℂ
  xi_unitary_slice_spectral_crossing_zL : ℝ → ℂ
  xi_unitary_slice_spectral_crossing_operator :
    Matrix (Fin xi_unitary_slice_spectral_crossing_size)
      (Fin xi_unitary_slice_spectral_crossing_size) ℂ
  xi_unitary_slice_spectral_crossing_uL_eq_zL :
    ∀ t : ℝ, xi_unitary_slice_spectral_crossing_uL t = xi_unitary_slice_spectral_crossing_zL t
  xi_unitary_slice_spectral_crossing_completed_section :
    ∀ t : ℝ,
      xi_unitary_slice_spectral_crossing_xi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
        xi_unitary_slice_spectral_crossing_prefactor t *
          Matrix.det
            (1 -
              xi_unitary_slice_spectral_crossing_uL t •
                xi_unitary_slice_spectral_crossing_operator)
  xi_unitary_slice_spectral_crossing_det_zero_iff_eigenvalue_one :
    ∀ t : ℝ,
      Matrix.det
          (1 -
            xi_unitary_slice_spectral_crossing_zL t •
              xi_unitary_slice_spectral_crossing_operator) = 0 ↔
        ∃ v : Fin xi_unitary_slice_spectral_crossing_size → ℂ,
          v ≠ 0 ∧
            Matrix.mulVec xi_unitary_slice_spectral_crossing_operator v =
              xi_unitary_slice_spectral_crossing_zL t⁻¹ • v

namespace xi_unitary_slice_spectral_crossing_data

/-- The critical-line parameter `s = 1/2 + i t`. -/
def xi_unitary_slice_spectral_crossing_slice
    (_D : xi_unitary_slice_spectral_crossing_data) (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- The determinant appearing after substituting the unitary-slice coordinate. -/
def xi_unitary_slice_spectral_crossing_determinant
    (D : xi_unitary_slice_spectral_crossing_data) (t : ℝ) : ℂ :=
  Matrix.det
    (1 -
      D.xi_unitary_slice_spectral_crossing_zL t •
        D.xi_unitary_slice_spectral_crossing_operator)

/-- The eigenvalue-one crossing predicate for the normalized slice variable. -/
def xi_unitary_slice_spectral_crossing_has_eigenvalue_one
    (D : xi_unitary_slice_spectral_crossing_data) (t : ℝ) : Prop :=
  ∃ v : Fin D.xi_unitary_slice_spectral_crossing_size → ℂ,
    v ≠ 0 ∧
      Matrix.mulVec D.xi_unitary_slice_spectral_crossing_operator v =
        D.xi_unitary_slice_spectral_crossing_zL t⁻¹ • v

end xi_unitary_slice_spectral_crossing_data

/-- Paper-facing statement: on the completed unitary slice, zeros of the section are exactly
spectral crossings of the normalized determinant. -/
def xi_unitary_slice_spectral_crossing_statement
    (D : xi_unitary_slice_spectral_crossing_data) : Prop :=
  ∀ t,
    D.xi_unitary_slice_spectral_crossing_xi
        (D.xi_unitary_slice_spectral_crossing_slice t) = 0 ↔
      D.xi_unitary_slice_spectral_crossing_has_eigenvalue_one t

/-- Paper label: `prop:xi-unitary-slice-spectral-crossing`. -/
theorem paper_xi_unitary_slice_spectral_crossing
    (D : xi_unitary_slice_spectral_crossing_data) :
    xi_unitary_slice_spectral_crossing_statement D := by
  intro t
  rw [xi_unitary_slice_spectral_crossing_data.xi_unitary_slice_spectral_crossing_slice,
    D.xi_unitary_slice_spectral_crossing_completed_section t]
  have hdet :
      Matrix.det
          (1 -
            D.xi_unitary_slice_spectral_crossing_uL t •
              D.xi_unitary_slice_spectral_crossing_operator) =
        Matrix.det
          (1 -
            D.xi_unitary_slice_spectral_crossing_zL t •
              D.xi_unitary_slice_spectral_crossing_operator) := by
    rw [D.xi_unitary_slice_spectral_crossing_uL_eq_zL t]
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with hpref | hdetzero
    · exact False.elim (D.xi_unitary_slice_spectral_crossing_prefactor_ne t hpref)
    · exact
        (D.xi_unitary_slice_spectral_crossing_det_zero_iff_eigenvalue_one t).mp
          (by rwa [hdet] at hdetzero)
  · intro h
    right
    rw [hdet]
    exact (D.xi_unitary_slice_spectral_crossing_det_zero_iff_eigenvalue_one t).mpr h

end

end Omega.Zeta
