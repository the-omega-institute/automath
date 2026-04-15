import Omega.Zeta.HankelVandermonde3Recovery
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

def hankel3 (ω1 ω2 ω3 a1 a2 a3 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![ω1 + ω2 + ω3,
     ω1 * a1 + ω2 * a2 + ω3 * a3,
     ω1 * a1^2 + ω2 * a2^2 + ω3 * a3^2;
     ω1 * a1 + ω2 * a2 + ω3 * a3,
     ω1 * a1^2 + ω2 * a2^2 + ω3 * a3^2,
     ω1 * a1^3 + ω2 * a2^3 + ω3 * a3^3;
     ω1 * a1^2 + ω2 * a2^2 + ω3 * a3^2,
     ω1 * a1^3 + ω2 * a2^3 + ω3 * a3^3,
     ω1 * a1^4 + ω2 * a2^4 + ω3 * a3^4]

/-- Scalar bridge: matrix-form Hankel3 determinant equals the pre-expanded scalar form.
    cor:xi-hankel-vs-prony-square-gap -/
theorem hankel3_det_eq_scalar
    (ω1 ω2 ω3 a1 a2 a3 : ℤ) :
    (hankel3 ω1 ω2 ω3 a1 a2 a3).det =
      hankel3DetScalar
        (hankelMoment0 ω1 ω2 ω3)
        (hankelMoment1 ω1 ω2 ω3 a1 a2 a3)
        (hankelMoment2 ω1 ω2 ω3 a1 a2 a3)
        (hankelMoment3 ω1 ω2 ω3 a1 a2 a3)
        (hankelMoment4 ω1 ω2 ω3 a1 a2 a3) := by
  -- Introduce abbreviations to compress the matrix entries before invoking the
  -- 3×3 determinant formula. This keeps `Matrix.det_fin_three` from triggering
  -- expensive whnf normalisation on the unfolded polynomial form.
  set m0 := hankelMoment0 ω1 ω2 ω3
  set m1 := hankelMoment1 ω1 ω2 ω3 a1 a2 a3
  set m2 := hankelMoment2 ω1 ω2 ω3 a1 a2 a3
  set m3 := hankelMoment3 ω1 ω2 ω3 a1 a2 a3
  set m4 := hankelMoment4 ω1 ω2 ω3 a1 a2 a3
  have hM : hankel3 ω1 ω2 ω3 a1 a2 a3 = !![m0, m1, m2; m1, m2, m3; m2, m3, m4] := rfl
  rw [hM, Matrix.det_fin_three]
  simp [hankel3DetScalar]
  ring

/-- 3×3 Hankel determinant equals the weighted Vandermonde square.
    cor:xi-hankel-vs-prony-square-gap -/
theorem hankel3_vandermonde_square
    (ω1 ω2 ω3 a1 a2 a3 : ℤ) :
    (hankel3 ω1 ω2 ω3 a1 a2 a3).det =
      ω1 * ω2 * ω3 * (a2 - a1)^2 * (a3 - a1)^2 * (a3 - a2)^2 := by
  rw [hankel3_det_eq_scalar]
  exact hankel3_vandermonde_square_scalar ω1 ω2 ω3 a1 a2 a3

/-- Hankel3 matrix determinant vanishes when a1 = a2.
    cor:xi-hankel-vs-prony-square-gap (matrix κ=3, a1=a2) -/
theorem hankel3_matrix_eq_zero_of_a1_a2
    (ω1 ω2 ω3 a a3 : ℤ) :
    (hankel3 ω1 ω2 ω3 a a a3).det = 0 := by
  rw [hankel3_vandermonde_square]
  ring

/-- Hankel3 matrix determinant vanishes when a2 = a3.
    cor:xi-hankel-vs-prony-square-gap (matrix κ=3, a2=a3) -/
theorem hankel3_matrix_eq_zero_of_a2_a3
    (ω1 ω2 ω3 a1 a : ℤ) :
    (hankel3 ω1 ω2 ω3 a1 a a).det = 0 := by
  rw [hankel3_vandermonde_square]
  ring

/-- Hankel3 matrix determinant vanishes when any two atoms collide.
    cor:xi-hankel-vs-prony-square-gap (matrix κ=3 general collision) -/
theorem hankel3_matrix_eq_zero_of_any_collision
    (ω1 ω2 ω3 a1 a2 a3 : ℤ)
    (hcoll : a1 = a2 ∨ a1 = a3 ∨ a2 = a3) :
    (hankel3 ω1 ω2 ω3 a1 a2 a3).det = 0 := by
  rw [hankel3_vandermonde_square]
  rcases hcoll with rfl | rfl | rfl <;> ring

/-- Paper package: κ=3 Hankel matrix collision degeneracy.
    cor:xi-hankel-vs-prony-square-gap (matrix form package) -/
theorem paper_hankel3_matrix_collision_degeneracy :
    (∀ ω1 ω2 ω3 a a3 : ℤ, (hankel3 ω1 ω2 ω3 a a a3).det = 0) ∧
    (∀ ω1 ω2 ω3 a1 a : ℤ, (hankel3 ω1 ω2 ω3 a1 a a).det = 0) ∧
    (∀ ω1 ω2 ω3 a1 a2 a3 : ℤ,
      a1 = a2 ∨ a1 = a3 ∨ a2 = a3 → (hankel3 ω1 ω2 ω3 a1 a2 a3).det = 0) :=
  ⟨hankel3_matrix_eq_zero_of_a1_a2,
   hankel3_matrix_eq_zero_of_a2_a3,
   hankel3_matrix_eq_zero_of_any_collision⟩

end Omega.Zeta
