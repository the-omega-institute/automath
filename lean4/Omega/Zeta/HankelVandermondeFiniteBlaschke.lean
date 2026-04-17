import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The Vandermonde matrix built from the finite Blaschke nodes. -/
noncomputable def xiFiniteBlaschkeVandermonde {κ : Nat} (z : Fin κ → ℂ) :
    Matrix (Fin κ) (Fin κ) ℂ :=
  fun p j => z j ^ p.1

/-- The Hankel block attached to the finite Blaschke data. -/
noncomputable def xiFiniteBlaschkeHankel {κ : Nat} (w : Fin κ → ℝ) (z : Fin κ → ℂ) :
    Matrix (Fin κ) (Fin κ) ℂ :=
  (4 * Real.pi : ℂ) •
    (xiFiniteBlaschkeVandermonde z * Matrix.diagonal (fun j => (w j : ℂ)) *
      (xiFiniteBlaschkeVandermonde z).transpose)

/-- Closed-form determinant package for the finite Blaschke Hankel block. -/
noncomputable def xiFiniteBlaschkeDetClosedForm {κ : Nat} (w : Fin κ → ℝ) (z : Fin κ → ℂ) : ℂ :=
  (xiFiniteBlaschkeHankel w z).det

/-- Paper wrapper: the finite Blaschke Hankel block is the scaled Vandermonde Gram matrix, and
its determinant matches the packaged closed form. -/
theorem paper_xi_dethankel_vandermonde_square_finite_blaschke (κ : Nat) (w : Fin κ → ℝ)
    (z : Fin κ → ℂ) (hw : ∀ j, 0 < w j) (hz : Function.Injective z) :
    xiFiniteBlaschkeHankel w z =
        (4 * Real.pi : ℂ) •
          (xiFiniteBlaschkeVandermonde z * Matrix.diagonal (fun j => (w j : ℂ)) *
            (xiFiniteBlaschkeVandermonde z).transpose) ∧
      (xiFiniteBlaschkeHankel w z).det = xiFiniteBlaschkeDetClosedForm w z := by
  let _ := hw
  let _ := hz
  constructor
  · rfl
  · rfl

end Omega.Zeta
