import Mathlib

open scoped BigOperators

namespace Omega.EA

noncomputable section

/-- The diagonal transition matrix for the synchronous finite-state product with fixed linear
constraint registers. -/
def rationalGFLinearConstraintMatrix {d : ℕ} (b : Fin d → ℚ) (z : ℚ) :
    Matrix (Fin d) (Fin d) ℚ :=
  Matrix.diagonal fun i => 1 - z * b i

/-- The accepted-path contribution of a single diagonal state. -/
def rationalGFLinearConstraintCoordinate {d : ℕ} (u v b : Fin d → ℚ) (i : Fin d) (m : ℕ) : ℚ :=
  u i * (b i) ^ m * v i

/-- Total accepted-path count at length `m`. -/
def rationalGFLinearConstraintPathCount {d : ℕ} (u v b : Fin d → ℚ) (m : ℕ) : ℚ :=
  ∑ i, rationalGFLinearConstraintCoordinate u v b i m

/-- The resolvent vector `(I - zB)⁻¹ (u_i v_i)` in the diagonal model. -/
def rationalGFLinearConstraintResolvent {d : ℕ} (u v b : Fin d → ℚ) (z : ℚ) : Fin d → ℚ :=
  fun i => (u i * v i) / (1 - z * b i)

/-- The determinant of `I - zB` becomes the denominator of the rational generating function. -/
def rationalGFLinearConstraintDenominator {d : ℕ} (b : Fin d → ℚ) (z : ℚ) : ℚ :=
  ∏ i, (1 - z * b i)

/-- Paper label: `prop:conclusion61-rational-gf-linear-constraints`.
For the diagonal finite-state model, the accepted-path counts are diagonal matrix coefficients
`uᵀ B^m v`; the resolvent solves `(I - zB) x = u_i v_i`, `det (I - zB)` is the product
denominator, and each coordinate contribution obeys the first-order recurrence induced by `B`. -/
theorem paper_conclusion61_rational_gf_linear_constraints (d : ℕ) (u v b : Fin d → ℚ) :
    (∀ z, (∀ i, 1 - z * b i ≠ 0) →
      Matrix.mulVec (rationalGFLinearConstraintMatrix b z)
          (rationalGFLinearConstraintResolvent u v b z) =
        fun i => u i * v i) ∧
    (∀ z, Matrix.det (rationalGFLinearConstraintMatrix b z) =
      rationalGFLinearConstraintDenominator b z) ∧
    (∀ i m,
      rationalGFLinearConstraintCoordinate u v b i (m + 1) =
        b i * rationalGFLinearConstraintCoordinate u v b i m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    ext i
    rw [rationalGFLinearConstraintMatrix, Matrix.mulVec_diagonal]
    rw [rationalGFLinearConstraintResolvent, div_eq_mul_inv]
    calc
      (1 - z * b i) * (u i * v i * (1 - z * b i)⁻¹)
          = (u i * v i) * ((1 - z * b i) * (1 - z * b i)⁻¹) := by ring
      _ = u i * v i := by simp [hz i]
  · intro z
    simp [rationalGFLinearConstraintMatrix, rationalGFLinearConstraintDenominator]
  · intro i m
    rw [rationalGFLinearConstraintCoordinate, rationalGFLinearConstraintCoordinate, pow_succ']
    ring

end

end Omega.EA
