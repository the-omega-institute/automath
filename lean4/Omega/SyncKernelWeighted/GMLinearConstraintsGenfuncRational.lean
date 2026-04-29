import Omega.EA.RationalGFLinearConstraints

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Paper label: `thm:gm-linear-constraints-genfunc-rational`. -/
theorem paper_gm_linear_constraints_genfunc_rational {d : ℕ} (u v b : Fin d → ℚ) :
    (∀ z, (∀ i, 1 - z * b i ≠ 0) →
      Matrix.mulVec (Matrix.diagonal fun i => 1 - z * b i)
        (fun i => (u i * v i) / (1 - z * b i)) =
          fun i => u i * v i) ∧
    (∀ z, Matrix.det (Matrix.diagonal fun i => 1 - z * b i) = ∏ i, (1 - z * b i)) := by
  rcases Omega.EA.paper_conclusion61_rational_gf_linear_constraints d u v b with ⟨hmul, hdet, _⟩
  exact ⟨by
      simpa [Omega.EA.rationalGFLinearConstraintMatrix] using hmul,
    by
      simpa [Omega.EA.rationalGFLinearConstraintMatrix,
        Omega.EA.rationalGFLinearConstraintDenominator] using hdet⟩
