import Omega.Zeta.XiBulkCurvatureExactDeconvolutionOperator

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-bulk-curvature-superresolution-pi-barrier`.
Pointwise noise of size `ε`, after exact deconvolution, is bounded by the supplied exponential
multiplier barrier. -/
theorem paper_xi_bulk_curvature_superresolution_pi_barrier {n : ℕ} (ξ : Fin n → ℝ)
    (η : xi_bulk_curvature_exact_deconvolution_operator_signal n) (ε : ℝ) (hε : 0 ≤ ε)
    (hnoise : ∀ k, |η k| ≤ ε)
    (hbarrier :
      ∀ k,
        ε * |xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier (ξ k)| ≤
          ε * Real.exp (Real.pi * |ξ k|)) :
    ∀ k,
      |xi_bulk_curvature_exact_deconvolution_operator_D ξ η k| ≤
        ε * Real.exp (Real.pi * |ξ k|) := by
  intro k
  have hε_abs : |ε| = ε := abs_of_nonneg hε
  unfold xi_bulk_curvature_exact_deconvolution_operator_D
  calc
    |xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier (ξ k) * η k| =
        |xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier (ξ k)| * |η k| := by
          rw [abs_mul]
    _ ≤ |xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier (ξ k)| * |ε| := by
          simpa [hε_abs] using mul_le_mul_of_nonneg_left (hnoise k) (abs_nonneg _)
    _ = ε * |xi_bulk_curvature_exact_deconvolution_operator_inverse_multiplier (ξ k)| := by
          rw [hε_abs, mul_comm]
    _ ≤ ε * Real.exp (Real.pi * |ξ k|) := hbarrier k

end

end Omega.Zeta
