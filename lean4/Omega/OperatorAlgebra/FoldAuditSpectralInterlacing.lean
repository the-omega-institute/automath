import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- The ambient self-adjoint operator is modeled by the ordered eigenvalue pair `μ₁ ≤ μ₂`. -/
def foldAuditAmbientOperatorNorm (μ₁ μ₂ : ℝ) : ℝ :=
  max |μ₁| |μ₂|

/-- The stable layer is the orthogonal compression `U*TU` onto the first eigendirection. -/
def foldAuditStableLayerEigenvalue (μ₁ _μ₂ : ℝ) : ℝ :=
  μ₁

/-- The operator norm of the compressed stable layer. -/
def foldAuditStableLayerNorm (μ₁ μ₂ : ℝ) : ℝ :=
  |foldAuditStableLayerEigenvalue μ₁ μ₂|

/-- Paper label: `prop:fold-audit-spectral-interlacing`.
For the rank-one orthogonal compression of a two-level self-adjoint operator, the compressed
eigenvalue interlaces the ambient spectrum and its operator norm is bounded by the ambient norm. -/
theorem paper_fold_audit_spectral_interlacing (μ₁ μ₂ : ℝ) (hμ : μ₁ ≤ μ₂) :
    μ₁ ≤ foldAuditStableLayerEigenvalue μ₁ μ₂ ∧
      foldAuditStableLayerEigenvalue μ₁ μ₂ ≤ μ₂ ∧
      foldAuditStableLayerNorm μ₁ μ₂ ≤ foldAuditAmbientOperatorNorm μ₁ μ₂ := by
  refine ⟨by simp [foldAuditStableLayerEigenvalue], ?_, ?_⟩
  · simpa [foldAuditStableLayerEigenvalue] using hμ
  · simp [foldAuditStableLayerNorm, foldAuditAmbientOperatorNorm, foldAuditStableLayerEigenvalue]

end Omega.OperatorAlgebra
