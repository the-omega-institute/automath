import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite certificate data for strictifiability on a bounded slice. The finite
signature `Xi_m` is represented by integer coordinates; the hypotheses identify anomaly,
semantic, and finite-coordinate residual vanishing. -/
structure conclusion_strictifiability_finite_certificate_completeness_data where
  m : ℕ
  xi : Fin m → ℤ
  anomalyResidual : Fin m → ℤ
  semanticResidual : Fin m → ℤ
  finiteCoordinateResidual : Fin m → ℤ
  strictificationResidual : ℤ
  strictifiable_iff_anomaly :
    strictificationResidual = 0 ↔ ∀ i, anomalyResidual i = 0
  anomaly_residual_iff_semantic :
    (∀ i, anomalyResidual i = 0) ↔ ∀ i, semanticResidual i = 0
  semantic_residual_iff_finite :
    (∀ i, semanticResidual i = 0) ↔ ∀ i, finiteCoordinateResidual i = 0
  signature_trivial_iff_finite :
    (∀ i, xi i = 0) ↔ ∀ i, finiteCoordinateResidual i = 0

/-- The finite signature `Xi_m` packaged as a coordinate vector. -/
def conclusion_strictifiability_finite_certificate_completeness_signature
    (D : conclusion_strictifiability_finite_certificate_completeness_data) : Fin D.m → ℤ :=
  D.xi

/-- Concrete strictifiability predicate: the strictification residual vanishes. -/
def conclusion_strictifiability_finite_certificate_completeness_strictifiable
    (D : conclusion_strictifiability_finite_certificate_completeness_data) : Prop :=
  D.strictificationResidual = 0

/-- Concrete triviality predicate for the finite signature. -/
def conclusion_strictifiability_finite_certificate_completeness_signature_trivial
    (D : conclusion_strictifiability_finite_certificate_completeness_data) : Prop :=
  ∀ i, conclusion_strictifiability_finite_certificate_completeness_signature D i = 0

namespace conclusion_strictifiability_finite_certificate_completeness_data

/-- Paper-facing finite-certificate claim. -/
def claim (D : conclusion_strictifiability_finite_certificate_completeness_data) : Prop :=
  conclusion_strictifiability_finite_certificate_completeness_strictifiable D ↔
    conclusion_strictifiability_finite_certificate_completeness_signature_trivial D

end conclusion_strictifiability_finite_certificate_completeness_data

open conclusion_strictifiability_finite_certificate_completeness_data

/-- Paper label: `thm:conclusion-strictifiability-finite-certificate-completeness`. -/
theorem paper_conclusion_strictifiability_finite_certificate_completeness
    (D : conclusion_strictifiability_finite_certificate_completeness_data) : D.claim := by
  unfold conclusion_strictifiability_finite_certificate_completeness_data.claim
  unfold conclusion_strictifiability_finite_certificate_completeness_strictifiable
  unfold conclusion_strictifiability_finite_certificate_completeness_signature_trivial
  unfold conclusion_strictifiability_finite_certificate_completeness_signature
  exact
    (D.strictifiable_iff_anomaly.trans D.anomaly_residual_iff_semantic).trans
      (D.semantic_residual_iff_finite.trans D.signature_trivial_iff_finite.symm)

end Omega.Conclusion
