import Omega.Folding.FoldGaugeAnomalyFieldEqualityUMuB
import Omega.Folding.GaugeAnomalyRateCurveIndexIdealFormula
import Omega.Folding.GaugeAnomalyRateCurveParam
import Omega.Folding.GaugeAnomalySpectralQuarticJacobianEndomorphism
import Omega.Folding.GaugeAnomalySpectralQuarticJacobianL13
import Omega.Folding.GaugeAnomalyTrigonalRamificationMu

namespace Omega.Folding

/-- Concrete function-field equality package used for the rate-curve/spectral-quartic comparison.
-/
def gaugeAnomalyRateCurveEqualFunctionFields : Prop :=
  gaugeAnomalyUStar = gaugeAnomalyMuStar ∧
    gaugeAnomalyMuStar = gaugeAnomalyBStar ∧
    gaugeAnomalyDegreeTenExtension ∧
    (∀ u μ : ℝ, gaugeAnomalyPressureQuarticReal u μ = 0 →
      gaugeAnomalyRateCurveAlpha u μ =
        -(u * gaugeAnomalyPressureQuarticFu u μ) / (μ * gaugeAnomalyPressureQuarticFμ u μ))

/-- Concrete birational-equivalence package assembled from the quartic Jacobian audit and the
trigonal ramification data. -/
def gaugeAnomalyRateCurveBirationalEquivalence : Prop :=
  gaugeAnomalyRateCurveEqualFunctionFields ∧
    spectralQuarticJacobianL13Irreducible ∧
    spectralQuarticJacobianL13Ordinary ∧
    gaugeAnomalyTrigonalInfinityNonramified ∧
    gaugeAnomalyTrigonalFullBranchCount = 2 ∧
    gaugeAnomalyTrigonalSimpleBranchCount = 6 ∧
    gaugeAnomalyTrigonalTotalRamification = 10

/-- Concrete normalization statement for the common function field: the discriminant quotient gives
the index ideal, and the quartic Jacobian endomorphism audit keeps the normalization absolutely
simple. -/
def gaugeAnomalyRateCurveNormalizationClaim : Prop :=
  gaugeAnomalyDiscAlpha = gaugeAnomalyDiscMu * gaugeAnomalyUPowFiveD19 ^ 2 ∧
    gaugeAnomalyIndexIdeal = gaugeAnomalyUPowFiveD19 ∧
    spectralQuarticCommonFrobeniusField = .base ∧
    spectralQuarticGeometricEndomorphismRing = spectralQuarticIntegerScalars ∧
    spectralQuarticAbsolutelySimple

/-- The rate-curve elimination and the spectral quartic share the same audited function field; the
same data package their birational equivalence and the normalization/index-ideal consequence.
    thm:fold-gauge-anomaly-rate-curve-function-field-identity -/
theorem paper_fold_gauge_anomaly_rate_curve_function_field_identity :
    gaugeAnomalyRateCurveEqualFunctionFields ∧
      gaugeAnomalyRateCurveBirationalEquivalence ∧
      gaugeAnomalyRateCurveNormalizationClaim := by
  rcases paper_fold_gauge_anomaly_field_equality_u_mu_b with ⟨huμ, hμb, hdeg⟩
  rcases paper_fold_gauge_anomaly_rate_curve_param with ⟨hα, _, _⟩
  rcases paper_fold_gauge_anomaly_spectral_quartic_jacobian_l13 with ⟨hL13irr, hL13ord⟩
  rcases paper_fold_gauge_anomaly_trigonal_ramification_mu with
    ⟨_, hInf, hFull, hSimple, hTotal⟩
  rcases paper_fold_gauge_anomaly_rate_curve_index_ideal_formula with ⟨hDisc, hIndex⟩
  rcases paper_fold_gauge_anomaly_spectral_quartic_jacobian_endomorphism_z with
    ⟨_, _, hBase, hRing, hAbs⟩
  have hEqual : gaugeAnomalyRateCurveEqualFunctionFields := ⟨huμ, hμb, hdeg, hα⟩
  refine ⟨hEqual, ?_, ?_⟩
  · exact ⟨hEqual, hL13irr, hL13ord, hInf, hFull, hSimple, hTotal⟩
  · exact ⟨hDisc, hIndex, hBase, hRing, hAbs⟩
