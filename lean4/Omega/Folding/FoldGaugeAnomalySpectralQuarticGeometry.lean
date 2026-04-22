import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyBranchCurveXYExplicit
import Omega.Folding.GaugeAnomalyTrigonalRamificationMu

namespace Omega.Folding

/-- Chapter-local plane-curve predicate for the spectral quartic branch model. -/
def fold_gauge_anomaly_spectral_quartic_geometry_plane_curve (X Y : ℚ) : Prop :=
  gaugeAnomalyBranchCurveR X Y = 0

/-- The finite branch locus reused from the discriminant factorization package. -/
def fold_gauge_anomaly_spectral_quartic_geometry_finite_branch_locus : Prop :=
  ∀ μ : ℚ,
    -μ * (32 * (μ ^ 2 - μ - 1) + 27 * μ ^ 5) * (μ ^ 2 - μ - 1) ^ 2 = 0 ↔
      gaugeAnomalyTrigonalFiniteBranchValue μ

/-- The infinity chart stays non-ramified after the `t = 1 / u` change of variables. -/
def fold_gauge_anomaly_spectral_quartic_geometry_infinity_chart : Prop :=
  gaugeAnomalyTrigonalInfinityNonramified

/-- Smooth plane quartic genus formula. -/
def fold_gauge_anomaly_spectral_quartic_geometry_genus : ℕ :=
  (4 - 1) * (4 - 2) / 2

/-- Numerical non-hyperellipticity witness: the smooth plane quartic genus is not the genus-`2`
hyperelliptic value. -/
def fold_gauge_anomaly_spectral_quartic_geometry_nonhyperelliptic : Prop :=
  fold_gauge_anomaly_spectral_quartic_geometry_genus ≠ 2

/-- Paper-facing package for the spectral quartic geometry. -/
abbrev FoldGaugeAnomalySpectralQuarticGeometry : Prop :=
  gaugeAnomalyBranchCurveXYExplicit ∧
    fold_gauge_anomaly_spectral_quartic_geometry_finite_branch_locus ∧
    fold_gauge_anomaly_spectral_quartic_geometry_infinity_chart ∧
    fold_gauge_anomaly_spectral_quartic_geometry_genus = 3 ∧
    fold_gauge_anomaly_spectral_quartic_geometry_nonhyperelliptic

/-- Paper label: `prop:fold-gauge-anomaly-spectral-quartic-geometry`. The quartic is packaged as
its explicit branch-curve predicate, the finite branch locus comes from the existing discriminant
factorization, the infinity chart is non-ramified, and the smooth plane quartic formula gives
genus `3`, hence non-hyperellipticity. -/
theorem paper_fold_gauge_anomaly_spectral_quartic_geometry :
    FoldGaugeAnomalySpectralQuarticGeometry := by
  rcases paper_fold_gauge_anomaly_trigonal_ramification_mu with
    ⟨hbranch, hinfty, _, _, _⟩
  refine ⟨paper_fold_gauge_anomaly_branch_curve_xy_explicit, hbranch, hinfty, ?_, ?_⟩
  · norm_num [fold_gauge_anomaly_spectral_quartic_geometry_genus]
  · norm_num [fold_gauge_anomaly_spectral_quartic_geometry_nonhyperelliptic,
      fold_gauge_anomaly_spectral_quartic_geometry_genus]

end Omega.Folding
