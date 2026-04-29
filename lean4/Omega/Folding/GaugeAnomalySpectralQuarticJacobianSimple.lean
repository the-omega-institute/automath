import Mathlib
import Omega.Folding.GaugeAnomalySpectralQuarticJacobianEndomorphism
import Omega.Folding.GaugeAnomalySpectralQuarticJacobianL13

namespace Omega.Folding

open Polynomial

/-- The audited good-reduction prime used in the quartic-Jacobian wrapper. -/
def fold_gauge_anomaly_spectral_quartic_jacobian_simple_good_reduction_prime : ℕ := 13

/-- Chapter-local copy of the explicit local `L`-polynomial at the good prime. -/
noncomputable def fold_gauge_anomaly_spectral_quartic_jacobian_simple_l7_polynomial :
    Polynomial ℤ :=
  spectralQuarticJacobianL13

/-- Chapter-local copy of the audited modular factor-degree certificate. -/
def fold_gauge_anomaly_spectral_quartic_jacobian_simple_factor_degrees : List ℕ :=
  spectralQuarticJacobianL13Mod43FactorDegrees

/-- Chapter-local irreducibility certificate for the good reduction. -/
def fold_gauge_anomaly_spectral_quartic_jacobian_simple_irreducibility_certificate : Prop :=
  spectralQuarticJacobianL13Irreducible

/-- Chapter-local ordinary-reduction certificate. -/
def fold_gauge_anomaly_spectral_quartic_jacobian_simple_ordinary_certificate : Prop :=
  spectralQuarticJacobianL13Ordinary

/-- In this wrapper, geometric simplicity is modeled by the already-audited absolute simplicity
certificate coming from the common-Frobenius-field computation. -/
def fold_gauge_anomaly_spectral_quartic_jacobian_simple_geometric_simplicity : Prop :=
  spectralQuarticAbsolutelySimple

/-- Proposition-level package for the spectral quartic Jacobian simplicity wrapper. -/
def fold_gauge_anomaly_spectral_quartic_jacobian_simple_statement : Prop :=
  fold_gauge_anomaly_spectral_quartic_jacobian_simple_good_reduction_prime = 13 ∧
    fold_gauge_anomaly_spectral_quartic_jacobian_simple_l7_polynomial = spectralQuarticJacobianL13 ∧
    fold_gauge_anomaly_spectral_quartic_jacobian_simple_factor_degrees = [6] ∧
    fold_gauge_anomaly_spectral_quartic_jacobian_simple_irreducibility_certificate ∧
    fold_gauge_anomaly_spectral_quartic_jacobian_simple_ordinary_certificate ∧
    spectralQuarticGeometricEndomorphismRing = spectralQuarticIntegerScalars ∧
    ((fold_gauge_anomaly_spectral_quartic_jacobian_simple_irreducibility_certificate ∧
        fold_gauge_anomaly_spectral_quartic_jacobian_simple_ordinary_certificate ∧
        spectralQuarticGeometricEndomorphismRing = spectralQuarticIntegerScalars) →
      fold_gauge_anomaly_spectral_quartic_jacobian_simple_geometric_simplicity)

/-- `prop:fold-gauge-anomaly-spectral-quartic-jacobian-simple` -/
theorem paper_fold_gauge_anomaly_spectral_quartic_jacobian_simple :
    fold_gauge_anomaly_spectral_quartic_jacobian_simple_statement := by
  rcases paper_fold_gauge_anomaly_spectral_quartic_jacobian_l13 with ⟨hIrr, hOrd⟩
  rcases paper_fold_gauge_anomaly_spectral_quartic_jacobian_endomorphism_z with
    ⟨_, _, _, hEnd, hSimple⟩
  refine ⟨rfl, rfl, rfl, hIrr, hOrd, hEnd, ?_⟩
  intro _
  exact hSimple

end Omega.Folding
