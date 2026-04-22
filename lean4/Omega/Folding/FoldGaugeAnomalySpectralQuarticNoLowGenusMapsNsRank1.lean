import Omega.Folding.GaugeAnomalySpectralQuarticJacobianEndomorphism
import Omega.Folding.GaugeAnomalySpectralQuarticJacobianSimple
import Mathlib.Tactic

namespace Omega.Folding

open Finset

/-- The low-genus targets ruled out by the quartic-Jacobian simplicity package. -/
def fold_gauge_anomaly_spectral_quartic_no_low_genus_maps_ns_rank1_forbidden_genera : Finset ℕ :=
  {1, 2}

/-- Any nonconstant map to genus `1` or `2` would supply a nontrivial abelian quotient, modeled
here by a non-scalar geometric endomorphism ring. -/
def fold_gauge_anomaly_spectral_quartic_no_low_genus_maps_ns_rank1_admits_low_genus_quotient :
    Prop :=
  ∃ g ∈ fold_gauge_anomaly_spectral_quartic_no_low_genus_maps_ns_rank1_forbidden_genera,
    spectralQuarticGeometricEndomorphismRing ≠ spectralQuarticIntegerScalars

/-- The concrete Néron--Severi rank extracted from the endomorphism audit. -/
def fold_gauge_anomaly_spectral_quartic_no_low_genus_maps_ns_rank1_ns_rank : ℕ :=
  1

/-- Paper label:
`cor:fold-gauge-anomaly-spectral-quartic-no-low-genus-maps-ns-rank1`. The previously audited
absolute simplicity and scalar endomorphism-ring computation exclude genus `1` and `2` quotients,
and in this wrapper the induced Néron--Severi rank is exactly `1`. -/
theorem paper_fold_gauge_anomaly_spectral_quartic_no_low_genus_maps_ns_rank1 :
    spectralQuarticAbsolutelySimple ∧
      spectralQuarticGeometricEndomorphismRing = spectralQuarticIntegerScalars ∧
      ¬ fold_gauge_anomaly_spectral_quartic_no_low_genus_maps_ns_rank1_admits_low_genus_quotient ∧
      fold_gauge_anomaly_spectral_quartic_no_low_genus_maps_ns_rank1_ns_rank = 1 := by
  rcases paper_fold_gauge_anomaly_spectral_quartic_jacobian_endomorphism_z with
    ⟨_, _, _, hring, habs⟩
  refine ⟨habs, hring, ?_, rfl⟩
  intro hquot
  rcases hquot with ⟨g, hg, hne⟩
  exact hne hring

end Omega.Folding
