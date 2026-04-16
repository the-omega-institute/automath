import Mathlib.Tactic

namespace Omega.GU.ParryEndpointPhiEstimators

/-- The `00/01` endpoint-ratio estimator for `φ`. -/
def phiEstimator00_01 (M00 M01 Fm Fm1 : ℚ) : ℚ :=
  (M00 / M01) * (Fm1 / Fm)

/-- The `01/11` endpoint-ratio estimator for `φ`. -/
def phiEstimator01_11 (M01 M11 Fm1 Fm2 : ℚ) : ℚ :=
  (M01 / M11) * (Fm2 / Fm1)

/-- Paper seed for the exact `φ` estimators coming from endpoint masses.
    cor:parry-endpoint-phi-estimators -/
theorem paper_parry_endpoint_phi_estimators_seeds
    (phiVal base M00 M01 M11 Fm Fm1 Fm2 : ℚ)
    (hphi : phiVal ≠ 0) (hbase : base ≠ 0)
    (hFm : Fm ≠ 0) (hFm1 : Fm1 ≠ 0) (hFm2 : Fm2 ≠ 0)
    (h00 : M00 = base * Fm)
    (h01 : M01 = base * Fm1 / phiVal)
    (h11 : M11 = base * Fm2 / (phiVal * phiVal)) :
    phiEstimator00_01 M00 M01 Fm Fm1 = phiVal ∧
      phiEstimator01_11 M01 M11 Fm1 Fm2 = phiVal := by
  constructor
  · unfold phiEstimator00_01
    rw [h00, h01]
    field_simp [hphi, hbase, hFm, hFm1]
  · unfold phiEstimator01_11
    rw [h01, h11]
    field_simp [hphi, hbase, hFm1, hFm2]

/-- Packaged form of the exact `φ` estimators.
    cor:parry-endpoint-phi-estimators -/
theorem paper_parry_endpoint_phi_estimators_package
    (phiVal base M00 M01 M11 Fm Fm1 Fm2 : ℚ)
    (hphi : phiVal ≠ 0) (hbase : base ≠ 0)
    (hFm : Fm ≠ 0) (hFm1 : Fm1 ≠ 0) (hFm2 : Fm2 ≠ 0)
    (h00 : M00 = base * Fm)
    (h01 : M01 = base * Fm1 / phiVal)
    (h11 : M11 = base * Fm2 / (phiVal * phiVal)) :
    phiEstimator00_01 M00 M01 Fm Fm1 = phiVal ∧
      phiEstimator01_11 M01 M11 Fm1 Fm2 = phiVal :=
  paper_parry_endpoint_phi_estimators_seeds phiVal base M00 M01 M11 Fm Fm1 Fm2 hphi hbase hFm
    hFm1 hFm2 h00 h01 h11

/-- Paper-facing corollary name for the endpoint `φ` estimators. -/
theorem paper_parry_endpoint_phi_estimators
    (phiVal base M00 M01 M11 Fm Fm1 Fm2 : ℚ)
    (hphi : phiVal ≠ 0) (hbase : base ≠ 0)
    (hFm : Fm ≠ 0) (hFm1 : Fm1 ≠ 0) (hFm2 : Fm2 ≠ 0)
    (h00 : M00 = base * Fm)
    (h01 : M01 = base * Fm1 / phiVal)
    (h11 : M11 = base * Fm2 / (phiVal * phiVal)) :
    phiEstimator00_01 M00 M01 Fm Fm1 = phiVal ∧
      phiEstimator01_11 M01 M11 Fm1 Fm2 = phiVal :=
  paper_parry_endpoint_phi_estimators_package phiVal base M00 M01 M11 Fm Fm1 Fm2 hphi hbase hFm
    hFm1 hFm2 h00 h01 h11

end Omega.GU.ParryEndpointPhiEstimators
