import Omega.Zeta.XiEndpointProfileCfiniteHankelRank
import Omega.Zeta.XiFiniteDefectRhScanTraceEquivalence

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-endpoint-tomography-certificate-chain`. The concrete endpoint profile
already carries the quadratic denominator factorization and the order-`2N` Hankel-rank package,
while the finite-defect scan-trace theorem converts vanishing of the total defect mass into the
endpoint Fourier certificate. Together these give the advertised one-variable endpoint certificate
chain for finite-defect approximations. -/
theorem paper_xi_endpoint_tomography_certificate_chain
    (N κ : ℕ) (γ δ : Fin N → ℚ) (mass defect : Fin κ → ℝ)
    (scanTraceLimit fourierAtZero : ℝ)
    (hScan : scanTraceLimit = ∑ j, mass j * defect j)
    (hFourier : fourierAtZero = 2 * Real.pi * scanTraceLimit) :
    (∀ q : ℚ,
      xi_endpoint_profile_cfinite_hankel_rank_denominator γ δ q =
        ∏ k, xi_endpoint_profile_cfinite_hankel_rank_quadratic_factor γ δ k q) ∧
      xi_endpoint_profile_cfinite_hankel_rank_minimal_order N = 2 * N ∧
      xi_endpoint_profile_cfinite_hankel_rank_hankel_rank N = 2 * N ∧
      ((∑ j, mass j * defect j = 0) ↔ fourierAtZero = 0) := by
  have hprofile := paper_xi_endpoint_profile_cfinite_hankel_rank N γ δ
  let D : XiFiniteDefectRhScanTraceEquivalenceData :=
    { κ := κ
      mass := mass
      delta := defect
      scanTraceLimit := scanTraceLimit
      fourierAtZero := fourierAtZero
      hScanTraceLimit := hScan
      hFourierAtZero := hFourier }
  have hfinite := paper_xi_finite_defect_rh_scan_trace_equivalence D
  refine ⟨hprofile.1, hprofile.2.2.2.1, hprofile.2.2.2.2, ?_⟩
  have hrh_fourier :
      D.rh ↔ D.fourierAtZeroVanishes := hfinite.2.1.trans hfinite.2.2
  simpa [XiFiniteDefectRhScanTraceEquivalenceData.rh,
    XiFiniteDefectRhScanTraceEquivalenceData.totalDefectMass,
    XiFiniteDefectRhScanTraceEquivalenceData.fourierAtZeroVanishes] using hrh_fourier

end Omega.Zeta
