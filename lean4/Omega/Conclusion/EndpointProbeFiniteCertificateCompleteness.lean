import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete endpoint-probe certificate data.  For each probe depth there is a finite
stabilization threshold; once all endpoint probes have stabilized, the endpoint inversion clause
recovers the Toeplitz principal block. -/
structure conclusion_endpoint_probe_finite_certificate_completeness_data where
  conclusion_endpoint_probe_finite_certificate_completeness_depth : ℕ
  conclusion_endpoint_probe_finite_certificate_completeness_threshold :
    Fin conclusion_endpoint_probe_finite_certificate_completeness_depth → ℕ
  conclusion_endpoint_probe_finite_certificate_completeness_endpointProbe :
    ℕ → Fin conclusion_endpoint_probe_finite_certificate_completeness_depth → ℤ
  conclusion_endpoint_probe_finite_certificate_completeness_endpointLimit :
    Fin conclusion_endpoint_probe_finite_certificate_completeness_depth → ℤ
  conclusion_endpoint_probe_finite_certificate_completeness_toeplitzWindow :
    ℕ →
      Fin conclusion_endpoint_probe_finite_certificate_completeness_depth →
        Fin conclusion_endpoint_probe_finite_certificate_completeness_depth → ℤ
  conclusion_endpoint_probe_finite_certificate_completeness_principalBlock :
    Fin conclusion_endpoint_probe_finite_certificate_completeness_depth →
      Fin conclusion_endpoint_probe_finite_certificate_completeness_depth → ℤ
  conclusion_endpoint_probe_finite_certificate_completeness_finiteWindowStabilization :
    ∀ d N,
      conclusion_endpoint_probe_finite_certificate_completeness_threshold d ≤ N →
        conclusion_endpoint_probe_finite_certificate_completeness_endpointProbe N d =
          conclusion_endpoint_probe_finite_certificate_completeness_endpointLimit d
  conclusion_endpoint_probe_finite_certificate_completeness_endpointProbeInversion :
    ∀ N,
      (∀ d,
        conclusion_endpoint_probe_finite_certificate_completeness_endpointProbe N d =
          conclusion_endpoint_probe_finite_certificate_completeness_endpointLimit d) →
        ∀ i j,
          conclusion_endpoint_probe_finite_certificate_completeness_toeplitzWindow N i j =
            conclusion_endpoint_probe_finite_certificate_completeness_principalBlock i j

/-- The global finite certificate level: the maximum of the local probe thresholds. -/
def conclusion_endpoint_probe_finite_certificate_completeness_data.certificateLevel
    (D : conclusion_endpoint_probe_finite_certificate_completeness_data) : ℕ :=
  (Finset.univ :
      Finset (Fin D.conclusion_endpoint_probe_finite_certificate_completeness_depth)).sup
    D.conclusion_endpoint_probe_finite_certificate_completeness_threshold

/-- Every local endpoint threshold is below the global finite certificate level. -/
lemma conclusion_endpoint_probe_finite_certificate_completeness_data.threshold_le_certificateLevel
    (D : conclusion_endpoint_probe_finite_certificate_completeness_data)
    (d : Fin D.conclusion_endpoint_probe_finite_certificate_completeness_depth) :
    D.conclusion_endpoint_probe_finite_certificate_completeness_threshold d ≤
      D.certificateLevel := by
  exact Finset.le_sup
    (s := (Finset.univ :
      Finset (Fin D.conclusion_endpoint_probe_finite_certificate_completeness_depth)))
    (f := D.conclusion_endpoint_probe_finite_certificate_completeness_threshold)
    (by simp : d ∈
      (Finset.univ :
        Finset (Fin D.conclusion_endpoint_probe_finite_certificate_completeness_depth)))

/-- Paper-facing finite-certificate completeness statement. -/
def conclusion_endpoint_probe_finite_certificate_completeness_data.Holds
    (D : conclusion_endpoint_probe_finite_certificate_completeness_data) : Prop :=
  ∃ N0 : ℕ,
    (∀ d, D.conclusion_endpoint_probe_finite_certificate_completeness_threshold d ≤ N0) ∧
      ∀ N, N0 ≤ N →
        ∀ i j,
          D.conclusion_endpoint_probe_finite_certificate_completeness_toeplitzWindow N i j =
            D.conclusion_endpoint_probe_finite_certificate_completeness_principalBlock i j

/-- Paper label: `thm:conclusion-endpoint-probe-finite-certificate-completeness`. -/
theorem paper_conclusion_endpoint_probe_finite_certificate_completeness
    (D : conclusion_endpoint_probe_finite_certificate_completeness_data) : D.Holds := by
  refine ⟨D.certificateLevel, ?_, ?_⟩
  · intro d
    exact D.threshold_le_certificateLevel d
  · intro N hN i j
    apply D.conclusion_endpoint_probe_finite_certificate_completeness_endpointProbeInversion N
    intro d
    exact D.conclusion_endpoint_probe_finite_certificate_completeness_finiteWindowStabilization
      d N (le_trans (D.threshold_le_certificateLevel d) hN)

end Omega.Conclusion
