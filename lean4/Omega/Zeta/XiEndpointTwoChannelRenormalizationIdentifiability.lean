import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete two-channel endpoint-renormalization data.  The two hypotheses record the already
available one-point estimates for the normalized endpoint channel and the absolutely continuous
channel; the conclusion packages the uniform estimates and their cross-point consequences. -/
structure xi_endpoint_two_channel_renormalization_identifiability_data where
  Point : Type
  scaledReadout : ℕ → Point → ℝ
  fiberReadout : ℕ → Point → ℝ
  endpointKernel : Point → ℝ
  atomMass : ℝ
  densityEndpoint : ℝ
  cK : ℝ
  CK : ℝ
  endpointRate : ℕ → ℝ
  fiberRate : ℕ → ℝ
  cK_pos : 0 < cK
  CK_nonneg : 0 ≤ CK
  endpointRate_nonneg : ∀ n, 0 ≤ endpointRate n
  endpointKernel_lower : ∀ w, cK ≤ endpointKernel w
  endpoint_estimate :
    ∀ n w, |scaledReadout n w - atomMass * endpointKernel w| ≤ CK * endpointRate n
  fiber_estimate : ∀ n w, |fiberReadout n w - densityEndpoint| ≤ CK * fiberRate n

/-- Endpoint-kernel normalized readout. -/
noncomputable def xi_endpoint_two_channel_renormalization_identifiability_A
    (D : xi_endpoint_two_channel_renormalization_identifiability_data)
    (n : ℕ) (w : D.Point) : ℝ :=
  D.scaledReadout n w / D.endpointKernel w

/-- Absolutely continuous channel readout. -/
def xi_endpoint_two_channel_renormalization_identifiability_F
    (D : xi_endpoint_two_channel_renormalization_identifiability_data)
    (n : ℕ) (w : D.Point) : ℝ :=
  D.fiberReadout n w

/-- The uniform one-point and two-point identifiability estimates. -/
def xi_endpoint_two_channel_renormalization_identifiability_data.Holds
    (D : xi_endpoint_two_channel_renormalization_identifiability_data) : Prop :=
  (∀ n w,
    |xi_endpoint_two_channel_renormalization_identifiability_A D n w - D.atomMass| ≤
      D.CK * D.endpointRate n / D.cK) ∧
    (∀ n w,
      |xi_endpoint_two_channel_renormalization_identifiability_F D n w - D.densityEndpoint| ≤
        D.CK * D.fiberRate n) ∧
      (∀ n w w',
        |xi_endpoint_two_channel_renormalization_identifiability_A D n w -
            xi_endpoint_two_channel_renormalization_identifiability_A D n w'| ≤
          2 * (D.CK * D.endpointRate n / D.cK)) ∧
        ∀ n w w',
          |xi_endpoint_two_channel_renormalization_identifiability_F D n w -
              xi_endpoint_two_channel_renormalization_identifiability_F D n w'| ≤
            2 * (D.CK * D.fiberRate n)

private lemma xi_endpoint_two_channel_renormalization_identifiability_endpoint_bound
    (D : xi_endpoint_two_channel_renormalization_identifiability_data)
    (n : ℕ) (w : D.Point) :
    |xi_endpoint_two_channel_renormalization_identifiability_A D n w - D.atomMass| ≤
      D.CK * D.endpointRate n / D.cK := by
  have hBpos : 0 < D.endpointKernel w :=
    lt_of_lt_of_le D.cK_pos (D.endpointKernel_lower w)
  have hden : D.cK ≤ |D.endpointKernel w| := by
    simpa [abs_of_pos hBpos] using D.endpointKernel_lower w
  have hnum := D.endpoint_estimate n w
  have hscale_nonneg : 0 ≤ D.CK * D.endpointRate n :=
    mul_nonneg D.CK_nonneg (D.endpointRate_nonneg n)
  have hinv : (|D.endpointKernel w|)⁻¹ ≤ D.cK⁻¹ :=
    by simpa [one_div] using one_div_le_one_div_of_le D.cK_pos hden
  have hdiff :
      xi_endpoint_two_channel_renormalization_identifiability_A D n w - D.atomMass =
        (D.scaledReadout n w - D.atomMass * D.endpointKernel w) / D.endpointKernel w := by
    rw [xi_endpoint_two_channel_renormalization_identifiability_A]
    field_simp [hBpos.ne']
  calc
    |xi_endpoint_two_channel_renormalization_identifiability_A D n w - D.atomMass|
        = |D.scaledReadout n w - D.atomMass * D.endpointKernel w| /
            |D.endpointKernel w| := by
          rw [hdiff, abs_div]
    _ ≤ D.CK * D.endpointRate n / |D.endpointKernel w| := by
          exact div_le_div_of_nonneg_right hnum (abs_nonneg _)
    _ ≤ D.CK * D.endpointRate n / D.cK := by
          simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hscale_nonneg

/-- Paper label: `thm:xi-endpoint-two-channel-renormalization-identifiability`. -/
theorem paper_xi_endpoint_two_channel_renormalization_identifiability
    (D : xi_endpoint_two_channel_renormalization_identifiability_data) : D.Holds := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n w
    exact xi_endpoint_two_channel_renormalization_identifiability_endpoint_bound D n w
  · intro n w
    simpa [xi_endpoint_two_channel_renormalization_identifiability_F] using D.fiber_estimate n w
  · intro n w w'
    have hw := xi_endpoint_two_channel_renormalization_identifiability_endpoint_bound D n w
    have hw' := xi_endpoint_two_channel_renormalization_identifiability_endpoint_bound D n w'
    have htri := abs_sub_le
      (xi_endpoint_two_channel_renormalization_identifiability_A D n w) D.atomMass
      (xi_endpoint_two_channel_renormalization_identifiability_A D n w')
    rw [abs_sub_comm D.atomMass
      (xi_endpoint_two_channel_renormalization_identifiability_A D n w')] at htri
    nlinarith
  · intro n w w'
    have hw :
        |xi_endpoint_two_channel_renormalization_identifiability_F D n w - D.densityEndpoint| ≤
          D.CK * D.fiberRate n := by
      simpa [xi_endpoint_two_channel_renormalization_identifiability_F] using D.fiber_estimate n w
    have hw' :
        |xi_endpoint_two_channel_renormalization_identifiability_F D n w' -
            D.densityEndpoint| ≤
          D.CK * D.fiberRate n := by
      simpa [xi_endpoint_two_channel_renormalization_identifiability_F] using D.fiber_estimate n w'
    have htri := abs_sub_le
      (xi_endpoint_two_channel_renormalization_identifiability_F D n w) D.densityEndpoint
      (xi_endpoint_two_channel_renormalization_identifiability_F D n w')
    rw [abs_sub_comm D.densityEndpoint
      (xi_endpoint_two_channel_renormalization_identifiability_F D n w')] at htri
    nlinarith

end Omega.Zeta
