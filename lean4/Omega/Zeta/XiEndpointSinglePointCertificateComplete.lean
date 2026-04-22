import Omega.Zeta.XiEndpointAbsorptionAdditiveTomography
import Omega.Zeta.XiExtremeResonanceCriterion

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Paper label: `thm:xi-endpoint-single-point-certificate-complete`. -/
theorem paper_xi_endpoint_single_point_certificate_complete {κ : Nat} (a : Fin κ → ℂ)
    (ha : ∀ k, ‖a k‖ < 1) (D : XiExtremeResonanceCriterionData)
    (hmatch : xiExtremeResonanceJinPi D = xiEndpointAbsorptionCoefficient a) :
    (κ = 0 ↔ xiExtremeResonanceJinPi D = 0) ∧
      (κ = 0 ↔ xiEndpointAbsorptionCoefficient a = 0) ∧
      (κ = 0 ↔ xiEndpointJuliaIndicator (fun _ => (1 : Real)) a = 0) ∧
      xiExtremeResonanceJinPi D = xiExtremeResonancePhiMinusOne D ∧
      xiExtremeResonancePhiMinusOne D = xiEndpointAbsorptionCoefficient a ∧
      xiExtremeResonancePhiMinusOne D = xiExtremeResonancePoissonSum D ∧
      (xiExtremeResonanceJinPi D = 0 ↔ xiExtremeResonanceDeltaSum D = 0) ∧
      (xiEndpointAbsorptionCoefficient a =
        ∑ k, (1 - ‖a k‖ ^ 2) / ‖1 + a k‖ ^ 2) ∧
      (xiEndpointJuliaIndicator (fun _ => (1 : Real)) a =
        Complex.re (-xiEndpointBoundaryLogDerivative (fun _ => (1 : Real)) a)) := by
  rcases paper_xi_extreme_resonance_criterion D with
    ⟨hjin_phi, hphi_sum, _hjin_zero, _hdelta_zero, hjin_delta, _hbound⟩
  rcases paper_xi_endpoint_absorption_coefficient a ha with ⟨hcoeff_sum, hcoeff_zero⟩
  have hjulia_coeff :
      xiEndpointJuliaIndicator (fun _ => (1 : Real)) a = xiEndpointAbsorptionCoefficient a := by
    simpa [xiEndpointAbsorptionCoefficient] using
      (paper_xi_endpoint_julia_indicator_equals_absorption (w := fun _ => (1 : Real))
        (z := a)).1
  have hjulia_boundary :
      xiEndpointJuliaIndicator (fun _ => (1 : Real)) a =
        Complex.re (-xiEndpointBoundaryLogDerivative (fun _ => (1 : Real)) a) := by
    calc
      xiEndpointJuliaIndicator (fun _ => (1 : Real)) a = xiEndpointAbsorptionCoefficient a := by
        exact hjulia_coeff
      _ = Complex.re (-xiEndpointBoundaryLogDerivative (fun _ => (1 : Real)) a) := by
        simpa [xiEndpointAbsorptionCoefficient] using
          (paper_xi_endpoint_absorption_additive_tomography a ha).2
  have hcurrent_coeff_zero :
      xiExtremeResonanceJinPi D = 0 ↔ xiEndpointAbsorptionCoefficient a = 0 := by
    constructor <;> intro hzero
    · rw [← hmatch, hzero]
    · rw [hmatch, hzero]
  have hκ_current : κ = 0 ↔ xiExtremeResonanceJinPi D = 0 := by
    exact hcoeff_zero.symm.trans hcurrent_coeff_zero.symm
  have hκ_julia : κ = 0 ↔ xiEndpointJuliaIndicator (fun _ => (1 : Real)) a = 0 := by
    constructor
    · intro hκ
      have hcoeff0 : xiEndpointAbsorptionCoefficient a = 0 := (hcoeff_zero).2 hκ
      simpa [hjulia_coeff] using hcoeff0
    · intro hjulia0
      have hcoeff0 : xiEndpointAbsorptionCoefficient a = 0 := by
        simpa [hjulia_coeff] using hjulia0
      exact (hcoeff_zero).1 hcoeff0
  have hphi_coeff : xiExtremeResonancePhiMinusOne D = xiEndpointAbsorptionCoefficient a := by
    rw [← hjin_phi, hmatch]
  refine ⟨hκ_current, hcoeff_zero.symm, hκ_julia, hjin_phi, hphi_coeff, hphi_sum, hjin_delta,
    hcoeff_sum, hjulia_boundary⟩

end

end Omega.Zeta
