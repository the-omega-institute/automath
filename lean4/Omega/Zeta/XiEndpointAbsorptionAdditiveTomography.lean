import Omega.Zeta.XiEndpointAbsorptionCoefficient

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Paper label: `cor:xi-endpoint-absorption-additive-tomography`. -/
theorem paper_xi_endpoint_absorption_additive_tomography {κ : Nat} (a : Fin κ → ℂ)
    (ha : ∀ k, ‖a k‖ < 1) :
    xiEndpointAbsorptionCoefficient a = ∑ k, (1 - ‖a k‖ ^ 2) / ‖1 + a k‖ ^ 2 ∧
      xiEndpointAbsorption (fun _ => (1 : Real)) a =
        Complex.re (-xiEndpointBoundaryLogDerivative (fun _ => (1 : Real)) a) := by
  refine ⟨(paper_xi_endpoint_absorption_coefficient a ha).1, ?_⟩
  simpa using
    (paper_xi_endpoint_julia_indicator_equals_absorption (w := fun _ => (1 : Real)) (z := a)).2

end

end Omega.Zeta
