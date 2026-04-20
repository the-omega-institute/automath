import Omega.TypedAddressBiaxialCompletion.RadialInformationProjectionLowerBound

namespace Omega.TypedAddressBiaxialCompletion

/-- Typed-address restatement of the compactified radial readout lower bound: the coordinate is
`u = arctan(x) / π`, the inverse-Jacobian amplification is `π (1 + x²)`, and any certified
`n`-bit dyadic readout must dominate the corresponding base-2 logarithmic budget.
    prop:typed-address-biaxial-completion-comoving-radial-bits -/
theorem paper_typed_address_biaxial_completion_comoving_radial_bits
    (x ε : ℝ) (n : ℕ) (hε : 0 < ε) (hcert : xiCertifiedRadialReadout x ε n) :
    xiCompactify x = Real.arctan x / Real.pi ∧
      xiJacobianAmplification x = Real.pi * (1 + x ^ 2) ∧
      Real.logb 2 (xiJacobianAmplification x / ε) ≤ n := by
  exact ⟨rfl, rfl, paper_xi_radial_information_projection_lower_bound x ε n hε hcert⟩

end Omega.TypedAddressBiaxialCompletion
