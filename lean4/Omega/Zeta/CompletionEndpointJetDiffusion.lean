import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Quartic endpoint jet for `S(t) = 2 cos (t / 2)`. -/
def completionEndpointSJet (t : ℝ) : ℝ :=
  2 - t ^ 2 / 4 + t ^ 4 / 192

/-- Quadratic jet for `g = log Λ` composed with the endpoint jet of `S`. -/
def completionEndpointLogEtaJet (g₁ g₂ t : ℝ) : ℝ :=
  g₁ * (completionEndpointSJet t - 2) + (g₂ / 2) * (completionEndpointSJet t - 2) ^ 2

/-- The quartic coefficient extracted from the endpoint composition. -/
def completionEndpointQuarticCoeff (g₁ g₂ : ℝ) : ℝ :=
  g₁ / 192 + g₂ / 32

/-- The explicit higher-order remainder retained after extracting the quadratic and quartic
coefficients. -/
def completionEndpointHigherRemainder (g₂ t : ℝ) : ℝ :=
  -(g₂ / 768) * t ^ 6 + (g₂ / 73728) * t ^ 8

/-- The diffusion variance read off from the endpoint derivative. -/
def completionEndpointSigmaSq (g₁ : ℝ) : ℝ :=
  g₁ / 2

/-- The dissipation coefficient `κ∞ = σ² / 2`. -/
def completionEndpointKappaInf (g₁ : ℝ) : ℝ :=
  g₁ / 4

/-- Real part of the pressure jet after phase--amplitude separation. -/
def completionEndpointRePJet (logLam g₁ g₂ t : ℝ) : ℝ :=
  logLam + completionEndpointLogEtaJet g₁ g₂ t

/-- The normalized pole trajectory pulled back to the `s`-plane. -/
def completionEndpointPoleJet (logLam g₁ g₂ t : ℝ) : ℂ :=
  1 + ((t / (2 * logLam)) : ℂ) * Complex.I +
    ((completionEndpointLogEtaJet g₁ g₂ t / logLam : ℝ) : ℂ)

/-- The real-valued correction term in the normalized pole trajectory. -/
def completionEndpointPoleCorrection (logLam g₁ g₂ t : ℝ) : ℂ :=
  (((-completionEndpointKappaInf g₁ * t ^ 2 +
      completionEndpointQuarticCoeff g₁ g₂ * t ^ 4 +
      completionEndpointHigherRemainder g₂ t) / logLam : ℝ) : ℂ)

/-- Endpoint-jet diffusion package for the completion channel: composing the endpoint expansion of
`S(t)` with the quadratic jet of `g = log Λ` produces the explicit quadratic and quartic
coefficients for `log η(t)` and `Re P(it)`, together with the normalized pole trajectory.
    prop:completion-endpoint-jet-diffusion -/
theorem paper_completion_endpoint_jet_diffusion (logLam g₁ g₂ t : ℝ) :
    completionEndpointLogEtaJet g₁ g₂ t =
      -completionEndpointKappaInf g₁ * t ^ 2 +
        completionEndpointQuarticCoeff g₁ g₂ * t ^ 4 +
        completionEndpointHigherRemainder g₂ t ∧
      completionEndpointSigmaSq g₁ = g₁ / 2 ∧
      completionEndpointKappaInf g₁ = g₁ / 4 ∧
      completionEndpointRePJet logLam g₁ g₂ t =
        logLam - completionEndpointKappaInf g₁ * t ^ 2 +
          completionEndpointQuarticCoeff g₁ g₂ * t ^ 4 +
          completionEndpointHigherRemainder g₂ t ∧
      completionEndpointPoleJet logLam g₁ g₂ t =
        1 + ((t / (2 * logLam)) : ℂ) * Complex.I +
          completionEndpointPoleCorrection logLam g₁ g₂ t := by
  have hEta :
      completionEndpointLogEtaJet g₁ g₂ t =
        -completionEndpointKappaInf g₁ * t ^ 2 +
          completionEndpointQuarticCoeff g₁ g₂ * t ^ 4 +
          completionEndpointHigherRemainder g₂ t := by
    unfold completionEndpointLogEtaJet completionEndpointSJet completionEndpointKappaInf
    unfold completionEndpointQuarticCoeff completionEndpointHigherRemainder
    ring
  refine ⟨hEta, rfl, rfl, ?_, ?_⟩
  · rw [completionEndpointRePJet, hEta]
    ring
  · simp [completionEndpointPoleJet, completionEndpointPoleCorrection, hEta]

end

end Omega.Zeta
