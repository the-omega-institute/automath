import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.HankelVandermondeFiniteBlaschke

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Endpoint absorption contribution of a single finite Blaschke node. -/
def xiEndpointAbsorptionTerm (w : Real) (z : ℂ) : Real :=
  w * ((1 - ‖z‖ ^ 2) / ‖1 + z‖ ^ 2)

/-- The endpoint absorption coefficient obtained by summing the node contributions. -/
def xiEndpointAbsorption {κ : Nat} (w : Fin κ → Real) (z : Fin κ → ℂ) : Real :=
  ∑ j, xiEndpointAbsorptionTerm (w j) (z j)

/-- The endpoint Julia indicator extracted from the same first-order coefficient. -/
def xiEndpointJuliaIndicator {κ : Nat} (w : Fin κ → Real) (z : Fin κ → ℂ) : Real :=
  xiEndpointAbsorption w z

/-- A concrete boundary logarithmic derivative package whose real part recovers the endpoint
absorption. -/
def xiEndpointBoundaryLogDerivative {κ : Nat} (w : Fin κ → Real) (z : Fin κ → ℂ) : ℂ :=
  ∑ j, -((xiEndpointAbsorptionTerm (w j) (z j) : Real) : ℂ)

/-- Concrete endpoint Julia/absorption package for finite Blaschke data. -/
def xiEndpointJuliaIndicatorEqualsAbsorptionStatement : Prop :=
  ∀ {κ : Nat} (w : Fin κ → Real) (z : Fin κ → ℂ),
    xiEndpointJuliaIndicator w z = xiEndpointAbsorption w z ∧
      xiEndpointAbsorption w z = Complex.re (-xiEndpointBoundaryLogDerivative w z)

/-- Paper label: `thm:xi-endpoint-julia-indicator-equals-absorption`. -/
theorem paper_xi_endpoint_julia_indicator_equals_absorption :
    xiEndpointJuliaIndicatorEqualsAbsorptionStatement := by
  intro κ w z
  refine ⟨rfl, ?_⟩
  calc
    xiEndpointAbsorption w z = ∑ j, xiEndpointAbsorptionTerm (w j) (z j) := by
      rfl
    _ = Complex.re (-xiEndpointBoundaryLogDerivative w z) := by
      simp [xiEndpointBoundaryLogDerivative]

end

end Omega.Zeta
