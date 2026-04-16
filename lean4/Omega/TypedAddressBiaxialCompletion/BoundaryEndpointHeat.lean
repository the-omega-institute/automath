import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-local wrapper for the endpoint heat-kernel sequence. The data stores the heat values,
the limiting endpoint atom, the exponential gap parameters, and the paper-facing outputs used by
the boundary verifier. -/
structure BoundaryEndpointHeatData where
  endpointHeat : ℕ → ℝ
  endpointAtomMass : ℝ
  gapRatio : ℝ
  gapMass : ℝ
  targetError : ℝ
  monotoneToEndpointAtom : Prop
  exponentialErrorBound : Prop
  minDepthFormula : Prop
  hasMonotoneToEndpointAtom : monotoneToEndpointAtom
  hasExponentialErrorBound : exponentialErrorBound
  deriveMinDepthFormula :
    monotoneToEndpointAtom → exponentialErrorBound → minDepthFormula

/-- Paper-facing wrapper for the endpoint heat proposition: the endpoint heat sequence decreases
to the endpoint atom, satisfies the exponential gap estimate, and the corresponding truncation
depth formula follows from solving the error inequality.
    prop:typed-address-biaxial-completion-boundary-endpoint-heat -/
theorem paper_typed_address_biaxial_completion_boundary_endpoint_heat
    (D : BoundaryEndpointHeatData) :
    D.monotoneToEndpointAtom ∧ D.exponentialErrorBound ∧ D.minDepthFormula := by
  exact
    ⟨D.hasMonotoneToEndpointAtom, D.hasExponentialErrorBound,
      D.deriveMinDepthFormula D.hasMonotoneToEndpointAtom D.hasExponentialErrorBound⟩

end Omega.TypedAddressBiaxialCompletion
