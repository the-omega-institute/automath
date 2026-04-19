import Omega.TypedAddressBiaxialCompletion.BoundaryEndpointHeat

namespace Omega.TypedAddressBiaxialCompletion

/-- Chapter-facing complement statement packaging the Caratheodory identity with the endpoint
heat monotone-limit and exponential-gap outputs.
    prop:typed-address-biaxial-completion-endpoint-heat-kernel-complement -/
theorem paper_typed_address_biaxial_completion_endpoint_heat_kernel_complement
    (D : BoundaryEndpointHeatData) (caratheodory_identity orthogonal_complement : Prop)
    (hCar : caratheodory_identity) (hOrth : orthogonal_complement) :
    caratheodory_identity ∧ D.monotoneToEndpointAtom ∧ D.exponentialErrorBound ∧
      orthogonal_complement := by
  rcases paper_typed_address_biaxial_completion_boundary_endpoint_heat D with
    ⟨hMono, hExp, _hMinDepth⟩
  exact ⟨hCar, hMono, hExp, hOrth⟩

end Omega.TypedAddressBiaxialCompletion
