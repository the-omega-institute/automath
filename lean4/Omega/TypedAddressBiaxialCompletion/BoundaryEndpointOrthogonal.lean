import Omega.TypedAddressBiaxialCompletion.BoundaryEndpointHeat
import Omega.TypedAddressBiaxialCompletion.BoundaryJointSufficiency

namespace Omega.TypedAddressBiaxialCompletion

/-- The endpoint-heat budget contributes its own paper-facing heat wrapper, and it is
logically non-substitutable even when the radius blindspot and address collision axes are
already closed.
    cor:typed-address-biaxial-completion-boundary-endpoint-orthogonal -/
theorem paper_typed_address_biaxial_completion_boundary_endpoint_orthogonal
    (V : BoundaryJointVerifierData) (E : BoundaryEndpointHeatData) :
    (E.monotoneToEndpointAtom ∧ E.exponentialErrorBound ∧ E.minDepthFormula) ∧
      ((V.axes.radiusBlindspotClosed ∧ V.axes.addressCollisionClosed ∧
          ¬ V.axes.endpointHeatClosed) →
        V.verifierResult ≠ BoundaryVerifierResult.certificate) := by
  refine ⟨paper_typed_address_biaxial_completion_boundary_endpoint_heat E, ?_⟩
  exact (paper_typed_address_biaxial_completion_boundary_joint_sufficiency V).2.2.2.2

end Omega.TypedAddressBiaxialCompletion
