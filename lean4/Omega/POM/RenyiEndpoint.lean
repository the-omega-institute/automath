namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the endpoint law for the partition constants in
    `2026_projection_ontological_mathematics_core_tams`.
    cor:renyi-endpoint -/
theorem paper_projection_renyi_endpoint
    (lpNormMonotonicity sannaEndpointLimit allQTransfer lambdaEndpointLaw rEndpointLaw : Prop)
    (hLambda : lpNormMonotonicity → sannaEndpointLimit → lambdaEndpointLaw)
    (hR : lambdaEndpointLaw → allQTransfer → rEndpointLaw) :
    lpNormMonotonicity →
      sannaEndpointLimit →
        allQTransfer →
          lambdaEndpointLaw ∧ rEndpointLaw := by
  intro hMono hSanna hTransfer
  have hLambdaLaw : lambdaEndpointLaw := hLambda hMono hSanna
  exact ⟨hLambdaLaw, hR hLambdaLaw hTransfer⟩

end Omega.POM
