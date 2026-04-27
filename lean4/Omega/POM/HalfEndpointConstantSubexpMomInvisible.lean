namespace Omega.POM

/-- Paper label: `cor:pom-half-endpoint-constant-subexp-mom-invisible`. -/
theorem paper_pom_half_endpoint_constant_subexp_mom_invisible
    (integerPowerSumsAgree halfEndpointRateSeparated endpointConstantNotUniformlyDetermined : Prop)
    (hsep : integerPowerSumsAgree → halfEndpointRateSeparated)
    (hnot : halfEndpointRateSeparated → endpointConstantNotUniformlyDetermined) :
    integerPowerSumsAgree → endpointConstantNotUniformlyDetermined := by
  intro hIntegerPowerSumsAgree
  exact hnot (hsep hIntegerPowerSumsAgree)

end Omega.POM
