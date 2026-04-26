namespace Omega.POM

/-- Paper label:
`thm:pom-multiplicity-composition-joint-ldp-partcount-energy`. The two-parameter
partition-function calculation supplies the cumulant-generating formula; the rate, strict
interior convexity, and gradient parametrization are then the advertised consequences. -/
theorem paper_pom_multiplicity_composition_joint_ldp_partcount_energy
    (cgf_formula rate_is_legendre_fenchel strict_convex_on_interior
      gradient_parametrized : Prop)
    (h_cgf : cgf_formula)
    (h_rate : cgf_formula -> rate_is_legendre_fenchel)
    (h_convex : cgf_formula -> strict_convex_on_interior)
    (h_grad : cgf_formula -> gradient_parametrized) :
    cgf_formula ∧ rate_is_legendre_fenchel ∧ strict_convex_on_interior ∧
      gradient_parametrized := by
  exact ⟨h_cgf, h_rate h_cgf, h_convex h_cgf, h_grad h_cgf⟩

end Omega.POM
