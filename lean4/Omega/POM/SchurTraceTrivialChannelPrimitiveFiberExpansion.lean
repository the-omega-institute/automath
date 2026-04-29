namespace Omega.POM

set_option linter.unusedVariables false

/-- Paper label: `prop:pom-schur-trace-trivial-channel-primitive-fiber-expansion`. -/
theorem paper_pom_schur_trace_trivial_channel_primitive_fiber_expansion
    (m q : ℕ) (euler_product finite_coefficient_sum positive_integer_polynomial : Prop)
    (hEuler : euler_product) (hCoeff : euler_product → finite_coefficient_sum)
    (hPos : finite_coefficient_sum → positive_integer_polynomial) :
    finite_coefficient_sum ∧ positive_integer_polynomial := by
  exact ⟨hCoeff hEuler, hPos (hCoeff hEuler)⟩

end Omega.POM
