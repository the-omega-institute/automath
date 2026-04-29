namespace Omega.Zeta

/-- Paper label: `cor:xi-output-potential-odd-prime-bad-moduli-prime-density-one`. -/
theorem paper_xi_output_potential_odd_prime_bad_moduli_prime_density_one
    (eventually_bad density_one : Prop) (h_eventual : eventually_bad)
    (h_density : eventually_bad → density_one) :
    density_one := by
  exact h_density h_eventual

end Omega.Zeta
