namespace Omega

/-- Paper label: `cor:xi-gaussian-but-nonrh-congruence-separation`. -/
theorem paper_xi_gaussian_but_nonrh_congruence_separation
    (real_direction cyclotomic_direction no_single_sqrt_law strict_split : Prop)
    (hreal : real_direction) (hcyc : cyclotomic_direction)
    (hcombine :
      real_direction → cyclotomic_direction → no_single_sqrt_law ∧ strict_split) :
    no_single_sqrt_law ∧ strict_split := by
  exact hcombine hreal hcyc

end Omega
