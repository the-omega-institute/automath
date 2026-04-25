import Omega.POM.MinimalIntegerizationFactorCokerExponent

namespace Omega.POM

/-- Paper label: `cor:pom-stiffness-vs-integerization-separation`.

The Smith cokernel exponent is the lcm of the cyclic component exponents.  Since each component
exponent appears in the finite product of all component exponents, the lcm divides that product. -/
theorem paper_pom_stiffness_vs_integerization_separation {d : ℕ} (g : Fin d → ℕ) :
    smithCokerExponent g ∣ Finset.univ.prod (fun i : Fin d => smithComponentExponent g i) := by
  rw [smithCokerExponent]
  exact Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem (f := smithComponentExponent g) hi)

end Omega.POM
