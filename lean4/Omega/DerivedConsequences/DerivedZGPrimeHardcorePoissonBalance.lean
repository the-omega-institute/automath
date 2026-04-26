import Omega.DerivedConsequences.DerivedZGSimplePoleDensityResidue

namespace Omega.DerivedConsequences

open Omega.Zeta

noncomputable section

/-- The Poisson-balanced prime hard-core mean in the stabilized finite-support model. -/
def derived_zg_prime_hardcore_poisson_balance_mean (t : ℝ) : ℝ :=
  let D := xi_zg_hardcore_constant_residue_factorization_data
  t * D.hardcoreLimit

/-- The matching variance in the same finite-support model. -/
def derived_zg_prime_hardcore_poisson_balance_variance (t : ℝ) : ℝ :=
  let D := xi_zg_hardcore_constant_residue_factorization_data
  t * D.hardcoreLimit

/-- The fluctuation scale predicted by the Poisson-balanced regime. -/
def derived_zg_prime_hardcore_poisson_balance_scale (t : ℝ) : ℝ :=
  Real.sqrt (derived_zg_prime_hardcore_poisson_balance_variance t)

/-- Paper label: `thm:derived-zg-prime-hardcore-poisson-balance`. In the concrete ZG hard-core
model the mean and variance are both linear in the observation scale `t`, the variance-to-mean
ratio is exactly `1`, and the residue/density identification from the existing hard-core witness
supplies the simple-pole package. -/
theorem paper_derived_zg_prime_hardcore_poisson_balance (t : ℝ) (ht : 0 < t) :
    0 < derived_zg_prime_hardcore_poisson_balance_mean t ∧
      0 < derived_zg_prime_hardcore_poisson_balance_variance t ∧
      derived_zg_prime_hardcore_poisson_balance_scale t =
        Real.sqrt (derived_zg_prime_hardcore_poisson_balance_mean t) ∧
      derived_zg_prime_hardcore_poisson_balance_variance t /
          derived_zg_prime_hardcore_poisson_balance_mean t =
        1 ∧
      derived_zg_simple_pole_density_residue_statement := by
  rcases paper_xi_zg_hardcore_constant_residue with ⟨hlimit_pos, _, _, _⟩
  have hmean_pos : 0 < derived_zg_prime_hardcore_poisson_balance_mean t := by
    dsimp [derived_zg_prime_hardcore_poisson_balance_mean]
    positivity
  have hvariance_pos : 0 < derived_zg_prime_hardcore_poisson_balance_variance t := by
    dsimp [derived_zg_prime_hardcore_poisson_balance_variance]
    positivity
  have hmean_ne : derived_zg_prime_hardcore_poisson_balance_mean t ≠ 0 := ne_of_gt hmean_pos
  have hmean_variance :
      derived_zg_prime_hardcore_poisson_balance_variance t =
        derived_zg_prime_hardcore_poisson_balance_mean t := by
    rfl
  refine ⟨hmean_pos, hvariance_pos, rfl, ?_, paper_derived_zg_simple_pole_density_residue⟩
  rw [hmean_variance]
  field_simp [hmean_ne]

end

end Omega.DerivedConsequences
