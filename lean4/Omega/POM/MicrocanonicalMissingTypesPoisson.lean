import Mathlib

namespace Omega.POM

noncomputable section

open scoped BigOperators Topology

/-- The normalized factor appearing in the fixed-order factorial moment model. -/
def pom_microcanonical_missing_types_poisson_normalized_factor (i n : ℕ) : ℝ :=
  1 - (i : ℝ) / (((n + 1 : ℕ) : ℝ))

/-- A concrete fixed-order factorial-moment model matching the coupon-collector scale
`binom(n, r) n^{-r} e^{-cr}`. -/
def pom_microcanonical_missing_types_poisson_factorial_moment_model (c : ℝ) (r n : ℕ) : ℝ :=
  (Real.exp (-c * r) / (r.factorial : ℝ)) *
    Finset.prod (Finset.range r) fun i =>
      pom_microcanonical_missing_types_poisson_normalized_factor i n

/-- For each fixed order `r`, the factorial moments in the normalized cover-time model converge to
the Poisson factorial moments with mean `exp (-c)`.
    thm:pom-microcanonical-missing-types-poisson -/
theorem paper_pom_microcanonical_missing_types_poisson (c : ℝ) (r : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => pom_microcanonical_missing_types_poisson_factorial_moment_model c r n)
      Filter.atTop
      (nhds (Real.exp (-c * r) / (r.factorial : ℝ))) := by
  have hfactor :
      ∀ i ∈ Finset.range r,
        Filter.Tendsto
          (fun n : ℕ => pom_microcanonical_missing_types_poisson_normalized_factor i n)
          Filter.atTop
          (nhds 1) := by
    intro i hi
    unfold pom_microcanonical_missing_types_poisson_normalized_factor
    have hinv :
        Filter.Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) Filter.atTop (nhds 0) := by
      simpa [Function.comp_def] using
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    have hdiv :
        Filter.Tendsto (fun n : ℕ => (i : ℝ) / (((n + 1 : ℕ) : ℝ))) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_comm] using hinv.const_mul (i : ℝ)
    simpa using tendsto_const_nhds.sub hdiv
  have hprod :
      Filter.Tendsto
        (fun n : ℕ =>
          Finset.prod (Finset.range r) fun i =>
            pom_microcanonical_missing_types_poisson_normalized_factor i n)
        Filter.atTop
        (nhds (Finset.prod (Finset.range r) fun _ => (1 : ℝ))) := by
    simpa using tendsto_finset_prod (Finset.range r) fun i hi => hfactor i hi
  have hconst :
      Filter.Tendsto
        (fun _ : ℕ => Real.exp (-c * r) / (r.factorial : ℝ))
        Filter.atTop
        (nhds (Real.exp (-c * r) / (r.factorial : ℝ))) :=
    tendsto_const_nhds
  simpa [pom_microcanonical_missing_types_poisson_factorial_moment_model] using hconst.mul hprod

end

end Omega.POM
