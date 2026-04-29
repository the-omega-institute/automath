import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic

namespace Omega.POM

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Paper label: `lem:pom-partition-monomial-exponential-main-term`.
For a fixed finite partition profile, eventual exponential main terms multiply to the exponential
main term whose coefficient and pressure are the corresponding finite products and sums. This is
the zero-error instance of the finite-product asymptotic interface used for partition monomials. -/
theorem paper_pom_partition_monomial_exponential_main_term
    {ι : Type*} [Fintype ι] (factor : ι → ℕ → ℝ) (coefficient pressure : ι → ℝ)
    (hfactor :
      ∀ i, factor i =ᶠ[atTop]
        fun m : ℕ => coefficient i * Real.exp ((m : ℝ) * pressure i)) :
    (fun m : ℕ => ∏ i, factor i m) =ᶠ[atTop]
      fun m : ℕ =>
        (∏ i, coefficient i) * Real.exp ((m : ℝ) * ∑ i, pressure i) := by
  classical
  have hprod :
      (∏ i, fun m : ℕ => factor i m) =ᶠ[atTop]
        ∏ i, fun m : ℕ => coefficient i * Real.exp ((m : ℝ) * pressure i) :=
    eventuallyEq_prod (s := Finset.univ) (l := atTop)
      (f := fun i m => factor i m)
      (g := fun i m => coefficient i * Real.exp ((m : ℝ) * pressure i))
      (by
        intro i _hi
        exact hfactor i)
  filter_upwards [hprod] with m hm
  calc
    (∏ i, factor i m) = (∏ i, fun m : ℕ => factor i m) m := by
      simp only [Finset.prod_apply]
    _ = (∏ i, fun m : ℕ => coefficient i * Real.exp ((m : ℝ) * pressure i)) m := hm
    _ = ∏ i, coefficient i * Real.exp ((m : ℝ) * pressure i) := by
      simp only [Finset.prod_apply]
    _ = (∏ i, coefficient i) * ∏ i, Real.exp ((m : ℝ) * pressure i) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ i, coefficient i) * Real.exp ((m : ℝ) * ∑ i, pressure i) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]

end

end Omega.POM
