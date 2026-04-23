import Mathlib
import Omega.Conclusion.ZeckendorfEulerPoissonBoundary
import Omega.Conclusion.ZeckendorfEulerReindexing
import Omega.Folding.Entropy

namespace Omega.Conclusion

open Filter Topology
open scoped BigOperators goldenRatio

/-- Concrete law packaging the factorial reindexing, the positive-temperature reciprocal-factorial
summability at `β = 1`, the finite-range Poisson boundary identification, and the zero-temperature
`log φ` entropy growth. -/
abbrev conclusion_factorial_potential_positive_temperature_pressure_collapse_law : Prop :=
  (∀ m : ℕ,
      (∑ x : Omega.X m, ((Nat.factorial (Omega.stableValue x) : ℕ) : ℝ)⁻¹) =
        ∑ i : Fin (Nat.fib (m + 2)), ((Nat.factorial i.1 : ℕ) : ℝ)⁻¹) ∧
    Summable (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹) ∧
    (∀ m : ℕ, zeckendorfEulerPoissonBoundaryLaw m) ∧
    Tendsto (fun t : ℕ => Real.log (Nat.fib (t + 2) : ℝ) / (t : ℝ)) atTop (𝓝 (Real.log φ))

/-- Paper label: `thm:conclusion-factorial-potential-positive-temperature-pressure-collapse`. -/
theorem paper_conclusion_factorial_potential_positive_temperature_pressure_collapse :
    conclusion_factorial_potential_positive_temperature_pressure_collapse_law := by
  refine ⟨paper_conclusion_zeckendorf_euler_reindexing, ?_, ?_, ?_⟩
  · simpa using (Real.summable_pow_div_factorial 1)
  · exact paper_conclusion_zeckendorf_euler_poisson_boundary
  · simpa using Omega.Entropy.topological_entropy_eq_log_phi

end Omega.Conclusion
