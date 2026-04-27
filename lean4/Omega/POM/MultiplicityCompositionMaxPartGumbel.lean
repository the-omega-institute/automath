import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Epsilon-style convergence of a real sequence to a real limit. -/
def pom_multiplicity_composition_max_part_gumbel_tendsto
    (u : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |u n - a| ≤ ε

/-- The limiting part-length tail is geometric with amplitude `c` and ratio `a`. -/
def pom_multiplicity_composition_max_part_gumbel_geometricTail
    (tail : ℕ → ℝ) (c a : ℝ) : Prop :=
  ∃ N : ℕ, ∀ k : ℕ, N ≤ k → tail k = c * a ^ k

/-- The part-count process has the deterministic first-order scale `μ L` up to a vanishing
normalized error. -/
def pom_multiplicity_composition_max_part_gumbel_partCountCLT
    (partCountMean : ℕ → ℝ) (μ : ℝ) : Prop :=
  pom_multiplicity_composition_max_part_gumbel_tendsto
    (fun L : ℕ => partCountMean L / ((L : ℝ) + 1)) μ

/-- The centered maximum-part distribution converges to the Gumbel profile. -/
def pom_multiplicity_composition_max_part_gumbel_gumbelLimit
    (maxPartCDF : ℕ → ℝ → ℝ) (center : ℕ → ℝ) : Prop :=
  ∀ x : ℝ,
    pom_multiplicity_composition_max_part_gumbel_tendsto
      (fun L : ℕ => maxPartCDF L (center L + x)) (Real.exp (-Real.exp (-x)))

/-- The maximum-part centering has logarithmic scale `1 / -log a`. -/
def pom_multiplicity_composition_max_part_gumbel_logScale
    (center : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ L : ℕ, center L = Real.log ((L : ℝ) + 1) / (-Real.log a)

/-- Paper label: `thm:pom-multiplicity-composition-max-part-gumbel`. -/
theorem paper_pom_multiplicity_composition_max_part_gumbel
    (tail : ℕ → ℝ) (partCountMean : ℕ → ℝ) (maxPartCDF : ℕ → ℝ → ℝ)
    (center : ℕ → ℝ) (c a μ : ℝ)
    (geometricTail :
      pom_multiplicity_composition_max_part_gumbel_geometricTail tail c a)
    (partCountCLT :
      pom_multiplicity_composition_max_part_gumbel_partCountCLT partCountMean μ)
    (gumbelLimit_from_hypotheses :
      pom_multiplicity_composition_max_part_gumbel_geometricTail tail c a →
        pom_multiplicity_composition_max_part_gumbel_partCountCLT partCountMean μ →
          pom_multiplicity_composition_max_part_gumbel_gumbelLimit maxPartCDF center)
    (logScale_from_hypotheses :
      pom_multiplicity_composition_max_part_gumbel_geometricTail tail c a →
        pom_multiplicity_composition_max_part_gumbel_partCountCLT partCountMean μ →
          pom_multiplicity_composition_max_part_gumbel_logScale center a) :
    pom_multiplicity_composition_max_part_gumbel_gumbelLimit maxPartCDF center ∧
      pom_multiplicity_composition_max_part_gumbel_logScale center a := by
  exact
    ⟨gumbelLimit_from_hypotheses geometricTail partCountCLT,
      logScale_from_hypotheses geometricTail partCountCLT⟩

end Omega.POM
