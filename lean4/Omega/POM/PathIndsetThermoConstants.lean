import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Independence polynomial of a path, encoded by the standard endpoint split recurrence. -/
def pom_path_indset_thermo_constants_partitionFunction : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => 1 + t
  | n + 2, t =>
      pom_path_indset_thermo_constants_partitionFunction (n + 1) t +
        t * pom_path_indset_thermo_constants_partitionFunction n t

/-- Dominant root of the path-independence characteristic equation `z^2 = z + t`. -/
noncomputable def pom_path_indset_thermo_constants_dominantRoot (t : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 4 * t)) / 2

/-- Occupancy-density constant obtained from the logarithmic derivative of the dominant root. -/
noncomputable def pom_path_indset_thermo_constants_density (t : ℝ) : ℝ :=
  t / (pom_path_indset_thermo_constants_dominantRoot t * Real.sqrt (1 + 4 * t))

/-- Variance-density constant obtained from the second logarithmic derivative. -/
noncomputable def pom_path_indset_thermo_constants_varianceDensity (t : ℝ) : ℝ :=
  t / (Real.sqrt (1 + 4 * t) ^ 3)

/-- Concrete chapter-local package formalizing the recurrence, dominant-root relation, and the
closed density constants used in the paper. -/
def pom_path_indset_thermo_constants_statement : Prop :=
  (∀ t : ℝ, pom_path_indset_thermo_constants_partitionFunction 0 t = 1) ∧
    (∀ t : ℝ, pom_path_indset_thermo_constants_partitionFunction 1 t = 1 + t) ∧
    (∀ ℓ : ℕ, ∀ t : ℝ,
      pom_path_indset_thermo_constants_partitionFunction (ℓ + 2) t =
        pom_path_indset_thermo_constants_partitionFunction (ℓ + 1) t +
          t * pom_path_indset_thermo_constants_partitionFunction ℓ t) ∧
    (∀ t : ℝ, 0 ≤ t →
      pom_path_indset_thermo_constants_dominantRoot t ^ 2 =
        pom_path_indset_thermo_constants_dominantRoot t + t) ∧
    pom_path_indset_thermo_constants_dominantRoot 1 = Real.goldenRatio ∧
    pom_path_indset_thermo_constants_density 1 = 1 / (Real.goldenRatio * Real.sqrt 5) ∧
    pom_path_indset_thermo_constants_varianceDensity 1 = 1 / (Real.sqrt 5 ^ 3)

/-- Paper label: `prop:pom-path-indset-thermo-constants`. The path-independence polynomial
satisfies the endpoint-split recurrence, the dominant branch solves `z^2 = z + t`, and the
logarithmic-derivative constants reduce to the explicit closed forms at `t = 1`. -/
theorem paper_pom_path_indset_thermo_constants : pom_path_indset_thermo_constants_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rfl
  · intro t
    rfl
  · intro ℓ t
    cases ℓ <;> rfl
  · intro t ht
    have hs : 0 ≤ 1 + 4 * t := by nlinarith
    have hsq : Real.sqrt (1 + 4 * t) ^ 2 = 1 + 4 * t := by
      nlinarith [Real.sq_sqrt hs]
    unfold pom_path_indset_thermo_constants_dominantRoot
    nlinarith
  · unfold pom_path_indset_thermo_constants_dominantRoot Real.goldenRatio
    ring_nf
  · have hdensity :
        pom_path_indset_thermo_constants_density 1 = 1 / (Real.goldenRatio * Real.sqrt 5) := by
      unfold pom_path_indset_thermo_constants_density
        pom_path_indset_thermo_constants_dominantRoot Real.goldenRatio
      ring_nf
    simpa using hdensity
  · unfold pom_path_indset_thermo_constants_varianceDensity
    ring_nf

end

end Omega.POM
