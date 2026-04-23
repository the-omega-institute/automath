import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing q=1 Markov package for the multiplicity-composition transfer matrix. -/
abbrev pom_multiplicity_composition_q1_markov_law : Prop :=
  let α : ℝ := (3 + Real.sqrt 17) / 4
  let ρ : ℝ := 1 / (2 * α)
  let π0 : ℝ := (17 + Real.sqrt 17) / 34
  let π1 : ℝ := (17 - Real.sqrt 17) / 34
  ((1 : ℝ) + (α - 1) = α) ∧
    ((1 : ℝ) + (1 / 2 : ℝ) * (α - 1) = α * (α - 1)) ∧
    (ρ = (Real.sqrt 17 - 3) / 4) ∧
    (1 - 2 * ρ = (5 - Real.sqrt 17) / 2) ∧
    (π0 + π1 = 1) ∧
    (π1 = π0 * (1 - 2 * ρ) + π1 * ρ) ∧
    (((3 - Real.sqrt 17) / 2) * ((3 + Real.sqrt 17) / 2) = (-2 : ℝ)) ∧
    (((3 - Real.sqrt 17) / 2) / ((3 + Real.sqrt 17) / 2) =
      (-2 : ℝ) / (((3 + Real.sqrt 17) / 2) ^ (2 : ℕ)))

/-- Paper label: `prop:pom-multiplicity-composition-q1-markov`. -/
theorem paper_pom_multiplicity_composition_q1_markov :
    pom_multiplicity_composition_q1_markov_law := by
  dsimp [pom_multiplicity_composition_q1_markov_law]
  have pom_multiplicity_composition_q1_markov_sqrt17_sq : (Real.sqrt 17 : ℝ)^2 = 17 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by positivity)]
  refine ⟨by ring, ?_, ?_, ?_, by ring, ?_, ?_, ?_⟩
  · field_simp [pom_multiplicity_composition_q1_markov_sqrt17_sq]
    nlinarith [pom_multiplicity_composition_q1_markov_sqrt17_sq]
  · field_simp [pom_multiplicity_composition_q1_markov_sqrt17_sq]
    nlinarith [pom_multiplicity_composition_q1_markov_sqrt17_sq]
  · field_simp [pom_multiplicity_composition_q1_markov_sqrt17_sq]
    nlinarith [pom_multiplicity_composition_q1_markov_sqrt17_sq]
  · field_simp [pom_multiplicity_composition_q1_markov_sqrt17_sq]
    nlinarith [pom_multiplicity_composition_q1_markov_sqrt17_sq]
  · nlinarith [pom_multiplicity_composition_q1_markov_sqrt17_sq]
  · have pom_multiplicity_composition_q1_markov_hden :
        ((3 + Real.sqrt 17) / 2 : ℝ) ≠ 0 := by
      have : 0 < ((3 + Real.sqrt 17) / 2 : ℝ) := by positivity
      linarith
    field_simp [pom_multiplicity_composition_q1_markov_hden,
      pom_multiplicity_composition_q1_markov_sqrt17_sq]
    nlinarith [pom_multiplicity_composition_q1_markov_sqrt17_sq]

end Omega.POM
