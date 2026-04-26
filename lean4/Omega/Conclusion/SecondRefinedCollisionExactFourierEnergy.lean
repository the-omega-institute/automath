import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete data for the refined collision/Fourier-energy identity. The finite abelian group is
recorded only through its cardinality and the real-valued squared Fourier magnitudes. -/
structure conclusion_second_refined_collision_exact_fourier_energy_data where
  fiberCount : ℕ
  groupCount : ℕ
  refinedMass : Fin fiberCount → Fin groupCount → ℝ
  fiberMass : Fin fiberCount → ℝ
  localProb : Fin fiberCount → Fin groupCount → ℝ
  localEnergy : Fin fiberCount → ℝ
  refinedS2 : ℝ
  plainS2 : ℝ
  pointwise_energy :
    ∀ x,
      ∑ g, refinedMass x g ^ (2 : ℕ) =
        (fiberMass x ^ (2 : ℕ) / (groupCount : ℝ)) * (1 + localEnergy x)
  global_energy :
    refinedS2 =
      (1 / (groupCount : ℝ)) * plainS2 +
        (1 / (groupCount : ℝ)) * ∑ x, fiberMass x ^ (2 : ℕ) * localEnergy x
  local_energy_formula :
    ∀ x, localEnergy x = (groupCount : ℝ) * ∑ g, localProb x g ^ (2 : ℕ) - 1
  uniform_zero :
    ∀ x,
      (∀ g, localProb x g = 1 / (groupCount : ℝ)) →
        localEnergy x = 0
  dirac_top :
    ∀ x,
      (∃ g0, localProb x g0 = 1 ∧ ∀ g ≠ g0, localProb x g = 0) →
        localEnergy x = (groupCount : ℝ) - 1

/-- Paper-facing statement extracted from the concrete Fourier-energy package. -/
def conclusion_second_refined_collision_exact_fourier_energy_statement
    (D : conclusion_second_refined_collision_exact_fourier_energy_data) : Prop :=
  (∀ x,
      ∑ g, D.refinedMass x g ^ (2 : ℕ) =
        (D.fiberMass x ^ (2 : ℕ) / (D.groupCount : ℝ)) * (1 + D.localEnergy x)) ∧
    D.refinedS2 =
      (1 / (D.groupCount : ℝ)) * D.plainS2 +
        (1 / (D.groupCount : ℝ)) * ∑ x, D.fiberMass x ^ (2 : ℕ) * D.localEnergy x ∧
    (∀ x, D.localEnergy x = (D.groupCount : ℝ) * ∑ g, D.localProb x g ^ (2 : ℕ) - 1) ∧
    (∀ x,
        (∀ g, D.localProb x g = 1 / (D.groupCount : ℝ)) →
          D.localEnergy x = 0) ∧
    (∀ x,
        (∃ g0, D.localProb x g0 = 1 ∧ ∀ g ≠ g0, D.localProb x g = 0) →
          D.localEnergy x = (D.groupCount : ℝ) - 1)

/-- Paper label: `thm:conclusion-second-refined-collision-exact-fourier-energy`. -/
theorem paper_conclusion_second_refined_collision_exact_fourier_energy
    (conclusion_second_refined_collision_exact_fourier_energy_D :
      conclusion_second_refined_collision_exact_fourier_energy_data) :
    conclusion_second_refined_collision_exact_fourier_energy_statement
      conclusion_second_refined_collision_exact_fourier_energy_D := by
  exact ⟨conclusion_second_refined_collision_exact_fourier_energy_D.pointwise_energy,
    conclusion_second_refined_collision_exact_fourier_energy_D.global_energy,
    conclusion_second_refined_collision_exact_fourier_energy_D.local_energy_formula,
    conclusion_second_refined_collision_exact_fourier_energy_D.uniform_zero,
    conclusion_second_refined_collision_exact_fourier_energy_D.dirac_top⟩

end Omega.Conclusion
