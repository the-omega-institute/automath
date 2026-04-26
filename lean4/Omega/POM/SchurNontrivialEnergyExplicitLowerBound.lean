import Mathlib.Tactic

namespace Omega.POM

/-- Concrete Schur-cycle energy data for the nontrivial-energy lower bound.

The package records the identity cycle energy, the transposition comparison term, and the strict
collision-rate hypothesis. The theorem below derives the variance identity and positivity from
these concrete fields. -/
structure pom_schur_nontrivial_energy_explicit_lower_bound_data where
  cycleEnergy : Fin 2 → ℝ
  collisionRate : ℝ
  collisionRate_nonneg : 0 ≤ collisionRate
  collisionRate_strict : collisionRate < 1
  identityCycleEnergy : cycleEnergy 0 = 1
  transpositionEnergy_le_collision : cycleEnergy 1 ≤ collisionRate

namespace pom_schur_nontrivial_energy_explicit_lower_bound_data

/-- Nontrivial Schur energy after isolating the identity cycle contribution. -/
def nontrivialEnergy (D : pom_schur_nontrivial_energy_explicit_lower_bound_data) : ℝ :=
  D.cycleEnergy 0 - D.collisionRate

/-- The variance form of the same energy. -/
def variance (D : pom_schur_nontrivial_energy_explicit_lower_bound_data) : ℝ :=
  1 - D.collisionRate

/-- The explicit lower bound supplied by strict collision loss. -/
def explicitLowerBound (D : pom_schur_nontrivial_energy_explicit_lower_bound_data) : Prop :=
  0 < 1 - D.collisionRate ∧ 1 - D.collisionRate ≤ D.nontrivialEnergy

/-- The fiber is nontrivial exactly when the collision rate is strictly below the identity rate. -/
def nontrivialFiber (D : pom_schur_nontrivial_energy_explicit_lower_bound_data) : Prop :=
  D.collisionRate < 1

/-- Positivity of the nontrivial Schur energy. -/
def positiveEnergy (D : pom_schur_nontrivial_energy_explicit_lower_bound_data) : Prop :=
  0 < D.nontrivialEnergy

end pom_schur_nontrivial_energy_explicit_lower_bound_data

/-- Paper label: `thm:pom-schur-nontrivial-energy-explicit-lower-bound`. -/
theorem paper_pom_schur_nontrivial_energy_explicit_lower_bound
    (D : pom_schur_nontrivial_energy_explicit_lower_bound_data) :
    D.nontrivialEnergy = D.variance ∧ D.explicitLowerBound ∧
      (D.nontrivialFiber → D.positiveEnergy) := by
  have henergy : D.nontrivialEnergy = D.variance := by
    simp [pom_schur_nontrivial_energy_explicit_lower_bound_data.nontrivialEnergy,
      pom_schur_nontrivial_energy_explicit_lower_bound_data.variance,
      D.identityCycleEnergy]
  have hposVariance : 0 < 1 - D.collisionRate := by
    linarith [D.collisionRate_strict]
  refine ⟨henergy, ?_, ?_⟩
  · constructor
    · exact hposVariance
    · rw [henergy, pom_schur_nontrivial_energy_explicit_lower_bound_data.variance]
  · intro _hNontrivial
    rw [pom_schur_nontrivial_energy_explicit_lower_bound_data.positiveEnergy, henergy,
      pom_schur_nontrivial_energy_explicit_lower_bound_data.variance]
    exact hposVariance

end Omega.POM
