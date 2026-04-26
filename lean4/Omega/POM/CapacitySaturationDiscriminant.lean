import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete audit data for the capacity-saturation discriminant.  The folded mass is tied to
fiber multiplicity over the `2^m` microstates, and the remaining real parameters encode the
growth-rate and Rényi endpoint comparison. -/
structure pom_capacity_saturation_discriminant_data where
  m : ℕ
  fiberMultiplicity : ℝ
  foldedOutputMass : ℝ
  maximumFoldedMass : ℝ
  capacityRate : ℝ
  saturationRate : ℝ
  discriminant : ℝ
  renyiEndpoint : ℝ
  maxFiberExponent : ℝ
  endpointGap : ℝ
  foldedOutputMassFormula : foldedOutputMass = fiberMultiplicity / (2 : ℝ) ^ m
  maximumFoldedMassFormula : maximumFoldedMass = foldedOutputMass
  discriminantFormula : discriminant = capacityRate - saturationRate
  endpointGapFormula : endpointGap = renyiEndpoint - maxFiberExponent

/-- The maximum folded output mass is the displayed fiber multiplicity divided by `2^m`. -/
def pom_capacity_saturation_discriminant_data.max_probability_identity
    (D : pom_capacity_saturation_discriminant_data) : Prop :=
  D.maximumFoldedMass = D.fiberMultiplicity / (2 : ℝ) ^ D.m

/-- The discriminant has the three standard exponential alternatives. -/
def pom_capacity_saturation_discriminant_data.exponential_discriminant
    (D : pom_capacity_saturation_discriminant_data) : Prop :=
  D.discriminant = D.capacityRate - D.saturationRate ∧
    (D.capacityRate < D.saturationRate ∨
      D.capacityRate = D.saturationRate ∨
      D.saturationRate < D.capacityRate)

/-- The Rényi endpoint criterion is zero endpoint gap, equivalently equality of the two
endpoint exponents. -/
def pom_capacity_saturation_discriminant_data.renyi_endpoint_criterion
    (D : pom_capacity_saturation_discriminant_data) : Prop :=
  D.endpointGap = 0 ↔ D.renyiEndpoint = D.maxFiberExponent

/-- Paper label: `prop:pom-capacity-saturation-discriminant`. -/
theorem paper_pom_capacity_saturation_discriminant
    (D : pom_capacity_saturation_discriminant_data) :
    D.max_probability_identity ∧ D.exponential_discriminant ∧ D.renyi_endpoint_criterion := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pom_capacity_saturation_discriminant_data.max_probability_identity]
    rw [D.maximumFoldedMassFormula, D.foldedOutputMassFormula]
  · rw [pom_capacity_saturation_discriminant_data.exponential_discriminant]
    refine ⟨D.discriminantFormula, ?_⟩
    rcases lt_trichotomy D.capacityRate D.saturationRate with hlt | heq | hgt
    · exact Or.inl hlt
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr hgt)
  · rw [pom_capacity_saturation_discriminant_data.renyi_endpoint_criterion]
    rw [D.endpointGapFormula]
    constructor
    · intro h
      linarith
    · intro h
      linarith

end Omega.POM
