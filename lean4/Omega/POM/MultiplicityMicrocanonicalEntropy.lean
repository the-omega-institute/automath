import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- The lower endpoint `\log φ` of the energy window from the multiplicity model. -/
noncomputable def pomMultiplicityEnergyLeft : ℝ :=
  Real.log Real.goldenRatio

/-- The upper endpoint `\log 2` of the energy window from the multiplicity model. -/
noncomputable def pomMultiplicityEnergyRight : ℝ :=
  Real.log 2

/-- The midpoint of the seed energy interval. -/
noncomputable def pomMultiplicityEnergyCenter : ℝ :=
  (pomMultiplicityEnergyLeft + pomMultiplicityEnergyRight) / 2

/-- Half the width of the seed energy interval. -/
noncomputable def pomMultiplicityEnergyRadius : ℝ :=
  (pomMultiplicityEnergyRight - pomMultiplicityEnergyLeft) / 2

/-- A concrete quadratic microcanonical entropy with endpoints `0` at `\log φ` and `\log 2`. -/
noncomputable def pomMultiplicityEntropy (e : ℝ) : ℝ :=
  pomMultiplicityEnergyRadius ^ 2 - (e - pomMultiplicityEnergyCenter) ^ 2

/-- The matching quadratic pressure profile, i.e. the Legendre dual of the seed entropy. -/
noncomputable def pomMultiplicityLogLambda (q : ℝ) : ℝ :=
  pomMultiplicityEnergyRadius ^ 2 + pomMultiplicityEnergyCenter * q + q ^ 2 / 4

/-- The optimizer realizing the quadratic Legendre transform. -/
noncomputable def pomMultiplicityExtremalEnergy (q : ℝ) : ℝ :=
  pomMultiplicityEnergyCenter + q / 2

/-- The seed microcanonical entropy is the exact quadratic Legendre dual of the seed pressure,
vanishes at the two extremal energies, and satisfies the exact midpoint-strict-concavity identity.
`thm:pom-multiplicity-microcanonical-entropy` -/
theorem paper_pom_multiplicity_microcanonical_entropy :
    (∀ q : ℝ,
      pomMultiplicityLogLambda q =
        pomMultiplicityEntropy (pomMultiplicityExtremalEnergy q) +
          q * pomMultiplicityExtremalEnergy q) ∧
      (∀ e : ℝ,
        pomMultiplicityEntropy e =
          pomMultiplicityLogLambda (2 * (e - pomMultiplicityEnergyCenter)) -
            (2 * (e - pomMultiplicityEnergyCenter)) * e) ∧
      pomMultiplicityEntropy pomMultiplicityEnergyLeft = 0 ∧
      pomMultiplicityEntropy pomMultiplicityEnergyRight = 0 ∧
      (∀ e₁ e₂ : ℝ,
        pomMultiplicityEntropy ((e₁ + e₂) / 2) -
            (pomMultiplicityEntropy e₁ + pomMultiplicityEntropy e₂) / 2 =
          (e₁ - e₂) ^ 2 / 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q
    unfold pomMultiplicityLogLambda pomMultiplicityEntropy pomMultiplicityExtremalEnergy
      pomMultiplicityEnergyRadius pomMultiplicityEnergyCenter
    ring_nf
  · intro e
    unfold pomMultiplicityLogLambda pomMultiplicityEntropy pomMultiplicityEnergyCenter
      pomMultiplicityEnergyRadius
    ring_nf
  · simp [pomMultiplicityEntropy, pomMultiplicityEnergyRadius, pomMultiplicityEnergyCenter,
      pomMultiplicityEnergyLeft, pomMultiplicityEnergyRight]
    ring
  · simp [pomMultiplicityEntropy, pomMultiplicityEnergyRadius, pomMultiplicityEnergyCenter,
      pomMultiplicityEnergyLeft, pomMultiplicityEnergyRight]
    ring
  · intro e₁ e₂
    unfold pomMultiplicityEntropy pomMultiplicityEnergyCenter pomMultiplicityEnergyRadius
    ring_nf

end Omega.POM
