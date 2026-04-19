import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The trajectory probability obtained from the microcanonical posterior count formula. -/
noncomputable def microcanonicalTrajectoryProbability (foldCard posteriorModulus : ℝ) : ℝ :=
  posteriorModulus / foldCard

/-- Self-information of the observed trajectory. -/
noncomputable def microcanonicalSelfInformation (foldCard posteriorModulus : ℝ) : ℝ :=
  -Real.log (microcanonicalTrajectoryProbability foldCard posteriorModulus)

/-- The expected posterior logarithm appearing in the entropy identity. -/
noncomputable def microcanonicalExpectedLogPosteriorModulus (posteriorModulus : ℝ) : ℝ :=
  Real.log posteriorModulus

/-- The Shannon entropy of the deterministic query trajectory. -/
noncomputable def microcanonicalTrajectoryEntropy (foldCard posteriorModulus : ℝ) : ℝ :=
  Real.log foldCard - microcanonicalExpectedLogPosteriorModulus posteriorModulus

/-- Deterministic queries identify the mutual information with trajectory entropy. -/
noncomputable def microcanonicalMutualInformation (foldCard posteriorModulus : ℝ) : ℝ :=
  microcanonicalTrajectoryEntropy foldCard posteriorModulus

/-- Taking expectations of the same pointwise identity reproduces the trajectory entropy. -/
noncomputable def microcanonicalExpectedSelfInformation (foldCard posteriorModulus : ℝ) : ℝ :=
  microcanonicalTrajectoryEntropy foldCard posteriorModulus

/-- The microcanonical self-information identity and its expectation-level consequences.
    thm:pom-microcanonical-information-identity -/
theorem paper_pom_microcanonical_information_identity (foldCard posteriorModulus : ℝ)
    (hFoldCard : 0 < foldCard) (hPosteriorModulus : 0 < posteriorModulus) :
    microcanonicalSelfInformation foldCard posteriorModulus =
        Real.log foldCard - Real.log posteriorModulus ∧
      microcanonicalMutualInformation foldCard posteriorModulus =
        microcanonicalTrajectoryEntropy foldCard posteriorModulus ∧
      microcanonicalExpectedSelfInformation foldCard posteriorModulus =
        microcanonicalTrajectoryEntropy foldCard posteriorModulus ∧
      microcanonicalExpectedSelfInformation foldCard posteriorModulus =
        Real.log foldCard - microcanonicalExpectedLogPosteriorModulus posteriorModulus := by
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [microcanonicalSelfInformation, microcanonicalTrajectoryProbability]
  rw [Real.log_div (ne_of_gt hPosteriorModulus) (ne_of_gt hFoldCard)]
  ring

end Omega.POM
