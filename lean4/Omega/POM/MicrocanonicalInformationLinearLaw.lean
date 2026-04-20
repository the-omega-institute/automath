import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalInformationIdentity

namespace Omega.POM

/-- The linear information law obtained by specializing the fold-count entropy and posterior
modulus to exponential scales `exp(H_w)` and `exp((1 - β) H_w)`. -/
def pomMicrocanonicalInformationLinearLawStatement (beta H_w : ℝ) : Prop :=
  microcanonicalTrajectoryEntropy (Real.exp H_w) (Real.exp ((1 - beta) * H_w)) = beta * H_w ∧
    microcanonicalMutualInformation (Real.exp H_w) (Real.exp ((1 - beta) * H_w)) = beta * H_w ∧
    microcanonicalExpectedSelfInformation (Real.exp H_w) (Real.exp ((1 - beta) * H_w)) =
      beta * H_w

/-- The microcanonical information identity turns the entropy-minus-posterior expression into the
linear law, and the same value is inherited by the mutual information and expected self-
information terms. -/
theorem pomMicrocanonicalInformationLinearLawStatement_true (beta H_w : ℝ) :
    pomMicrocanonicalInformationLinearLawStatement beta H_w := by
  let foldCard := Real.exp H_w
  let posteriorModulus := Real.exp ((1 - beta) * H_w)
  have hInfo :=
    paper_pom_microcanonical_information_identity foldCard posteriorModulus
      (by simpa [foldCard] using Real.exp_pos H_w)
      (by simpa [posteriorModulus] using Real.exp_pos ((1 - beta) * H_w))
  have hEntropy : microcanonicalTrajectoryEntropy foldCard posteriorModulus = beta * H_w := by
    simp [microcanonicalTrajectoryEntropy, microcanonicalExpectedLogPosteriorModulus,
      foldCard, posteriorModulus]
    ring
  refine ⟨hEntropy, ?_, ?_⟩
  · calc
      microcanonicalMutualInformation foldCard posteriorModulus
          = microcanonicalTrajectoryEntropy foldCard posteriorModulus := hInfo.2.1
      _ = beta * H_w := hEntropy
  · calc
      microcanonicalExpectedSelfInformation foldCard posteriorModulus
          = microcanonicalTrajectoryEntropy foldCard posteriorModulus := hInfo.2.2.1
      _ = beta * H_w := hEntropy

/-- Paper proposition wrapper for the microcanonical information linear law.
    thm:pom-microcanonical-information-linear-law -/
def paper_pom_microcanonical_information_linear_law (beta H_w : ℝ) : Prop := by
  exact pomMicrocanonicalInformationLinearLawStatement beta H_w

end Omega.POM
