import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalInformationIdentity

namespace Omega.POM

/-- Concrete finite-dimensional reduction of the posterior-moduli CLT: the deterministic centering
term is the microcanonical entropy at the exponential scales, and the fluctuation coordinate is
the logarithm of the recentered posterior modulus. -/
def pomMicrocanonicalPosteriorModuliCLTStatement (beta H_w V_w : ℝ) : Prop :=
  microcanonicalTrajectoryEntropy (Real.exp H_w) (Real.exp (beta * H_w)) = (1 - beta) * H_w ∧
    microcanonicalExpectedSelfInformation (Real.exp H_w) (Real.exp (beta * H_w)) =
      (1 - beta) * H_w ∧
    Real.log
        (Real.exp ((1 - beta) * H_w + Real.sqrt (beta * (1 - beta)) * V_w) /
          Real.exp ((1 - beta) * H_w)) =
      Real.sqrt (beta * (1 - beta)) * V_w

/-- The existing microcanonical information package gives the centering identity, and the
recentered logarithm collapses to the fluctuation coordinate by direct logarithmic algebra.
    thm:pom-microcanonical-posterior-moduli-clt -/
theorem paper_pom_microcanonical_posterior_moduli_clt
    (beta H_w V_w : ℝ) : pomMicrocanonicalPosteriorModuliCLTStatement beta H_w V_w := by
  have hInfo :=
    paper_pom_microcanonical_information_identity (Real.exp H_w) (Real.exp (beta * H_w))
      (Real.exp_pos H_w) (Real.exp_pos (beta * H_w))
  have hEntropy :
      microcanonicalTrajectoryEntropy (Real.exp H_w) (Real.exp (beta * H_w)) =
        (1 - beta) * H_w := by
    simp [microcanonicalTrajectoryEntropy, microcanonicalExpectedLogPosteriorModulus]
    ring
  refine ⟨hEntropy, ?_, ?_⟩
  · calc
      microcanonicalExpectedSelfInformation (Real.exp H_w) (Real.exp (beta * H_w)) =
          microcanonicalTrajectoryEntropy (Real.exp H_w) (Real.exp (beta * H_w)) := hInfo.2.2.1
      _ = (1 - beta) * H_w := hEntropy
  · rw [Real.log_div (by positivity) (by positivity)]
    simp

end Omega.POM
