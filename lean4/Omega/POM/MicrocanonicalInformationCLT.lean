import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalInformationLinearLaw
import Omega.POM.MicrocanonicalPosteriorModuliCLT

namespace Omega.POM

noncomputable section

/-- Centered information fluctuation obtained by rewriting the posterior-moduli logarithm inside
the microcanonical information identity. -/
def pomMicrocanonicalInformationCLTStatement (beta H_w V_w : ℝ) : Prop :=
  microcanonicalTrajectoryEntropy (Real.exp H_w) (Real.exp ((1 - beta) * H_w)) = beta * H_w ∧
    microcanonicalExpectedSelfInformation (Real.exp H_w) (Real.exp ((1 - beta) * H_w)) =
      beta * H_w ∧
    let s := Real.sqrt (beta * (1 - beta)) * V_w
    Real.log (Real.exp H_w / Real.exp ((1 - beta) * H_w + s)) - beta * H_w = -s

/-- Paper label: `cor:pom-microcanonical-information-clt`. The information linear law supplies the
centering `β H(w)`, and the posterior-moduli CLT rewrites the same normalization as the centered
information fluctuation. -/
theorem paper_pom_microcanonical_information_clt (beta H_w V_w : ℝ) :
    pomMicrocanonicalInformationCLTStatement beta H_w V_w := by
  rcases pomMicrocanonicalInformationLinearLawStatement_true beta H_w with ⟨hEntropy, _, hSelf⟩
  have hPosterior :=
    (paper_pom_microcanonical_posterior_moduli_clt beta H_w V_w).2.2
  refine ⟨hEntropy, hSelf, ?_⟩
  dsimp
  have hrewrite :
      Real.log
          (Real.exp H_w /
            Real.exp ((1 - beta) * H_w + Real.sqrt (beta * (1 - beta)) * V_w)) -
        beta * H_w =
          -Real.log
            (Real.exp
                ((1 - beta) * H_w + Real.sqrt (beta * (1 - beta)) * V_w) /
              Real.exp ((1 - beta) * H_w)) := by
    rw [Real.log_div (by positivity) (by positivity)]
    rw [Real.log_div (by positivity) (by positivity)]
    simp
    ring
  rw [hrewrite, hPosterior]

end

end Omega.POM
