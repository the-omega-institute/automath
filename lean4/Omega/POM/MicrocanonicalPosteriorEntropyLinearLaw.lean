import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.MicrocanonicalFoldEntropy
import Omega.POM.MicrocanonicalPosteriorModuliCLT

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The posterior moduli count is the same multinomial quotient as the microcanonical fold count. -/
def microcanonicalPosteriorModuliCount (d : α → ℕ) : ℕ :=
  microcanonicalFoldClassCount d

/-- Concrete finite-volume posterior entropy package: the posterior size is the multinomial
quotient, the logarithmic main term is exactly the Shannon term, and the exponential-scale
posterior entropy contracts linearly with slope `1 - β`. -/
def MicrocanonicalPosteriorEntropyLinearLaw (d : α → ℕ) (beta : ℝ) : Prop :=
  microcanonicalPosteriorModuliCount d =
      Nat.factorial (microcanonicalTotalMass d) /
        ∏ x ∈ (Finset.univ : Finset α), Nat.factorial (d x) ∧
    microcanonicalFoldEntropyMainTerm d =
      (microcanonicalTotalMass d : ℝ) * microcanonicalFoldShannonEntropy d ∧
    microcanonicalTrajectoryEntropy
        (Real.exp (microcanonicalFoldEntropyMainTerm d))
        (Real.exp (beta * microcanonicalFoldEntropyMainTerm d)) =
      (1 - beta) * microcanonicalFoldEntropyMainTerm d ∧
    microcanonicalExpectedSelfInformation
        (Real.exp (microcanonicalFoldEntropyMainTerm d))
        (Real.exp (beta * microcanonicalFoldEntropyMainTerm d)) =
      (1 - beta) * microcanonicalFoldEntropyMainTerm d

/-- Paper label: `thm:pom-microcanonical-posterior-entropy-linear-law`. The multinomial posterior
count, the Shannon main term, and the exponential-scale entropy contraction are all concrete
rewrites of the existing microcanonical fold-count and posterior-moduli identities. -/
theorem paper_pom_microcanonical_posterior_entropy_linear_law
    (d : α → ℕ) (beta : ℝ) (hmass : 0 < microcanonicalTotalMass d) :
    MicrocanonicalPosteriorEntropyLinearLaw d beta := by
  have hFold := paper_pom_microcanonical_fold_entropy d hmass
  have hClt :=
    paper_pom_microcanonical_posterior_moduli_clt beta (microcanonicalFoldEntropyMainTerm d) 0
  refine ⟨hFold.1, hFold.2, hClt.1, hClt.2.1⟩

end

end Omega.POM
