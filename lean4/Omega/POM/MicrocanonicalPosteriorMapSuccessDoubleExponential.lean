import Omega.POM.MicrocanonicalFoldBayesSuccessNminusT
import Omega.POM.MicrocanonicalPosteriorEntropyLinearLaw

namespace Omega.POM

open scoped BigOperators

section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Paper label:
`cor:pom-microcanonical-posterior-map-success-double-exponential`. -/
theorem paper_pom_microcanonical_posterior_map_success_double_exponential
    (d : α → ℕ) (t : ℕ) (beta : ℝ) (hmass : 0 < microcanonicalTotalMass d) :
    (∀ r : α → ℕ,
      microcanonicalResidualBayesSuccess r =
        (∏ x : α, (Nat.factorial (r x) : ℚ)) /
          (Nat.factorial (microcanonicalTotalMass r) : ℚ)) ∧
      MicrocanonicalPosteriorEntropyLinearLaw d beta := by
  have _ : ℕ := t
  refine ⟨?_, paper_pom_microcanonical_posterior_entropy_linear_law d beta hmass⟩
  intro r
  rfl

end

end Omega.POM
