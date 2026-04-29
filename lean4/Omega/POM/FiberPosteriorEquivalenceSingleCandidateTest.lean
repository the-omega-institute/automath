import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.POM.FiberPosteriorEquivalenceActivityField
import Omega.POM.FiberPosteriorEquivalenceModuli

namespace Omega.POM

noncomputable section

/-- The single-candidate test at position `i` reads exactly one log-activity coordinate and then
exponentiates it back to the odds scale. -/
def pom_fiber_posterior_equivalence_single_candidate_test_value
    (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  Real.exp (pom_fiber_posterior_equivalence_moduli_log_activity_map y i)

/-- Concrete statement for the single-candidate test family: each test reads one local
log-activity coordinate, equality of all tests is equivalent to equality of those coordinates, and
dropping any one test leaves a remaining family that cannot distinguish a perturbation supported at
the omitted coordinate. -/
def pomFiberPosteriorEquivalenceSingleCandidateTestStatement (m : ℕ) : Prop :=
  (∀ y : ℕ → ℝ, ∀ i, i + 2 < m →
    pom_fiber_posterior_equivalence_single_candidate_test_value y i =
      Real.exp (y (i + 1) + y (i + 2) - y i)) ∧
    (∀ y₁ y₂ : ℕ → ℝ,
      (∀ i, i + 2 < m →
        pom_fiber_posterior_equivalence_single_candidate_test_value y₁ i =
          pom_fiber_posterior_equivalence_single_candidate_test_value y₂ i) ↔
        (∀ i, i + 2 < m →
          pom_fiber_posterior_equivalence_moduli_log_activity_map y₁ i =
            pom_fiber_posterior_equivalence_moduli_log_activity_map y₂ i)) ∧
    (∀ i₀, i₀ + 2 < m →
      ∃ y₁ y₂ : ℕ → ℝ,
        (∀ j, j + 2 < m → j ≠ i₀ →
          pom_fiber_posterior_equivalence_single_candidate_test_value y₁ j =
            pom_fiber_posterior_equivalence_single_candidate_test_value y₂ j) ∧
        pom_fiber_posterior_equivalence_single_candidate_test_value y₁ i₀ ≠
          pom_fiber_posterior_equivalence_single_candidate_test_value y₂ i₀)

/-- Paper label: `prop:pom-fiber-posterior-equivalence-single-candidate-test`. In log-activity
coordinates, the single-candidate fibers read the coordinates of the surjective map
`j ↦ y (j + 1) + y (j + 2) - y j`; exponentiating gives the odds readout. Hence the full
single-candidate family determines exactly the same data as the activity field, and omitting one
test leaves a coordinate that can still be changed independently. -/
theorem paper_pom_fiber_posterior_equivalence_single_candidate_test
    (m : ℕ) : pomFiberPosteriorEquivalenceSingleCandidateTestStatement m := by
  refine ⟨?_, ?_, ?_⟩
  · intro y i hi
    rfl
  · intro y₁ y₂
    constructor
    · intro h i hi
      exact Real.exp_injective <| by
        simpa [pom_fiber_posterior_equivalence_single_candidate_test_value] using h i hi
    · intro h i hi
      exact congrArg Real.exp <| by
        simpa [pom_fiber_posterior_equivalence_moduli_log_activity_map] using h i hi
  · intro i₀ hi₀
    let z₀ : ℕ → ℝ := fun _ => 0
    let z₁ : ℕ → ℝ := fun j => if j = i₀ then 1 else 0
    rcases (paper_pom_fiber_posterior_equivalence_moduli m).1 z₀ with ⟨y₀, hy₀⟩
    rcases (paper_pom_fiber_posterior_equivalence_moduli m).1 z₁ with ⟨y₁, hy₁⟩
    refine ⟨y₀, y₁, ?_, ?_⟩
    · intro j hj hjne
      have hz₀ : pom_fiber_posterior_equivalence_moduli_log_activity_map y₀ j = 0 := by
        simpa [z₀] using hy₀ j hj
      have hz₁ : pom_fiber_posterior_equivalence_moduli_log_activity_map y₁ j = 0 := by
        simpa [z₁, hjne] using hy₁ j hj
      simp [pom_fiber_posterior_equivalence_single_candidate_test_value, hz₀, hz₁]
    · have hz₀ : pom_fiber_posterior_equivalence_moduli_log_activity_map y₀ i₀ = 0 := by
        simpa [z₀] using hy₀ i₀ hi₀
      have hz₁ : pom_fiber_posterior_equivalence_moduli_log_activity_map y₁ i₀ = 1 := by
        simpa [z₁] using hy₁ i₀ hi₀
      have hexp : Real.exp (0 : ℝ) ≠ Real.exp 1 := by
        exact ne_of_lt <| Real.exp_strictMono (by norm_num : (0 : ℝ) < 1)
      simpa [pom_fiber_posterior_equivalence_single_candidate_test_value, hz₀, hz₁] using hexp

end

end Omega.POM
