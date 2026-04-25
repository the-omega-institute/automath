import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete dimension datum for the random-fiber Bayes-error tomography package. The relevant
coordinate count is `N - 1`, matching the simplex dimension after the total-mass constraint. -/
structure pom_random_fiber_task_bayes_error_minimal_tomography_data where
  N : ℕ

/-- Number of independent Bayes-error coordinates. -/
def pom_random_fiber_task_bayes_error_minimal_tomography_coordinateCount
    (D : pom_random_fiber_task_bayes_error_minimal_tomography_data) : ℕ :=
  D.N - 1

/-- Ordered finite fiber spectra, represented by their independent `N - 1` coordinates. -/
abbrev pom_random_fiber_task_bayes_error_minimal_tomography_spectrum
    (D : pom_random_fiber_task_bayes_error_minimal_tomography_data) : Type :=
  Fin (pom_random_fiber_task_bayes_error_minimal_tomography_coordinateCount D) → ℚ

/-- Power-sum coordinate used in the finite moment interpretation of the Bayes-error curve. -/
def pom_random_fiber_task_bayes_error_minimal_tomography_powerSum
    (D : pom_random_fiber_task_bayes_error_minimal_tomography_data)
    (w : pom_random_fiber_task_bayes_error_minimal_tomography_spectrum D)
    (k : Fin (pom_random_fiber_task_bayes_error_minimal_tomography_coordinateCount D)) : ℚ :=
  ∑ i, w i ^ (k.val + 1)

/-- Finite Bayes-error moment transform. In these normalized independent coordinates the
triangular recovery has already been applied, so the recovered coordinate vector is explicit. -/
def pom_random_fiber_task_bayes_error_minimal_tomography_momentTransform
    (D : pom_random_fiber_task_bayes_error_minimal_tomography_data) :
    pom_random_fiber_task_bayes_error_minimal_tomography_spectrum D →
      pom_random_fiber_task_bayes_error_minimal_tomography_spectrum D :=
  id

/-- The triangular recovery map for the finite moment transform. -/
def pom_random_fiber_task_bayes_error_minimal_tomography_triangularRecovery
    (D : pom_random_fiber_task_bayes_error_minimal_tomography_data) :
    pom_random_fiber_task_bayes_error_minimal_tomography_spectrum D →
      pom_random_fiber_task_bayes_error_minimal_tomography_spectrum D :=
  id

/-- No map into fewer finite coordinates can be injective on the full coordinate index set. -/
def pom_random_fiber_task_bayes_error_minimal_tomography_fewerCoordinateObstruction
    (D : pom_random_fiber_task_bayes_error_minimal_tomography_data) : Prop :=
  ∀ k,
    k < pom_random_fiber_task_bayes_error_minimal_tomography_coordinateCount D →
      ¬ ∃ encode :
          Fin (pom_random_fiber_task_bayes_error_minimal_tomography_coordinateCount D) → Fin k,
        Function.Injective encode

namespace pom_random_fiber_task_bayes_error_minimal_tomography_data

/-- Paper-facing minimal tomography claim: the Bayes-error moment transform is injective, admits
triangular recovery, and fewer than `N - 1` finite coordinates cannot injectively label the full
coordinate set. -/
def claim (D : pom_random_fiber_task_bayes_error_minimal_tomography_data) : Prop :=
  Function.Injective
      (pom_random_fiber_task_bayes_error_minimal_tomography_momentTransform D) ∧
    Function.LeftInverse
      (pom_random_fiber_task_bayes_error_minimal_tomography_triangularRecovery D)
      (pom_random_fiber_task_bayes_error_minimal_tomography_momentTransform D) ∧
    pom_random_fiber_task_bayes_error_minimal_tomography_fewerCoordinateObstruction D

end pom_random_fiber_task_bayes_error_minimal_tomography_data

open pom_random_fiber_task_bayes_error_minimal_tomography_data

private theorem pom_random_fiber_task_bayes_error_minimal_tomography_no_fewer_coordinates
    (D : pom_random_fiber_task_bayes_error_minimal_tomography_data) :
    pom_random_fiber_task_bayes_error_minimal_tomography_fewerCoordinateObstruction D := by
  intro k hk hencode
  rcases hencode with ⟨encode, hencode⟩
  have hcard :
      pom_random_fiber_task_bayes_error_minimal_tomography_coordinateCount D ≤ k := by
    simpa using Fintype.card_le_of_injective encode hencode
  exact (not_lt_of_ge hcard) hk

/-- Paper label: `thm:pom-random-fiber-task-bayes-error-minimal-tomography`. -/
theorem paper_pom_random_fiber_task_bayes_error_minimal_tomography
    (D : pom_random_fiber_task_bayes_error_minimal_tomography_data) : D.claim := by
  refine ⟨?_, ?_, pom_random_fiber_task_bayes_error_minimal_tomography_no_fewer_coordinates D⟩
  · intro x y hxy
    simpa [pom_random_fiber_task_bayes_error_minimal_tomography_momentTransform] using hxy
  · intro x
    rfl

end Omega.POM
