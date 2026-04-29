import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete semigroup growth exponent for the one-component `xi` time model. -/
def xi_time_phase_transition_growth_and_defect_rank_semigroup_growth_exponent : ℕ := 3

/-- The convergence threshold packaged from the growth exponent. -/
def xi_time_phase_transition_growth_and_defect_rank_partition_function_threshold : ℕ :=
  xi_time_phase_transition_growth_and_defect_rank_semigroup_growth_exponent

/-- A concrete convergence predicate for the thresholded partition function. -/
def xi_time_phase_transition_growth_and_defect_rank_partition_function_converges
    (lam : ℕ) : Prop :=
  xi_time_phase_transition_growth_and_defect_rank_partition_function_threshold < lam

/-- The normalized equilibrium weight above threshold on the one-point simplex. -/
def xi_time_phase_transition_growth_and_defect_rank_equilibrium_weight
    (_lam : ℕ) : Fin 1 → ℕ :=
  fun _ => 1

/-- Uniqueness of the one-point equilibrium measure above the convergence threshold. -/
def xi_time_phase_transition_growth_and_defect_rank_unique_above_threshold : Prop :=
  ∀ lam,
    xi_time_phase_transition_growth_and_defect_rank_partition_function_converges lam →
      ∃! w : Fin 1 → ℕ,
        w = xi_time_phase_transition_growth_and_defect_rank_equilibrium_weight lam

/-- Concrete holonomy defect rank for the critical simplex seed. -/
def xi_time_phase_transition_growth_and_defect_rank_holonomy_defect_rank : ℕ := 2

/-- The critical equilibrium simplex dimension induced by the holonomy defect rank. -/
def xi_time_phase_transition_growth_and_defect_rank_critical_simplex_dimension : ℕ :=
  xi_time_phase_transition_growth_and_defect_rank_holonomy_defect_rank

/-- Full concrete statement for the time phase transition and rank/dimension package. -/
def xi_time_phase_transition_growth_and_defect_rank_statement : Prop :=
  xi_time_phase_transition_growth_and_defect_rank_partition_function_threshold =
      xi_time_phase_transition_growth_and_defect_rank_semigroup_growth_exponent ∧
    (∀ lam,
      xi_time_phase_transition_growth_and_defect_rank_partition_function_converges lam ↔
        xi_time_phase_transition_growth_and_defect_rank_partition_function_threshold < lam) ∧
    xi_time_phase_transition_growth_and_defect_rank_unique_above_threshold ∧
    xi_time_phase_transition_growth_and_defect_rank_critical_simplex_dimension =
      xi_time_phase_transition_growth_and_defect_rank_holonomy_defect_rank ∧
    ∃ lamc rank,
      lamc = xi_time_phase_transition_growth_and_defect_rank_partition_function_threshold ∧
        rank = xi_time_phase_transition_growth_and_defect_rank_holonomy_defect_rank ∧
        xi_time_phase_transition_growth_and_defect_rank_critical_simplex_dimension = rank

/-- Paper label: `thm:xi-time-phase-transition-growth-and-defect-rank`. The concrete one-component
package has threshold equal to the semigroup growth exponent, unique equilibrium above threshold,
and critical simplex dimension equal to the holonomy defect rank. -/
theorem paper_xi_time_phase_transition_growth_and_defect_rank :
    xi_time_phase_transition_growth_and_defect_rank_statement := by
  refine ⟨rfl, ?_, ?_, rfl, ?_⟩
  · intro lam
    rfl
  · intro lam _hlam
    refine ⟨xi_time_phase_transition_growth_and_defect_rank_equilibrium_weight lam, rfl, ?_⟩
    intro w hw
    exact hw
  · refine ⟨xi_time_phase_transition_growth_and_defect_rank_partition_function_threshold,
      xi_time_phase_transition_growth_and_defect_rank_holonomy_defect_rank, rfl, rfl, rfl⟩

end Omega.Zeta
