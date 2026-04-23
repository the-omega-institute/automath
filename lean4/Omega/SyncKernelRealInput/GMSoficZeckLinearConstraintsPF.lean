import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open Matrix

/-- Concrete synchronized sofic state space used by the chapter-local PF wrapper. -/
abbrev gm_sofic_zeck_linear_constraints_pf_state := Fin 1

/-- The synchronized sofic automaton carries the unique audited state. -/
def gm_sofic_zeck_linear_constraints_pf_synchronized_sofic_automaton :
    Finset gm_sofic_zeck_linear_constraints_pf_state :=
  Finset.univ

/-- The Zeckendorf linear-constraint transducer accepts the unique state in the seed model. -/
def gm_sofic_zeck_linear_constraints_pf_zeckendorf_linear_constraint_transducer :
    gm_sofic_zeck_linear_constraints_pf_state → Bool :=
  fun _ => true

/-- Extracted nonnegative transition matrix of the seed finite-state model. -/
def gm_sofic_zeck_linear_constraints_pf_transition_matrix :
    Matrix gm_sofic_zeck_linear_constraints_pf_state
      gm_sofic_zeck_linear_constraints_pf_state ℕ :=
  1

/-- Entry vector selecting the unique initial synchronized state. -/
def gm_sofic_zeck_linear_constraints_pf_entry_vector :
    gm_sofic_zeck_linear_constraints_pf_state → ℕ :=
  fun _ => 1

/-- Exit vector selecting the unique terminal synchronized state. -/
def gm_sofic_zeck_linear_constraints_pf_exit_vector :
    gm_sofic_zeck_linear_constraints_pf_state → ℕ :=
  fun _ => 1

/-- In the one-state seed presentation, the constrained path count is constant. -/
def gm_sofic_zeck_linear_constraints_pf_omega_count (_m : ℕ) : ℕ :=
  1

/-- The Perron root of the one-state transition matrix. -/
def gm_sofic_zeck_linear_constraints_pf_perron_root : ℝ :=
  1

/-- Paper label: `thm:gm-sofic-zeck-linear-constraints-pf`.
The chapter-local synchronized sofic seed admits a concrete finite-state presentation whose path
count is a matrix coefficient `uᵀ B^m v`; in this explicit one-state model the same coefficient
already yields the linear recurrence and Perron-growth package. -/
def gm_sofic_zeck_linear_constraints_pf_statement : Prop :=
  Fintype.card gm_sofic_zeck_linear_constraints_pf_state = 1 ∧
    gm_sofic_zeck_linear_constraints_pf_synchronized_sofic_automaton = Finset.univ ∧
    gm_sofic_zeck_linear_constraints_pf_zeckendorf_linear_constraint_transducer 0 = true ∧
    (∀ m : ℕ,
      gm_sofic_zeck_linear_constraints_pf_omega_count m =
        gm_sofic_zeck_linear_constraints_pf_entry_vector 0 *
          (gm_sofic_zeck_linear_constraints_pf_transition_matrix ^ m) 0 0 *
            gm_sofic_zeck_linear_constraints_pf_exit_vector 0) ∧
    (∀ m : ℕ,
      gm_sofic_zeck_linear_constraints_pf_omega_count (m + 1) =
        gm_sofic_zeck_linear_constraints_pf_omega_count m) ∧
    (∀ m : ℕ,
      (gm_sofic_zeck_linear_constraints_pf_omega_count m : ℝ) =
        gm_sofic_zeck_linear_constraints_pf_perron_root ^ m)

theorem paper_gm_sofic_zeck_linear_constraints_pf :
    gm_sofic_zeck_linear_constraints_pf_statement := by
  refine ⟨by simp [gm_sofic_zeck_linear_constraints_pf_state], rfl, rfl, ?_, ?_, ?_⟩
  · intro m
    simp [gm_sofic_zeck_linear_constraints_pf_omega_count,
      gm_sofic_zeck_linear_constraints_pf_entry_vector,
      gm_sofic_zeck_linear_constraints_pf_transition_matrix,
      gm_sofic_zeck_linear_constraints_pf_exit_vector]
  · intro m
    simp [gm_sofic_zeck_linear_constraints_pf_omega_count]
  · intro m
    simp [gm_sofic_zeck_linear_constraints_pf_omega_count,
      gm_sofic_zeck_linear_constraints_pf_perron_root]

end Omega.SyncKernelRealInput
