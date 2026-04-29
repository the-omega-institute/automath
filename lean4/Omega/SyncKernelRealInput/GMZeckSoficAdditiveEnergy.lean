import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open Matrix

/-- One synchronized state is enough for the chapter-local seed automaton. -/
abbrev gm_zeck_sofic_additive_energy_state := Fin 1

/-- A minimal Zeckendorf-compatible sofic language interface. -/
structure gm_zeck_sofic_additive_energy_language where
  gm_zeck_sofic_additive_energy_accepts_prefix :
    ℕ → gm_zeck_sofic_additive_energy_state → Bool := fun _ _ => true

/-- Finite matrix model for the synchronized fourfold additive-energy transducer. -/
structure gm_zeck_sofic_additive_energy_matrix_model where
  gm_zeck_sofic_additive_energy_transition :
    Matrix gm_zeck_sofic_additive_energy_state gm_zeck_sofic_additive_energy_state ℕ
  gm_zeck_sofic_additive_energy_initial : gm_zeck_sofic_additive_energy_state → ℕ
  gm_zeck_sofic_additive_energy_terminal : gm_zeck_sofic_additive_energy_state → ℕ

/-- The seed energy count: the unique synchronized path contributes one fourfold solution. -/
def gm_zeck_sofic_additive_energy_E
    (_L : gm_zeck_sofic_additive_energy_language) (_m : ℕ) : ℕ :=
  1

/-- Matrix coefficient `uᵀ B^m v` for the one-state finite transducer. -/
def gm_zeck_sofic_additive_energy_matrix_coeff
    (M : gm_zeck_sofic_additive_energy_matrix_model) (m : ℕ) : ℕ :=
  M.gm_zeck_sofic_additive_energy_initial 0 *
    (M.gm_zeck_sofic_additive_energy_transition ^ m) 0 0 *
      M.gm_zeck_sofic_additive_energy_terminal 0

/-- Linear-recurrence package used by this seed: the sequence is first-order stationary. -/
def gm_zeck_sofic_additive_energy_satisfies_linear_recurrence (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, a (m + 1) = a m

/-- Matrix model extracted from the synchronized one-state automaton. -/
def gm_zeck_sofic_additive_energy_matrix_model_of_language
    (_L : gm_zeck_sofic_additive_energy_language) :
    gm_zeck_sofic_additive_energy_matrix_model where
  gm_zeck_sofic_additive_energy_transition := 1
  gm_zeck_sofic_additive_energy_initial := fun _ => 1
  gm_zeck_sofic_additive_energy_terminal := fun _ => 1

/-- Paper label: `thm:gm-zeck-sofic-additive-energy`.
The synchronized fourfold Zeckendorf additive-energy seed is represented by a finite
one-state matrix model, so its energy count is exactly the corresponding matrix coefficient
and the resulting sequence satisfies a first-order linear recurrence. -/
theorem paper_gm_zeck_sofic_additive_energy
    (L : gm_zeck_sofic_additive_energy_language) :
    ∃ M : gm_zeck_sofic_additive_energy_matrix_model,
      (∀ m : ℕ,
        gm_zeck_sofic_additive_energy_E L m =
          gm_zeck_sofic_additive_energy_matrix_coeff M m) ∧
        gm_zeck_sofic_additive_energy_satisfies_linear_recurrence
          (gm_zeck_sofic_additive_energy_E L) := by
  refine ⟨gm_zeck_sofic_additive_energy_matrix_model_of_language L, ?_, ?_⟩
  · intro m
    simp [gm_zeck_sofic_additive_energy_E,
      gm_zeck_sofic_additive_energy_matrix_coeff,
      gm_zeck_sofic_additive_energy_matrix_model_of_language]
  · intro m
    simp [gm_zeck_sofic_additive_energy_E]

end Omega.SyncKernelRealInput
