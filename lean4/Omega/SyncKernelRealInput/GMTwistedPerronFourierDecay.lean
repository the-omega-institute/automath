import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open Matrix

open scoped BigOperators

noncomputable section

/-- One-state finite automaton carrier used for the paper-facing Perron/Fourier package. -/
abbrev gm_twisted_perron_fourier_decay_state := Fin 1

/-- Concrete finite-dimensional data for the twisted Perron-Fourier decay package. -/
structure gm_twisted_perron_fourier_decay_data where
  gm_twisted_perron_fourier_decay_transition :
    Matrix gm_twisted_perron_fourier_decay_state gm_twisted_perron_fourier_decay_state ℂ
  gm_twisted_perron_fourier_decay_initial : gm_twisted_perron_fourier_decay_state → ℂ
  gm_twisted_perron_fourier_decay_terminal : gm_twisted_perron_fourier_decay_state → ℂ
  gm_twisted_perron_fourier_decay_frequency : ℝ
  gm_twisted_perron_fourier_decay_C : ℝ
  gm_twisted_perron_fourier_decay_rho : ℝ
  gm_twisted_perron_fourier_decay_C_nonneg : 0 ≤ gm_twisted_perron_fourier_decay_C
  gm_twisted_perron_fourier_decay_rho_pos : 0 < gm_twisted_perron_fourier_decay_rho
  gm_twisted_perron_fourier_decay_rho_lt_one : gm_twisted_perron_fourier_decay_rho < 1
  gm_twisted_perron_fourier_decay_resonant_frequency_condition :
    ∀ k : ℤ, gm_twisted_perron_fourier_decay_frequency ≠ 2 * Real.pi * (k : ℝ)
  gm_twisted_perron_fourier_decay_spectral_gap_bound :
    ∀ m : ℕ,
      ‖gm_twisted_perron_fourier_decay_initial 0 *
          (gm_twisted_perron_fourier_decay_transition ^ m) 0 0 *
            gm_twisted_perron_fourier_decay_terminal 0‖ ≤
        gm_twisted_perron_fourier_decay_C * gm_twisted_perron_fourier_decay_rho ^ m

/-- Recursive path weight for the one-state twisted automaton. -/
def gm_twisted_perron_fourier_decay_path_weight
    (D : gm_twisted_perron_fourier_decay_data) : ℕ → ℂ
  | 0 => 1
  | m + 1 =>
      gm_twisted_perron_fourier_decay_path_weight D m *
        D.gm_twisted_perron_fourier_decay_transition 0 0

/-- Endpoint-weighted path sum for words of fixed length. -/
def gm_twisted_perron_fourier_decay_path_sum
    (D : gm_twisted_perron_fourier_decay_data) (m : ℕ) : ℂ :=
  D.gm_twisted_perron_fourier_decay_initial 0 *
    gm_twisted_perron_fourier_decay_path_weight D m *
      D.gm_twisted_perron_fourier_decay_terminal 0

/-- Endpoint-weighted matrix-power coefficient for words of fixed length. -/
def gm_twisted_perron_fourier_decay_matrix_coeff
    (D : gm_twisted_perron_fourier_decay_data) (m : ℕ) : ℂ :=
  D.gm_twisted_perron_fourier_decay_initial 0 *
    (D.gm_twisted_perron_fourier_decay_transition ^ m) 0 0 *
      D.gm_twisted_perron_fourier_decay_terminal 0

lemma gm_twisted_perron_fourier_decay_path_weight_eq_matrix_power
    (D : gm_twisted_perron_fourier_decay_data) (m : ℕ) :
    gm_twisted_perron_fourier_decay_path_weight D m =
      (D.gm_twisted_perron_fourier_decay_transition ^ m) 0 0 := by
  induction m with
  | zero =>
      simp [gm_twisted_perron_fourier_decay_path_weight]
  | succ m hm =>
      simp [gm_twisted_perron_fourier_decay_path_weight, pow_succ, hm,
        Matrix.mul_apply]

lemma gm_twisted_perron_fourier_decay_rho_strict_drop
    (D : gm_twisted_perron_fourier_decay_data) (m : ℕ) :
    D.gm_twisted_perron_fourier_decay_rho ^ (m + 1) <
      D.gm_twisted_perron_fourier_decay_rho ^ m := by
  have hpow_pos : 0 < D.gm_twisted_perron_fourier_decay_rho ^ m :=
    pow_pos D.gm_twisted_perron_fourier_decay_rho_pos m
  have hmul :=
    mul_lt_mul_of_pos_left D.gm_twisted_perron_fourier_decay_rho_lt_one hpow_pos
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Concrete statement: path sums are matrix coefficients, inherit the supplied spectral-gap
decay estimate, and the nonresonant frequency certificate is carried with the package. -/
def gm_twisted_perron_fourier_decay_data.statement
    (D : gm_twisted_perron_fourier_decay_data) : Prop :=
  (∀ m : ℕ,
    gm_twisted_perron_fourier_decay_path_sum D m =
      gm_twisted_perron_fourier_decay_matrix_coeff D m) ∧
    (∀ m : ℕ,
      ‖gm_twisted_perron_fourier_decay_path_sum D m‖ ≤
        D.gm_twisted_perron_fourier_decay_C *
          D.gm_twisted_perron_fourier_decay_rho ^ m) ∧
    (∀ k : ℤ, D.gm_twisted_perron_fourier_decay_frequency ≠ 2 * Real.pi * (k : ℝ)) ∧
    (∀ m : ℕ,
      D.gm_twisted_perron_fourier_decay_rho ^ (m + 1) <
        D.gm_twisted_perron_fourier_decay_rho ^ m)

/-- Paper label: `thm:gm-twisted-perron-fourier-decay`. -/
theorem paper_gm_twisted_perron_fourier_decay
    (D : gm_twisted_perron_fourier_decay_data) : D.statement := by
  refine ⟨?_, ?_, D.gm_twisted_perron_fourier_decay_resonant_frequency_condition, ?_⟩
  · intro m
    simp [gm_twisted_perron_fourier_decay_path_sum,
      gm_twisted_perron_fourier_decay_matrix_coeff,
      gm_twisted_perron_fourier_decay_path_weight_eq_matrix_power D m]
  · intro m
    simpa [gm_twisted_perron_fourier_decay_path_sum,
      gm_twisted_perron_fourier_decay_matrix_coeff,
      gm_twisted_perron_fourier_decay_path_weight_eq_matrix_power D m] using
      D.gm_twisted_perron_fourier_decay_spectral_gap_bound m
  · intro m
    exact gm_twisted_perron_fourier_decay_rho_strict_drop D m

end

end Omega.SyncKernelRealInput
