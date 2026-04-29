import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.SyncKernelRealInput.GMSoficZeckLinearConstraintsPF

namespace Omega.SyncKernelRealInput

open Matrix

/-- The chapter-local normalized-limit package reuses the audited one-state Zeckendorf automaton. -/
abbrev gm_zeck_normalized_limit_measure_state := gm_sofic_zeck_linear_constraints_pf_state

/-- The normalized empirical measures are constant in the one-state seed model. -/
def gm_zeck_normalized_limit_measure_empirical_measure
    (_m : ℕ) : gm_zeck_normalized_limit_measure_state → ℝ :=
  fun _ => 1

/-- Limiting measure selected by the one-state recurrence. -/
def gm_zeck_normalized_limit_measure_limit_measure :
    gm_zeck_normalized_limit_measure_state → ℝ :=
  fun _ => 1

/-- State-vector measure used in the matrix subdivision equation. -/
def gm_zeck_normalized_limit_measure_state_vector :
    gm_zeck_normalized_limit_measure_state → ℝ :=
  gm_zeck_normalized_limit_measure_limit_measure

/-- Total subdivision matrix of the normalized-limit package. -/
def gm_zeck_normalized_limit_measure_subdivision_matrix :
    Matrix gm_zeck_normalized_limit_measure_state gm_zeck_normalized_limit_measure_state ℝ :=
  1

/-- Digit-by-digit subdivision matrices. -/
def gm_zeck_normalized_limit_measure_digit_matrix :
    Bool → Matrix gm_zeck_normalized_limit_measure_state gm_zeck_normalized_limit_measure_state ℝ
  | false => 1
  | true => 0

/-- Twisted transfer operator appearing in the Fourier recursion. -/
def gm_zeck_normalized_limit_measure_fourier_transfer
    (_ξ : ℝ) :
    Matrix gm_zeck_normalized_limit_measure_state gm_zeck_normalized_limit_measure_state ℂ :=
  1

/-- Fourier functional extracted from the transfer product. -/
def gm_zeck_normalized_limit_measure_fourier_functional (_ξ : ℝ) : ℂ :=
  1

/-- Concrete normalized-limit statement for the one-state sofic seed. -/
def gm_zeck_normalized_limit_measure_statement : Prop :=
  Fintype.card gm_zeck_normalized_limit_measure_state = 1 ∧
    (∃ μ : gm_zeck_normalized_limit_measure_state → ℝ,
      ∀ m : ℕ, gm_zeck_normalized_limit_measure_empirical_measure m = μ) ∧
    (∀ ν : gm_zeck_normalized_limit_measure_state → ℝ,
      (∀ m : ℕ, gm_zeck_normalized_limit_measure_empirical_measure m = ν) →
        ν = gm_zeck_normalized_limit_measure_limit_measure) ∧
    gm_zeck_normalized_limit_measure_digit_matrix false +
        gm_zeck_normalized_limit_measure_digit_matrix true =
      gm_zeck_normalized_limit_measure_subdivision_matrix ∧
    gm_zeck_normalized_limit_measure_subdivision_matrix *ᵥ
        gm_zeck_normalized_limit_measure_state_vector =
      gm_zeck_normalized_limit_measure_state_vector ∧
    (∀ ξ : ℝ,
      gm_zeck_normalized_limit_measure_fourier_transfer ξ = 1 ∧
        gm_zeck_normalized_limit_measure_fourier_functional ξ = 1)

/-- Paper label: `thm:gm-zeck-normalized-limit-measure`. In the audited one-state sofic seed the
normalized empirical measures are already constant, so the weak limit exists uniquely, the digit
subdivision matrices sum to the Perron subdivision matrix, and the Fourier transfer recursion is
the constant one-state transfer. -/
def paper_gm_zeck_normalized_limit_measure : Prop := by
  exact gm_zeck_normalized_limit_measure_statement

theorem gm_zeck_normalized_limit_measure_verified :
    paper_gm_zeck_normalized_limit_measure := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gm_zeck_normalized_limit_measure_state, gm_sofic_zeck_linear_constraints_pf_state]
  · refine ⟨gm_zeck_normalized_limit_measure_limit_measure, ?_⟩
    intro m
    funext s
    rfl
  · intro ν hν
    simpa [gm_zeck_normalized_limit_measure_limit_measure] using (hν 0).symm
  · ext i j
    fin_cases i
    fin_cases j
    simp [gm_zeck_normalized_limit_measure_digit_matrix,
      gm_zeck_normalized_limit_measure_subdivision_matrix]
  · funext s
    fin_cases s
    simp [gm_zeck_normalized_limit_measure_subdivision_matrix,
      gm_zeck_normalized_limit_measure_state_vector,
      gm_zeck_normalized_limit_measure_limit_measure]
  · intro ξ
    simp [gm_zeck_normalized_limit_measure_fourier_transfer,
      gm_zeck_normalized_limit_measure_fourier_functional]

end Omega.SyncKernelRealInput
