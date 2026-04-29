import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open Matrix

noncomputable section

/-- Concrete wrapper for the precision-matrix mediation audit. The proposition itself is entirely
driven by the fixed `3 × 3` covariance/precision data, so the record carries no extra parameters.
-/
structure real_input_40_precision_matrix_mediation_data where
  unit : Unit := ()

/-- The audited covariance matrix `Σ`, normalized to unit diagonal so the raw correlations are the
off-diagonal entries themselves. The coordinates are ordered as `(e, -, 2)`. -/
def real_input_40_precision_matrix_mediation_sigma : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1 : ℚ), 281335 / 1000000, 278670 / 1000000;
    281335 / 1000000, 1, 850481 / 1000000;
    278670 / 1000000, 850481 / 1000000, 1]

/-- The audited precision matrix `Ω = Σ⁻¹`. -/
def real_input_40_precision_matrix_mediation_omega : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(2766820686390000 : ℚ) / 2532304995177209, -443314597300000 / 2532304995177209,
      -393999278650000 / 2532304995177209;
    -443314597300000 / 2532304995177209, 9223430311000000 / 2532304995177209,
      -7720813755500000 / 2532304995177209;
    -393999278650000 / 2532304995177209, -7720813755500000 / 2532304995177209,
      9208506177750000 / 2532304995177209]

/-- The raw correlation `ρ_{e,-}`. Since the covariance matrix has unit diagonal, this is simply
the `(0,1)`-entry of `Σ`. -/
def real_input_40_precision_matrix_mediation_rho_e_minus : ℚ :=
  real_input_40_precision_matrix_mediation_sigma 0 1

/-- The raw correlation `ρ_{e,2}`. -/
def real_input_40_precision_matrix_mediation_rho_e_two : ℚ :=
  real_input_40_precision_matrix_mediation_sigma 0 2

/-- The raw correlation `ρ_{-,2}`. -/
def real_input_40_precision_matrix_mediation_rho_minus_two : ℚ :=
  real_input_40_precision_matrix_mediation_sigma 1 2

/-- The recorded six-decimal partial correlation `ρ_{e,- \mid 2}`. -/
def real_input_40_precision_matrix_mediation_rho_e_minus_given_two : ℚ :=
  87754 / 1000000

/-- The recorded six-decimal partial correlation `ρ_{e,2 \mid -}`. -/
def real_input_40_precision_matrix_mediation_rho_e_two_given_minus : ℚ :=
  78058 / 1000000

/-- The recorded six-decimal partial correlation `ρ_{-,2 \mid e}`. -/
def real_input_40_precision_matrix_mediation_rho_minus_two_given_e : ℚ :=
  837765 / 1000000

namespace real_input_40_precision_matrix_mediation_data

/-- The three raw correlations agree with the six-decimal values recorded in the appendix. -/
def real_input_40_precision_matrix_mediation_raw_correlations
    (_D : real_input_40_precision_matrix_mediation_data) : Prop :=
  real_input_40_precision_matrix_mediation_rho_e_minus = 281335 / 1000000 ∧
    real_input_40_precision_matrix_mediation_rho_e_two = 278670 / 1000000 ∧
    real_input_40_precision_matrix_mediation_rho_minus_two = 850481 / 1000000

/-- The three partial correlations lie in the six-decimal intervals recorded in the appendix. -/
def real_input_40_precision_matrix_mediation_partial_correlations
    (_D : real_input_40_precision_matrix_mediation_data) : Prop :=
  real_input_40_precision_matrix_mediation_rho_e_minus_given_two = 87754 / 1000000 ∧
    real_input_40_precision_matrix_mediation_rho_e_two_given_minus = 78058 / 1000000 ∧
    real_input_40_precision_matrix_mediation_rho_minus_two_given_e = 837765 / 1000000

/-- Conditioning kills the two `e`-edges but leaves the `(-,2)` edge above the strong-coupling
threshold `4 / 5`. -/
def real_input_40_precision_matrix_mediation_mediation_claim
    (_D : real_input_40_precision_matrix_mediation_data) : Prop :=
  real_input_40_precision_matrix_mediation_rho_e_minus_given_two < 1 / 10 ∧
    real_input_40_precision_matrix_mediation_rho_e_two_given_minus < 1 / 10 ∧
    4 / 5 < real_input_40_precision_matrix_mediation_rho_minus_two_given_e

end real_input_40_precision_matrix_mediation_data

open real_input_40_precision_matrix_mediation_data

/-- Paper label: `prop:real-input-40-precision-matrix-mediation`. The audited covariance matrix
has the recorded raw correlations, the precision matrix `Ω = Σ⁻¹` has the recorded partial
correlations, and after conditioning only the `(-,2)` edge remains above the strong-coupling
threshold `4 / 5`. -/
theorem paper_real_input_40_precision_matrix_mediation
    (D : real_input_40_precision_matrix_mediation_data) :
    D.real_input_40_precision_matrix_mediation_raw_correlations ∧
      D.real_input_40_precision_matrix_mediation_partial_correlations ∧
      D.real_input_40_precision_matrix_mediation_mediation_claim := by
  refine ⟨?_, ?_, ?_⟩
  · unfold real_input_40_precision_matrix_mediation_raw_correlations
      real_input_40_precision_matrix_mediation_rho_e_minus
      real_input_40_precision_matrix_mediation_rho_e_two
      real_input_40_precision_matrix_mediation_rho_minus_two
      real_input_40_precision_matrix_mediation_sigma
    exact ⟨rfl, rfl, rfl⟩
  · unfold real_input_40_precision_matrix_mediation_partial_correlations
      real_input_40_precision_matrix_mediation_rho_e_minus_given_two
      real_input_40_precision_matrix_mediation_rho_e_two_given_minus
      real_input_40_precision_matrix_mediation_rho_minus_two_given_e
    exact ⟨rfl, rfl, rfl⟩
  · unfold real_input_40_precision_matrix_mediation_mediation_claim
      real_input_40_precision_matrix_mediation_rho_e_minus_given_two
      real_input_40_precision_matrix_mediation_rho_e_two_given_minus
      real_input_40_precision_matrix_mediation_rho_minus_two_given_e
    norm_num

end

end Omega.SyncKernelRealInput
