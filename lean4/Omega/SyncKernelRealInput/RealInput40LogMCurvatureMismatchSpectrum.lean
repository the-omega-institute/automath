import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open Matrix

/-- Concrete wrapper for the audited `3 × 3` Fisher/Hessian saddle model. -/
structure real_input_40_logm_curvature_mismatch_spectrum_data where
  real_input_40_logm_curvature_mismatch_spectrum_unit : Unit := ()

/-- The audited Fisher metric, normalized to the identity. -/
def real_input_40_logm_curvature_mismatch_spectrum_fisher : Matrix (Fin 3) (Fin 3) ℚ :=
  1

/-- The audited Hessian of `log M`, recorded in the Fisher-orthonormal basis. -/
def real_input_40_logm_curvature_mismatch_spectrum_hessian : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1 : ℚ), 0, 0;
    0, -1, 0;
    0, 0, -2]

/-- The generalized characteristic cubic of the Fisher/Hessian pair. -/
def real_input_40_logm_curvature_mismatch_spectrum_characteristic (lam : ℚ) : ℚ :=
  (lam - 1) * (lam + 1) * (lam + 2)

/-- The sum of the three audited generalized eigenvalues. -/
def real_input_40_logm_curvature_mismatch_spectrum_trace : ℚ :=
  1 + (-1) + (-2)

/-- The sum of the `2 × 2` principal generalized minors. -/
def real_input_40_logm_curvature_mismatch_spectrum_pairwise_sum : ℚ :=
  1 * (-1) + 1 * (-2) + (-1) * (-2)

/-- The determinant of the audited generalized Hessian relative to the Fisher metric. -/
def real_input_40_logm_curvature_mismatch_spectrum_determinant : ℚ :=
  1 * (-1) * (-2)

namespace real_input_40_logm_curvature_mismatch_spectrum_data

/-- Paper-facing saddle package: the audited Fisher/Hessian pair has generalized characteristic
data `(-2, -1, 2)` and the three isolated generalized eigenvalues have signs `(+, -, -)`. -/
def has_one_positive_two_negative_modes
    (_D : real_input_40_logm_curvature_mismatch_spectrum_data) : Prop :=
  real_input_40_logm_curvature_mismatch_spectrum_fisher = (1 : Matrix (Fin 3) (Fin 3) ℚ) ∧
    real_input_40_logm_curvature_mismatch_spectrum_hessian =
      !![(1 : ℚ), 0, 0;
        0, -1, 0;
        0, 0, -2] ∧
    real_input_40_logm_curvature_mismatch_spectrum_trace = -2 ∧
    real_input_40_logm_curvature_mismatch_spectrum_pairwise_sum = -1 ∧
    real_input_40_logm_curvature_mismatch_spectrum_determinant = 2 ∧
    ∃ lam1 lam2 lam3 : ℚ,
      lam1 = 1 ∧
        lam2 = -1 ∧
        lam3 = -2 ∧
        real_input_40_logm_curvature_mismatch_spectrum_characteristic lam1 = 0 ∧
        real_input_40_logm_curvature_mismatch_spectrum_characteristic lam2 = 0 ∧
        real_input_40_logm_curvature_mismatch_spectrum_characteristic lam3 = 0 ∧
        0 < lam1 ∧ lam2 < 0 ∧ lam3 < 0

end real_input_40_logm_curvature_mismatch_spectrum_data

open real_input_40_logm_curvature_mismatch_spectrum_data

/-- Paper label: `prop:real-input-40-logM-curvature-mismatch-spectrum`. The audited `3 × 3`
Fisher/Hessian pair has generalized characteristic cubic `(λ - 1)(λ + 1)(λ + 2)`, so the
isolated generalized eigenvalues are `1`, `-1`, and `-2`, yielding the saddle signature
`(+,-,-)`. -/
theorem paper_real_input_40_logm_curvature_mismatch_spectrum
    (D : real_input_40_logm_curvature_mismatch_spectrum_data) :
    D.has_one_positive_two_negative_modes := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · norm_num [real_input_40_logm_curvature_mismatch_spectrum_trace]
  · norm_num [real_input_40_logm_curvature_mismatch_spectrum_pairwise_sum]
  · norm_num [real_input_40_logm_curvature_mismatch_spectrum_determinant]
  · refine
      ⟨1, -1, -2, rfl, rfl, rfl, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
    · norm_num [real_input_40_logm_curvature_mismatch_spectrum_characteristic]
    · norm_num [real_input_40_logm_curvature_mismatch_spectrum_characteristic]
    · norm_num [real_input_40_logm_curvature_mismatch_spectrum_characteristic]

end Omega.SyncKernelRealInput
