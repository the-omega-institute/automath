import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

def xi_time_part9x_index_relative_entropy_identity_total_index_weight : ℕ :=
  8 * 2 + 4 * 3 + 9 * 4

def xi_time_part9x_index_relative_entropy_identity_kappa_6 : ℝ :=
  (11 / 8 : ℝ) * Real.log 2 + (3 / 16 : ℝ) * Real.log 3

def xi_time_part9x_index_relative_entropy_identity_index_log_expectation : ℝ :=
  ((8 : ℝ) * 2 * Real.log 2 + (4 : ℝ) * 3 * Real.log 3 +
      (9 : ℝ) * 4 * Real.log 4) / 64

def xi_time_part9x_index_relative_entropy_identity_kl_to_uniform : ℝ :=
  xi_time_part9x_index_relative_entropy_identity_index_log_expectation -
    Real.log ((64 : ℝ) / 21)

def xi_time_part9x_index_relative_entropy_identity_statement : Prop :=
  xi_time_part9x_index_relative_entropy_identity_total_index_weight = 64 ∧
    xi_time_part9x_index_relative_entropy_identity_index_log_expectation =
      xi_time_part9x_index_relative_entropy_identity_kappa_6 ∧
    xi_time_part9x_index_relative_entropy_identity_kl_to_uniform =
      xi_time_part9x_index_relative_entropy_identity_kappa_6 -
        Real.log ((64 : ℝ) / 21)

/-- Paper label: `thm:xi-time-part9x-index-relative-entropy-identity`. -/
theorem paper_xi_time_part9x_index_relative_entropy_identity :
    xi_time_part9x_index_relative_entropy_identity_statement := by
  have hindex :
      xi_time_part9x_index_relative_entropy_identity_index_log_expectation =
        xi_time_part9x_index_relative_entropy_identity_kappa_6 := by
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [xi_time_part9x_index_relative_entropy_identity_index_log_expectation,
      xi_time_part9x_index_relative_entropy_identity_kappa_6, hlog4]
    ring
  refine ⟨by native_decide, hindex, ?_⟩
  simpa [xi_time_part9x_index_relative_entropy_identity_kl_to_uniform] using
    congrArg (fun x => x - Real.log ((64 : ℝ) / 21)) hindex

end

end Omega.Zeta
