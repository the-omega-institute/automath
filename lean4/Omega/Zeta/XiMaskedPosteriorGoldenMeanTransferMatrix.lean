import Mathlib.Tactic

namespace Omega.Zeta

/-- One-step adjacency for the golden-mean shift, where `true` denotes bit `1`. -/
def xi_masked_posterior_golden_mean_transfer_matrix_step (a b : Bool) : ℕ :=
  if a && b then 0 else 1

/-- The length-`n` transfer count from boundary state `a` to boundary state `b`. -/
def xi_masked_posterior_golden_mean_transfer_matrix_transfer :
    ℕ → Bool → Bool → ℕ
  | 0, a, b => if a = b then 1 else 0
  | n + 1, a, b =>
      xi_masked_posterior_golden_mean_transfer_matrix_step a false *
          xi_masked_posterior_golden_mean_transfer_matrix_transfer n false b +
        xi_masked_posterior_golden_mean_transfer_matrix_step a true *
          xi_masked_posterior_golden_mean_transfer_matrix_transfer n true b

/-- Direct recursive count of legal completions of an `L`-site masked block. -/
def xi_masked_posterior_golden_mean_transfer_matrix_completion :
    ℕ → Bool → Bool → ℕ
  | 0, a, b => xi_masked_posterior_golden_mean_transfer_matrix_step a b
  | L + 1, a, b =>
      xi_masked_posterior_golden_mean_transfer_matrix_step a false *
          xi_masked_posterior_golden_mean_transfer_matrix_completion L false b +
        xi_masked_posterior_golden_mean_transfer_matrix_step a true *
          xi_masked_posterior_golden_mean_transfer_matrix_completion L true b

/-- Count of legal completions in which the queried position `j` is fixed to bit `1`. -/
def xi_masked_posterior_golden_mean_transfer_matrix_query_one
    (L j : ℕ) (a b : Bool) : ℕ :=
  xi_masked_posterior_golden_mean_transfer_matrix_completion (j - 1) a true *
    xi_masked_posterior_golden_mean_transfer_matrix_completion (L - j) true b

/-- Posterior marginal as a finite counting ratio. -/
noncomputable def xi_masked_posterior_golden_mean_transfer_matrix_posterior
    (L j : ℕ) (a b : Bool) : ℚ :=
  (xi_masked_posterior_golden_mean_transfer_matrix_query_one L j a b : ℚ) /
    (xi_masked_posterior_golden_mean_transfer_matrix_completion L a b : ℚ)

theorem xi_masked_posterior_golden_mean_transfer_matrix_completion_eq_transfer
    (L : ℕ) (a b : Bool) :
    xi_masked_posterior_golden_mean_transfer_matrix_completion L a b =
      xi_masked_posterior_golden_mean_transfer_matrix_transfer (L + 1) a b := by
  induction L generalizing a with
  | zero =>
      cases a <;> cases b <;>
        simp [xi_masked_posterior_golden_mean_transfer_matrix_completion,
          xi_masked_posterior_golden_mean_transfer_matrix_transfer,
          xi_masked_posterior_golden_mean_transfer_matrix_step]
  | succ L ih =>
      simp [xi_masked_posterior_golden_mean_transfer_matrix_completion,
        xi_masked_posterior_golden_mean_transfer_matrix_transfer, ih]

/-- Paper label: `thm:xi-masked-posterior-golden-mean-transfer-matrix`. -/
theorem paper_xi_masked_posterior_golden_mean_transfer_matrix
    (L j : ℕ) (a b : Bool) (hj_pos : 1 ≤ j) (hj_le : j ≤ L) :
    xi_masked_posterior_golden_mean_transfer_matrix_completion L a b =
        xi_masked_posterior_golden_mean_transfer_matrix_transfer (L + 1) a b ∧
      xi_masked_posterior_golden_mean_transfer_matrix_query_one L j a b =
        xi_masked_posterior_golden_mean_transfer_matrix_transfer j a true *
          xi_masked_posterior_golden_mean_transfer_matrix_transfer (L + 1 - j) true b ∧
      xi_masked_posterior_golden_mean_transfer_matrix_posterior L j a b =
        ((xi_masked_posterior_golden_mean_transfer_matrix_transfer j a true *
            xi_masked_posterior_golden_mean_transfer_matrix_transfer (L + 1 - j) true b :
            ℕ) : ℚ) /
          (xi_masked_posterior_golden_mean_transfer_matrix_transfer (L + 1) a b : ℚ) := by
  have h_completion :=
    xi_masked_posterior_golden_mean_transfer_matrix_completion_eq_transfer L a b
  have h_left : j - 1 + 1 = j := by omega
  have h_right : L - j + 1 = L + 1 - j := by omega
  have h_query :
      xi_masked_posterior_golden_mean_transfer_matrix_query_one L j a b =
        xi_masked_posterior_golden_mean_transfer_matrix_transfer j a true *
          xi_masked_posterior_golden_mean_transfer_matrix_transfer (L + 1 - j) true b := by
    simp [xi_masked_posterior_golden_mean_transfer_matrix_query_one,
      xi_masked_posterior_golden_mean_transfer_matrix_completion_eq_transfer, h_left, h_right]
  refine ⟨h_completion, h_query, ?_⟩
  simp [xi_masked_posterior_golden_mean_transfer_matrix_posterior, h_completion, h_query]

end Omega.Zeta
