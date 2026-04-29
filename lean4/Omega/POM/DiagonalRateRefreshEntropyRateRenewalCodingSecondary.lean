import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshEntropyRateRenewalCoding

namespace Omega.POM

noncomputable section

/-- Block entropy of `n` IID regeneration blocks. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_block_entropy (n : ℕ) : ℝ :=
  n * pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy

/-- Renewal-count proxy `N_m ≈ m / E[H]` used in the path-level entropy bookkeeping. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_renewal_count (m : ℕ) : ℝ :=
  m / pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length

/-- Path entropy obtained by expanding the path into the corresponding number of IID regeneration
blocks. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_path_entropy (m : ℕ) : ℝ :=
  pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_renewal_count m *
    pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy

/-- The corresponding entropy per time step. -/
def pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_path_entropy_per_step
    (m : ℕ) : ℝ :=
  pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_path_entropy m / m

private lemma pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_expected_length_pos :
    0 < pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length := by
  norm_num [pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length,
    pom_diagonal_rate_refresh_entropy_rate_renewal_coding_pi_delta,
    pom_diagonal_rate_refresh_entropy_rate_renewal_coding_r_delta]

/-- Paper label: `prop:pom-diagonal-rate-refresh-entropy-rate-renewal-coding-secondary`.
Reusing the chapter-local renewal-coding theorem, the block entropy is additive on IID
regeneration blocks and the path entropy per time step is therefore the block entropy divided by
the expected block length. -/
theorem paper_pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary :
    pom_diagonal_rate_refresh_renewal_coding_statement
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_witness ∧
      (∀ n : ℕ,
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_block_entropy n =
          n * pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy) ∧
      (∀ m : ℕ,
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_path_entropy m =
          pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_renewal_count m *
            pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy) ∧
      (∀ m : ℕ,
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_path_entropy_per_step
            (m + 1) =
          pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy /
            pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length) ∧
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_entropy_rate =
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_joint_entropy /
          pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length := by
  refine ⟨paper_pom_diagonal_rate_refresh_renewal_coding
      pom_diagonal_rate_refresh_entropy_rate_renewal_coding_witness, ?_, ?_, ?_, rfl⟩
  · intro n
    rfl
  · intro m
    rfl
  · intro m
    have hlen :
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_expected_length ≠ 0 :=
      ne_of_gt
        pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_expected_length_pos
    have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    unfold pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_path_entropy_per_step
    unfold pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_path_entropy
    unfold pom_diagonal_rate_refresh_entropy_rate_renewal_coding_secondary_renewal_count
    field_simp [hlen, hm]

end

end Omega.POM
