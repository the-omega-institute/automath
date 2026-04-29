import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite Schur-channel data for the variance/support lower-bound statement. -/
structure xi_time_part63_schur_variance_forcing_support_lower_bound_data where
  channels : Finset ℕ
  amplitude : ℕ → ℝ
  variance : ℝ
  maxChannelCount : ℕ
  maxSquareBound : ℝ
  variance_eq_sum_sq : variance = channels.sum (fun lam => amplitude lam ^ 2)
  channel_count_le : channels.card ≤ maxChannelCount
  maxSquareBound_nonneg : 0 ≤ maxSquareBound
  maxSquareBound_spec : ∀ lam, lam ∈ channels → amplitude lam ^ 2 ≤ maxSquareBound

/-- The active nontrivial Schur channels are exactly the channels with nonzero amplitude. -/
def xi_time_part63_schur_variance_forcing_support_lower_bound_active
    (D : xi_time_part63_schur_variance_forcing_support_lower_bound_data) : Finset ℕ :=
  D.channels.filter fun lam => D.amplitude lam ≠ 0

/-- Paper-facing finite variance/support lower-bound package. -/
def xi_time_part63_schur_variance_forcing_support_lower_bound_statement
    (D : xi_time_part63_schur_variance_forcing_support_lower_bound_data) : Prop :=
  let A := xi_time_part63_schur_variance_forcing_support_lower_bound_active D
  (D.variance = 0 ↔ A = ∅) ∧
    (0 < D.variance →
      A.Nonempty ∧
        D.variance ≤ (D.maxChannelCount : ℝ) * D.maxSquareBound ∧
          D.variance ≤ (A.card : ℝ) * D.maxSquareBound)

private lemma xi_time_part63_schur_variance_forcing_support_lower_bound_sum_active
    (D : xi_time_part63_schur_variance_forcing_support_lower_bound_data) :
    D.channels.sum (fun lam => D.amplitude lam ^ 2) =
      (xi_time_part63_schur_variance_forcing_support_lower_bound_active D).sum
        (fun lam => D.amplitude lam ^ 2) := by
  classical
  rw [xi_time_part63_schur_variance_forcing_support_lower_bound_active]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro lam hlam
  by_cases hlam_ne : D.amplitude lam ≠ 0
  · simp [hlam_ne]
  · have hlam_zero : D.amplitude lam = 0 := by
      exact not_not.mp hlam_ne
    simp [hlam_zero]

/-- Paper label: `thm:xi-time-part63-schur-variance-forcing-support-lower-bound`. -/
theorem paper_xi_time_part63_schur_variance_forcing_support_lower_bound
    (D : xi_time_part63_schur_variance_forcing_support_lower_bound_data) :
    xi_time_part63_schur_variance_forcing_support_lower_bound_statement D := by
  classical
  let A := xi_time_part63_schur_variance_forcing_support_lower_bound_active D
  have hsumA :
      D.channels.sum (fun lam => D.amplitude lam ^ 2) =
        A.sum (fun lam => D.amplitude lam ^ 2) :=
    xi_time_part63_schur_variance_forcing_support_lower_bound_sum_active D
  have hvarA : D.variance = A.sum (fun lam => D.amplitude lam ^ 2) := by
    rw [D.variance_eq_sum_sq, hsumA]
  have hzero_iff : D.variance = 0 ↔ A = ∅ := by
    constructor
    · intro hvar_zero
      by_contra hA_ne
      obtain ⟨lam, hlamA⟩ := Finset.nonempty_iff_ne_empty.mpr hA_ne
      have hterm_zero :
          D.amplitude lam ^ 2 = 0 := by
        have hsum_zero : A.sum (fun lam => D.amplitude lam ^ 2) = 0 := by
          rw [← hvarA, hvar_zero]
        exact
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun i _ => sq_nonneg (D.amplitude i))).mp hsum_zero lam hlamA
      have hlam_ne : D.amplitude lam ≠ 0 := by
        have hlam_pair : lam ∈ D.channels ∧ D.amplitude lam ≠ 0 := by
          simpa [A, xi_time_part63_schur_variance_forcing_support_lower_bound_active]
            using hlamA
        exact hlam_pair.2
      exact hlam_ne (sq_eq_zero_iff.mp hterm_zero)
    · intro hA_empty
      rw [hvarA, hA_empty]
      simp
  refine ⟨hzero_iff, ?_⟩
  intro hvar_pos
  have hA_nonempty : A.Nonempty := by
    by_contra hnot
    have hA_empty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hvar_zero : D.variance = 0 := hzero_iff.mpr hA_empty
    linarith
  have hchannels_bound :
      D.variance ≤ (D.maxChannelCount : ℝ) * D.maxSquareBound := by
    have hsum_le :
        D.channels.sum (fun lam => D.amplitude lam ^ 2) ≤
          D.channels.sum (fun _lam => D.maxSquareBound) := by
      exact Finset.sum_le_sum fun lam hlam => D.maxSquareBound_spec lam hlam
    calc
      D.variance = D.channels.sum (fun lam => D.amplitude lam ^ 2) := D.variance_eq_sum_sq
      _ ≤ D.channels.sum (fun _lam => D.maxSquareBound) := hsum_le
      _ = (D.channels.card : ℝ) * D.maxSquareBound := by simp [nsmul_eq_mul]
      _ ≤ (D.maxChannelCount : ℝ) * D.maxSquareBound := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast D.channel_count_le)
          D.maxSquareBound_nonneg
  have hactive_bound :
      D.variance ≤ (A.card : ℝ) * D.maxSquareBound := by
    have hsum_le :
        A.sum (fun lam => D.amplitude lam ^ 2) ≤
          A.sum (fun _lam => D.maxSquareBound) := by
      exact Finset.sum_le_sum fun lam hlam =>
        D.maxSquareBound_spec lam
          (by
            have hlam_pair : lam ∈ D.channels ∧ D.amplitude lam ≠ 0 := by
              simpa [A, xi_time_part63_schur_variance_forcing_support_lower_bound_active]
                using hlam
            exact hlam_pair.1)
    calc
      D.variance = A.sum (fun lam => D.amplitude lam ^ 2) := hvarA
      _ ≤ A.sum (fun _lam => D.maxSquareBound) := hsum_le
      _ = (A.card : ℝ) * D.maxSquareBound := by simp [nsmul_eq_mul]
  exact ⟨hA_nonempty, hchannels_bound, hactive_bound⟩

end

end Omega.Zeta
