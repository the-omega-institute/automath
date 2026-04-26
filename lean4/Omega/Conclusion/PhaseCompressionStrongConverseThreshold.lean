import Mathlib.Tactic
import Omega.Conclusion.CdimPhaseCompressionBitLowerBound

namespace Omega.Conclusion

/-- Concrete data for the strong-converse threshold package. A stage `m` carries a dyadic budget
`b_m`; any uniquely decodable stage must satisfy the unavoidable bit lower bound coming from the
phase-collision scale. A chosen subsequence is declared subcritical when its budgets stay strictly
below the threshold slope. -/
structure conclusion_phase_compression_strong_converse_threshold_data where
  conclusion_phase_compression_strong_converse_threshold_core :
    conclusion_cdim_phase_compression_power_law_data
  conclusion_phase_compression_strong_converse_threshold_dyadicBudget : ℕ → ℝ
  conclusion_phase_compression_strong_converse_threshold_uniqueDecoding : ℕ → Prop
  conclusion_phase_compression_strong_converse_threshold_subseq : ℕ → ℕ
  conclusion_phase_compression_strong_converse_threshold_dyadicResolutionBound :
    ∀ m,
      conclusion_phase_compression_strong_converse_threshold_uniqueDecoding m →
        conclusion_cdim_phase_compression_bit_lower_bound_bits
            conclusion_phase_compression_strong_converse_threshold_core ≤
          conclusion_phase_compression_strong_converse_threshold_dyadicBudget m
  conclusion_phase_compression_strong_converse_threshold_belowSlope :
    ∀ k,
      conclusion_phase_compression_strong_converse_threshold_dyadicBudget
          (conclusion_phase_compression_strong_converse_threshold_subseq k) <
        ((conclusion_phase_compression_strong_converse_threshold_core.r : ℝ) /
            conclusion_phase_compression_strong_converse_threshold_core.d) *
          Real.logb 2 (conclusion_phase_compression_strong_converse_threshold_core.N + 1) - 1

/-- The explicit dyadic threshold slope forced by the finite-box phase-collision theorem. -/
noncomputable def conclusion_phase_compression_strong_converse_threshold_threshold
    (D : conclusion_phase_compression_strong_converse_threshold_data) : ℝ :=
  ((D.conclusion_phase_compression_strong_converse_threshold_core.r : ℝ) /
      D.conclusion_phase_compression_strong_converse_threshold_core.d) *
    Real.logb 2 (D.conclusion_phase_compression_strong_converse_threshold_core.N + 1) - 1

/-- Any uniquely decodable stage must stay above the dyadic threshold. -/
def conclusion_phase_compression_strong_converse_threshold_data.threshold_lower_bound
    (D : conclusion_phase_compression_strong_converse_threshold_data) : Prop :=
  ∀ m,
    D.conclusion_phase_compression_strong_converse_threshold_uniqueDecoding m →
      conclusion_phase_compression_strong_converse_threshold_threshold D ≤
        D.conclusion_phase_compression_strong_converse_threshold_dyadicBudget m

/-- Along the chosen subcritical subsequence, unique decoding necessarily fails. -/
def conclusion_phase_compression_strong_converse_threshold_data.subsequence_failure
    (D : conclusion_phase_compression_strong_converse_threshold_data) : Prop :=
  ∀ k,
    ¬ D.conclusion_phase_compression_strong_converse_threshold_uniqueDecoding
        (D.conclusion_phase_compression_strong_converse_threshold_subseq k)

theorem paper_conclusion_phase_compression_strong_converse_threshold
    (D : conclusion_phase_compression_strong_converse_threshold_data) :
    D.threshold_lower_bound ∧ D.subsequence_failure := by
  have hbit :=
    paper_conclusion_cdim_phase_compression_bit_lower_bound
      D.conclusion_phase_compression_strong_converse_threshold_core
  refine ⟨?_, ?_⟩
  · intro m hm
    simpa [conclusion_phase_compression_strong_converse_threshold_threshold, hbit.2] using
      D.conclusion_phase_compression_strong_converse_threshold_dyadicResolutionBound m hm
  · intro k hk
    have hlow :
        conclusion_phase_compression_strong_converse_threshold_threshold D ≤
          D.conclusion_phase_compression_strong_converse_threshold_dyadicBudget
            (D.conclusion_phase_compression_strong_converse_threshold_subseq k) := by
      simpa [conclusion_phase_compression_strong_converse_threshold_threshold, hbit.2] using
        D.conclusion_phase_compression_strong_converse_threshold_dyadicResolutionBound
          (D.conclusion_phase_compression_strong_converse_threshold_subseq k) hk
    exact not_lt_of_ge hlow
      (D.conclusion_phase_compression_strong_converse_threshold_belowSlope k)

end Omega.Conclusion
