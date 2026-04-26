import Omega.Folding.MismatchLanguage
import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing recurrence package for the mismatch-language word counts.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem paper_fold_gauge_anomaly_mismatch_language_word_count_recurrence :
    (∀ n : ℕ,
      Omega.mismatchWordCount (n + 5) =
        Omega.mismatchWordCount (n + 4) + Omega.mismatchWordCount (n + 3) +
          Omega.mismatchWordCount (n + 1) + Omega.mismatchWordCount n) ∧
      Omega.mismatchWordCount 1 = 2 ∧
      Omega.mismatchWordCount 2 = 4 ∧
      Omega.mismatchWordCount 3 = 8 ∧
      Omega.mismatchWordCount 4 = 14 ∧
      Omega.mismatchWordCount 5 = 25 ∧
      (∀ n : ℕ, Omega.mismatchWordCount n < Omega.mismatchWordCount (n + 1)) ∧
      (∀ n : ℕ, 4 ≤ n → Omega.mismatchWordCount n < 2 ^ n) ∧
      ((1 : ℤ)^5 - 1^4 - 1^3 - 1 - 1 = -3) ∧
      ((2 : ℤ)^5 - 2^4 - 2^3 - 2 - 1 = 5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · exact (Omega.paper_mismatch_word_count_initial_values.1)
  · exact (Omega.paper_mismatch_word_count_initial_values.2.1)
  · exact (Omega.paper_mismatch_word_count_initial_values.2.2.1)
  · exact (Omega.paper_mismatch_word_count_initial_values.2.2.2.1)
  · exact (Omega.paper_mismatch_word_count_initial_values.2.2.2.2.1)
  · exact Omega.paper_mismatch_word_count_strict_mono.1
  · exact Omega.mismatchWordCount_lt_pow_two
  · exact Omega.paper_mismatch_perron_root_bound.1
  · exact Omega.paper_mismatch_perron_root_bound.2.1

end Omega.Folding
