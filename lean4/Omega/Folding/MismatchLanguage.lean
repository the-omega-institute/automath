import Mathlib.Tactic

/-!
# Mismatch Language Word Count

The mismatch language word count N(m) satisfies a linear recurrence
N(m+5) = N(m+4) + N(m+3) + N(m+1) + N(m) with initial values
N(0)=1, N(1)=2, N(2)=4, N(3)=8, N(4)=14.
-/

namespace Omega

/-- Mismatch language word count: number of words of length m in the mismatch language.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
def mismatchWordCount : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 14
  | (n + 5) => mismatchWordCount (n + 4) + mismatchWordCount (n + 3) +
                mismatchWordCount (n + 1) + mismatchWordCount n

/-- Mismatch language word count initial values and recurrence verification.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem paper_mismatch_word_count_initial_values :
    mismatchWordCount 1 = 2 ∧ mismatchWordCount 2 = 4 ∧
    mismatchWordCount 3 = 8 ∧ mismatchWordCount 4 = 14 ∧
    mismatchWordCount 5 = 25 ∧ mismatchWordCount 6 = 45 ∧
    mismatchWordCount 7 = 82 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem mismatchWordCount_pos (m : ℕ) : 0 < mismatchWordCount m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 | 2 | 3 | 4 => simp [mismatchWordCount]
    | m + 5 =>
      simp only [mismatchWordCount]
      have := ih (m + 4) (by omega)
      have := ih (m + 3) (by omega)
      have := ih (m + 1) (by omega)
      have := ih m (by omega)
      omega

/-- Mismatch language word count is strictly monotone increasing.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem paper_mismatch_word_count_strict_mono :
    (∀ m : ℕ, mismatchWordCount m < mismatchWordCount (m + 1)) ∧
    mismatchWordCount 8 = 149 ∧
    mismatchWordCount 9 = 270 ∧
    mismatchWordCount 10 = 489 := by
  refine ⟨fun m => ?_, by native_decide, by native_decide, by native_decide⟩
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 | 1 | 2 | 3 => simp [mismatchWordCount]
    | m + 4 =>
      -- mwc(m+5) = mwc(m+4) + mwc(m+3) + mwc(m+1) + mwc(m) > mwc(m+4)
      show mismatchWordCount (m + 4) < mismatchWordCount (m + 5)
      simp only [mismatchWordCount]
      have := mismatchWordCount_pos (m + 3)
      have := mismatchWordCount_pos (m + 1)
      have := mismatchWordCount_pos m
      omega

end Omega
