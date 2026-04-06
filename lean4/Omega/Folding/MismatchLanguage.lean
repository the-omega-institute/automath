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

/-- Mismatch language Perron root bound.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem paper_mismatch_perron_root_bound :
    (1 : ℤ)^5 - 1^4 - 1^3 - 1 - 1 = -3 ∧
    (2 : ℤ)^5 - 2^4 - 2^3 - 2 - 1 = 5 ∧
    (-3 : ℤ) < 0 ∧ (0 : ℤ) < 5 ∧
    mismatchWordCount 4 < 2 ^ 4 ∧
    mismatchWordCount 8 < 2 ^ 8 ∧
    mismatchWordCount 10 > Nat.fib 12 := by
  refine ⟨by omega, by omega, by omega, by omega,
    by native_decide, by native_decide, by native_decide⟩

-- ══════════════════════════════════════════════════════════════
-- Phase R307: mismatchWordCount extended + 2^m upper bound
-- ══════════════════════════════════════════════════════════════

/-- prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem mismatchWordCount_eleven : mismatchWordCount 11 = 886 := by native_decide

/-- prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem mismatchWordCount_twelve : mismatchWordCount 12 = 1606 := by native_decide

/-- prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem mismatchWordCount_thirteen : mismatchWordCount 13 = 2911 := by native_decide

/-- prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem mismatchWordCount_lt_pow_two (m : Nat) (hm : 4 ≤ m) :
    mismatchWordCount m < 2 ^ m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m, hm with
    | 4, _ => native_decide
    | 5, _ => native_decide
    | 6, _ => native_decide
    | 7, _ => native_decide
    | 8, _ => native_decide
    | m + 9, _ =>
      -- N(m+9) = N(m+8) + N(m+7) + N(m+5) + N(m+4)
      -- < 2^(m+8) + 2^(m+7) + 2^(m+5) + 2^(m+4)
      -- = 2^(m+4) * (16+8+2+1) = 27 * 2^(m+4) < 32 * 2^(m+4) = 2^(m+9)
      simp only [mismatchWordCount]
      have h8 := ih (m + 8) (by omega) (by omega)
      have h7 := ih (m + 7) (by omega) (by omega)
      have h5 := ih (m + 5) (by omega) (by omega)
      have h4 := ih (m + 4) (by omega) (by omega)
      calc mismatchWordCount (m + 8) + mismatchWordCount (m + 7) +
              mismatchWordCount (m + 5) + mismatchWordCount (m + 4)
          < 2 ^ (m + 8) + 2 ^ (m + 7) + 2 ^ (m + 5) + 2 ^ (m + 4) := by linarith
        _ = 27 * 2 ^ (m + 4) := by ring
        _ < 32 * 2 ^ (m + 4) := by nlinarith [Nat.one_le_pow (m + 4) 2 (by omega)]
        _ = 2 ^ (m + 9) := by ring

/-- Paper package. prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem paper_mismatchWordCount_extended :
    mismatchWordCount 11 = 886 ∧ mismatchWordCount 12 = 1606 ∧
    mismatchWordCount 13 = 2911 ∧
    (∀ m, 4 ≤ m → mismatchWordCount m < 2 ^ m) :=
  ⟨by native_decide, by native_decide, by native_decide, mismatchWordCount_lt_pow_two⟩

end Omega
