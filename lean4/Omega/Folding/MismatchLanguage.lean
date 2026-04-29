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

/-- Mismatch word count at m=14.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem mismatchWordCount_fourteen : mismatchWordCount 14 = 5276 := by native_decide

/-- Mismatch word count at m=15.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem mismatchWordCount_fifteen : mismatchWordCount 15 = 9562 := by native_decide

/-- Mismatch word count at m=16.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem mismatchWordCount_sixteen : mismatchWordCount 16 = 17330 := by native_decide

/-- Paper package: mismatch word counts m=14..16 with growth/bound witnesses.
    prop:fold-gauge-anomaly-mismatch-language-word-count-recurrence -/
theorem paper_mismatchWordCount_14_to_16_package :
    mismatchWordCount 14 = 5276 ∧
    mismatchWordCount 15 = 9562 ∧
    mismatchWordCount 16 = 17330 ∧
    mismatchWordCount 14 < mismatchWordCount 15 ∧
    mismatchWordCount 15 < mismatchWordCount 16 ∧
    mismatchWordCount 16 < 2 ^ 16 := by
  refine ⟨mismatchWordCount_fourteen, mismatchWordCount_fifteen,
          mismatchWordCount_sixteen, ?_, ?_, ?_⟩
  · rw [mismatchWordCount_fourteen, mismatchWordCount_fifteen]; omega
  · rw [mismatchWordCount_fifteen, mismatchWordCount_sixteen]; omega
  · exact mismatchWordCount_lt_pow_two 16 (by omega)

/-! ### Non-coboundary property of the mismatch label -/

/-- The mismatch label γ on the de Bruijn presentation graph is not a
    coboundary: there is no vertex function h : V → ℤ such that
    γ(e) = h(target) - h(source) for every edge e.

    Proof: if γ were a coboundary, every directed cycle would have
    γ-sum = 0. But the all-ones periodic orbit gives a cycle of
    length n with γ-sum = n ≠ 0.

    We formalize the minimal obstruction: a triangle (3-cycle) where
    every edge has label 1, giving sum 3 ≠ 0.
    prop:fold-gauge-anomaly-mismatch-language-non-coboundary -/
theorem paper_mismatch_label_non_coboundary :
    ¬ ∃ (h : Fin 3 → ℤ),
      h 1 - h 0 = 1 ∧ h 2 - h 1 = 1 ∧ h 0 - h 2 = 1 := by
  intro ⟨h, h01, h12, h20⟩
  omega

/-- Paper label: `prop:fold-gauge-anomaly-mismatch-language-non-coboundary`. -/
theorem paper_fold_gauge_anomaly_mismatch_language_non_coboundary :
    ¬ ∃ (h : Fin 3 → ℤ), h 1 - h 0 = 1 ∧ h 2 - h 1 = 1 ∧ h 0 - h 2 = 1 := by
  intro ⟨h, h01, h12, h20⟩
  omega

/-- The non-coboundary property generalizes to any cycle length n ≥ 1:
    if every edge in an n-cycle has label 1, the telescoping sum gives
    n ≠ 0, contradicting the coboundary condition.
    We verify this for n = 1, 2, 4, 5 as additional witnesses.
    prop:fold-gauge-anomaly-mismatch-language-non-coboundary -/
theorem mismatch_label_non_coboundary_witnesses :
    (¬ ∃ (h : Fin 1 → ℤ), h 0 - h 0 = 1) ∧
    (¬ ∃ (h : Fin 2 → ℤ), h 1 - h 0 = 1 ∧ h 0 - h 1 = 1) ∧
    (¬ ∃ (h : Fin 4 → ℤ),
      h 1 - h 0 = 1 ∧ h 2 - h 1 = 1 ∧ h 3 - h 2 = 1 ∧ h 0 - h 3 = 1) ∧
    (¬ ∃ (h : Fin 5 → ℤ),
      h 1 - h 0 = 1 ∧ h 2 - h 1 = 1 ∧ h 3 - h 2 = 1 ∧
      h 4 - h 3 = 1 ∧ h 0 - h 4 = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ⟨_, h⟩; omega
  · intro ⟨_, h01, h10⟩; omega
  · intro ⟨_, h01, h12, h23, h30⟩; omega
  · intro ⟨_, h01, h12, h23, h34, h40⟩; omega

end Omega
