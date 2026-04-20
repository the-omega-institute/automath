import Mathlib.Tactic

namespace Omega.Folding

/-- Fiber-size histogram at the truncated support value `2`. -/
def foldTruncatedHistogram2 (m : Nat) : ℤ := (m : ℤ) + 2

/-- Fiber-size histogram at the truncated support value `3`. -/
def foldTruncatedHistogram3 (m : Nat) : ℤ := (m : ℤ) + 1

/-- Fiber-size histogram at the truncated support value `4`. -/
def foldTruncatedHistogram4 (m : Nat) : ℤ := m

/-- The truncated `q`-moment on the support `{2, 3, 4}`. -/
def foldTruncatedMoment (m q : Nat) : ℤ :=
  foldTruncatedHistogram2 m * (2 : ℤ) ^ q +
    foldTruncatedHistogram3 m * (3 : ℤ) ^ q +
    foldTruncatedHistogram4 m * (4 : ℤ) ^ q

/-- Vandermonde determinant for the support `{2, 3, 4}`. -/
def foldTruncatedMomentVandermondeDet : ℤ := ((3 : ℤ) - 2) * (4 - 2) * (4 - 3)

/-- The audited window-`6` histogram with counts `(8, 4, 9)`. -/
def auditedWindow6TruncatedMoment (q : Nat) : ℤ :=
  (8 : ℤ) * (2 : ℤ) ^ q + (4 : ℤ) * (3 : ℤ) ^ q + (9 : ℤ) * (4 : ℤ) ^ q

/-- The first three truncated moments determine the histogram on `{2, 3, 4}`, and the same
closed formulas recover the audited window-`6` histogram. -/
def foldTruncatedMomentCompleteInversionStatement (m : Nat) : Prop :=
  foldTruncatedMomentVandermondeDet = 2 ∧
    foldTruncatedMomentVandermondeDet ≠ 0 ∧
    (12 * foldTruncatedMoment m 0 - 7 * foldTruncatedMoment m 1 + foldTruncatedMoment m 2) / 2 =
      foldTruncatedHistogram2 m ∧
    -8 * foldTruncatedMoment m 0 + 6 * foldTruncatedMoment m 1 - foldTruncatedMoment m 2 =
      foldTruncatedHistogram3 m ∧
    (6 * foldTruncatedMoment m 0 - 5 * foldTruncatedMoment m 1 + foldTruncatedMoment m 2) / 2 =
      foldTruncatedHistogram4 m ∧
    (12 * auditedWindow6TruncatedMoment 0 - 7 * auditedWindow6TruncatedMoment 1 +
        auditedWindow6TruncatedMoment 2) / 2 = 8 ∧
    -8 * auditedWindow6TruncatedMoment 0 + 6 * auditedWindow6TruncatedMoment 1 -
        auditedWindow6TruncatedMoment 2 = 4 ∧
    (6 * auditedWindow6TruncatedMoment 0 - 5 * auditedWindow6TruncatedMoment 1 +
        auditedWindow6TruncatedMoment 2) / 2 = 9

private theorem foldTruncatedMoment_histogram2_numerator (m : Nat) :
    12 * foldTruncatedMoment m 0 - 7 * foldTruncatedMoment m 1 + foldTruncatedMoment m 2 =
      2 * foldTruncatedHistogram2 m := by
  simp [foldTruncatedMoment, foldTruncatedHistogram2, foldTruncatedHistogram3,
    foldTruncatedHistogram4]
  ring

private theorem foldTruncatedMoment_histogram3_formula (m : Nat) :
    -8 * foldTruncatedMoment m 0 + 6 * foldTruncatedMoment m 1 - foldTruncatedMoment m 2 =
      foldTruncatedHistogram3 m := by
  simp [foldTruncatedMoment, foldTruncatedHistogram2, foldTruncatedHistogram3,
    foldTruncatedHistogram4]
  ring

private theorem foldTruncatedMoment_histogram4_numerator (m : Nat) :
    6 * foldTruncatedMoment m 0 - 5 * foldTruncatedMoment m 1 + foldTruncatedMoment m 2 =
      2 * foldTruncatedHistogram4 m := by
  simp [foldTruncatedMoment, foldTruncatedHistogram2, foldTruncatedHistogram3,
    foldTruncatedHistogram4]
  ring

/-- The first three moment rows invert the histogram on `{2, 3, 4}`, and the same inverse
specializes to the window-`6` audit `(8, 4, 9)`.
    thm:fold-fiber-truncated-moment-complete-inversion -/
theorem paper_fold_fiber_truncated_moment_complete_inversion (m : Nat) :
    foldTruncatedMomentCompleteInversionStatement m := by
  refine ⟨by norm_num [foldTruncatedMomentVandermondeDet],
    by norm_num [foldTruncatedMomentVandermondeDet], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [foldTruncatedMoment_histogram2_numerator]
    have hdiv : (2 : ℤ) ∣ 2 * foldTruncatedHistogram2 m := dvd_mul_right _ _
    simpa using (Int.ediv_mul_cancel hdiv).symm
  · exact foldTruncatedMoment_histogram3_formula m
  · rw [foldTruncatedMoment_histogram4_numerator]
    have hdiv : (2 : ℤ) ∣ 2 * foldTruncatedHistogram4 m := dvd_mul_right _ _
    simpa using (Int.ediv_mul_cancel hdiv).symm
  · norm_num [auditedWindow6TruncatedMoment]
  · norm_num [auditedWindow6TruncatedMoment]
  · norm_num [auditedWindow6TruncatedMoment]

end Omega.Folding
