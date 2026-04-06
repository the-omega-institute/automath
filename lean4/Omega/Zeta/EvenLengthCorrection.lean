import Mathlib.Tactic

namespace Omega.Zeta

def evenLengthCorrection (v n : Nat) : Nat :=
  if Even n then 2 * v ^ (n / 2) else 0

/-- Odd lengths contribute no even-length atomic correction.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem evenLengthCorrection_odd (v n : Nat) (hn : ¬ Even n) :
    evenLengthCorrection v n = 0 := by
  simp [evenLengthCorrection, hn]

/-- Even lengths contribute the half-length monomial term.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem evenLengthCorrection_even (v m : Nat) :
    evenLengthCorrection v (2 * m) = 2 * v ^ m := by
  simp [evenLengthCorrection]

/-- Case split form of the even-length correction.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem evenLengthCorrection_cases (v n : Nat) :
    evenLengthCorrection v n =
      if Even n then 2 * v ^ (n / 2) else 0 := by
  rfl

/-- The even-length correction vanishes exactly at odd lengths when `v` is positive.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem evenLengthCorrection_eq_zero_iff
    {v n : Nat} (hv : 0 < v) :
    evenLengthCorrection v n = 0 ↔ ¬ Even n := by
  by_cases hn : Even n
  · constructor
    · intro hzero
      exfalso
      rcases hn with ⟨m, hm⟩
      rw [hm, show m + m = 2 * m by omega] at hzero
      rw [evenLengthCorrection_even] at hzero
      have hpos : 0 < 2 * v ^ m := by
        exact Nat.mul_pos (by decide) (pow_pos hv _)
      exact (Nat.ne_of_gt hpos) hzero
    · intro hnot
      exact (hnot hn).elim
  · constructor
    · intro _
      exact hn
    · intro _
      exact evenLengthCorrection_odd v n hn

/-- For positive `v`, the even-length correction is positive exactly at even lengths.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem evenLengthCorrection_pos_iff
    {v n : Nat} (hv : 0 < v) :
    0 < evenLengthCorrection v n ↔ Even n := by
  constructor
  · intro hpos
    by_contra hn
    have hzero : evenLengthCorrection v n = 0 := evenLengthCorrection_odd v n hn
    simp [hzero] at hpos
  · intro hn
    rcases hn with ⟨m, hm⟩
    rw [hm, show m + m = 2 * m by omega, evenLengthCorrection_even]
    exact Nat.mul_pos (by decide) (pow_pos hv _)

/-- Even-length correction combined audit.
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem paper_zeta_evenLength_correction_package :
    (∀ v n : Nat, ¬ Even n → evenLengthCorrection v n = 0) ∧
    (∀ v m : Nat, evenLengthCorrection v (2 * m) = 2 * v ^ m) ∧
    (∀ m : Nat, 0 < evenLengthCorrection 2 (2 * (m + 1))) := by
  refine ⟨evenLengthCorrection_odd, evenLengthCorrection_even, ?_⟩
  intro m; rw [evenLengthCorrection_even]; positivity

end Omega.Zeta
