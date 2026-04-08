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

/-- Even-length correction partial sum (integer form avoiding division).
    (v-1) · Σ_{k=1}^{n} E(v,2k) = 2·(v^{n+1} - v).
    cor:xi-time-part73c-fixed-parameter-necklace-correction -/
theorem evenLengthCorrection_partial_sum (v n : Nat) (hv : 2 ≤ v) :
    (v - 1) * ∑ k ∈ Finset.range n, evenLengthCorrection v (2 * (k + 1)) =
    2 * (v ^ (n + 1) - v) := by
  -- Unfold E(v, 2(k+1)) = 2·v^(k+1)
  simp_rw [evenLengthCorrection_even]
  -- Goal: (v-1) · Σ_{k=0}^{n-1} 2·v^(k+1) = 2·(v^{n+1} - v)
  -- = (v-1) · 2 · Σ_{k=0}^{n-1} v^(k+1) = 2(v-1) · v · Σ v^k
  -- Use geometric sum: (v-1) · Σ_{k=0}^{n-1} v^k = v^n - 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    -- Need: 2*(v^{n+1}-v) + (v-1)*(2*v^{n+1}) = 2*(v^{n+2}-v) in ℕ
    -- Lift to ℤ
    have hv1 : 1 ≤ v := by omega
    have hvn1 : v ≤ v ^ (n + 1) := Nat.le_self_pow (by omega) v
    have hvn2 : v ≤ v ^ (n + 2) := Nat.le_self_pow (by omega) v
    -- All subtractions are valid in ℕ
    zify [hvn1, hvn2, hv1]
    zify [hvn1] at ih
    have hpow : (v : ℤ) ^ (n + 1 + 1) = v * v ^ (n + 1) := by
      rw [pow_succ]; ring
    nlinarith

/-- E(v, 0) = 2.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
@[simp] theorem evenLengthCorrection_zero (v : Nat) :
    evenLengthCorrection v 0 = 2 := by
  simp [evenLengthCorrection]

/-- E(v, 2) = 2v.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
@[simp] theorem evenLengthCorrection_two (v : Nat) :
    evenLengthCorrection v 2 = 2 * v := by
  have := evenLengthCorrection_even v 1
  simpa using this

/-- Small-value table for E(v, n), n = 0..5.
    thm:xi-time-part73c-periodic-evenlength-atomic-correction -/
theorem paper_zeta_evenLength_small_values_table (v : Nat) :
    evenLengthCorrection v 0 = 2 ∧
    evenLengthCorrection v 1 = 0 ∧
    evenLengthCorrection v 2 = 2 * v ∧
    evenLengthCorrection v 3 = 0 ∧
    evenLengthCorrection v 4 = 2 * v ^ 2 ∧
    evenLengthCorrection v 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact evenLengthCorrection_zero v
  · exact evenLengthCorrection_odd v 1 (by decide)
  · exact evenLengthCorrection_two v
  · exact evenLengthCorrection_odd v 3 (by decide)
  · have := evenLengthCorrection_even v 2
    simpa using this
  · exact evenLengthCorrection_odd v 5 (by decide)

end Omega.Zeta
