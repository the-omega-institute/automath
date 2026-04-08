import Mathlib.Tactic

namespace Omega.SPG

/-- Discrete Tanaka increment. thm:spg-scan-tanaka-stokes -/
noncomputable def tanakaIncrement (x y a : ℚ) : ℚ :=
  |y - a| - |x - a| - (if x - a > 0 then 1 else if x - a < 0 then -1 else 0) * (y - x)

/-- The Tanaka increment is non-negative. thm:spg-scan-tanaka-stokes -/
theorem tanakaIncrement_nonneg (x y a : ℚ) : 0 ≤ tanakaIncrement x y a := by
  unfold tanakaIncrement
  by_cases hpos : x - a > 0
  · simp only [hpos, ↓reduceIte, one_mul]
    have hxa : |x - a| = x - a := abs_of_pos hpos
    rw [hxa]
    linarith [abs_nonneg (y - a), le_abs_self (y - a)]
  · by_cases hneg : x - a < 0
    · simp only [show ¬(x - a > 0) from hpos, hneg, ↓reduceIte, neg_one_mul]
      have hxa : |x - a| = -(x - a) := abs_of_neg hneg
      rw [hxa]
      linarith [abs_nonneg (y - a), neg_abs_le (y - a)]
    · have hzero : x - a = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
      simp only [show ¬(x - a > 0) from hpos, show ¬(x - a < 0) from hneg, ↓reduceIte, zero_mul,
        sub_zero]
      have hxa : |x - a| = 0 := by rw [abs_eq_zero]; linarith
      rw [hxa]
      simp [abs_nonneg]

/-- Discrete local time (sum of Tanaka increments) is non-negative.
    thm:spg-scan-tanaka-stokes -/
theorem tanakaLocalTime_nonneg (seq : ℕ → ℚ) (a : ℚ) (m : ℕ) :
    0 ≤ ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) a :=
  Finset.sum_nonneg (fun k _ => tanakaIncrement_nonneg (seq k) (seq (k + 1)) a)

/-- Discrete local time is monotone non-decreasing in m.
    thm:spg-scan-tanaka-stokes -/
theorem tanakaLocalTime_mono (seq : ℕ → ℚ) (a : ℚ) (m : ℕ) :
    ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) a ≤
    ∑ k ∈ Finset.range (m + 1), tanakaIncrement (seq k) (seq (k + 1)) a := by
  rw [Finset.sum_range_succ]
  linarith [tanakaIncrement_nonneg (seq m) (seq (m + 1)) a]

/-- Single-step Tanaka identity: |y-a| = |x-a| + sgn(x-a)·(y-x) + tI(x,y,a).
    thm:spg-scan-tanaka-stokes -/
private theorem tanakaIncrement_identity (x y a : ℚ) :
    |y - a| = |x - a| +
      (if x - a > 0 then 1 else if x - a < 0 then -1 else 0) * (y - x) +
      tanakaIncrement x y a := by
  unfold tanakaIncrement; ring

/-- Discrete Tanaka decomposition: |seq(m) - a| = |seq(0) - a| + signed_sum + local_time.
    thm:spg-scan-tanaka-stokes -/
theorem tanakaDecomposition (seq : ℕ → ℚ) (a : ℚ) (m : ℕ) :
    |seq m - a| = |seq 0 - a| +
      ∑ k ∈ Finset.range m,
        (if seq k - a > 0 then 1 else if seq k - a < 0 then -1 else 0) * (seq (k + 1) - seq k) +
      ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have := tanakaIncrement_identity (seq m) (seq (m + 1)) a
    linarith

/-- Complete Tanaka-Stokes package: items (1)-(4) of thm:spg-scan-tanaka-stokes.
    thm:spg-scan-tanaka-stokes -/
theorem paper_spg_tanaka_stokes_complete :
    (∀ (x y a : ℚ), 0 ≤ tanakaIncrement x y a) ∧
    (∀ (seq : ℕ → ℚ) (a : ℚ) (m : ℕ),
      0 ≤ ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) a) ∧
    (∀ (seq : ℕ → ℚ) (a : ℚ) (m : ℕ),
      ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) a ≤
      ∑ k ∈ Finset.range (m + 1), tanakaIncrement (seq k) (seq (k + 1)) a) ∧
    (∀ (seq : ℕ → ℚ) (a : ℚ) (m : ℕ),
      |seq m - a| = |seq 0 - a| +
        ∑ k ∈ Finset.range m,
          (if seq k - a > 0 then 1 else if seq k - a < 0 then -1 else 0) *
            (seq (k + 1) - seq k) +
        ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) a) :=
  ⟨tanakaIncrement_nonneg, tanakaLocalTime_nonneg, tanakaLocalTime_mono, tanakaDecomposition⟩

/-- Self-increment of Tanaka is zero: tI(x,x,a) = 0.
    thm:spg-scan-tanaka-stokes -/
theorem tanakaIncrement_self (x a : ℚ) :
    tanakaIncrement x x a = 0 := by
  unfold tanakaIncrement
  simp

/-- Tanaka increment at origin: tI(a,y,a) = |y - a|.
    thm:spg-scan-tanaka-stokes -/
theorem tanakaIncrement_at_a_eq_x (a y : ℚ) :
    tanakaIncrement a y a = |y - a| := by
  unfold tanakaIncrement
  simp

/-- Constant-sequence Tanaka local time vanishes.
    thm:spg-scan-tanaka-stokes -/
theorem tanakaLocalTime_constant_seq (c a : ℚ) (m : ℕ) :
    ∑ _k ∈ Finset.range m, tanakaIncrement c c a = 0 := by
  apply Finset.sum_eq_zero
  intros _k _
  exact tanakaIncrement_self c a

/-- Paper-facing Tanaka increment degeneracy package.
    thm:spg-scan-tanaka-stokes -/
theorem paper_tanakaIncrement_degenerate_package :
    (∀ x a : ℚ, tanakaIncrement x x a = 0) ∧
    (∀ a y : ℚ, tanakaIncrement a y a = |y - a|) ∧
    (∀ c a : ℚ, ∀ m : ℕ,
      ∑ _k ∈ Finset.range m, tanakaIncrement c c a = 0) :=
  ⟨tanakaIncrement_self,
   tanakaIncrement_at_a_eq_x,
   tanakaLocalTime_constant_seq⟩

end Omega.SPG
