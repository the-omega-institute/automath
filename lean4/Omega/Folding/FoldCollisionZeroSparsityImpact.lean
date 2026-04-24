import Mathlib
import Omega.Core.Fib
import Omega.Folding.FoldZeroDensitySparse

namespace Omega.Folding

private lemma fib_half_ratio_denominator_bound (m : ℕ) :
    Nat.fib ((m + 2) / 2) * Nat.fib (((m + 2) / 2) + 1) ≤ Nat.fib (m + 2) := by
  let h := (m + 2) / 2
  have hmod : (m + 2) % 2 = 0 ∨ (m + 2) % 2 = 1 := Nat.mod_two_eq_zero_or_one (m + 2)
  rcases hmod with h0 | h1
  · have hn : m + 2 = 2 * h := by
      dsimp [h]
      omega
    calc
      Nat.fib h * Nat.fib (h + 1) ≤ Nat.fib h * (2 * Nat.fib (h + 1) - Nat.fib h) := by
        gcongr
        have hmono : Nat.fib h ≤ Nat.fib (h + 1) := Nat.fib_mono (Nat.le_succ h)
        omega
      _ = Nat.fib (2 * h) := by rw [Omega.fib_double]
      _ = Nat.fib (m + 2) := by simp [hn]
  · have hn : m + 2 = 2 * h + 1 := by
      dsimp [h]
      omega
    calc
      Nat.fib h * Nat.fib (h + 1) ≤ Nat.fib (h + 1) * Nat.fib (h + 1) := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right (Nat.fib (h + 1))
          (Nat.fib_mono (Nat.le_succ h))
      _ = Nat.fib (h + 1) ^ 2 := by rw [pow_two]
      _ ≤ Nat.fib (h + 1) ^ 2 + Nat.fib h ^ 2 := Nat.le_add_right _ _
      _ = Nat.fib h ^ 2 + Nat.fib (h + 1) ^ 2 := by rw [Nat.add_comm]
      _ = Nat.fib (2 * h + 1) := Omega.fib_sq_add_sq h
      _ = Nat.fib (m + 2) := by simp [hn]

/-- Paper label: `cor:fold-collision-zero-sparsity-impact`.

The sparse zero-density bound becomes a relative bound after dividing by `M = F_{m+2}`. The
Fibonacci doubling formulas show that the core ratio `F_{⌊(m+2)/2⌋} / F_{m+2}` is bounded by the
reciprocal `1 / F_{⌊(m+2)/2⌋+1}`, so the zero-set correction is exponentially small on the
Fibonacci scale. -/
theorem paper_fold_collision_zero_sparsity_impact (m : ℕ) (hM : Even (Nat.fib (m + 2))) :
    let M := Nat.fib (m + 2)
    let h := (m + 2) / 2
    let Z := foldZeroFrequencyUnion m
    (Z.card : ℚ) / M ≤ ((((m + 2).divisors.card * Nat.fib h : ℕ) : ℚ) / M) ∧
      (Z.card : ℚ) / M ≤ (((m + 2).divisors.card : ℕ) : ℚ) / Nat.fib (h + 1) := by
  dsimp
  have hsparse := (paper_fold_zero_density_sparse m hM).2
  have hratioNat :
      Nat.fib ((m + 2) / 2) * Nat.fib (((m + 2) / 2) + 1) ≤ Nat.fib (m + 2) :=
    fib_half_ratio_denominator_bound m
  have hMPos : 0 < Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
  have hHalfPos : 0 < Nat.fib (((m + 2) / 2) + 1) := Nat.fib_pos.mpr (by omega)
  have hMPosQ : (0 : ℚ) < Nat.fib (m + 2) := by
    exact_mod_cast hMPos
  have hHalfPosQ : (0 : ℚ) < Nat.fib (((m + 2) / 2) + 1) := by
    exact_mod_cast hHalfPos
  have hratioCast :
      ((Nat.fib ((m + 2) / 2) : ℚ) * Nat.fib (((m + 2) / 2) + 1)) ≤ Nat.fib (m + 2) := by
    exact_mod_cast hratioNat
  have hratio :
      ((Nat.fib ((m + 2) / 2) : ℚ) / Nat.fib (m + 2)) ≤
        1 / Nat.fib (((m + 2) / 2) + 1) := by
    have hleft :
        ((Nat.fib ((m + 2) / 2) : ℚ) / Nat.fib (m + 2)) =
          (((Nat.fib ((m + 2) / 2) : ℚ) * Nat.fib (((m + 2) / 2) + 1)) /
            ((Nat.fib (m + 2) : ℚ) * Nat.fib (((m + 2) / 2) + 1))) := by
      field_simp [hMPosQ.ne', hHalfPosQ.ne']
    have hright :
        (1 : ℚ) / Nat.fib (((m + 2) / 2) + 1) =
          (Nat.fib (m + 2) : ℚ) /
            ((Nat.fib (m + 2) : ℚ) * Nat.fib (((m + 2) / 2) + 1)) := by
      field_simp [hMPosQ.ne', hHalfPosQ.ne']
    rw [hleft, hright]
    exact div_le_div_of_nonneg_right hratioCast (by positivity)
  have hscaled :
      (((((m + 2).divisors.card : ℕ) : ℚ) * ((Nat.fib ((m + 2) / 2) : ℚ) / Nat.fib (m + 2))) ≤
        (((m + 2).divisors.card : ℕ) : ℚ) * (1 / Nat.fib (((m + 2) / 2) + 1))) := by
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  constructor
  · exact hsparse
  · calc
      ((foldZeroFrequencyUnion m).card : ℚ) / Nat.fib (m + 2) ≤
          (((m + 2).divisors.card * Nat.fib ((m + 2) / 2) : ℕ) : ℚ) / Nat.fib (m + 2) := hsparse
      _ = (((m + 2).divisors.card : ℕ) : ℚ) *
            ((Nat.fib ((m + 2) / 2) : ℚ) / Nat.fib (m + 2)) := by
          rw [Nat.cast_mul]
          field_simp [hMPosQ.ne']
      _ ≤ (((m + 2).divisors.card : ℕ) : ℚ) * (1 / Nat.fib (((m + 2) / 2) + 1)) := hscaled
      _ = (((m + 2).divisors.card : ℕ) : ℚ) / Nat.fib (((m + 2) / 2) + 1) := by
          field_simp [hHalfPosQ.ne']

end Omega.Folding
