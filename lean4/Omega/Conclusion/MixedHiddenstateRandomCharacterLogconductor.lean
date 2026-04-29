import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-mixed-hiddenstate-random-character-logconductor`. -/
theorem paper_conclusion_mixed_hiddenstate_random_character_logconductor (p a : ℕ)
    (hp : 2 ≤ p) :
    (∑ j ∈ Finset.Icc 1 a, (j : ℝ) * ((p : ℝ) ^ j - (p : ℝ) ^ (j - 1))) /
        (p : ℝ) ^ a =
      (a : ℝ) - (((p : ℝ) ^ a - 1) / (((p : ℝ) - 1) * (p : ℝ) ^ a)) := by
  induction a with
  | zero =>
      norm_num
  | succ a ih =>
      have hp0 : (p : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
      have hp1 : (p : ℝ) ≠ 1 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 1 < 2) hp))
      have hpow_a : (p : ℝ) ^ a ≠ 0 := pow_ne_zero a hp0
      have hpow_succ : (p : ℝ) ^ (a + 1) ≠ 0 := pow_ne_zero (a + 1) hp0
      have hden_a : ((p : ℝ) - 1) * (p : ℝ) ^ a ≠ 0 := by
        exact mul_ne_zero (sub_ne_zero.mpr hp1) hpow_a
      have hden_succ : ((p : ℝ) - 1) * (p : ℝ) ^ (a + 1) ≠ 0 := by
        exact mul_ne_zero (sub_ne_zero.mpr hp1) hpow_succ
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ a + 1)]
      simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
      have hsum :
          (∑ j ∈ Finset.Icc 1 a, (j : ℝ) * ((p : ℝ) ^ j - (p : ℝ) ^ (j - 1))) =
            (p : ℝ) ^ a *
              ((a : ℝ) -
                (((p : ℝ) ^ a - 1) / (((p : ℝ) - 1) * (p : ℝ) ^ a))) := by
        rw [← ih]
        field_simp [hpow_a]
      rw [hsum]
      field_simp [hpow_a, hpow_succ, hden_a, hden_succ]
      field_simp [sub_ne_zero.mpr hp1]
      ring_nf

end Omega.Conclusion
