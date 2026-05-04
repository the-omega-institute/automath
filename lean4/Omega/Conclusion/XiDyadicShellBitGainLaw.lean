import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-xi-dyadic-shell-bit-gain-law`. -/
theorem paper_conclusion_xi_dyadic_shell_bit_gain_law
    (E B : ℕ → ℝ) (hEpos : ∀ K, 0 < E K)
    (hB : ∀ K, B K = - Real.log (E K) / Real.log 2)
    (hRatio :
      ∀ K,
        E (K + 1) / E K =
          (2 : ℝ) ^ (-(3 / 4 : ℝ)) *
            Real.exp (-Real.pi * ((2 ^ K : ℕ) : ℝ))) :
    ∀ K, B (K + 1) - B K =
      (Real.pi / Real.log 2) * ((2 ^ K : ℕ) : ℝ) + 3 / 4 := by
  intro K
  have hlog2_ne : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hE_ne : E K ≠ 0 := (hEpos K).ne'
  have hE_succ_ne : E (K + 1) ≠ 0 := (hEpos (K + 1)).ne'
  have hpow_ne : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(3 / 4 : ℝ))).ne'
  have hexp_ne : Real.exp (-Real.pi * ((2 ^ K : ℕ) : ℝ)) ≠ 0 :=
    (Real.exp_pos (-Real.pi * ((2 ^ K : ℕ) : ℝ))).ne'
  have hlog_ratio :
      Real.log (E (K + 1) / E K) =
        (-(3 / 4 : ℝ)) * Real.log 2 + -Real.pi * ((2 ^ K : ℕ) : ℝ) := by
    rw [hRatio K]
    rw [Real.log_mul hpow_ne hexp_ne,
      Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_exp]
  calc
    B (K + 1) - B K = -Real.log (E (K + 1) / E K) / Real.log 2 := by
      rw [hB (K + 1), hB K, Real.log_div hE_succ_ne hE_ne]
      ring
    _ = (Real.pi / Real.log 2) * ((2 ^ K : ℕ) : ℝ) + 3 / 4 := by
      rw [hlog_ratio]
      field_simp [hlog2_ne]
      ring

end Omega.Conclusion
