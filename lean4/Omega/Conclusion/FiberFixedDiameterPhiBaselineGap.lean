import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fiber-fixed-diameter-phi-baseline-gap`. The logarithmic
baseline gap is squeezed by the stated lower Fibonacci multiplicity and upper hypercube
multiplicity bounds. -/
theorem paper_conclusion_fiber_fixed_diameter_phi_baseline_gap (D d : ℕ) (Δ φ : ℝ)
    (hφ : φ = (1 + Real.sqrt 5) / 2)
    (hd_lower : (Nat.fib (D + 2) : ℝ) ≤ (d : ℝ))
    (hd_upper : (d : ℝ) ≤ (2 : ℝ) ^ D)
    (hΔ : Δ = Real.log (d : ℝ) - (D : ℝ) * Real.log φ) :
    Real.log (Nat.fib (D + 2) : ℝ) - (D : ℝ) * Real.log φ ≤ Δ ∧
      Δ ≤ (D : ℝ) * Real.log (2 / φ) := by
  subst Δ
  have hfib_pos : 0 < (Nat.fib (D + 2) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hd_pos : 0 < (d : ℝ) := lt_of_lt_of_le hfib_pos hd_lower
  have hφ_pos : 0 < φ := by
    rw [hφ]
    positivity
  constructor
  · have hlog_lower : Real.log (Nat.fib (D + 2) : ℝ) ≤ Real.log (d : ℝ) :=
      Real.log_le_log hfib_pos hd_lower
    linarith
  · have hlog_upper : Real.log (d : ℝ) ≤ Real.log ((2 : ℝ) ^ D) :=
      Real.log_le_log hd_pos hd_upper
    have hlog_pow : Real.log ((2 : ℝ) ^ D) = (D : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    have hlog_div : Real.log (2 / φ) = Real.log 2 - Real.log φ := by
      rw [Real.log_div (by norm_num) hφ_pos.ne']
    calc
      Real.log (d : ℝ) - (D : ℝ) * Real.log φ
          ≤ Real.log ((2 : ℝ) ^ D) - (D : ℝ) * Real.log φ :=
            sub_le_sub_right hlog_upper _
      _ = (D : ℝ) * Real.log 2 - (D : ℝ) * Real.log φ := by rw [hlog_pow]
      _ = (D : ℝ) * (Real.log 2 - Real.log φ) := by ring
      _ = (D : ℝ) * Real.log (2 / φ) := by rw [hlog_div]

end Omega.Conclusion
