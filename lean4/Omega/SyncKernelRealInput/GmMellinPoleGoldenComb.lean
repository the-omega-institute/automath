import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

open scoped BigOperators

/-- `cor:gm-mellin-pole-golden-comb` -/
theorem paper_gm_mellin_pole_golden_comb (z0 : ℂ) (hz0 : z0 ≠ 0) :
    ∃ base : ℂ, ∀ s : ℂ,
      Complex.exp (-(s * (Real.log Real.goldenRatio : ℂ))) = z0 ↔
        ∃ k : ℤ,
          s =
            base + (k : ℂ) * ((2 * Real.pi / Real.log Real.goldenRatio : ℝ) : ℂ) *
              Complex.I := by
  let L : ℝ := Real.log Real.goldenRatio
  have hL_pos : 0 < L := by
    simpa [L] using Real.log_pos Real.one_lt_goldenRatio
  have hL_ne : (L : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hL_pos
  let base : ℂ := -Complex.log z0 / (L : ℂ)
  refine ⟨base, ?_⟩
  intro s
  have hbase_exp : Complex.exp (-(base * (L : ℂ))) = z0 := by
    have harg : -(base * (L : ℂ)) = Complex.log z0 := by
      simp [base, hL_ne]
    rw [harg, Complex.exp_log hz0]
  constructor
  · intro hs
    have hExp : Complex.exp (-(s * (L : ℂ))) = Complex.exp (-(base * (L : ℂ))) := by
      rw [hs, hbase_exp]
    obtain ⟨n, hn⟩ := (Complex.exp_eq_exp_iff_exists_int).mp hExp
    refine ⟨-n, ?_⟩
    have hlinear :
        s =
          base + ((-n : ℤ) : ℂ) * ((2 * Real.pi / L : ℝ) : ℂ) * Complex.I := by
      have hmul : s * (L : ℂ) = base * (L : ℂ) - (n : ℂ) * (2 * Real.pi * Complex.I) := by
        calc
          s * (L : ℂ) = -(-(s * (L : ℂ))) := by ring
          _ = - (-(base * (L : ℂ)) + (n : ℂ) * (2 * Real.pi * Complex.I)) := by rw [hn]
          _ = base * (L : ℂ) - (n : ℂ) * (2 * Real.pi * Complex.I) := by ring
      have hmul' :
          s * (L : ℂ) =
            (base + ((-n : ℤ) : ℂ) * ((2 * Real.pi / L : ℝ) : ℂ) * Complex.I) *
              (L : ℂ) := by
        rw [hmul]
        field_simp [hL_ne]
        norm_num [div_eq_mul_inv]
        field_simp [hL_ne]
        ring_nf
      exact mul_right_cancel₀ hL_ne hmul'
    simpa [L] using hlinear
  · rintro ⟨k, rfl⟩
    have hperiod :
        -((base + (k : ℂ) * ((2 * Real.pi / L : ℝ) : ℂ) * Complex.I) * (L : ℂ)) =
          -(base * (L : ℂ)) + (-k : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp [hL_ne]
      norm_num [div_eq_mul_inv]
      field_simp [hL_ne]
      ring_nf
    calc
      Complex.exp
          (-((base + (k : ℂ) * ((2 * Real.pi / L : ℝ) : ℂ) * Complex.I) * (L : ℂ))) =
          Complex.exp (-(base * (L : ℂ))) := by
            rw [hperiod]
            exact (Complex.exp_eq_exp_iff_exists_int).mpr ⟨-k, by simp⟩
      _ = z0 := hbase_exp

end Omega.SyncKernelRealInput
