import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Solving `cos (((K log 2)/2) t) = 0` gives the odd-π lattice
`t = (2l+1)π / (K log 2)` for every nonzero shell index `K`.
    thm:conclusion-xi-dyadic-shell-zero-lattice -/
theorem paper_conclusion_xi_dyadic_shell_zero_lattice (K : ℤ) (hK : K ≠ 0) (t : ℝ) :
    Real.cos ((((K : ℝ) * Real.log 2) / 2) * t) = 0 ↔
      ∃ l : ℤ, t = ((((2 * l + 1 : ℤ) : ℝ) * Real.pi) / ((K : ℝ) * Real.log 2)) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast hK
  have hscale_ne : ((((K : ℝ) * Real.log 2) / 2 : ℝ)) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hKreal hlog2) two_ne_zero
  constructor
  · intro hcos
    rcases Real.cos_eq_zero_iff.mp hcos with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    have hdiv := congrArg (fun x : ℝ => x / ((((K : ℝ) * Real.log 2) / 2))) hl
    have hdiv' :
        ((((K : ℝ) * Real.log 2) / 2) * t) / ((((K : ℝ) * Real.log 2) / 2)) =
          ((((2 * l + 1 : ℤ) : ℝ) * Real.pi) / 2) / ((((K : ℝ) * Real.log 2) / 2)) := by
      simpa using hdiv
    have hleft :
        ((((K : ℝ) * Real.log 2) / 2) * t) / ((((K : ℝ) * Real.log 2) / 2)) = t := by
      field_simp [hscale_ne]
    have hright :
        ((((2 * l + 1 : ℤ) : ℝ) * Real.pi) / 2) / ((((K : ℝ) * Real.log 2) / 2)) =
          ((((2 * l + 1 : ℤ) : ℝ) * Real.pi) / ((K : ℝ) * Real.log 2)) := by
      field_simp [hscale_ne, hKreal, hlog2]
    calc
      t = ((((2 * l + 1 : ℤ) : ℝ) * Real.pi) / 2) / ((((K : ℝ) * Real.log 2) / 2)) := by
            rw [← hleft]
            exact hdiv'
      _ = ((((2 * l + 1 : ℤ) : ℝ) * Real.pi) / ((K : ℝ) * Real.log 2)) := hright
  · rintro ⟨l, rfl⟩
    apply Real.cos_eq_zero_iff.mpr
    refine ⟨l, ?_⟩
    norm_num
    field_simp [hKreal, hlog2]

end Omega.CircleDimension
