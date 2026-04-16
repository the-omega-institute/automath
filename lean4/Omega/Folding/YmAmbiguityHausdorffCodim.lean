import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing algebraic wrapper for the ambiguity-shell entropy gap formulas.
    cor:Ym-amb-hausdorff-codim -/
theorem paper_Ym_amb_hausdorff_codim (ρAmb εm dimH codim : ℝ) (hρ : 0 < ρAmb) (hρlt : ρAmb < 2)
    (hdim : dimH = Real.log ρAmb / Real.log 2) (hε : εm = Real.log 2 - Real.log ρAmb)
    (hcodim : codim = 1 - dimH) :
    dimH = 1 - εm / Real.log 2 ∧ codim = εm / Real.log 2 := by
  have _ := hρ
  have _ := hρlt
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by norm_num)
  constructor
  · rw [hdim, hε]
    field_simp [hlog2]
    ring
  · rw [hcodim]
    have hdim' : dimH = 1 - εm / Real.log 2 := by
      rw [hdim, hε]
      field_simp [hlog2]
      ring
    rw [hdim']
    field_simp [hlog2]
    ring

end Omega.Folding
