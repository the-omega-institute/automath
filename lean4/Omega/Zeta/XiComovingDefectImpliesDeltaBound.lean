import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-comoving-defect-implies-delta-bound`. -/
theorem paper_xi_comoving_defect_implies_delta_bound {ρ ε δ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (h : ρ * Real.exp (-ε) ≤ (1 - δ) / (1 + δ)) :
    δ ≤ (1 - ρ * Real.exp (-ε)) / (1 + ρ * Real.exp (-ε)) := by
  let a : ℝ := ρ * Real.exp (-ε)
  have ha0 : 0 < a := by
    exact mul_pos hρ0 (Real.exp_pos _)
  have : a < 1 := by
    have hexp_le_one : Real.exp (-ε) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-ε)]
  have hdenδ : 0 < 1 + δ := by
    linarith
  have hmul : a * (1 + δ) ≤ 1 - δ := by
    exact (le_div_iff₀ hdenδ).mp (by simpa [a] using h)
  have hdena : 0 < 1 + a := by
    linarith
  have htarget : δ * (1 + a) ≤ 1 - a := by
    nlinarith
  exact (le_div_iff₀ hdena).mpr (by simpa [a] using htarget)

end Omega.Zeta
