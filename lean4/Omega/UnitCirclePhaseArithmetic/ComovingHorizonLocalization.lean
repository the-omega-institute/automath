import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

theorem paper_app_comoving_horizon_localization (γ δ x0 : ℝ) (hδ : 0 < δ) :
    let t : ℂ := ((γ - x0 : ℝ) : ℂ) + Complex.I * (δ : ℂ)
    let w : ℂ := (1 + Complex.I * t) / (1 - Complex.I * t)
    (1 - Complex.normSq w = 4 * δ / ((γ - x0) ^ 2 + (1 + δ) ^ 2)) ∧
      (Complex.normSq (1 + w) = 4 / ((γ - x0) ^ 2 + (1 + δ) ^ 2)) := by
  dsimp
  let t : ℂ := ((γ - x0 : ℝ) : ℂ) + Complex.I * (δ : ℂ)
  let w : ℂ := (1 + Complex.I * t) / (1 - Complex.I * t)
  change (1 - Complex.normSq w = 4 * δ / ((γ - x0) ^ 2 + (1 + δ) ^ 2)) ∧
      (Complex.normSq (1 + w) = 4 / ((γ - x0) ^ 2 + (1 + δ) ^ 2))
  have hden :
      Complex.normSq (1 - Complex.I * t) = (γ - x0) ^ 2 + (1 + δ) ^ 2 := by
    simp [t, Complex.normSq_apply, pow_two]
    ring
  have hnum :
      Complex.normSq (1 + Complex.I * t) = (γ - x0) ^ 2 + (1 - δ) ^ 2 := by
    simp [t, Complex.normSq_apply, pow_two]
    ring
  have hden_pos : 0 < (γ - x0) ^ 2 + (1 + δ) ^ 2 := by
    nlinarith [sq_nonneg (γ - x0), hδ]
  have hden_ne_real : (γ - x0) ^ 2 + (1 + δ) ^ 2 ≠ 0 := ne_of_gt hden_pos
  have hden_ne : 1 - Complex.I * t ≠ 0 := by
    intro hz
    have : Complex.normSq (1 - Complex.I * t) = 0 := by
      simp [hz]
    rw [hden] at this
    linarith
  have hnorm_w :
      Complex.normSq w = ((γ - x0) ^ 2 + (1 - δ) ^ 2) / ((γ - x0) ^ 2 + (1 + δ) ^ 2) := by
    dsimp [w]
    rw [Complex.normSq_div, hnum, hden]
  have hplus :
      1 + w = (2 : ℂ) / (1 - Complex.I * t) := by
    dsimp [w]
    field_simp [hden_ne]
    ring
  constructor
  · rw [hnorm_w]
    field_simp [hden_ne_real]
    ring_nf
  · rw [hplus, Complex.normSq_div, hden]
    norm_num

end Omega.UnitCirclePhaseArithmetic
