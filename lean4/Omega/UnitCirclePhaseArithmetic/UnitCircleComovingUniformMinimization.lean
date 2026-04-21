import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Specializing the comoving-defect bound at the aligned chart `x₀ = γ` and using the uniform
defect envelope `Dζ n γ ≤ εₙ` lets one replace the chart defect by the global defect bound `εₙ`.
Rewriting the appendix parameter `δ` as `1 / 2 - β` yields the paper's minimization inequality.
    thm:unit-circle-comoving-uniform-minimization -/
theorem paper_unit_circle_comoving_uniform_minimization (rho eps : ℕ → ℝ) (Dζ : ℕ → ℝ → ℝ)
    (β γ : ℝ) (hρ0 : ∀ n, 0 < rho n) (hρ1 : ∀ n, rho n < 1) (hε : ∀ n, 0 ≤ eps n)
    (hβ : β ≤ 1 / 2) (huniform : ∀ n x0, Dζ n x0 ≤ eps n)
    (hdefect :
      ∀ n, rho n * Real.exp (-(Dζ n γ)) ≤ (1 - (1 / 2 - β)) / (1 + (1 / 2 - β))) :
    ∀ n, β ≥ 1 / 2 - ((1 - rho n * Real.exp (-eps n)) / (1 + rho n * Real.exp (-eps n))) := by
  intro n
  let a : ℝ := rho n * Real.exp (-eps n)
  have _hεn : 0 ≤ eps n := hε n
  have hρpos : 0 < rho n := hρ0 n
  have hρlt : rho n < 1 := hρ1 n
  have hρnonneg : 0 ≤ rho n := le_of_lt hρpos
  have hD : Dζ n γ ≤ eps n := huniform n γ
  have hexp : Real.exp (-eps n) ≤ Real.exp (-(Dζ n γ)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hmul : a ≤ rho n * Real.exp (-(Dζ n γ)) := by
    dsimp [a]
    exact mul_le_mul_of_nonneg_left hexp hρnonneg
  have hbound :
      a ≤ (1 - (1 / 2 - β)) / (1 + (1 / 2 - β)) :=
    le_trans hmul (hdefect n)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact mul_pos hρpos (Real.exp_pos _)
  have hone_add_pos : 0 < 1 + a := by
    linarith
  have hden_pos : 0 < 3 / 2 - β := by
    linarith
  have hscaled : a * (3 / 2 - β) ≤ β + 1 / 2 := by
    calc
      a * (3 / 2 - β)
          ≤ ((1 - (1 / 2 - β)) / (1 + (1 / 2 - β))) * (3 / 2 - β) := by
              exact mul_le_mul_of_nonneg_right hbound hden_pos.le
      _ = β + 1 / 2 := by
            rw [show 1 - (1 / 2 - β) = β + 1 / 2 by ring]
            rw [show 1 + (1 / 2 - β) = 3 / 2 - β by ring]
            have hne : 3 / 2 - β ≠ 0 := by linarith
            exact div_mul_cancel₀ (β + 1 / 2) hne
  have hone_add_ne : 1 + a ≠ 0 := ne_of_gt hone_add_pos
  have hgoal : β ≥ 1 / 2 - ((1 - a) / (1 + a)) := by
    field_simp [hone_add_ne]
    nlinarith [hscaled]
  dsimp [a] at hgoal ⊢
  exact hgoal

end Omega.UnitCirclePhaseArithmetic
