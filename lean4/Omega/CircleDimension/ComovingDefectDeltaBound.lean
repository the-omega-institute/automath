import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.CircleDimension.ComovingDefectDeltaBound

/-- Paper seed: solving the comoving Jensen-defect inequality for the horizontal offset.
    prop:cdim-comoving-defect-implies-delta-bound -/
theorem paper_cdim_comoving_defect_implies_delta_bound_seeds
    {ρ ε δ : ℝ}
    (hρ : 0 < ρ) (_hρlt : ρ < 1) (_hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hbound : ρ * Real.exp (-ε) ≤ (1 - δ) / (1 + δ)) :
    δ ≤ (1 - ρ * Real.exp (-ε)) / (1 + ρ * Real.exp (-ε)) := by
  set r : ℝ := ρ * Real.exp (-ε)
  have hden : 0 < 1 + δ := by linarith
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hstep : r * (1 + δ) ≤ 1 - δ := by
    dsimp [r] at *
    exact (le_div_iff₀ hden).mp hbound
  have hrden : 0 < 1 + r := by linarith
  change δ ≤ (1 - r) / (1 + r)
  exact (le_div_iff₀ hrden).2 (by nlinarith [hstep])

/-- Packaged form of the comoving defect-to-offset bound.
    prop:cdim-comoving-defect-implies-delta-bound -/
theorem paper_cdim_comoving_defect_implies_delta_bound_package
    {ρ ε δ : ℝ}
    (hρ : 0 < ρ) (hρlt : ρ < 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hbound : ρ * Real.exp (-ε) ≤ (1 - δ) / (1 + δ)) :
    δ ≤ (1 - ρ * Real.exp (-ε)) / (1 + ρ * Real.exp (-ε)) :=
  paper_cdim_comoving_defect_implies_delta_bound_seeds hρ hρlt hε hδ hbound

/-- Paper-facing wrapper for the comoving Jensen-defect offset bound.
    prop:cdim-comoving-defect-implies-delta-bound -/
theorem paper_cdim_comoving_defect_implies_delta_bound
    {ρ ε δ : ℝ}
    (hρ : 0 < ρ) (hρlt : ρ < 1) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hbound : ρ * Real.exp (-ε) ≤ (1 - δ) / (1 + δ)) :
    δ ≤ (1 - ρ * Real.exp (-ε)) / (1 + ρ * Real.exp (-ε)) :=
  paper_cdim_comoving_defect_implies_delta_bound_package hρ hρlt hε hδ hbound

end Omega.CircleDimension.ComovingDefectDeltaBound
