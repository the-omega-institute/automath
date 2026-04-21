import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.CriticalCircleDensityCalibration

open scoped goldenRatio

namespace Omega.Zeta

noncomputable section

/-- Linear main term contributed by `B` critical-circle mode families at base `λ`. -/
def criticalCircleMainTerm (lam B T : ℝ) : ℝ :=
  B * Real.log lam * T

/-- The mode budget required to turn the linear `T` factor into `T log T`. -/
def criticalCircleModeBudget (lam T : ℝ) : ℝ :=
  Real.log T / Real.log lam

/-- Paper label: `cor:critical-circle-mode-growth`. Matching a linear critical-circle main term
against `T log T` forces the budget `B(T) = log T / log λ`; for `λ = φ²` this becomes
`log T / (2 log φ)`. -/
theorem paper_critical_circle_mode_growth {lam T : ℝ} (hlam : 1 < lam) (hT : 0 < T) :
    criticalCircleMainTerm lam (criticalCircleModeBudget lam T) T = T * Real.log T ∧
      criticalCircleModeBudget (Real.goldenRatio ^ (2 : ℝ)) T =
        Real.log T / (2 * Real.log Real.goldenRatio) ∧
      criticalCircleMainTerm (Real.goldenRatio ^ (2 : ℝ))
          (criticalCircleModeBudget (Real.goldenRatio ^ (2 : ℝ)) T) T =
        T * Real.log T := by
  have hloglam_ne : Real.log lam ≠ 0 := ne_of_gt (Real.log_pos hlam)
  have hlogφ_ne : Real.log Real.goldenRatio ≠ 0 := ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  have hlogφ2 :
      Real.log (Real.goldenRatio ^ (2 : ℝ)) = 2 * Real.log Real.goldenRatio := by
    simpa using (Real.log_rpow Real.goldenRatio_pos (2 : ℝ))
  have hmain :
      criticalCircleMainTerm lam (criticalCircleModeBudget lam T) T = T * Real.log T := by
    unfold criticalCircleMainTerm criticalCircleModeBudget
    field_simp [hloglam_ne]
  have hbudgetφ :
      criticalCircleModeBudget (Real.goldenRatio ^ (2 : ℝ)) T =
        Real.log T / (2 * Real.log Real.goldenRatio) := by
    rw [criticalCircleModeBudget, hlogφ2]
  have hmainφ :
      criticalCircleMainTerm (Real.goldenRatio ^ (2 : ℝ))
          (criticalCircleModeBudget (Real.goldenRatio ^ (2 : ℝ)) T) T =
        T * Real.log T := by
    rw [hbudgetφ]
    unfold criticalCircleMainTerm
    rw [hlogφ2]
    have hdenom_ne : 2 * Real.log Real.goldenRatio ≠ 0 := by
      exact mul_ne_zero (by norm_num) hlogφ_ne
    field_simp [hdenom_ne]
  exact ⟨hmain, hbudgetφ, hmainφ⟩

end

end Omega.Zeta
