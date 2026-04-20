import Mathlib.Tactic
import Omega.Zeta.FiniteKernelLatticeObstruction

namespace Omega.Zeta

/-- A normalized critical-circle pole family is determined by one of `B` unit-step vertical
arithmetic progressions, each with phase `0` or `1`. Counting poles up to a discrete height `T`
then contributes either `T + 1` or `T` points from each progression. -/
structure CriticalCircleDensityCalibrationData where
  B : ℕ
  phase : Fin B → ℕ
  phase_le_one : ∀ b : Fin B, phase b ≤ 1

namespace CriticalCircleDensityCalibrationData

/-- Pole count contributed by one normalized vertical arithmetic progression. -/
def progressionCount (D : CriticalCircleDensityCalibrationData) (b : Fin D.B) (T : ℕ) : ℕ :=
  T + 1 - D.phase b

/-- Total critical-line pole count up to normalized height `T`. -/
def poleCount (D : CriticalCircleDensityCalibrationData) (T : ℕ) : ℕ :=
  ∑ b : Fin D.B, D.progressionCount b T

/-- The existing finite-kernel dictionary attached to the critical-circle counting model. -/
def toFiniteKernel (D : CriticalCircleDensityCalibrationData) : FiniteKernel where
  poleFamilies := D.B
  poleCount := D.poleCount

/-- Concrete linear-density calibration: the pole count is trapped between `B * T` and
`B * (T + 1)`, hence is linear in the height with an additive `O(1)` error. -/
def mainClaim (D : CriticalCircleDensityCalibrationData) : Prop :=
  linearPoleCount D.toFiniteKernel ∧
    ∀ T : ℕ, D.B * T ≤ D.poleCount T ∧ D.poleCount T ≤ D.B * (T + 1)

end CriticalCircleDensityCalibrationData

open CriticalCircleDensityCalibrationData

/-- The critical-circle pole families form `B` vertical arithmetic progressions, and summing the
per-family floor bounds gives the linear main term with an additive bounded error.
    prop:critical-circle-density-calibration -/
theorem paper_critical_circle_density_calibration (D : CriticalCircleDensityCalibrationData) :
    D.mainClaim := by
  constructor
  · intro T
    calc
      D.poleCount T = ∑ b : Fin D.B, D.progressionCount b T := by
        simp [CriticalCircleDensityCalibrationData.poleCount]
      _ ≤ ∑ b : Fin D.B, (T + 1) := by
        refine Finset.sum_le_sum ?_
        intro b hb
        unfold CriticalCircleDensityCalibrationData.progressionCount
        omega
      _ = D.B * (T + 1) := by simp
  · intro T
    constructor
    · calc
        D.B * T = ∑ b : Fin D.B, T := by simp
        _ ≤ ∑ b : Fin D.B, D.progressionCount b T := by
          refine Finset.sum_le_sum ?_
          intro b hb
          unfold CriticalCircleDensityCalibrationData.progressionCount
          have hbnd : D.phase b ≤ 1 := D.phase_le_one b
          omega
        _ = D.poleCount T := by
          simp [CriticalCircleDensityCalibrationData.poleCount]
    · calc
        D.poleCount T = ∑ b : Fin D.B, D.progressionCount b T := by
          simp [CriticalCircleDensityCalibrationData.poleCount]
        _ ≤ ∑ b : Fin D.B, (T + 1) := by
          refine Finset.sum_le_sum ?_
          intro b hb
          unfold CriticalCircleDensityCalibrationData.progressionCount
          omega
        _ = D.B * (T + 1) := by simp

end Omega.Zeta
