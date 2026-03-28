import Omega.Folding.Defect

namespace Omega.Frontier

/-- Full generation hypothesis for finite defect patterns at resolution `m`. -/
def FullGeneration (m : Nat) : Prop :=
  ∀ d : Word m, ∃ k : Nat, ∃ ω : Word (m + k), globalDefect (Nat.le_add_right m k) ω = d

/-- Abstract uniform spectral gap datum for the defect process. -/
structure UniformGap where
  η : ℝ
  η_pos : 0 < η
  η_lt_one : η < 1

/-- A coarse defect-budget hypothesis on finite scales. -/
def DefectBudget (m : Nat) : Prop :=
  ∀ k : Nat, ∃ C : Nat, C ≤ m + k

/-- Global full-generation hypothesis across all finite resolutions. -/
def GlobalFullGeneration : Prop :=
  ∀ m : Nat, FullGeneration m

/-- Global coarse defect-budget hypothesis across all finite resolutions. -/
def GlobalDefectBudget : Prop :=
  ∀ m : Nat, DefectBudget m

end Omega.Frontier
