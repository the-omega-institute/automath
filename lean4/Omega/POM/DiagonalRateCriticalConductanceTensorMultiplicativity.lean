import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete scalar data for the diagonal-rate critical-conductance tensor product identity. The
endpoint amplitudes multiply, while the critical conductance coefficient is encoded by the closed
form `C_Ω = C_w + C_v + C_w C_v`. -/
structure PomDiagonalRateCriticalConductanceTensorMultiplicativityData where
  Aw : ℝ
  Av : ℝ
  Cw : ℝ
  Cv : ℝ

namespace PomDiagonalRateCriticalConductanceTensorMultiplicativityData

def Aomega (D : PomDiagonalRateCriticalConductanceTensorMultiplicativityData) : ℝ :=
  D.Aw * D.Av

def Comega (D : PomDiagonalRateCriticalConductanceTensorMultiplicativityData) : ℝ :=
  D.Cw + D.Cv + D.Cw * D.Cv

def criticalConductance (D : PomDiagonalRateCriticalConductanceTensorMultiplicativityData) : ℝ :=
  D.Aomega * (1 + D.Comega)

def conductanceTensorFactorization
    (D : PomDiagonalRateCriticalConductanceTensorMultiplicativityData) : Prop :=
  D.criticalConductance = (D.Aw * (1 + D.Cw)) * (D.Av * (1 + D.Cv))

end PomDiagonalRateCriticalConductanceTensorMultiplicativityData

open PomDiagonalRateCriticalConductanceTensorMultiplicativityData

/-- Paper label: `cor:pom-diagonal-rate-critical-conductance-tensor-multiplicativity`. -/
theorem paper_pom_diagonal_rate_critical_conductance_tensor_multiplicativity
    (D : PomDiagonalRateCriticalConductanceTensorMultiplicativityData) :
    D.Aomega = D.Aw * D.Av ∧
      1 + D.Comega = (1 + D.Cw) * (1 + D.Cv) ∧
      D.Comega = D.Cw + D.Cv + D.Cw * D.Cv ∧
      D.conductanceTensorFactorization := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · unfold PomDiagonalRateCriticalConductanceTensorMultiplicativityData.Comega
    ring
  ·
    unfold PomDiagonalRateCriticalConductanceTensorMultiplicativityData.conductanceTensorFactorization
    unfold PomDiagonalRateCriticalConductanceTensorMultiplicativityData.criticalConductance
    unfold PomDiagonalRateCriticalConductanceTensorMultiplicativityData.Aomega
    unfold PomDiagonalRateCriticalConductanceTensorMultiplicativityData.Comega
    ring

end Omega.POM
