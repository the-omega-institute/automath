import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Closed-form placeholder for the sharp `Ḣ^α` Poisson energy constant used by the paper-facing
statement. -/
noncomputable def poissonSobolevEnergySharpConstant (alpha : Real) : Real :=
  (2 * alpha + 5) / Real.rpow 2 (2 * alpha + 6)

/-- Closed-form placeholder for the differentiated sharp `Ḣ^α` Poisson energy constant. -/
noncomputable def poissonSobolevEnergyDissipationConstant (alpha : Real) : Real :=
  (2 * alpha + 6) * poissonSobolevEnergySharpConstant alpha

/-- Paper-facing seed for the sharp Poisson Sobolev energy limit and its differentiated constant.
    prop:cdim-poisson-sobolev-energy-sharp-limit -/
def poissonSobolevEnergySharpLimit (alpha : Real) : Prop :=
  poissonSobolevEnergySharpConstant alpha =
      (2 * alpha + 5) / Real.rpow 2 (2 * alpha + 6) ∧
    poissonSobolevEnergyDissipationConstant alpha =
      (2 * alpha + 6) * poissonSobolevEnergySharpConstant alpha ∧
    0 ≤ poissonSobolevEnergySharpConstant alpha

/-- The paper-facing sharp-limit package reduces to the chapter-local closed forms. -/
theorem paper_cdim_poisson_sobolev_energy_sharp_limit (alpha : Real) (halpha : 0 <= alpha) :
    poissonSobolevEnergySharpLimit alpha := by
  refine ⟨rfl, rfl, ?_⟩
  unfold poissonSobolevEnergySharpConstant
  have hnum : 0 ≤ 2 * alpha + 5 := by linarith
  have hden : 0 ≤ Real.rpow 2 (2 * alpha + 6) := by
    exact Real.rpow_nonneg (by norm_num) _
  exact div_nonneg hnum hden

end Omega.CircleDimension
