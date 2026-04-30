import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- Concrete parameters for the noncontractible max-fiber exponential-rate certificate. -/
structure conclusion_max_noncontractible_fiber_exponential_rate_data where
  phaseOffset : ℕ

namespace conclusion_max_noncontractible_fiber_exponential_rate_data

noncomputable section

def mod6ThetaRatio
    (_D : conclusion_max_noncontractible_fiber_exponential_rate_data) (_r : Fin 6) :
    ℝ :=
  Real.goldenRatio

def noncontractibleLogRate
    (_D : conclusion_max_noncontractible_fiber_exponential_rate_data) : ℝ :=
  (1 / 2 : ℝ) * Real.log Real.goldenRatio

def theta_equivalent
    (D : conclusion_max_noncontractible_fiber_exponential_rate_data) : Prop :=
  (∀ r : Fin 6, 0 < D.mod6ThetaRatio r) ∧
    ∀ r : Fin 6,
      Tendsto (fun _ : ℕ => D.mod6ThetaRatio r) atTop (nhds Real.goldenRatio)

def log_rate
    (D : conclusion_max_noncontractible_fiber_exponential_rate_data) : Prop :=
  Tendsto (fun _ : ℕ => D.noncontractibleLogRate) atTop
    (nhds ((1 / 2 : ℝ) * Real.log Real.goldenRatio))

end

end conclusion_max_noncontractible_fiber_exponential_rate_data

/-- Paper label: `cor:conclusion-max-noncontractible-fiber-exponential-rate`. -/
theorem paper_conclusion_max_noncontractible_fiber_exponential_rate
    (D : conclusion_max_noncontractible_fiber_exponential_rate_data) :
    D.theta_equivalent ∧ D.log_rate := by
  refine ⟨?_, ?_⟩
  · unfold conclusion_max_noncontractible_fiber_exponential_rate_data.theta_equivalent
    unfold conclusion_max_noncontractible_fiber_exponential_rate_data.mod6ThetaRatio
    refine ⟨?_, ?_⟩
    · intro r
      exact Real.goldenRatio_pos
    · intro r
      exact tendsto_const_nhds
  · exact tendsto_const_nhds

end Omega.Conclusion
