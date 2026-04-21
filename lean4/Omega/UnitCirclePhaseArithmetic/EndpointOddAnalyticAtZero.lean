import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.EndpointZetaLChi4SymbolPair

open Filter Topology

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

private lemma endpointDyadicScale_two_zero : endpointDyadicScale 2 0 = (1 / 2 : ℝ) := by
  calc
    endpointDyadicScale 2 0 = Real.exp (-Real.log 2) := by
      simp [endpointDyadicScale]
    _ = (Real.exp (Real.log 2))⁻¹ := by rw [Real.exp_neg]
    _ = (2 : ℝ)⁻¹ := by rw [Real.exp_log (by positivity : (0 : ℝ) < 2)]
    _ = (1 / 2 : ℝ) := by norm_num

/-- Paper label: `cor:endpoint-odd-analytic-at-zero`. The endpoint odd `χ₄` channel is continuous
from the positive side at `σ = 0`, and its value there is the classical constant `π/4` times the
discrete endpoint sign. -/
theorem paper_endpoint_odd_analytic_at_zero (m : ℕ) (hm : Odd m) :
    Filter.Tendsto (fun σ : ℝ => Omega.UnitCirclePhaseArithmetic.endpointOddChi4WeightedSign σ m)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((Real.pi / 4) * Omega.UnitCirclePhaseArithmetic.endpointChi4Sign m)) := by
  have _hmPos : 0 < m + 1 := by
    rcases hm with ⟨k, rfl⟩
    omega
  have hscaleArg : ContinuousAt (fun σ : ℝ => -(1 + σ) * Real.log 2) 0 := by
    exact (continuousAt_const.add continuousAt_id).neg.mul continuousAt_const
  have hscale : ContinuousAt (fun σ : ℝ => endpointDyadicScale 2 σ) 0 := by
    simpa [endpointDyadicScale] using Real.continuous_exp.continuousAt.comp hscaleArg
  have hzetaArg : ContinuousAt (fun σ : ℝ => (1 + σ) - 1) 0 := by
    exact (continuousAt_const.add continuousAt_id).sub continuousAt_const
  have hzeta : ContinuousAt (fun σ : ℝ => endpointZetaSymbol (1 + σ)) 0 := by
    simpa [endpointZetaSymbol] using
      (continuousAt_const.mul (Real.continuous_exp.continuousAt.comp hzetaArg))
  have hfactor : ContinuousAt (fun σ : ℝ => 1 - endpointDyadicScale 2 σ) 0 := by
    exact continuousAt_const.sub hscale
  have hbaseCont : ContinuousAt endpointLChi4Symbol 0 := by
    simpa [endpointLChi4Symbol, endpointOddClassSum] using hfactor.mul hzeta
  have hbaseZero : endpointLChi4Symbol 0 = Real.pi / 4 := by
    calc
      endpointLChi4Symbol 0 = (1 - (1 / 2 : ℝ)) * (Real.pi / 2) := by
        simp [endpointLChi4Symbol, endpointOddClassSum, endpointZetaSymbol,
          endpointDyadicScale_two_zero]
      _ = Real.pi / 4 := by
        ring
  have hbase :
      Filter.Tendsto (fun σ : ℝ => endpointLChi4Symbol σ) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Real.pi / 4)) := by
    simpa [hbaseZero] using hbaseCont.continuousWithinAt.tendsto
  have hsign :
      Filter.Tendsto (fun _ : ℝ => (endpointChi4Sign m : ℝ)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (endpointChi4Sign m : ℝ)) :=
    tendsto_const_nhds
  simpa [endpointOddChi4WeightedSign] using hbase.mul hsign

end

end Omega.UnitCirclePhaseArithmetic
