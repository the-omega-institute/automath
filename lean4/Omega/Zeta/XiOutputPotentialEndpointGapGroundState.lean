import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40GroundEntropy
import Omega.SyncKernelWeighted.RealInput40PositiveEntropyFreezing

namespace Omega.Zeta

open Omega.SyncKernelWeighted

/-- Paper label: `thm:xi-output-potential-endpoint-gap-ground-state`.
Writing the endpoint values as `I(0) = log (φ²)` and `I(1/2) = log (φ² / c)`, the endpoint gap is
exactly `log c`, hence exactly the previously registered ground-state entropy. -/
def xi_output_potential_endpoint_gap_ground_state_statement : Prop :=
  ∀ c : ℝ, 1 < c →
    let I0 : ℝ := Real.log (Real.goldenRatio ^ 2)
    let Ihalf : ℝ := Real.log (Real.goldenRatio ^ 2 / c)
    I0 - Ihalf = Real.log c ∧ I0 - Ihalf = realInput40GroundEntropy c

theorem paper_xi_output_potential_endpoint_gap_ground_state :
    xi_output_potential_endpoint_gap_ground_state_statement := by
  intro c hc
  dsimp
  have hfreeze := paper_killo_real_input_40_positive_entropy_freezing c hc
  have hgap_ground :
      Real.log (Real.goldenRatio ^ 2) - Real.log (Real.goldenRatio ^ 2 / c) =
        realInput40GroundEntropy c := by
    linarith [hfreeze.2.2]
  refine ⟨?_, hgap_ground⟩
  rw [hgap_ground, hfreeze.2.1]

end Omega.Zeta
