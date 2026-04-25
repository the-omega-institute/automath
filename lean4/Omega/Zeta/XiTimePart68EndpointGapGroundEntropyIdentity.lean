import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40AlphaMax
import Omega.SyncKernelWeighted.RealInput40GroundEntropy
import Omega.SyncKernelWeighted.RealInput40PositiveEntropyFreezing

namespace Omega.Zeta

open Omega.SyncKernelWeighted

/-- Paper label: `prop:xi-time-part68-endpoint-gap-ground-entropy-identity`. The already
formalized endpoint-gap theorem, the audited identity `α_max = 1 / 2`, and the definition
`h_ground = log c` combine to give the exact endpoint entropy identity in closed form. -/
theorem paper_xi_time_part68_endpoint_gap_ground_entropy_identity :
    ∀ c : ℝ, 1 < c →
      let I0 : ℝ := Real.log (Real.goldenRatio ^ 2)
      let Iαmax : ℝ := Real.log (Real.goldenRatio ^ 2 / c)
      let αmax : ℝ := real_input_40_alpha_max_value
      let hground : ℝ := realInput40GroundEntropy c
      I0 - Iαmax = hground ∧
        αmax = (1 / 2 : ℝ) ∧
        hground = Real.log c ∧
        I0 = Real.log (Real.goldenRatio ^ 2) ∧
        Iαmax = Real.log (Real.goldenRatio ^ 2 / c) := by
  intro c hc
  dsimp
  have hfreeze := paper_killo_real_input_40_positive_entropy_freezing c hc
  have hendpoint :
      Real.log (Real.goldenRatio ^ 2) - Real.log (Real.goldenRatio ^ 2 / c) =
        realInput40GroundEntropy c := by
    linarith [hfreeze.2.2]
  have halpha := paper_real_input_40_alpha_max
  exact ⟨hendpoint, halpha.2.2.2.2, rfl, rfl, rfl⟩

end Omega.Zeta
