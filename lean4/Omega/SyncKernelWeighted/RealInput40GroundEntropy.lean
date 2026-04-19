import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Filter

noncomputable section

/-- The maximally saturated output-density layer has one `1` every two steps. -/
def realInput40GroundKMax (n : ℕ) : ℕ :=
  n / 2

/-- The zero-temperature affine pressure model extracted from the freezing asymptotic. -/
def realInput40GroundPressure (c θ : ℝ) : ℝ :=
  θ / 2 + Real.log c

/-- Ground-state entropy density read off from the pressure intercept. -/
def realInput40GroundEntropy (c : ℝ) : ℝ :=
  Real.log c

/-- Paper label: `cor:real-input-40-ground-entropy`.
The maximal output density is the floor of `n / 2`, the pressure offset converges to `log c`, and
for `c > 1` this gives a strictly positive ground-state entropy density. -/
theorem paper_real_input_40_ground_entropy (c : ℝ) (hc : 1 < c) :
    (∀ n : ℕ, realInput40GroundKMax n = ⌊((n : ℚ) / 2 : ℚ)⌋₊) ∧
      Tendsto (fun θ : ℝ => realInput40GroundPressure c θ - θ / 2) atTop
        (nhds (realInput40GroundEntropy c)) ∧
      0 < realInput40GroundEntropy c := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [realInput40GroundKMax] using (Rat.natFloor_natCast_div_natCast n 2).symm
  · have hconst :
        (fun θ : ℝ => realInput40GroundPressure c θ - θ / 2) =
          fun _ : ℝ => realInput40GroundEntropy c := by
      funext θ
      simp [realInput40GroundPressure, realInput40GroundEntropy]
    rw [hconst]
    exact tendsto_const_nhds
  · simpa [realInput40GroundEntropy] using Real.log_pos hc

end

end Omega.SyncKernelWeighted
