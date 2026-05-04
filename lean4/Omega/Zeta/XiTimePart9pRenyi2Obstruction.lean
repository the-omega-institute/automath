import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9pChi2RanktwoResonantFloor

namespace Omega.Zeta

open Omega.Folding

noncomputable section

/-- Collision scale against the uniform law on the bin-fold fiber. -/
def xi_time_part9p_renyi2_obstruction_collision_scale (m : ℕ) : ℝ :=
  (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ)

/-- Order-`2` Rényi divergence against the uniform law, written through collision scale. -/
def xi_time_part9p_renyi2_obstruction_divergence (m : ℕ) : ℝ :=
  Real.log (xi_time_part9p_renyi2_obstruction_collision_scale m)

/-- The retained rank-two Fibonacci resonance obstruction constant. -/
def xi_time_part9p_renyi2_obstruction_positive_floor (Cphi : ℝ) : ℝ :=
  xi_time_part9p_chi2_ranktwo_resonant_floor_floor Cphi

/-- Paper-facing concrete Rényi-`2` obstruction statement. -/
def xi_time_part9p_renyi2_obstruction_statement : Prop :=
  (∀ m : ℕ,
      xi_time_part9p_renyi2_obstruction_divergence m =
        Real.log (xi_time_part9p_renyi2_obstruction_collision_scale m)) ∧
    (∀ m : ℕ, ∀ Cphi : ℝ,
      (((Omega.Folding.foldBinChi2Col m : ℚ) : ℝ) + 1 =
          xi_time_part9p_renyi2_obstruction_collision_scale m) ∧
        0 < xi_time_part9p_renyi2_obstruction_positive_floor Cphi)

/-- Paper label: `thm:xi-time-part9p-renyi2-obstruction`. -/
theorem paper_xi_time_part9p_renyi2_obstruction :
    xi_time_part9p_renyi2_obstruction_statement := by
  refine ⟨?_, ?_⟩
  · intro m
    rfl
  · intro m Cphi
    have hrank := paper_xi_time_part9p_chi2_ranktwo_resonant_floor m Cphi
    exact
      ⟨by
        simpa [xi_time_part9p_renyi2_obstruction_collision_scale,
          xi_time_part9p_chi2_ranktwo_resonant_floor_collision_mass] using hrank.1,
        by
          simpa [xi_time_part9p_renyi2_obstruction_positive_floor] using hrank.2⟩

end

end Omega.Zeta
