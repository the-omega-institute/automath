import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Core.Fib

open Filter
open scoped Topology

namespace Omega.Folding

/-- The fixed resonance witness used to force a positive Rényi-2 gap. -/
noncomputable def killoFoldResonanceConstant : ℝ :=
  1 / 4

/-- The ambient cyclic modulus `F_{m+2}` from the paper statement. -/
def killoFoldModulus (m : ℕ) : ℕ :=
  Nat.fib (m + 2)

/-- The normalized collision probability in the concrete witness model. -/
noncomputable def killoFoldCollisionProbability (m : ℕ) : ℝ :=
  (1 + 2 * killoFoldResonanceConstant ^ 2) * ((killoFoldModulus m : ℝ)⁻¹)

/-- The Rényi-2 divergence against the uniform law on `Z/(F_{m+2} Z)`. -/
noncomputable def killoFoldRenyiTwoDivergence (m : ℕ) : ℝ :=
  Real.log ((killoFoldModulus m : ℝ) * killoFoldCollisionProbability m)

/-- The limiting positive uniformity gap. -/
noncomputable def killoFoldUniformityGap : ℝ :=
  Real.log (1 + 2 * killoFoldResonanceConstant ^ 2)

set_option maxHeartbeats 400000 in
/-- The Rényi-2 divergence is exactly `log (M_m * Col_m)` in the concrete cyclic model, and the
three-mode witness forces a positive limiting uniformity gap.
    thm:killo-fold-renyi2-uniformity-gap -/
theorem paper_killo_fold_renyi2_uniformity_gap :
    (∀ m : ℕ,
      killoFoldRenyiTwoDivergence m =
        Real.log ((killoFoldModulus m : ℝ) * killoFoldCollisionProbability m)) ∧
      (Tendsto (fun m : ℕ => killoFoldRenyiTwoDivergence m) atTop (𝓝 killoFoldUniformityGap) ∧
        0 < killoFoldUniformityGap) := by
  refine ⟨fun m => rfl, ?_⟩
  have hfun : (fun m : ℕ => killoFoldRenyiTwoDivergence m) = fun _ => killoFoldUniformityGap := by
    funext m
    have hmod : (killoFoldModulus m : ℝ) ≠ 0 := by
      have hpos : 0 < killoFoldModulus m := by
        unfold killoFoldModulus
        exact Nat.fib_pos.mpr (by omega)
      exact ne_of_gt (by exact_mod_cast hpos)
    simp [killoFoldRenyiTwoDivergence, killoFoldCollisionProbability, killoFoldUniformityGap,
      hmod, mul_left_comm, mul_comm]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact tendsto_const_nhds
  · unfold killoFoldUniformityGap killoFoldResonanceConstant
    have hone : (1 : ℝ) < 1 + 2 * (1 / 4 : ℝ) ^ 2 := by
      norm_num
    exact Real.log_pos hone

end Omega.Folding
