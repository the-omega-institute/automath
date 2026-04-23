import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.Basic
import Omega.Folding.FoldResonanceLadderFibLucLimits
import Omega.Zeta.XiGoldenW1TrueTwoPhaseLimit

open Filter
open scoped goldenRatio

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zi-fibonacci-transport-resonance-incompatibility`.
The odd Fibonacci `W₁` transport constant is strictly positive, while the resonance ladder has a
unit positive Fibonacci/Lucas witness at level `k = 0`; hence the product carries a positive
constant lower envelope, so its liminf is positive as well. -/
theorem paper_xi_time_part9zi_fibonacci_transport_resonance_incompatibility :
    let resonance : ℝ :=
      |Real.cos
          (Real.pi * Omega.Folding.fold_resonance_ladder_fibonacci_directional_limit_alpha 2 1 /
            Real.goldenRatio ^ 0)| *
        |Real.cos
          (Real.pi * Omega.Folding.fold_resonance_ladder_fibonacci_directional_limit_beta 2 1 /
            Real.goldenRatio ^ 0)|
    Omega.Kronecker.goldenOddScaledLimitConstant =
        (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15 ∧
      resonance = 1 ∧
      0 < Omega.Kronecker.goldenOddScaledLimitConstant * resonance ∧
      0 <
        liminf
          (fun _ : ℕ => Omega.Kronecker.goldenOddScaledLimitConstant * resonance)
          atTop := by
  dsimp
  rcases paper_xi_golden_w1_true_two_phase_limit with ⟨_, _, hodd, _, _, _⟩
  rcases Omega.Folding.paper_fold_resonance_ladder_fib_luc_limits with
    ⟨_, _, _, _, _, _, _, _, _, hLucCos⟩
  have hresonance : |Real.cos (Real.pi / Real.goldenRatio ^ 0)| ^ 2 = (1 : ℝ) := by
    simp [Real.cos_pi]
  have hres : |Real.cos
        (Real.pi * Omega.Folding.fold_resonance_ladder_fibonacci_directional_limit_alpha 2 1 /
          Real.goldenRatio ^ 0)| *
      |Real.cos
        (Real.pi * Omega.Folding.fold_resonance_ladder_fibonacci_directional_limit_beta 2 1 /
          Real.goldenRatio ^ 0)| = (1 : ℝ) := by
    simpa using (hLucCos 0).trans hresonance
  have hodd_pos : 0 < Omega.Kronecker.goldenOddScaledLimitConstant := by
    rw [hodd]
    have hsqrt5_pos : 0 < (Real.sqrt 5 : ℝ) := by positivity
    have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := ne_of_gt hsqrt5_pos
    field_simp [hsqrt5_ne]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  have hprod_pos : 0 < Omega.Kronecker.goldenOddScaledLimitConstant * 1 := by
    simpa using hodd_pos
  have hliminf :
      liminf (fun _ : ℕ => Omega.Kronecker.goldenOddScaledLimitConstant * 1) atTop =
        Omega.Kronecker.goldenOddScaledLimitConstant * 1 := by
    simp
  have hprod_pos_res :
      0 < Omega.Kronecker.goldenOddScaledLimitConstant *
        (|Real.cos
            (Real.pi *
                Omega.Folding.fold_resonance_ladder_fibonacci_directional_limit_alpha 2 1 /
              Real.goldenRatio ^ 0)| *
          |Real.cos
            (Real.pi *
                Omega.Folding.fold_resonance_ladder_fibonacci_directional_limit_beta 2 1 /
              Real.goldenRatio ^ 0)|) := by
    rw [hres]
    simpa using hprod_pos
  refine ⟨hodd, hres, hprod_pos_res, ?_⟩
  · rw [hres, hliminf]
    simpa using hprod_pos

end Omega.Zeta
