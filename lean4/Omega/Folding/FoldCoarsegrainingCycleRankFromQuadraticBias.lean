import Mathlib.Tactic
import Omega.Folding.CoarsegrainingQuadraticStokesAreaRigidity
import Omega.SPG.BoundaryMultigraphH1Cdim

namespace Omega.Folding

noncomputable section

/-- Paper label: `cor:fold-coarsegraining-cycle-rank-from-quadratic-bias`. -/
theorem paper_fold_coarsegraining_cycle_rank_from_quadratic_bias
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (f : Omega.Word n → X) (A c : Int)
    (hA : (A : ℝ) = coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ))) :
    (Omega.SPG.boundaryMultigraphH1Cdim A (Fintype.card X : Int) c : ℝ) ≥
      coarsegrainingQuadraticBiasSum f (fun _ => (1 : ℝ)) / (2 : ℝ) ^ n -
        (Fintype.card X : ℝ) + (c : ℝ) := by
  have hquad :
      coarsegrainingQuadraticBiasSum f (fun _ => (1 : ℝ)) ≤
        (2 : ℝ) ^ n * coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ)) :=
    (paper_fold_coarsegraining_quadratic_stokes_area_rigidity f (fun _ => (1 : ℝ))
      (fun _ => by norm_num)).1
  have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
  have hbias :
      coarsegrainingQuadraticBiasSum f (fun _ => (1 : ℝ)) / (2 : ℝ) ^ n ≤
        coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ)) := by
    rw [_root_.div_le_iff₀ hpow_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hquad
  have hbias' :
      coarsegrainingQuadraticBiasSum f (fun _ => (1 : ℝ)) / (2 : ℝ) ^ n ≤ (A : ℝ) := by
    simpa [hA] using hbias
  have hrank :
      (Omega.SPG.boundaryMultigraphH1Cdim A (Fintype.card X : Int) c : ℝ) =
        (A : ℝ) - (Fintype.card X : ℝ) + (c : ℝ) := by
    rw [Omega.SPG.paper_hypercube_boundary_multigraph_h1_cdim]
    norm_num
  linarith

end

end Omega.Folding
