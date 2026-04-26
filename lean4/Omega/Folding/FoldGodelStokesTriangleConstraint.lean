import Mathlib.Tactic
import Omega.Folding.CoarsegrainingQuadraticStokesAreaRigidity
import Omega.Folding.FoldCoarsegrainingGodelLengthSquareArea

namespace Omega.Folding

noncomputable section

/-- Paper label: `cor:fold-godel-stokes-triangle-constraint`. The already-formalized
coarsegraining Gödel square-length estimate and the quadratic Stokes-area inequality together give
the two bounds asserted in the paper notation. -/
theorem paper_fold_godel_stokes_triangle_constraint
    {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (f : Omega.Word n → X) (p : Fin n → ℕ) :
    (∑ x, (hypercubeGodelLength (coarsegrainingFiber f x) p) ^ 2 ≤
        (2 : ℝ) ^ n * coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ)) *
          ∑ i : Fin n, (Real.log (p i)) ^ 2) ∧
      coarsegrainingQuadraticBiasSum f (fun _ => (1 : ℝ)) ≤
        (2 : ℝ) ^ n * coarsegrainingWeightedCutCount f (fun _ => (1 : ℝ)) := by
  refine ⟨paper_fold_coarsegraining_godel_length_square_area f p, ?_⟩
  simpa using
    (paper_fold_coarsegraining_quadratic_stokes_area_rigidity
      (f := f) (w := fun _ => (1 : ℝ)) (hw := fun _ => by norm_num)).1

end

end Omega.Folding
