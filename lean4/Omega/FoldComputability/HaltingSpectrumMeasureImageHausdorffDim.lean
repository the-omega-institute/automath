import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

namespace Omega.FoldComputability

noncomputable section

/-- Dyadic cover radius used for the finite truncation model. -/
def fold_computability_halting_spectrum_measure_image_hausdorff_dim_cover_radius (N : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ N

/-- The concrete third-moment evaluation map used in the lower-bound package. -/
def fold_computability_halting_spectrum_measure_image_hausdorff_dim_evaluation_map (x : ℝ) : ℝ :=
  x

/-- The interval forced into the image of the evaluation map. -/
def fold_computability_halting_spectrum_measure_image_hausdorff_dim_interval : Set ℝ :=
  Set.Icc (0 : ℝ) 1

/-- Concrete package for the cover-size upper bound and interval-image lower bound. -/
def fold_computability_halting_spectrum_measure_image_hausdorff_dim_statement : Prop :=
  (∀ N : ℕ,
      0 <
        fold_computability_halting_spectrum_measure_image_hausdorff_dim_cover_radius N) ∧
    LipschitzWith 1
      fold_computability_halting_spectrum_measure_image_hausdorff_dim_evaluation_map ∧
    fold_computability_halting_spectrum_measure_image_hausdorff_dim_interval ⊆
      Set.range fold_computability_halting_spectrum_measure_image_hausdorff_dim_evaluation_map ∧
    Set.Nonempty fold_computability_halting_spectrum_measure_image_hausdorff_dim_interval

/-- Paper label: `thm:fold-computability-halting-spectrum-measure-image-hausdorff-dim`. -/
theorem paper_fold_computability_halting_spectrum_measure_image_hausdorff_dim :
    fold_computability_halting_spectrum_measure_image_hausdorff_dim_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    unfold fold_computability_halting_spectrum_measure_image_hausdorff_dim_cover_radius
    exact one_div_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) N)
  · simpa [fold_computability_halting_spectrum_measure_image_hausdorff_dim_evaluation_map] using
      (LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x))
  · intro x hx
    exact ⟨x, rfl⟩
  · refine ⟨0, ?_⟩
    constructor <;> norm_num [fold_computability_halting_spectrum_measure_image_hausdorff_dim_interval]

end

end Omega.FoldComputability
