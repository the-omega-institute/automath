import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Omega.SyncKernelWeighted.RealInputDigitwiseSumLayer

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The product-shift entropy coming from two independent golden-mean inputs. -/
def real_input_digitwise_sum_topological_degeneracy_product_entropy : ℝ :=
  Real.log (goldenRatio ^ 2)

/-- The Perron root of the three-state digitwise-sum SFT. -/
def real_input_digitwise_sum_topological_degeneracy_image_radius : ℝ :=
  1 + 2 * Real.cos (2 * Real.pi / 7)

/-- The image-shift entropy of the digitwise-sum layer. -/
def real_input_digitwise_sum_topological_degeneracy_image_entropy : ℝ :=
  Real.log real_input_digitwise_sum_topological_degeneracy_image_radius

/-- The exponential degeneracy rate, i.e. the entropy drop from the product shift to its image. -/
def real_input_digitwise_sum_topological_degeneracy_entropy_gap : ℝ :=
  real_input_digitwise_sum_topological_degeneracy_product_entropy -
    real_input_digitwise_sum_topological_degeneracy_image_entropy

/-- Compact paper-facing package for the product entropy, image entropy, and their difference. -/
def real_input_digitwise_sum_topological_degeneracy_statement : Prop :=
  real_input_digitwise_sum_topological_degeneracy_product_entropy =
      Real.log (goldenRatio ^ 2) ∧
    real_input_digitwise_sum_topological_degeneracy_image_entropy =
      Real.log real_input_digitwise_sum_topological_degeneracy_image_radius ∧
    real_input_digitwise_sum_topological_degeneracy_entropy_gap =
      Real.log (goldenRatio ^ 2) -
        Real.log real_input_digitwise_sum_topological_degeneracy_image_radius

/-- Paper label: `cor:real-input-digitwise-sum-topological-degeneracy`. -/
theorem paper_real_input_digitwise_sum_topological_degeneracy :
    real_input_digitwise_sum_topological_degeneracy_statement := by
  refine ⟨rfl, rfl, ?_⟩
  simp [real_input_digitwise_sum_topological_degeneracy_entropy_gap,
    real_input_digitwise_sum_topological_degeneracy_product_entropy,
    real_input_digitwise_sum_topological_degeneracy_image_entropy]

end

end Omega.SyncKernelWeighted
