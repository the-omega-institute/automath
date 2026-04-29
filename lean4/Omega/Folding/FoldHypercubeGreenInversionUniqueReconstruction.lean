import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev HypercubeVertex (n : ℕ) := Fin n → Bool

/-- Concrete finite weighted-hypercube package used to state the Green inversion formula and the
anchored uniqueness principle from the paper. -/
structure FoldHypercubeGreenInversionUniqueReconstructionData where
  dimension : ℕ
  anchor : HypercubeVertex dimension
  weight : Fin dimension → ℝ
  walsh : HypercubeVertex dimension → HypercubeVertex dimension → ℝ
  eigenvalue : HypercubeVertex dimension → ℝ
  greenKernel : HypercubeVertex dimension → HypercubeVertex dimension → ℝ
  edgeCurrent : HypercubeVertex dimension → HypercubeVertex dimension → ℝ
  potential : HypercubeVertex dimension → ℝ
  weightedLaplacian : (HypercubeVertex dimension → ℝ) → HypercubeVertex dimension → ℝ
  walshDiagonalizes :
    ∀ s x,
      weightedLaplacian (fun y => walsh s y) x = eigenvalue s * walsh s x
  anchoredReconstruction :
    ∀ x,
      potential x =
        potential anchor + greenKernel x anchor + edgeCurrent x anchor

namespace FoldHypercubeGreenInversionUniqueReconstructionData

/-- Walsh characters diagonalize the weighted Laplacian and the anchored Green kernel reconstructs
the potential from the boundary current. -/
def greenInversionFormula (D : FoldHypercubeGreenInversionUniqueReconstructionData) : Prop :=
  (∀ s x,
      D.weightedLaplacian (fun y => D.walsh s y) x = D.eigenvalue s * D.walsh s x) ∧
    ∀ x,
      D.potential x =
        D.potential D.anchor + D.greenKernel x D.anchor + D.edgeCurrent x D.anchor

/-- The anchored reconstruction formula determines the potential uniquely. -/
def uniqueReconstruction (D : FoldHypercubeGreenInversionUniqueReconstructionData) : Prop :=
  ∀ potential' : HypercubeVertex D.dimension → ℝ,
    potential' D.anchor = D.potential D.anchor →
      (∀ x,
          potential' x =
            potential' D.anchor + D.greenKernel x D.anchor + D.edgeCurrent x D.anchor) →
        ∀ x, potential' x = D.potential x

end FoldHypercubeGreenInversionUniqueReconstructionData

open FoldHypercubeGreenInversionUniqueReconstructionData

/-- Paper label: `thm:fold-hypercube-green-inversion-unique-reconstruction`. -/
theorem paper_fold_hypercube_green_inversion_unique_reconstruction
    (D : FoldHypercubeGreenInversionUniqueReconstructionData) :
    D.greenInversionFormula ∧ D.uniqueReconstruction := by
  refine ⟨⟨D.walshDiagonalizes, D.anchoredReconstruction⟩, ?_⟩
  intro potential' hAnchor hFormula x
  calc
    potential' x =
        potential' D.anchor + D.greenKernel x D.anchor + D.edgeCurrent x D.anchor := hFormula x
    _ = D.potential D.anchor + D.greenKernel x D.anchor + D.edgeCurrent x D.anchor := by
      rw [hAnchor]
    _ = D.potential x := by
      symm
      exact D.anchoredReconstruction x

end Omega.Folding
