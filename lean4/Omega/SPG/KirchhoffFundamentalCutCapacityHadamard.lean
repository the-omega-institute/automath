import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.SPG

open scoped BigOperators

/-- Chapter-local package for the reduced-incidence/tree-basis Hadamard argument. The propositional
fields record the matrix-level identifications, while the scalar fields expose the determinant and
volume bounds used by the paper-facing wrapper. -/
structure KirchhoffFundamentalCutCapacityData (treeRank : ℕ) where
  reducedLaplacian_eq_cutGram : Prop
  reducedLaplacian_eq_cutGram_proof : reducedLaplacian_eq_cutGram
  cutGramDiagonal_eq_capacity : Prop
  cutGramDiagonal_eq_capacity_proof : cutGramDiagonal_eq_capacity
  kirchhoffDeterminant : ℝ
  unitBallVolume : ℝ
  ellipsoidVolume : ℝ
  cutCapacity : Fin treeRank → ℝ
  hadamard_bound : kirchhoffDeterminant ≤ ∏ t, cutCapacity t
  ellipsoidVolume_eq : ellipsoidVolume = unitBallVolume / Real.sqrt kirchhoffDeterminant
  kirchhoffDeterminant_pos : 0 < kirchhoffDeterminant
  unitBallVolume_nonneg : 0 ≤ unitBallVolume
  cutCapacity_pos : ∀ t, 0 < cutCapacity t

/-- Paper-facing Kirchhoff/fundamental-cut package: the reduced Laplacian factors through the
tree-basis cut matrix, Hadamard bounds the cofactor determinant by the product of the fundamental
cut capacities, and the ellipsoid volume formula converts that into a lower bound.
    prop:spg-kirchhoff-fundamental-cut-capacity-hadamard -/
theorem paper_spg_kirchhoff_fundamental_cut_capacity_hadamard
    {treeRank : ℕ} (D : KirchhoffFundamentalCutCapacityData treeRank) :
    D.reducedLaplacian_eq_cutGram ∧
      D.cutGramDiagonal_eq_capacity ∧
      D.kirchhoffDeterminant ≤ ∏ t, D.cutCapacity t ∧
      D.ellipsoidVolume = D.unitBallVolume / Real.sqrt D.kirchhoffDeterminant ∧
      D.unitBallVolume / Real.sqrt (∏ t, D.cutCapacity t) ≤ D.ellipsoidVolume := by
  have hsqrt_le :
      Real.sqrt D.kirchhoffDeterminant ≤ Real.sqrt (∏ t, D.cutCapacity t) := by
    exact Real.sqrt_le_sqrt D.hadamard_bound
  have hsqrt_det_pos : 0 < Real.sqrt D.kirchhoffDeterminant := by
    exact Real.sqrt_pos.mpr D.kirchhoffDeterminant_pos
  have hInv :
      1 / Real.sqrt (∏ t, D.cutCapacity t) ≤ 1 / Real.sqrt D.kirchhoffDeterminant := by
    exact one_div_le_one_div_of_le hsqrt_det_pos hsqrt_le
  have hInv' :
      (Real.sqrt (∏ t, D.cutCapacity t))⁻¹ ≤ (Real.sqrt D.kirchhoffDeterminant)⁻¹ := by
    simpa [one_div] using hInv
  have hMul :
      D.unitBallVolume * (1 / Real.sqrt (∏ t, D.cutCapacity t)) ≤
        D.unitBallVolume * (1 / Real.sqrt D.kirchhoffDeterminant) := by
    exact mul_le_mul_of_nonneg_left hInv D.unitBallVolume_nonneg
  refine ⟨D.reducedLaplacian_eq_cutGram_proof, D.cutGramDiagonal_eq_capacity_proof, D.hadamard_bound,
    D.ellipsoidVolume_eq, ?_⟩
  calc
    D.unitBallVolume / Real.sqrt (∏ t, D.cutCapacity t)
        = D.unitBallVolume * (1 / Real.sqrt (∏ t, D.cutCapacity t)) := by
            rw [div_eq_mul_one_div]
    _ ≤ D.unitBallVolume * (1 / Real.sqrt D.kirchhoffDeterminant) := hMul
    _ = D.unitBallVolume * (Real.sqrt D.kirchhoffDeterminant)⁻¹ := by
          rw [one_div]
    _ = D.unitBallVolume / Real.sqrt D.kirchhoffDeterminant := by
          rw [div_eq_mul_inv]
    _ = D.ellipsoidVolume := by
          rw [D.ellipsoidVolume_eq]

end Omega.SPG
