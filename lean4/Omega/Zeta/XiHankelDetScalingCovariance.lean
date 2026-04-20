import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic
import Omega.Zeta.XiDepthHankelDeterminantVandermondeSquare

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Concrete finite-atomic data for the Hankel determinant scaling law. The raw atom weights are
`weights`, the unscaled depth parameters are `delta`, and `scale` is the renormalization
parameter. The nonvanishing assumptions keep the reciprocal nodes well-defined. -/
structure XiHankelDetScalingCovarianceData (k : Nat) where
  weights : Fin k → ℂ
  delta : Fin k → ℝ
  scale : ℝ
  baseDenom_ne_zero : ∀ j, 1 + delta j ≠ 0
  scaledDenom_ne_zero : ∀ j, 1 + scale * delta j ≠ 0

namespace XiHankelDetScalingCovarianceData

/-- The original reciprocal depth node `b_j = (1 + δ_j)⁻¹`. -/
noncomputable def baseNode {k : Nat} (D : XiHankelDetScalingCovarianceData k) (j : Fin k) : ℂ :=
  (((1 + D.delta j : ℝ) : ℂ))⁻¹

/-- The scaled reciprocal depth node `b̃_j = (1 + m δ_j)⁻¹`. -/
noncomputable def scaledNode {k : Nat} (D : XiHankelDetScalingCovarianceData k) (j : Fin k) : ℂ :=
  (((1 + D.scale * D.delta j : ℝ) : ℂ))⁻¹

/-- The single-node scaling ratio `(1 + δ_j) / (1 + m δ_j)`. -/
noncomputable def nodeRatio {k : Nat} (D : XiHankelDetScalingCovarianceData k) (j : Fin k) : ℂ :=
  (((1 + D.delta j : ℝ) : ℂ)) / (((1 + D.scale * D.delta j : ℝ) : ℂ))

/-- The rescaled atomic weight `w_j b_j`. -/
noncomputable def originalAtomicWeight {k : Nat} (D : XiHankelDetScalingCovarianceData k)
    (j : Fin k) : ℂ :=
  D.weights j * D.baseNode j

/-- The renormalized atomic weight `w_j b̃_j`. -/
noncomputable def scaledAtomicWeight {k : Nat} (D : XiHankelDetScalingCovarianceData k)
    (j : Fin k) : ℂ :=
  D.weights j * D.scaledNode j

/-- The pairwise scaling factor extracted from `b̃_j - b̃_i`. -/
noncomputable def pairScalingTerm {k : Nat} (D : XiHankelDetScalingCovarianceData k)
    (i j : Fin k) : ℂ :=
  (D.scale : ℂ) * D.nodeRatio i * D.nodeRatio j

/-- The original finite-atomic moment system `μ_n = Σ_j (w_j b_j) b_j^n`. -/
noncomputable def originalData {k : Nat} (D : XiHankelDetScalingCovarianceData k) :
    XiFiniteAtomicMomentData k where
  weights := D.originalAtomicWeight
  nodes := D.baseNode
  moments n := ∑ j, D.originalAtomicWeight j * D.baseNode j ^ n
  moments_eq _ := rfl

/-- The scaled finite-atomic moment system `μ̃_n = Σ_j (w_j b̃_j) b̃_j^n`. -/
noncomputable def scaledData {k : Nat} (D : XiHankelDetScalingCovarianceData k) :
    XiFiniteAtomicMomentData k where
  weights := D.scaledAtomicWeight
  nodes := D.scaledNode
  moments n := ∑ j, D.scaledAtomicWeight j * D.scaledNode j ^ n
  moments_eq _ := rfl

/-- Explicit covariance factor obtained by comparing the single-node weight rescaling with the
pairwise node-difference rescaling. This is the unsimplified product form of the paper's `J`. -/
noncomputable def scalingFactor {k : Nat} (D : XiHankelDetScalingCovarianceData k) : ℂ :=
  (∏ j, D.nodeRatio j) * (∏ i, ∏ j ∈ Finset.Ioi i, D.pairScalingTerm i j) ^ 2

/-- The scaled Hankel determinant differs from the original one by the explicit factor
`scalingFactor`. -/
def scalingCovariance {k : Nat} (D : XiHankelDetScalingCovarianceData k) : Prop :=
  D.scaledData.hankel.det = D.originalData.hankel.det * D.scalingFactor

lemma baseNode_mul_nodeRatio {k : Nat} (D : XiHankelDetScalingCovarianceData k) (j : Fin k) :
    D.baseNode j * D.nodeRatio j = D.scaledNode j := by
  unfold baseNode nodeRatio scaledNode
  have hbase : (((1 + D.delta j : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast D.baseDenom_ne_zero j
  have hscaled : (((1 + D.scale * D.delta j : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast D.scaledDenom_ne_zero j
  field_simp [hbase, hscaled]

lemma originalAtomicWeight_mul_nodeRatio {k : Nat} (D : XiHankelDetScalingCovarianceData k)
    (j : Fin k) :
    D.originalAtomicWeight j * D.nodeRatio j = D.scaledAtomicWeight j := by
  simp [originalAtomicWeight, scaledAtomicWeight, mul_assoc, D.baseNode_mul_nodeRatio]

lemma pairwise_scaledNode_sub {k : Nat} (D : XiHankelDetScalingCovarianceData k)
    (i j : Fin k) :
    D.scaledNode j - D.scaledNode i =
      D.pairScalingTerm i j * (D.baseNode j - D.baseNode i) := by
  unfold scaledNode pairScalingTerm nodeRatio baseNode
  have hbase_i : (((1 + D.delta i : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast D.baseDenom_ne_zero i
  have hbase_j : (((1 + D.delta j : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast D.baseDenom_ne_zero j
  have hscaled_i : (((1 + D.scale * D.delta i : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast D.scaledDenom_ne_zero i
  have hscaled_j : (((1 + D.scale * D.delta j : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast D.scaledDenom_ne_zero j
  field_simp [hbase_i, hbase_j, hscaled_i, hscaled_j]
  have hs :
      ((((1 + D.scale * D.delta i) - (1 + D.scale * D.delta j) : ℝ) : ℂ)) =
        (((D.scale * (1 + D.delta i) - D.scale * (1 + D.delta j) : ℝ) : ℂ)) := by
    congr 1
    ring
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add] using hs

lemma prod_scaledAtomicWeight {k : Nat} (D : XiHankelDetScalingCovarianceData k) :
    (∏ j, D.scaledAtomicWeight j) =
      (∏ j, D.originalAtomicWeight j) * ∏ j, D.nodeRatio j := by
  calc
    (∏ j, D.scaledAtomicWeight j) = ∏ j, D.originalAtomicWeight j * D.nodeRatio j := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      symm
      exact D.originalAtomicWeight_mul_nodeRatio j
    _ = (∏ j, D.originalAtomicWeight j) * ∏ j, D.nodeRatio j := by
      simp_rw [Finset.prod_mul_distrib]

lemma vandermonde_det_scaled {k : Nat} (D : XiHankelDetScalingCovarianceData k) :
    (Matrix.vandermonde D.scaledNode).det =
      (Matrix.vandermonde D.baseNode).det * (∏ i, ∏ j ∈ Finset.Ioi i, D.pairScalingTerm i j) := by
  rw [Matrix.det_vandermonde, Matrix.det_vandermonde]
  calc
    (∏ i, ∏ j ∈ Finset.Ioi i, (D.scaledNode j - D.scaledNode i)) =
        ∏ i, ∏ j ∈ Finset.Ioi i, D.pairScalingTerm i j * (D.baseNode j - D.baseNode i) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          refine Finset.prod_congr rfl ?_
          intro j hj
          exact D.pairwise_scaledNode_sub i j
    _ = (∏ i, ∏ j ∈ Finset.Ioi i, (D.baseNode j - D.baseNode i)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, D.pairScalingTerm i j) := by
          simp_rw [Finset.prod_mul_distrib]
          ac_rfl

end XiHankelDetScalingCovarianceData

open XiHankelDetScalingCovarianceData

set_option maxHeartbeats 400000 in
/-- The finite-atomic Hankel determinant is covariant under depth rescaling: the scaled Hankel
block differs from the original one by the explicit multiplicative factor extracted from the
single-node weight rescaling and the pairwise node-difference rescaling.
    prop:xi-hankel-det-scaling-covariance -/
theorem paper_xi_hankel_det_scaling_covariance (k : Nat)
    (D : XiHankelDetScalingCovarianceData k) : D.scalingCovariance := by
  unfold XiHankelDetScalingCovarianceData.scalingCovariance
  have hOrig :=
    (paper_xi_depth_hankel_determinant_vandermonde_square k D.originalData).2
  have hScaled :=
    (paper_xi_depth_hankel_determinant_vandermonde_square k D.scaledData).2
  have hOrig' :
      ((∏ j, D.originalAtomicWeight j) * (Matrix.vandermonde D.baseNode).det ^ 2) =
        D.originalData.hankel.det := by
    simpa [XiHankelDetScalingCovarianceData.originalData] using hOrig.symm
  calc
    D.scaledData.hankel.det =
        (∏ j, D.scaledAtomicWeight j) * (Matrix.vandermonde D.scaledNode).det ^ 2 := by
          simpa [XiHankelDetScalingCovarianceData.originalData,
            XiHankelDetScalingCovarianceData.scaledData] using hScaled
    _ = ((∏ j, D.originalAtomicWeight j) * ∏ j, D.nodeRatio j) *
          ((Matrix.vandermonde D.baseNode).det *
            (∏ i, ∏ j ∈ Finset.Ioi i, D.pairScalingTerm i j)) ^ 2 := by
          rw [D.prod_scaledAtomicWeight, D.vandermonde_det_scaled]
    _ = ((∏ j, D.originalAtomicWeight j) * (Matrix.vandermonde D.baseNode).det ^ 2) *
          ((∏ j, D.nodeRatio j) * (∏ i, ∏ j ∈ Finset.Ioi i, D.pairScalingTerm i j) ^ 2) := by
          ring
    _ = D.originalData.hankel.det * ((∏ j, D.nodeRatio j) *
          (∏ i, ∏ j ∈ Finset.Ioi i, D.pairScalingTerm i j) ^ 2) := by
          rw [hOrig']
    _ = D.originalData.hankel.det * D.scalingFactor := by
          rfl

end Omega.Zeta
