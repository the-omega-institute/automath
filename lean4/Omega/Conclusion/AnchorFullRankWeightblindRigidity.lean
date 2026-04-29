import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Omega.Zeta.XiBasepointScanFullRankWeightGaugeInvariance

namespace Omega.Conclusion

open Matrix

/-- The pole-side evaluation vector `u(x)`. -/
noncomputable def xiBasepointPoleVector {kappa : ℕ}
    (D : Omega.Zeta.XiBasepointAnchorData kappa kappa) (x : ℂ) : Fin kappa → ℂ :=
  fun j => 1 / (x - D.poles j)

/-- The interpolation vector obtained from the Cauchy matrix alone. -/
noncomputable def xiBasepointInterpolationVector {kappa : ℕ}
    (D : Omega.Zeta.XiBasepointAnchorData kappa kappa) (x : ℂ) : Fin kappa → ℂ :=
  D.anchorCauchyMatrix.transpose⁻¹.mulVec (xiBasepointPoleVector D x)

/-- The product of the positive anchor weights. -/
def xiBasepointWeightProduct {kappa : ℕ}
    (D : Omega.Zeta.XiBasepointAnchorData kappa kappa) : ℝ :=
  ∏ j, D.weights j

/-- The weight-blind score controlling full-rank optimality. -/
noncomputable def xiBasepointWeightBlindScore {kappa : ℕ}
    (D : Omega.Zeta.XiBasepointAnchorData kappa kappa) : ℝ :=
  ‖D.anchorCauchyMatrix.det‖ ^ (2 : ℕ)

/-- Comparison by Gram determinant. -/
def xiBasepointGramBeats {kappa : ℕ}
    (D E : Omega.Zeta.XiBasepointAnchorData kappa kappa) : Prop :=
  ‖D.anchorGram.det‖ ≤ ‖E.anchorGram.det‖

/-- Comparison by the weight-blind Cauchy score. -/
def xiBasepointWeightBlindBeats {kappa : ℕ}
    (D E : Omega.Zeta.XiBasepointAnchorData kappa kappa) : Prop :=
  xiBasepointWeightBlindScore D ≤ xiBasepointWeightBlindScore E

private lemma xiBasepoint_weight_norm_product {kappa : ℕ}
    (D : Omega.Zeta.XiBasepointAnchorData kappa kappa) (hwt : ∀ j, 0 < D.weights j) :
    ‖((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ)‖ = xiBasepointWeightProduct D := by
  unfold xiBasepointWeightProduct
  rw [norm_prod]
  refine Finset.prod_congr rfl ?_
  intro j hj
  simp [Real.norm_eq_abs, abs_of_pos (hwt j)]

private lemma xiBasepoint_anchorGram_norm_factorization {kappa : ℕ}
    (D : Omega.Zeta.XiBasepointAnchorData kappa kappa)
    (hdet : D.anchorFrame.det ≠ 0) (hwt : ∀ j, 0 < D.weights j) :
    ‖D.anchorGram.det‖ = xiBasepointWeightProduct D * xiBasepointWeightBlindScore D := by
  obtain ⟨_, _, hfactor⟩ :=
    Omega.Zeta.paper_xi_basepoint_scan_full_rank_weight_gauge_invariance D hdet hwt
  unfold xiBasepointWeightBlindScore
  rw [hfactor, norm_mul, norm_pow, xiBasepoint_weight_norm_product D hwt]

/-- Paper label: `thm:conclusion-anchor-full-rank-weightblind-rigidity`. -/
theorem paper_conclusion_anchor_full_rank_weightblind_rigidity {kappa : ℕ} :
    (∀ D E : Omega.Zeta.XiBasepointAnchorData kappa kappa,
      D.poles = E.poles → D.anchors = E.anchors →
      ∀ x : ℂ, xiBasepointInterpolationVector D x = xiBasepointInterpolationVector E x) ∧
    (∀ D : Omega.Zeta.XiBasepointAnchorData kappa kappa,
      D.anchorFrame.det ≠ 0 → (∀ j, 0 < D.weights j) →
      D.anchorGram.det =
        ((∏ j, ((D.weights j : ℝ) : ℂ)) : ℂ) * D.anchorCauchyMatrix.det ^ (2 : ℕ)) ∧
    (∀ D E : Omega.Zeta.XiBasepointAnchorData kappa kappa,
      D.weights = E.weights →
      D.anchorFrame.det ≠ 0 →
      E.anchorFrame.det ≠ 0 →
      (∀ j, 0 < D.weights j) →
      (∀ j, 0 < E.weights j) →
      (xiBasepointGramBeats D E ↔ xiBasepointWeightBlindBeats D E)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro D E hpoles hanchors x
    have hCauchy : D.anchorCauchyMatrix = E.anchorCauchyMatrix := by
      ext i j
      simp [Omega.Zeta.XiBasepointAnchorData.anchorCauchyMatrix, hpoles, hanchors]
    have hPole : xiBasepointPoleVector D x = xiBasepointPoleVector E x := by
      ext j
      simp [xiBasepointPoleVector, hpoles]
    unfold xiBasepointInterpolationVector
    rw [hPole, hCauchy]
  · intro D hdet hwt
    exact (Omega.Zeta.paper_xi_basepoint_scan_full_rank_weight_gauge_invariance D hdet hwt).2.2
  · intro D E hweights hdetD hdetE hwtD hwtE
    have hDnorm := xiBasepoint_anchorGram_norm_factorization D hdetD hwtD
    have hEnorm := xiBasepoint_anchorGram_norm_factorization E hdetE hwtE
    have hprodEq : xiBasepointWeightProduct D = xiBasepointWeightProduct E := by
      simp [xiBasepointWeightProduct, hweights]
    have hprodPos : 0 < xiBasepointWeightProduct D := by
      unfold xiBasepointWeightProduct
      exact Finset.prod_pos fun j _ => hwtD j
    constructor
    · intro h
      have h' : xiBasepointWeightProduct D * xiBasepointWeightBlindScore D ≤
          xiBasepointWeightProduct D * xiBasepointWeightBlindScore E := by
        simpa [xiBasepointGramBeats, xiBasepointWeightBlindBeats, hDnorm, hEnorm, hprodEq] using h
      exact le_of_mul_le_mul_left h' hprodPos
    · intro h
      have h' : xiBasepointWeightProduct D * xiBasepointWeightBlindScore D ≤
          xiBasepointWeightProduct D * xiBasepointWeightBlindScore E := by
        exact mul_le_mul_of_nonneg_left h hprodPos.le
      simpa [xiBasepointGramBeats, xiBasepointWeightBlindBeats, hDnorm, hEnorm, hprodEq] using h'

end Omega.Conclusion
