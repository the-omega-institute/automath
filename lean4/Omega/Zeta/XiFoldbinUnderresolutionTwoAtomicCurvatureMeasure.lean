import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Folding.FoldBinDegeneracyTailCapacityKinks

namespace Omega.Zeta

noncomputable section

/-- Paper label: `thm:xi-foldbin-underresolution-two-atomic-curvature-measure`. -/
theorem paper_xi_foldbin_underresolution_two_atomic_curvature_measure
    (D : Omega.Folding.FoldBinDegeneracyTailCapacityKinksData) :
    D.tailLimit ∧ D.capacityLimit ∧
      (∀ s : ℝ, s < Real.goldenRatio⁻¹ →
        Omega.Folding.foldBinDegeneracyTailLimitFn s = 1) ∧
      (∀ s : ℝ, Real.goldenRatio⁻¹ < s → s < 1 →
        Omega.Folding.foldBinDegeneracyTailLimitFn s = Real.goldenRatio⁻¹) ∧
      (∀ s : ℝ, 1 < s → Omega.Folding.foldBinDegeneracyTailLimitFn s = 0) := by
  have hlimits := Omega.Folding.paper_fold_bin_degeneracy_tail_capacity_kinks D
  refine ⟨hlimits.1, hlimits.2, ?_, ?_, ?_⟩
  · intro s hs
    unfold Omega.Folding.foldBinDegeneracyTailLimitFn
    exact if_pos hs.le
  · intro s hs_phi hs_one
    unfold Omega.Folding.foldBinDegeneracyTailLimitFn
    rw [if_neg (not_le_of_gt hs_phi), if_pos hs_one.le]
  · intro s hs_one
    unfold Omega.Folding.foldBinDegeneracyTailLimitFn
    have hphi_lt_one : (Real.goldenRatio⁻¹ : ℝ) < 1 := by
      simpa using inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
    rw [if_neg (not_le_of_gt (lt_trans hphi_lt_one hs_one)),
      if_neg (not_le_of_gt hs_one)]

end

end Omega.Zeta
