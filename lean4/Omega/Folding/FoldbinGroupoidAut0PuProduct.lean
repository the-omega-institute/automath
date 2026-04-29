import Mathlib.Tactic
import Omega.Folding.FoldBinM6FiberHist

namespace Omega.Folding

/-- The audited multiplicity of connected `PU(d)` factors in the foldbin identity component. -/
def foldbin_groupoid_aut0_pu_product_connected_factor_count (d : ℕ) : ℕ :=
  cBinFiberHist 6 d

/-- Permutations of equal-size matrix blocks are discrete and do not contribute to the identity
component. -/
def foldbin_groupoid_aut0_pu_product_identity_component_permutation_rank (_d : ℕ) : ℕ :=
  0

/-- The total number of connected projective-unitary factors in the audited product decomposition. -/
def foldbin_groupoid_aut0_pu_product_total_connected_factor_count : ℕ :=
  foldbin_groupoid_aut0_pu_product_connected_factor_count 2 +
    foldbin_groupoid_aut0_pu_product_connected_factor_count 3 +
    foldbin_groupoid_aut0_pu_product_connected_factor_count 4

/-- The audited simple Lie types visible in the identity component. Type `A_n` corresponds to a
`PU(n + 1)` factor. -/
def foldbin_groupoid_aut0_pu_product_connected_lie_type (n : ℕ) : Prop :=
  foldbin_groupoid_aut0_pu_product_connected_factor_count (n + 1) ≠ 0

/-- Paper label: `thm:foldbin-groupoid-aut0-pu-product`. -/
theorem paper_foldbin_groupoid_aut0_pu_product :
    foldbin_groupoid_aut0_pu_product_connected_factor_count 1 = 0 ∧
      foldbin_groupoid_aut0_pu_product_connected_factor_count 2 = 8 ∧
      foldbin_groupoid_aut0_pu_product_connected_factor_count 3 = 4 ∧
      foldbin_groupoid_aut0_pu_product_connected_factor_count 4 = 9 ∧
      foldbin_groupoid_aut0_pu_product_connected_factor_count 5 = 0 ∧
      cBinFiberMax 6 = 4 ∧
      foldbin_groupoid_aut0_pu_product_total_connected_factor_count = 21 ∧
      (2 * foldbin_groupoid_aut0_pu_product_connected_factor_count 2 +
          3 * foldbin_groupoid_aut0_pu_product_connected_factor_count 3 +
          4 * foldbin_groupoid_aut0_pu_product_connected_factor_count 4 = 64) ∧
      (∀ d : ℕ, foldbin_groupoid_aut0_pu_product_identity_component_permutation_rank d = 0) ∧
      foldbin_groupoid_aut0_pu_product_connected_lie_type 1 ∧
      foldbin_groupoid_aut0_pu_product_connected_lie_type 2 ∧
      foldbin_groupoid_aut0_pu_product_connected_lie_type 3 ∧
      ¬ foldbin_groupoid_aut0_pu_product_connected_lie_type 4 := by
  refine ⟨cBinFiberHist_6_1, cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4,
    cBinFiberHist_6_5, cBinFiberMax_six, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold foldbin_groupoid_aut0_pu_product_total_connected_factor_count
    unfold foldbin_groupoid_aut0_pu_product_connected_factor_count
    rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]
  · unfold foldbin_groupoid_aut0_pu_product_connected_factor_count
    rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]
  · intro d
    rfl
  · unfold foldbin_groupoid_aut0_pu_product_connected_lie_type
    unfold foldbin_groupoid_aut0_pu_product_connected_factor_count
    rw [cBinFiberHist_6_2]
    norm_num
  · unfold foldbin_groupoid_aut0_pu_product_connected_lie_type
    unfold foldbin_groupoid_aut0_pu_product_connected_factor_count
    rw [cBinFiberHist_6_3]
    norm_num
  · unfold foldbin_groupoid_aut0_pu_product_connected_lie_type
    unfold foldbin_groupoid_aut0_pu_product_connected_factor_count
    rw [cBinFiberHist_6_4]
    norm_num
  · unfold foldbin_groupoid_aut0_pu_product_connected_lie_type
    unfold foldbin_groupoid_aut0_pu_product_connected_factor_count
    rw [cBinFiberHist_6_5]
    simp

end Omega.Folding
