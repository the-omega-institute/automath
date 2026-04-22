import Mathlib.Tactic
import Omega.Folding.FoldBinM6FiberHist
import Omega.Folding.FoldbinGroupoidAut0PuProduct

namespace Omega.Folding

/-- In the audited `PU(d)` product decomposition, a `U(1)` direct factor would force a nonzero
`d = 1` multiplicity. -/
def foldbin6_no_u1_in_aut0_groupoid_algebra_has_u1_direct_factor : Prop :=
  foldbin_groupoid_aut0_pu_product_connected_factor_count 1 ≠ 0

/-- Every connected factor recorded by the audited window-`6` `PU(d)` product decomposition has
rank at least `2`, hence is one of the compact semisimple projective-unitary factors. -/
def foldbin6_no_u1_in_aut0_groupoid_algebra_all_connected_factors_semisimple : Prop :=
  ∀ d : ℕ, foldbin_groupoid_aut0_pu_product_connected_factor_count d ≠ 0 → 2 ≤ d

/-- The verified window-`6` histogram and the verified `PU(d)` product decomposition leave no room
for a `U(1)` direct factor in the connected automorphism group.
Paper label: `cor:foldbin6-no-u1-in-aut0-groupoid-algebra`. -/
theorem paper_foldbin6_no_u1_in_aut0_groupoid_algebra :
    cBinFiberHist 6 2 = 8 ∧
      cBinFiberHist 6 3 = 4 ∧
      cBinFiberHist 6 4 = 9 ∧
      foldbin_groupoid_aut0_pu_product_connected_factor_count 1 = 0 ∧
      foldbin_groupoid_aut0_pu_product_connected_factor_count 2 = 8 ∧
      foldbin_groupoid_aut0_pu_product_connected_factor_count 3 = 4 ∧
      foldbin_groupoid_aut0_pu_product_connected_factor_count 4 = 9 ∧
      foldbin6_no_u1_in_aut0_groupoid_algebra_all_connected_factors_semisimple ∧
      ¬ foldbin6_no_u1_in_aut0_groupoid_algebra_has_u1_direct_factor := by
  rcases paper_fold_bin_m6_fiber_hist with ⟨_, _, h2, h3, h4, _, _⟩
  rcases paper_foldbin_groupoid_aut0_pu_product with
    ⟨h1', h2', h3', h4', _, _, _, _, _, _, _, _, _⟩
  refine ⟨h2, h3, h4, h1', h2', h3', h4', ?_, ?_⟩
  · intro d hd
    have hd' : cBinFiberHist 6 d ≠ 0 := by
      simpa [foldbin_groupoid_aut0_pu_product_connected_factor_count] using hd
    cases d with
    | zero =>
        exfalso
        exact hd' cBinFiberHist_6_0
    | succ d =>
        cases d with
        | zero =>
            exfalso
            exact hd' cBinFiberHist_6_1
        | succ d =>
            omega
  · unfold foldbin6_no_u1_in_aut0_groupoid_algebra_has_u1_direct_factor
    simp [h1']

end Omega.Folding
