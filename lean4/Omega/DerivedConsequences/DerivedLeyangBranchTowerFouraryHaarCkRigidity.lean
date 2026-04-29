import Omega.DerivedConsequences.DerivedLeyangBranchsetHaarLimit
import Omega.Zeta.DerivedLeyangBfCkRigidity

namespace Omega.DerivedConsequences

/-- Paper label: `thm:derived-leyang-branch-tower-fourary-haar-ck-rigidity`. -/
theorem paper_derived_leyang_branch_tower_fourary_haar_ck_rigidity (n r : ℕ) (h : r ≤ n) :
    ((4 : ℚ) ^ (n - r)) / (5 * (4 : ℚ) ^ n) = (1 : ℚ) / (5 * (4 : ℚ) ^ r) ∧
      (∀ z : ℚ, Omega.Zeta.derivedLeyangArtinMazurZeta z = 1 / (1 - 4 * z) ^ 5) ∧
      Omega.Zeta.derived_leyang_bf_ck_rigidity_single_block_snf = ![1, 1, 1, 3] ∧
      Fintype.card Omega.Zeta.derived_leyang_bf_ck_rigidity_bowen_franks_group = 3 ^ 5 := by
  have hzeta : ∀ z : ℚ, Omega.Zeta.derivedLeyangArtinMazurZeta z = 1 / (1 - 4 * z) ^ 5 := by
    intro z
    rfl
  have hsnf : Omega.Zeta.derived_leyang_bf_ck_rigidity_single_block_snf = ![1, 1, 1, 3] := by
    rfl
  have hcard : Fintype.card Omega.Zeta.derived_leyang_bf_ck_rigidity_bowen_franks_group = 3 ^ 5 := by
    simp [Omega.Zeta.derived_leyang_bf_ck_rigidity_bowen_franks_group,
      Omega.Zeta.derivedLeyangBranchCount]
  exact ⟨paper_derived_leyang_branchset_haar_limit n r h, hzeta, hsnf, hcard⟩

end Omega.DerivedConsequences
