import Omega.CircleDimension.S4V4ComplementaryRamificationLinearEquivalence

namespace Omega.CircleDimension

/-- Paper label: `cor:cdim-s4-v4-complementary-branch-square-root-line-bundle`. -/
theorem paper_cdim_s4_v4_complementary_branch_square_root_line_bundle
    (infinityFiber : Finset S4V4FiberPoint) (hcard : infinityFiber.card = 3) :
    let D : S4V4ComplementaryRamificationData := ⟨infinityFiber, hcard⟩
    D.complementaryBranchLinearEquiv ∧ divisorDegree D.pullbackInfinityDivisor = 3 := by
  let D : S4V4ComplementaryRamificationData := ⟨infinityFiber, hcard⟩
  change D.complementaryBranchLinearEquiv ∧ divisorDegree D.pullbackInfinityDivisor = 3
  exact
    ⟨(S4V4ComplementaryRamificationData.paper_cdim_s4_v4_complementary_ramification_linear_equivalence D).2.2,
      S4V4ComplementaryRamificationData.pullbackInfinityDivisor_degree D⟩

end Omega.CircleDimension
