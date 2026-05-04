import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete certificate for
`thm:conclusion-window6-triple-abelian-shadow-coincidence`.

It records the three window-6 abelian-shadow dimensions and the comparison triple
`(dim Spin(7), spin module dimension, rank Spin(7)) = (21, 8, 3)`. -/
structure conclusion_window6_triple_abelian_shadow_coincidence_data where
  matrixCenterDim : ℕ
  gaugeCenterDim : ℕ
  boundaryDim : ℕ
  spinLieDim : ℕ
  spinModuleDim : ℕ
  spinRank : ℕ
  matrixCenterDimEq : matrixCenterDim = 21
  gaugeCenterDimEq : gaugeCenterDim = 8
  boundaryDimEq : boundaryDim = 3
  spinLieDimEq : spinLieDim = 21
  spinModuleDimEq : spinModuleDim = 8
  spinRankEq : spinRank = 3

/-- Paper label: `thm:conclusion-window6-triple-abelian-shadow-coincidence`. -/
theorem paper_conclusion_window6_triple_abelian_shadow_coincidence
    (D : conclusion_window6_triple_abelian_shadow_coincidence_data) :
    D.matrixCenterDim = 21 ∧ D.gaugeCenterDim = 8 ∧ D.boundaryDim = 3 ∧
      D.matrixCenterDim = D.spinLieDim ∧ D.gaugeCenterDim = D.spinModuleDim ∧
        D.boundaryDim = D.spinRank := by
  refine ⟨D.matrixCenterDimEq, D.gaugeCenterDimEq, D.boundaryDimEq, ?_, ?_, ?_⟩
  · rw [D.matrixCenterDimEq, D.spinLieDimEq]
  · rw [D.gaugeCenterDimEq, D.spinModuleDimEq]
  · rw [D.boundaryDimEq, D.spinRankEq]

end Omega.Conclusion
