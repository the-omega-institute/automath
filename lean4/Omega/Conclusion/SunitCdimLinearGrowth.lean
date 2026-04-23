import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete package for the `S`-unit circle-dimension growth law. The free-rank contribution of
the `S`-part is `sCard`, while the rational case is written as torsion times a free group of the
same rank. -/
structure SUnitCdimLinearGrowthData where
  unitCdim : ℤ
  sCard : ℤ
  sUnitCdim : ℤ
  qCaseCdim : ℤ
  qTorsionCdim : ℤ
  qFreeRank : ℤ
  sUnit_rank_formula : sUnitCdim = unitCdim + sCard
  qCase_decomposition : qCaseCdim = qTorsionCdim + qFreeRank
  qTorsion_trivial_cdim : qTorsionCdim = 0
  qFreeRank_eq_sCard : qFreeRank = sCard

/-- Paper label: `thm:conclusion-sunit-cdim-linear-growth`. The `S`-unit rank formula adds
`|S|` to the ordinary unit circle dimension, and in the rational case the torsion factor
contributes zero while the free factor contributes exactly `|S|`. -/
theorem paper_conclusion_sunit_cdim_linear_growth (D : SUnitCdimLinearGrowthData) :
    D.sUnitCdim = D.unitCdim + D.sCard ∧ D.qCaseCdim = D.sCard := by
  refine ⟨D.sUnit_rank_formula, ?_⟩
  calc
    D.qCaseCdim = D.qTorsionCdim + D.qFreeRank := D.qCase_decomposition
    _ = 0 + D.qFreeRank := by rw [D.qTorsion_trivial_cdim]
    _ = D.qFreeRank := by norm_num
    _ = D.sCard := D.qFreeRank_eq_sCard

end Omega.Conclusion
