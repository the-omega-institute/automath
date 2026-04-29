import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper wrapper for the circle-dimension defect chain rule and subadditivity package.
    thm:cdim-defect-chain-rule -/
theorem paper_cdim_defect_chain_rule (f g : CircleDimHomData)
    (hfg : f.targetRank = g.sourceRank) (restrictedKerRank : Nat)
    (hRestrict : restrictedKerRank ≤ g.kernelRank)
    (hRestrictBound : restrictedKerRank ≤ f.imageRank)
    (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank) :
    cdimDefect
        (CircleDimHomData.comp f g hfg restrictedKerRank hRestrict hRestrictBound
          hImageSplit) =
      cdimDefect f + restrictedKerRank ∧
      cdimDefect
          (CircleDimHomData.comp f g hfg restrictedKerRank hRestrict hRestrictBound
            hImageSplit) ≤
        cdimDefect f + cdimDefect g := by
  exact ⟨cdimDefect_comp f g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit,
    cdimDefect_comp_le f g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit⟩

end Omega.CircleDimension
