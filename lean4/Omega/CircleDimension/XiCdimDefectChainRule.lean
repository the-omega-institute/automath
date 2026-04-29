import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Xi paper wrapper for the exact circle-dimension defect chain rule together with its
subadditivity corollary.
    thm:xi-cdim-defect-chain-rule -/
theorem paper_xi_cdim_defect_chain_rule (f g : Omega.CircleDimension.CircleDimHomData)
    (hfg : f.targetRank = g.sourceRank) (restrictedKerRank : Nat)
    (hRestrict : restrictedKerRank ≤ g.kernelRank)
    (hRestrictBound : restrictedKerRank ≤ f.imageRank)
    (hImageSplit : f.imageRank ≤ restrictedKerRank + g.imageRank) :
    Omega.CircleDimension.cdimDefect
        (Omega.CircleDimension.CircleDimHomData.comp f g hfg restrictedKerRank hRestrict
          hRestrictBound hImageSplit) =
      Omega.CircleDimension.cdimDefect f + restrictedKerRank ∧
      Omega.CircleDimension.cdimDefect
          (Omega.CircleDimension.CircleDimHomData.comp f g hfg restrictedKerRank hRestrict
            hRestrictBound hImageSplit) ≤
        Omega.CircleDimension.cdimDefect f + Omega.CircleDimension.cdimDefect g := by
  refine ⟨?_, ?_⟩
  · exact cdimDefect_comp f g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit
  · exact cdimDefect_comp_le f g hfg restrictedKerRank hRestrict hRestrictBound hImageSplit

end Omega.CircleDimension
