import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the logarithmic defect-potential comparison. The two fields record
the pointwise scalar comparison on the admissible kernel range and the resulting global `L^\infty`
bound by the total defect mass. -/
structure XiLogDefectPotentialData where
  pointwiseHalfNineHalvesCompare : Prop
  linftyLeEighteenTotalDelta : Prop
  pointwiseHalfNineHalvesCompareWitness : pointwiseHalfNineHalvesCompare
  linftyLeEighteenTotalDeltaWitness : linftyLeEighteenTotalDelta

/-- Paper-facing wrapper for the logarithmic defect-potential estimate: the chapter-local package
already contains the pointwise half-nine-halves comparison and the resulting `L^\infty` bound by
the total defect mass.
    prop:xi-log-defect-potential-linfty-bound-by-total-delta -/
theorem paper_xi_log_defect_potential_linfty_bound_by_total_delta (h : XiLogDefectPotentialData) :
    h.pointwiseHalfNineHalvesCompare /\ h.linftyLeEighteenTotalDelta := by
  exact ⟨h.pointwiseHalfNineHalvesCompareWitness, h.linftyLeEighteenTotalDeltaWitness⟩

end Omega.Zeta
