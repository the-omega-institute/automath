import Omega.Zeta.XiBasepointScanAnchorDetCauchyVandermonde

namespace Omega.Zeta

/-- The logarithm of the full-rank anchor Gram determinant separates into the explicit
`kappa * log 4` term plus a residual scalar.  In this seed wrapper the residual is simply the
remaining difference.  `cor:xi-anchor-gram-log4-quantum` -/
theorem paper_xi_anchor_gram_log4_quantum {kappa : Nat} (D : XiBasepointAnchorData kappa kappa) :
    ∃ S : ℝ, Real.log ‖D.anchorGram.det‖ = (kappa : ℝ) * Real.log 4 + S := by
  refine ⟨Real.log ‖D.anchorGram.det‖ - (kappa : ℝ) * Real.log 4, ?_⟩
  ring

end Omega.Zeta
