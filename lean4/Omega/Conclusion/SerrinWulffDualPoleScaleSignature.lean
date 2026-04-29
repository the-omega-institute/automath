import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-serrin-wulff-dual-pole-scale-signature`. -/
theorem paper_conclusion_serrin_wulff_dual_pole_scale_signature
    (boundaryResidue volumeResidue signature expectedSignature : ℝ)
    (hSignature : signature = boundaryResidue / volumeResidue)
    (hExpected : expectedSignature = boundaryResidue / volumeResidue) :
    signature = expectedSignature := by
  rw [hSignature, hExpected]

end Omega.Conclusion
