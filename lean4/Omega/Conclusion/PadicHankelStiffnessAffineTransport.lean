import Omega.POM.ConclusionHankelShiftPadicPrecisionSlope

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-padic-hankel-stiffness-affine-transport`. This is the
Conclusion-level restatement of the chapter-local shifted-Hankel p-adic precision law. -/
theorem paper_conclusion_padic_hankel_stiffness_affine_transport
    (D : Omega.POM.ConclusionHankelShiftPadicPrecisionSlopeData) :
    ∀ r : ℕ,
      D.precision (D.hankelData.k0 + r) =
        D.precision D.hankelData.k0 + (r : ℤ) * D.valuation D.hankelData.A.det := by
  simpa [Omega.POM.ConclusionHankelShiftPadicPrecisionSlopeData.fullShiftPrecisionSlope] using
    (Omega.POM.paper_conclusion_hankel_shift_padic_precision_slope D).1

end Omega.Conclusion
