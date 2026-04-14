namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the explicit class Mertens theorem and
    Chebotarev density consequence in the ETDS finite-group section.
    thm:class-mertens-explicit -/
theorem paper_etds_class_mertens_explicit
    (twistedSpectralGap explicitAsymptotic classMertensLog
      classMertensConstant chebotarevDensity : Prop)
    (hAsymptotic : twistedSpectralGap → explicitAsymptotic)
    (hLog : explicitAsymptotic → classMertensLog)
    (hConst : classMertensLog → classMertensConstant)
    (hDensity : explicitAsymptotic → chebotarevDensity)
    (hGap : twistedSpectralGap) :
    explicitAsymptotic ∧
      classMertensLog ∧
      classMertensConstant ∧
      chebotarevDensity := by
  have hExplicit : explicitAsymptotic := hAsymptotic hGap
  have hLog' : classMertensLog := hLog hExplicit
  exact ⟨hExplicit, hLog', hConst hLog', hDensity hExplicit⟩

end Omega.Zeta
