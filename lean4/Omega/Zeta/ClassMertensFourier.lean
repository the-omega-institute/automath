import Omega.Zeta.ClassMertensExplicit

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for non-abelian Fourier reconstruction of class
    Mertens constants.
    thm:class-mertens-fourier -/
theorem paper_etds_class_mertens_fourier
    (twistedSpectralGap explicitAsymptotic classMertensLog classMertensConstant
      chebotarevDensity fourierInversion parsevalIdentity : Prop)
    (hAsymptotic : twistedSpectralGap → explicitAsymptotic)
    (hLog : explicitAsymptotic → classMertensLog)
    (hConst : classMertensLog → classMertensConstant)
    (hDensity : explicitAsymptotic → chebotarevDensity)
    (hFourier : explicitAsymptotic → fourierInversion)
    (hParseval : explicitAsymptotic → parsevalIdentity)
    (hGap : twistedSpectralGap) :
    explicitAsymptotic ∧
      classMertensLog ∧
      classMertensConstant ∧
      chebotarevDensity ∧
      fourierInversion ∧
      parsevalIdentity := by
  have hMertens :=
    paper_etds_class_mertens_explicit
      twistedSpectralGap
      explicitAsymptotic
      classMertensLog
      classMertensConstant
      chebotarevDensity
      hAsymptotic
      hLog
      hConst
      hDensity
      hGap
  exact
    ⟨hMertens.1, hMertens.2.1, hMertens.2.2.1, hMertens.2.2.2,
      hFourier hMertens.1, hParseval hMertens.1⟩

end Omega.Zeta
