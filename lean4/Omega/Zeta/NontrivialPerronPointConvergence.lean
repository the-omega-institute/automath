import Omega.Zeta.ClassMertensExplicit

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for absolute convergence at the Perron point in
    the ETDS Chebotarev section.
    lem:nontrivial-perron-point-convergence -/
theorem paper_etds_nontrivial_perron_point_convergence
    (twistedSpectralGap explicitAsymptotic classMertensLog classMertensConstant
      chebotarevDensity nontrivialChannelBound absoluteConvergence : Prop)
    (hAsymptotic : twistedSpectralGap → explicitAsymptotic)
    (hLog : explicitAsymptotic → classMertensLog)
    (hConst : classMertensLog → classMertensConstant)
    (hDensity : explicitAsymptotic → chebotarevDensity)
    (hChannel : explicitAsymptotic → nontrivialChannelBound)
    (hConv : nontrivialChannelBound → absoluteConvergence)
    (hGap : twistedSpectralGap) :
    absoluteConvergence := by
  have hExplicit :=
    (paper_etds_class_mertens_explicit
      twistedSpectralGap explicitAsymptotic classMertensLog classMertensConstant
      chebotarevDensity hAsymptotic hLog hConst hDensity hGap).1
  exact hConv (hChannel hExplicit)

end Omega.Zeta
