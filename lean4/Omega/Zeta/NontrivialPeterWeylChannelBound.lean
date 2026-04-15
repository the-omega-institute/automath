import Omega.Zeta.ClassMertensExplicit

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the non-trivial Peter--Weyl channel bound
    in the ETDS Chebotarev section.
    lem:nontrivial-peter-weyl-channel-bound -/
theorem paper_etds_nontrivial_peter_weyl_channel_bound
    (twistedSpectralGap explicitAsymptotic classMertensLog classMertensConstant
      chebotarevDensity nontrivialChannelBound : Prop)
    (hAsymptotic : twistedSpectralGap → explicitAsymptotic)
    (hLog : explicitAsymptotic → classMertensLog)
    (hConst : classMertensLog → classMertensConstant)
    (hDensity : explicitAsymptotic → chebotarevDensity)
    (hChannel : explicitAsymptotic → nontrivialChannelBound)
    (hGap : twistedSpectralGap) :
    nontrivialChannelBound := by
  have hExplicit :=
    (paper_etds_class_mertens_explicit
      twistedSpectralGap explicitAsymptotic classMertensLog classMertensConstant
      chebotarevDensity hAsymptotic hLog hConst hDensity hGap).1
  exact hChannel hExplicit

end Omega.Zeta
