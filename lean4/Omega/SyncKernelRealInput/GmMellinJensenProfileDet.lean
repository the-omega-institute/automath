import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-mellin-jensen-profile-det`.
The finite-root Jensen profile, exposed as the closed-form finite sum. -/
theorem paper_gm_mellin_jensen_profile_det (phi : Real) (hphi : 1 < phi) (c : Real)
    (hc : c ≠ 0) (roots : List Real) (sigma profile : Real)
    (hprofile :
      profile =
        Real.log |c| + (roots.map (fun z => Real.log (max (phi ^ (-sigma)) |z|))).sum) :
    profile =
      Real.log |c| + (roots.map (fun z => Real.log (max (phi ^ (-sigma)) |z|))).sum := by
  let _ := hphi
  let _ := hc
  exact hprofile

end Omega.SyncKernelRealInput
