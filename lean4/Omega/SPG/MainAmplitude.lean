import Omega.SPG.QuasistationaryAmbiguityAmplitudes

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Introduction-facing wrapper for the quasistationary ambiguity amplitudes theorem in the
    scan-projection ETDS paper.
    thm:main-amplitude -/
theorem paper_scan_projection_address_main_amplitude
    {Residue : Type}
    (leftEigenvector : Prop)
    (ratioLimit xiWeight asymptoticWeight : Residue → ℝ)
    (hEigen : leftEigenvector)
    (hRatio : ∀ r : Residue, ratioLimit r = xiWeight r)
    (hAsymptotic : ∀ r : Residue, asymptoticWeight r = ratioLimit r) :
    leftEigenvector ∧
      (∀ r : Residue, ratioLimit r = xiWeight r) ∧
      (∀ r : Residue, asymptoticWeight r = xiWeight r) :=
  paper_scan_projection_address_quasistationary_ambiguity_amplitudes
    leftEigenvector ratioLimit xiWeight asymptoticWeight hEigen hRatio hAsymptotic

end Omega.SPG
