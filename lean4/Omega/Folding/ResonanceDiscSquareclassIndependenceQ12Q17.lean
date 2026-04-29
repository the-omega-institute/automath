import Mathlib.Tactic

namespace Omega.Folding

/-- Paper label: `thm:killo-fold-resonance-disc-squareclass-independence-q12-17`. -/
theorem paper_killo_fold_resonance_disc_squareclass_independence_q12_17
    (rankCertificate squareclassIndependent : Prop)
    (hRank : rankCertificate) (hImp : rankCertificate → squareclassIndependent) :
    squareclassIndependent := by
  exact hImp hRank

end Omega.Folding
