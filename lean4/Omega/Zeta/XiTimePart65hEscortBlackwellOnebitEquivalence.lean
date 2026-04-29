import Omega.Conclusion.BinfoldEscortBlackwellEquivalence

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65h-escort-blackwell-onebit-equivalence`. The
conclusion-facing bin-fold Blackwell wrapper supplies the bounded-temperature one-bit
equivalence package used in the Zeta chapter. -/
theorem paper_xi_time_part65h_escort_blackwell_onebit_equivalence
    (D : Omega.Conclusion.BinfoldEscortBlackwellDatum) :
    D.AsymptoticallyBlackwellEquivalent := by
  exact Omega.Conclusion.paper_conclusion_binfold_escort_blackwell_equivalence D

end Omega.Zeta
