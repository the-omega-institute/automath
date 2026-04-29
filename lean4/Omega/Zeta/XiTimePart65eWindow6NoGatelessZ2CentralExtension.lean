import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65e-window6-no-gateless-z2-central-extension`. -/
theorem paper_xi_time_part65e_window6_no_gateless_z2_central_extension
    (crossScaleRule recoversWindow6Parity naturalUnderUplift noExtraProtocolGate
      higherBoundaryFibersTernary : Prop)
    (hNoBinaryOnTernary :
      recoversWindow6Parity → naturalUnderUplift → noExtraProtocolGate →
        higherBoundaryFibersTernary → False)
    (hHigher : higherBoundaryFibersTernary) :
    ¬ (crossScaleRule ∧ recoversWindow6Parity ∧ naturalUnderUplift ∧ noExtraProtocolGate) := by
  intro h
  exact hNoBinaryOnTernary h.2.1 h.2.2.1 h.2.2.2 hHigher

end Omega.Zeta
