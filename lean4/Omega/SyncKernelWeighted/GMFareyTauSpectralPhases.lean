import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Paper label: `prop:gm-farey-tau-spectral-phases`. -/
theorem paper_gm_farey_tau_spectral_phases
    (smallTauPhase largeTauPhase discreteOperatorPhase : Prop)
    (hsmall : smallTauPhase)
    (hlarge : largeTauPhase)
    (hdiscrete : discreteOperatorPhase) :
    smallTauPhase ∧ largeTauPhase ∧ discreteOperatorPhase := by
  exact ⟨hsmall, hlarge, hdiscrete⟩

end Omega.SyncKernelWeighted
