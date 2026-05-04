import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part62d-universal-solenoid-phase-completed-scan`. -/
theorem paper_xi_time_part62d_universal_solenoid_phase_completed_scan
    {Sigma C Layer : Type*} (phiCos phiSin : Rat → Sigma → C)
    (finiteLayer : Finset Rat → Type*)
    (hInjective :
      Function.Injective (fun x : Sigma => fun q : Rat => (phiCos q x, phiSin q x)))
    (hFactor :
      ∀ E : Finset Rat, ∃ project : Sigma → finiteLayer E, ∀ q ∈ E,
        ∃ read : finiteLayer E → C × C, ∀ x, read (project x) = (phiCos q x, phiSin q x)) :
    Function.Injective (fun x : Sigma => fun q : Rat => (phiCos q x, phiSin q x)) ∧
      (∀ E : Finset Rat, ∃ project : Sigma → finiteLayer E, ∀ q ∈ E,
        ∃ read : finiteLayer E → C × C, ∀ x,
          read (project x) = (phiCos q x, phiSin q x)) := by
  exact ⟨hInjective, hFactor⟩

end Omega.Zeta
