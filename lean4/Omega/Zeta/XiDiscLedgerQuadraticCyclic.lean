import Mathlib.Tactic

namespace Omega.Zeta

/-- `cor:xi-disc-ledger-quadratic-cyclic` -/
theorem paper_xi_disc_ledger_quadratic_cyclic
    (quadraticLocalLedger globalCyclicLedger singleAxisDepth : Prop)
    (hlocal : quadraticLocalLedger) (hglobal : globalCyclicLedger)
    (haxis : singleAxisDepth) :
    quadraticLocalLedger ∧ globalCyclicLedger ∧ singleAxisDepth := by
  exact ⟨hlocal, hglobal, haxis⟩

end Omega.Zeta
