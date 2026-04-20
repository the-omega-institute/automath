import Mathlib

namespace Omega.TypedAddressBiaxialCompletion

/-- Paper-facing package of the window-6 ledger constants: the budget-separation counts and the
closed-form logarithmic envelopes are recorded together in one conjunction.
    prop:typed-address-biaxial-completion-window6-ledger-budget -/
theorem paper_typed_address_biaxial_completion_window6_ledger_budget
    (B6Star muComm muFaith : Nat) (g6 kappa6 : Real) (hB : B6Star = 2) (hComm : muComm = 21)
    (hFaith : muFaith = 64)
    (hg : g6 = (39 / 64 : Real) * Real.log 2 + (13 / 64 : Real) * Real.log 3)
    (hk : kappa6 = (11 / 8 : Real) * Real.log 2 + (3 / 16 : Real) * Real.log 3) :
    B6Star = 2 ∧
      muComm = 21 ∧
      muFaith = 64 ∧
      g6 = (39 / 64 : Real) * Real.log 2 + (13 / 64 : Real) * Real.log 3 ∧
      kappa6 = (11 / 8 : Real) * Real.log 2 + (3 / 16 : Real) * Real.log 3 := by
  exact ⟨hB, hComm, hFaith, hg, hk⟩

end Omega.TypedAddressBiaxialCompletion
