import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hankel-single-circle-prime-ledger-terminal-object`. -/
theorem paper_conclusion_hankel_single_circle_prime_ledger_terminal_object (q : Nat)
    (distortionSupportFinite shortExactPrimeLedger recoverSupport terminalObject : Prop)
    (hFinite : distortionSupportFinite)
    (hLedger : distortionSupportFinite -> shortExactPrimeLedger ∧ recoverSupport)
    (hTerminal : shortExactPrimeLedger -> recoverSupport -> terminalObject) :
    shortExactPrimeLedger ∧ recoverSupport ∧ terminalObject := by
  have _ : q = q := rfl
  rcases hLedger hFinite with ⟨hShort, hRecover⟩
  exact ⟨hShort, hRecover, hTerminal hShort hRecover⟩

end Omega.Conclusion
