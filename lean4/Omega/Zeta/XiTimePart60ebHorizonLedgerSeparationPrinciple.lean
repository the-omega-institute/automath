import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part60eb-horizon-ledger-separation-principle`. -/
theorem paper_xi_time_part60eb_horizon_ledger_separation_principle
    {Ledger Visible : Type} (visible : Ledger → Visible) (truth : Ledger → Prop)
    (hNonfaithful :
      ∃ L1 L2 : Ledger, visible L1 = visible L2 ∧ truth L1 ∧ ¬ truth L2) :
    ¬ ∃ recover : Visible → Prop, ∀ L : Ledger, recover (visible L) ↔ truth L := by
  rintro ⟨recover, hrecover⟩
  rcases hNonfaithful with ⟨L1, L2, hvisible, htruth1, hnot_truth2⟩
  have hrecovered1 : recover (visible L1) := (hrecover L1).2 htruth1
  have hrecovered2 : recover (visible L2) := by
    simpa [hvisible] using hrecovered1
  exact hnot_truth2 ((hrecover L2).1 hrecovered2)

end Omega.Zeta
