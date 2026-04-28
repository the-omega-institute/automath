import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-2adic-address-prime-ledger-orthogonal-irreducibility`. -/
theorem paper_conclusion_2adic_address_prime_ledger_orthogonal_irreducibility
    (twoAdicAddressCompression finiteRankLedgerImpossible primeLedgerKernelRigid
      orthogonalAxes : Prop)
    (haddr : twoAdicAddressCompression) (hledger : finiteRankLedgerImpossible)
    (hkernel : primeLedgerKernelRigid)
    (horth : twoAdicAddressCompression -> primeLedgerKernelRigid -> orthogonalAxes) :
    twoAdicAddressCompression ∧ finiteRankLedgerImpossible ∧ primeLedgerKernelRigid ∧
      orthogonalAxes := by
  exact ⟨haddr, hledger, hkernel, horth haddr hkernel⟩

end Omega.Conclusion
