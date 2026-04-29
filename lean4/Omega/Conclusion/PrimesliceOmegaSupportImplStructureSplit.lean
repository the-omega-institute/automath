import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-primeslice-omega-support-impl-structure-split`. -/
theorem paper_conclusion_primeslice_omega_support_impl_structure_split
    (omegaSupportFreeMonoid primeLedgerEquivalent : Prop)
    (implementationDimension structuralHomDimensionUnbounded : Prop)
    (hFree : omegaSupportFreeMonoid)
    (hEquiv : omegaSupportFreeMonoid → primeLedgerEquivalent)
    (hImpl : primeLedgerEquivalent → implementationDimension)
    (hStruct : primeLedgerEquivalent → structuralHomDimensionUnbounded) :
    primeLedgerEquivalent ∧ implementationDimension ∧ structuralHomDimensionUnbounded := by
  have hPrimeLedger : primeLedgerEquivalent := hEquiv hFree
  exact ⟨hPrimeLedger, hImpl hPrimeLedger, hStruct hPrimeLedger⟩

end Omega.Conclusion
