import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the Toeplitz-scan audit functor.  The representative shifted by the
imaginary gauge has the same audit object but is a distinct representative; orbit constancy is
recorded by an explicit factor through the strictification quotient. -/
structure conclusion_toeplitz_scan_audit_functor_nonfaithful_data where
  conclusion_toeplitz_scan_audit_functor_nonfaithful_representative : Type
  conclusion_toeplitz_scan_audit_functor_nonfaithful_auditObject : Type
  conclusion_toeplitz_scan_audit_functor_nonfaithful_strictificationQuotient : Type
  conclusion_toeplitz_scan_audit_functor_nonfaithful_scanAudit :
    conclusion_toeplitz_scan_audit_functor_nonfaithful_representative →
      conclusion_toeplitz_scan_audit_functor_nonfaithful_auditObject
  conclusion_toeplitz_scan_audit_functor_nonfaithful_strictificationClass :
    conclusion_toeplitz_scan_audit_functor_nonfaithful_representative →
      conclusion_toeplitz_scan_audit_functor_nonfaithful_strictificationQuotient
  conclusion_toeplitz_scan_audit_functor_nonfaithful_shiftByImaginaryEta :
    conclusion_toeplitz_scan_audit_functor_nonfaithful_representative →
      conclusion_toeplitz_scan_audit_functor_nonfaithful_representative
  conclusion_toeplitz_scan_audit_functor_nonfaithful_baseRepresentative :
    conclusion_toeplitz_scan_audit_functor_nonfaithful_representative
  conclusion_toeplitz_scan_audit_functor_nonfaithful_shiftDistinct :
    conclusion_toeplitz_scan_audit_functor_nonfaithful_shiftByImaginaryEta
        conclusion_toeplitz_scan_audit_functor_nonfaithful_baseRepresentative ≠
      conclusion_toeplitz_scan_audit_functor_nonfaithful_baseRepresentative
  conclusion_toeplitz_scan_audit_functor_nonfaithful_imaginaryEtaInvariance :
    conclusion_toeplitz_scan_audit_functor_nonfaithful_scanAudit
        (conclusion_toeplitz_scan_audit_functor_nonfaithful_shiftByImaginaryEta
          conclusion_toeplitz_scan_audit_functor_nonfaithful_baseRepresentative) =
      conclusion_toeplitz_scan_audit_functor_nonfaithful_scanAudit
        conclusion_toeplitz_scan_audit_functor_nonfaithful_baseRepresentative
  conclusion_toeplitz_scan_audit_functor_nonfaithful_quotientAudit :
    conclusion_toeplitz_scan_audit_functor_nonfaithful_strictificationQuotient →
      conclusion_toeplitz_scan_audit_functor_nonfaithful_auditObject
  conclusion_toeplitz_scan_audit_functor_nonfaithful_orbitConstancy :
    ∀ C,
      conclusion_toeplitz_scan_audit_functor_nonfaithful_quotientAudit
          (conclusion_toeplitz_scan_audit_functor_nonfaithful_strictificationClass C) =
        conclusion_toeplitz_scan_audit_functor_nonfaithful_scanAudit C

/-- The audit map is not faithful: two distinct representatives share one audit object. -/
def conclusion_toeplitz_scan_audit_functor_nonfaithful_data.nonfaithful
    (D : conclusion_toeplitz_scan_audit_functor_nonfaithful_data) : Prop :=
  ∃ C C' : D.conclusion_toeplitz_scan_audit_functor_nonfaithful_representative,
    C ≠ C' ∧
      D.conclusion_toeplitz_scan_audit_functor_nonfaithful_scanAudit C =
        D.conclusion_toeplitz_scan_audit_functor_nonfaithful_scanAudit C'

/-- The audit map factors through the strictification orbit quotient. -/
def conclusion_toeplitz_scan_audit_functor_nonfaithful_data.factorsThroughStrictificationQuotient
    (D : conclusion_toeplitz_scan_audit_functor_nonfaithful_data) : Prop :=
  ∃ quotientAudit :
      D.conclusion_toeplitz_scan_audit_functor_nonfaithful_strictificationQuotient →
        D.conclusion_toeplitz_scan_audit_functor_nonfaithful_auditObject,
    ∀ C,
      quotientAudit
          (D.conclusion_toeplitz_scan_audit_functor_nonfaithful_strictificationClass C) =
        D.conclusion_toeplitz_scan_audit_functor_nonfaithful_scanAudit C

/-- Paper label: `thm:conclusion-toeplitz-scan-audit-functor-nonfaithful`. -/
theorem paper_conclusion_toeplitz_scan_audit_functor_nonfaithful
    (D : conclusion_toeplitz_scan_audit_functor_nonfaithful_data) :
    D.nonfaithful ∧ D.factorsThroughStrictificationQuotient := by
  refine ⟨?_, ?_⟩
  · refine ⟨
      D.conclusion_toeplitz_scan_audit_functor_nonfaithful_shiftByImaginaryEta
        D.conclusion_toeplitz_scan_audit_functor_nonfaithful_baseRepresentative,
      D.conclusion_toeplitz_scan_audit_functor_nonfaithful_baseRepresentative,
      D.conclusion_toeplitz_scan_audit_functor_nonfaithful_shiftDistinct,
      D.conclusion_toeplitz_scan_audit_functor_nonfaithful_imaginaryEtaInvariance⟩
  · exact ⟨
      D.conclusion_toeplitz_scan_audit_functor_nonfaithful_quotientAudit,
      D.conclusion_toeplitz_scan_audit_functor_nonfaithful_orbitConstancy⟩

end Omega.Conclusion
