namespace Omega.Conclusion

/-- Once both the entropy bit count and the minimum audit bit count are identified with the common
fiber exponent `rS`, the claimed entropy/audit identity is immediate.
    thm:conclusion-screen-entropy-audit-identity -/
theorem paper_conclusion_screen_entropy_audit_identity
    (rS entropyBits minAuditBits : ℕ) (hEntropy : entropyBits = rS) (hAudit : minAuditBits = rS) :
    entropyBits = rS ∧ minAuditBits = rS := by
  exact ⟨hEntropy, hAudit⟩

end Omega.Conclusion
