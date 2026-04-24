import Omega.Conclusion.FiniteVerificationClosureComplexityTrilemma

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-boundary-finite-audit-complexity-barrier`. This is the
paper-facing projection of the finite-verification-closure trilemma onto the four complexity
consequences used in the boundary-audit discussion. -/
theorem paper_conclusion_boundary_finite_audit_complexity_barrier
    {Instance Theta Mode Obj : Type}
    (D : Omega.SPG.FiniteAuditBidirectionalCertificateData Instance Theta Mode)
    (satReducesToPi npEqCoNp pEqNp : Prop)
    (hCollapse : satReducesToPi → D.inNP → D.inCoNP → npEqCoNp)
    (hP : satReducesToPi → D.inP → pEqNp)
    (equiv : Obj → Obj → Prop)
    (hUndecidable : ¬ Omega.SPG.RelationDecidable equiv) :
    D.inNP ∧ D.inCoNP ∧
      (D.enumerableInPolyTime → D.inP) ∧
      (satReducesToPi → npEqCoNp) ∧
      (satReducesToPi → D.inP → pEqNp) := by
  rcases
      paper_conclusion_finite_verification_closure_complexity_trilemma
        D satReducesToPi npEqCoNp pEqNp hCollapse hP equiv hUndecidable with
    ⟨hNP, hCoNP, hPoly, hCollapseProj, _hNoInvariant⟩
  refine ⟨hNP, hCoNP, hPoly, ?_, ?_⟩
  · intro hSat
    exact (hCollapseProj hSat).1
  · intro hSat hInP
    exact (hCollapseProj hSat).2 hInP

end Omega.Conclusion
