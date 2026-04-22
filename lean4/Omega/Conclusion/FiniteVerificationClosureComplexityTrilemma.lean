import Omega.SPG.FiniteAuditBidirectionalCertificates
import Omega.SPG.FiniteAuditNpCompleteBarrier
import Omega.SPG.UndecidableNoFiniteComputableCompleteInvariant

namespace Omega.Conclusion

/-- The abstract decision problem determined by a finite verification package. -/
def conclusion_finite_verification_closure_complexity_trilemma_problem
    {Instance Theta Mode : Type}
    (D : Omega.SPG.FiniteAuditBidirectionalCertificateData Instance Theta Mode) : Instance → Prop :=
  fun x => ∀ θ : Theta, ∀ m : Mode, ¬ D.Bad x θ m

/-- Finite-valued complete invariants for an equivalence relation. -/
def conclusion_finite_verification_closure_complexity_trilemma_complete_invariant
    {Obj : Type} (equiv : Obj → Obj → Prop) : Prop :=
  ∃ M : Nat, ∃ I : Obj → Fin M, ∀ A B, equiv A B ↔ I A = I B

/-- A finite verification package gives the `NP ∩ coNP` certificate consequences, polynomial-time
enumeration upgrades them to `P`, any SAT reduction forces the usual collapse consequences, and an
undecidable equivalence relation cannot admit a finite-valued computable complete invariant.
    thm:conclusion-finite-verification-closure-complexity-trilemma -/
theorem paper_conclusion_finite_verification_closure_complexity_trilemma
    {Instance Theta Mode Obj : Type}
    (D : Omega.SPG.FiniteAuditBidirectionalCertificateData Instance Theta Mode)
    (satReducesToPi npEqCoNp pEqNp : Prop)
    (hCollapse : satReducesToPi → D.inNP → D.inCoNP → npEqCoNp)
    (hP : satReducesToPi → D.inP → pEqNp)
    (equiv : Obj → Obj → Prop)
    (hUndecidable : ¬ Omega.SPG.RelationDecidable equiv) :
    D.inNP ∧ D.inCoNP ∧
      (D.enumerableInPolyTime → D.inP) ∧
      (satReducesToPi → npEqCoNp ∧ (D.inP → pEqNp)) ∧
      ¬ conclusion_finite_verification_closure_complexity_trilemma_complete_invariant equiv := by
  have hCertificates := Omega.SPG.paper_spg_finite_audit_bidirectional_certificates_np_conp D
  have hBarrier :=
    Omega.SPG.paper_spg_finite_audit_np_complete_barrier D satReducesToPi npEqCoNp pEqNp
      hCollapse hP
  have hNoInvariant :=
    Omega.SPG.paper_spg_undecidable_no_finite_computable_complete_invariant equiv hUndecidable
  refine ⟨hCertificates.1, hCertificates.2.1, hCertificates.2.2, ?_, ?_⟩
  · intro hSat
    exact hBarrier hSat
  · simpa [conclusion_finite_verification_closure_complexity_trilemma_complete_invariant] using
      hNoInvariant

end Omega.Conclusion
