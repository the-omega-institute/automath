import Omega.POM.SoftOrderFixedTempNondefinability

namespace Omega.POM

/-- If first-fit hard equivalence compiles extensionally into a soft fragment, then any decision
procedure for the soft extensional equivalence would induce one for the hard equivalence.
Therefore undecidability of the hard relation transfers to the soft relation.
    thm:pom-firstfit-extensional-undecidable -/
theorem paper_pom_firstfit_extensional_undecidable {Hard Soft : Type*}
    (hardEq : Hard → Hard → Prop) (softEq : Soft → Soft → Prop) (compile : Hard → Soft)
    (hCompile : ∀ w1 w2, hardEq w1 w2 ↔ softEq (compile w1) (compile w2))
    (hHardUndecidable : ¬ Nonempty (∀ w1 w2, Decidable (hardEq w1 w2))) :
    ¬ Nonempty (∀ u v, Decidable (softEq u v)) := by
  intro hSoftDecidable
  have hNoCompile :=
    paper_pom_soft_order_fixed_temp_nondefinability hardEq softEq hSoftDecidable
      hHardUndecidable
  exact hNoCompile ⟨compile, hCompile⟩

end Omega.POM
