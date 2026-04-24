import Omega.POM.NoGlobalComputableCanonicalRepresentative
import Omega.POM.RewriteNormalformMinimalAudit

namespace Omega.POM

/-- Concrete wrapper contrasting the finite rewrite-normal-form regime with the unrestricted
semantic regime where no implementation-independent canonical representative can exist. -/
structure pom_normalform_vs_turing_budget_undecidable_data where
  Slice : Type
  rewriteNormal : Slice → Slice
  rewriteEquiv : Slice → Slice → Prop
  rewriteAudit : Slice → Nat
  rewriteMinimal :
    ∀ W W', rewriteEquiv W' W → rewriteAudit (rewriteNormal W) ≤ rewriteAudit W'
  rewriteUnique :
    ∀ W W', rewriteEquiv W' W →
      rewriteAudit W' = rewriteAudit (rewriteNormal W) → W' = rewriteNormal W
  Code : Type
  Alg : Type
  Normal : Type
  PW : Type
  instDecidableEqNormal : DecidableEq Normal
  semEq : Alg → Alg → Prop
  embed : Code → Alg
  ref : Alg
  nonHalting : Code → Prop
  pwEq : PW → PW → Prop
  pwEmbed : PW → Alg
  semReduction : ∀ c, nonHalting c ↔ semEq (embed c) ref
  nonHaltingUndecidable : ¬ Omega.Conclusion.PredicatePointwiseDecidable nonHalting

attribute [instance] pom_normalform_vs_turing_budget_undecidable_data.instDecidableEqNormal

/-- Finite rewrite slices admit a minimal audit representative, but unrestricted semantic classes
do not admit a global implementation-independent canonical representative. -/
def pom_normalform_vs_turing_budget_undecidable_statement
    (D : pom_normalform_vs_turing_budget_undecidable_data) : Prop :=
  (∀ W W', D.rewriteEquiv W' W →
      D.rewriteAudit (D.rewriteNormal W) ≤ D.rewriteAudit W' ∧
        (D.rewriteAudit W' = D.rewriteAudit (D.rewriteNormal W) →
          W' = D.rewriteNormal W)) ∧
    ¬ ∃ normalize : D.Alg → D.Normal,
        (∃ realize : D.Normal → D.Alg, ∀ A, D.semEq (realize (normalize A)) A) ∧
        pom_no_global_computable_canonical_representative_normalizes D.semEq normalize ∧
        pom_no_global_computable_canonical_representative_pw_compatible
          D.semEq D.pwEq D.pwEmbed

/-- Paper label: `cor:pom-normalform-vs-turing-budget-undecidable`. -/
theorem paper_pom_normalform_vs_turing_budget_undecidable
    (D : pom_normalform_vs_turing_budget_undecidable_data) :
    pom_normalform_vs_turing_budget_undecidable_statement D := by
  refine ⟨?_, ?_⟩
  · exact
      paper_pom_rewrite_normalform_minimal_audit D.rewriteNormal D.rewriteEquiv D.rewriteAudit
        D.rewriteMinimal D.rewriteUnique
  · exact
      paper_pom_no_global_computable_canonical_representative
        D.semEq D.embed D.ref D.nonHalting D.pwEq D.pwEmbed D.semReduction
        D.nonHaltingUndecidable

end Omega.POM
