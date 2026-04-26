import Omega.POM.NoGlobalComputableCanonicalRepresentative

namespace Omega.FoldComputability

/-- Paper label: `thm:fold-computability-no-computable-normal-form-selector`.
Any total computable normal-form selector would decide semantic equivalence by normalize-and-compare,
contradicting the underlying halting reduction. -/
theorem paper_fold_computability_no_computable_normal_form_selector
    {Code Alg Normal PW : Type*} [DecidableEq Normal]
    (semEq : Alg → Alg → Prop) (embed : Code → Alg) (ref : Alg) (nonHalting : Code → Prop)
    (pwEq : PW → PW → Prop) (pwEmbed : PW → Alg)
    (hReduction : ∀ c, nonHalting c ↔ semEq (embed c) ref)
    (hUndecidable : ¬ Omega.Conclusion.PredicatePointwiseDecidable nonHalting) :
    ¬ ∃ normalize : Alg → Normal,
        (∃ realize : Normal → Alg, ∀ A, semEq (realize (normalize A)) A) ∧
          Omega.POM.pom_no_global_computable_canonical_representative_normalizes
            semEq normalize ∧
          Omega.POM.pom_no_global_computable_canonical_representative_pw_compatible
            semEq pwEq pwEmbed := by
  exact Omega.POM.paper_pom_no_global_computable_canonical_representative
    semEq embed ref nonHalting pwEq pwEmbed hReduction hUndecidable

end Omega.FoldComputability
