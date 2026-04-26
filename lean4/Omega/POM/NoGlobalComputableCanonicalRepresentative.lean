import Omega.Conclusion.SemanticEquivalenceUndecidable

namespace Omega.POM

/-- Canonical normalization decides semantic equivalence by normalize-and-compare. -/
def pom_no_global_computable_canonical_representative_normalizes
    {Alg Normal : Type*} (semEq : Alg → Alg → Prop) (normalize : Alg → Normal) : Prop :=
  ∀ A B, semEq A B ↔ normalize A = normalize B

/-- Compatibility of the ambient semantic model with the embedded finite PW fragment. -/
def pom_no_global_computable_canonical_representative_pw_compatible
    {PW Alg : Type*} (semEq : Alg → Alg → Prop) (pwEq : PW → PW → Prop) (pwEmbed : PW → Alg) :
    Prop :=
  ∀ p q, pwEq p q ↔ semEq (pwEmbed p) (pwEmbed q)

/-- If a semantically Turing-complete model had a total implementation-independent canonical
representative map, then semantic equivalence would become decidable by comparing normal forms,
contradicting the ambient undecidability theorem.
    thm:pom-no-global-computable-canonical-representative -/
theorem paper_pom_no_global_computable_canonical_representative
    {Code Alg Normal PW : Type*} [DecidableEq Normal]
    (semEq : Alg → Alg → Prop) (embed : Code → Alg) (ref : Alg) (nonHalting : Code → Prop)
    (pwEq : PW → PW → Prop) (pwEmbed : PW → Alg)
    (hReduction : ∀ c, nonHalting c ↔ semEq (embed c) ref)
    (hUndecidable : ¬ Omega.Conclusion.PredicatePointwiseDecidable nonHalting) :
    ¬ ∃ normalize : Alg → Normal,
        (∃ realize : Normal → Alg, ∀ A, semEq (realize (normalize A)) A) ∧
        pom_no_global_computable_canonical_representative_normalizes semEq normalize ∧
        pom_no_global_computable_canonical_representative_pw_compatible semEq pwEq pwEmbed := by
  intro hCanonical
  rcases hCanonical with ⟨normalize, hSound, hNormalize, hPwCompat⟩
  let _ := hSound
  let _ := hPwCompat
  have hSemUndecidable :
      ¬ Nonempty (∀ f g, Decidable (semEq f g)) :=
    Omega.Conclusion.paper_conclusion_semantic_equivalence_undecidable
      semEq embed ref nonHalting hReduction hUndecidable
  apply hSemUndecidable
  refine ⟨?_⟩
  intro A B
  exact decidable_of_iff (normalize A = normalize B) (hNormalize A B).symm

end Omega.POM
