import Omega.Conclusion.SemanticEquivalenceUndecidable

namespace Omega.FoldComputability

/-- Paper label: `thm:fold-computability-no-re-complete-certificates-for-extensional-equality`.
If extensional equality were witnessed by a finite decidable certificate predicate, one could
search all certificates and thereby decide the equality relation, contradicting the standard
halting reduction. -/
theorem paper_fold_computability_no_re_complete_certificates_for_extensional_equality
    {Code Alg Cert : Type*} [Fintype Cert]
    (extEq : Alg → Alg → Prop) (embed : Code → Alg) (ref : Alg) (nonHalting : Code → Prop)
    (hReduction : ∀ c, nonHalting c ↔ extEq (embed c) ref)
    (hUndecidable : ¬ Omega.Conclusion.PredicatePointwiseDecidable nonHalting) :
    ¬ ∃ verify : Cert → Alg → Alg → Bool,
        ∀ A B, extEq A B ↔ ∃ cert, verify cert A B = true := by
  intro hCertificates
  rcases hCertificates with ⟨verify, hComplete⟩
  have hSemUndecidable :
      ¬ Nonempty (∀ A B, Decidable (extEq A B)) :=
    Omega.Conclusion.paper_conclusion_semantic_equivalence_undecidable
      extEq embed ref nonHalting hReduction hUndecidable
  apply hSemUndecidable
  refine ⟨?_⟩
  intro A B
  exact decidable_of_iff (∃ cert, verify cert A B = true) (hComplete A B).symm

end Omega.FoldComputability
