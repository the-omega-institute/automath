import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-oddtail-ordered-nevanlinna-completeness`. -/
theorem paper_conclusion_oddtail_ordered_nevanlinna_completeness {Pair : Type*}
    (canonical : Pair) (sameOrderedNevanlinna sameSupport unitarilyEquivalent : Pair → Pair → Prop)
    (complete : ∀ J, sameOrderedNevanlinna J canonical → unitarilyEquivalent J canonical)
    (support_counterexample : ∃ J, sameSupport J canonical ∧ ¬ unitarilyEquivalent J canonical) :
    (∀ J, sameOrderedNevanlinna J canonical → unitarilyEquivalent J canonical) ∧
      (∃ J, sameSupport J canonical ∧ ¬ unitarilyEquivalent J canonical) := by
  exact ⟨complete, support_counterexample⟩

end Omega.Conclusion
