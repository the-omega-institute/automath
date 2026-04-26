import Omega.Conclusion.LocalizedShadowProductBinaryCarryingRank

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-localized-shadow-minimal-binary-carrying-number`. The
window-6 boundary parity and anomaly ledgers require binary carrying ranks `3` and `21`
respectively, so the general localized-shadow rank criterion yields both cardinality bounds. -/
theorem paper_conclusion_window6_localized_shadow_minimal_binary_carrying_number {m : Nat}
    (T : Fin m -> Finset Nat)
    (h3 : Exists fun I : Finset (Fin m) => I.card = 3 ∧ forall i, i ∈ I -> 2 ∉ T i)
    (h21 : Exists fun I : Finset (Fin m) => I.card = 21 ∧ forall i, i ∈ I -> 2 ∉ T i) :
    And (3 <= (Finset.univ.filter (fun i : Fin m => 2 ∉ T i)).card)
      (21 <= (Finset.univ.filter (fun i : Fin m => 2 ∉ T i)).card) := by
  constructor
  · exact (paper_conclusion_localized_shadow_product_binary_carrying_rank (T := T)).mp h3
  · exact (paper_conclusion_localized_shadow_product_binary_carrying_rank (T := T)).mp h21

end Omega.Conclusion
