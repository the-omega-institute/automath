import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The available binary carrying directions are exactly the indices whose localized shadow still
sees the prime `2`, so the existence of `ν` such directions is equivalent to a cardinality bound.
    thm:conclusion-localized-shadow-product-binary-carrying-rank -/
theorem paper_conclusion_localized_shadow_product_binary_carrying_rank {m nu : Nat}
    (T : Fin m -> Finset Nat) :
    (∃ I : Finset (Fin m), I.card = nu ∧ ∀ i, i ∈ I -> 2 ∉ T i) ↔
      nu ≤ (Finset.univ.filter (fun i : Fin m => 2 ∉ T i)).card := by
  let I0 : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => 2 ∉ T i)
  constructor
  · rintro ⟨I, hIcard, hIgood⟩
    have hsubset : I ⊆ I0 := by
      intro i hi
      simp [I0, hIgood i hi]
    simpa [I0, hIcard] using Finset.card_le_card hsubset
  · intro hnu
    have hnu' : nu ≤ I0.card := by
      simpa [I0] using hnu
    obtain ⟨I, hsubset, hIcard⟩ := Finset.exists_subset_card_eq hnu'
    refine ⟨I, hIcard, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hsubset hi)).2

end Omega.Conclusion
