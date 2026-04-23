import Mathlib.Tactic

namespace Omega.Folding

/-- The `n`-th size-`r` block, encoded by the natural pairing function. -/
def killo_localization_fixed_cardinality_nonclassification_block (r n : ℕ) : Finset ℕ :=
  (Finset.range r).image (Nat.pair n)

lemma killo_localization_fixed_cardinality_nonclassification_block_card (r n : ℕ) :
    (killo_localization_fixed_cardinality_nonclassification_block r n).card = r := by
  unfold killo_localization_fixed_cardinality_nonclassification_block
  simpa using
    Finset.card_image_of_injective (s := Finset.range r) (f := Nat.pair n) (by
      intro a b hab
      exact (Nat.pair_eq_pair.mp hab).2)

lemma killo_localization_fixed_cardinality_nonclassification_left_endpoint_mem
    (r n : ℕ) (hr : 1 ≤ r) :
    Nat.pair n 0 ∈ killo_localization_fixed_cardinality_nonclassification_block r n := by
  unfold killo_localization_fixed_cardinality_nonclassification_block
  refine Finset.mem_image.mpr ?_
  refine ⟨0, ?_, by simp⟩
  simpa using hr

lemma killo_localization_fixed_cardinality_nonclassification_left_endpoint_not_mem
    (r i j : ℕ) (hij : i ≠ j) :
    Nat.pair i 0 ∉ killo_localization_fixed_cardinality_nonclassification_block r j := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨k, _hk, hkEq⟩
  exact hij <| (Nat.pair_eq_pair.mp hkEq).1.symm

/-- Paper label: `cor:killo-localization-fixed-cardinality-nonclassification`. -/
theorem paper_killo_localization_fixed_cardinality_nonclassification (r : ℕ) (hr : 1 ≤ r) :
    ∃ S : ℕ → Finset ℕ, (∀ n, (S n).card = r) ∧ Pairwise (fun i j => S i ≠ S j) := by
  refine ⟨killo_localization_fixed_cardinality_nonclassification_block r, ?_, ?_⟩
  · intro n
    exact killo_localization_fixed_cardinality_nonclassification_block_card r n
  · intro i j hij hEq
    have hmem :
        Nat.pair i 0 ∈ killo_localization_fixed_cardinality_nonclassification_block r i :=
      killo_localization_fixed_cardinality_nonclassification_left_endpoint_mem r i hr
    have hmem' :
        Nat.pair i 0 ∈ killo_localization_fixed_cardinality_nonclassification_block r j := by
      simpa [hEq] using hmem
    exact
      killo_localization_fixed_cardinality_nonclassification_left_endpoint_not_mem r i j hij hmem'

end Omega.Folding
