import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/--
Partitioning a finite replay type by its descent count expresses the total count as the sum of
the descent-count fiber cardinalities.

thm:conclusion-zigzag-hstar-strict-refinement-of-replay-count
-/
theorem paper_conclusion_zigzag_hstar_strict_refinement_of_replay_count {σ : Type*}
    [Fintype σ] (des : σ → ℕ) (hstarCoeff : ℕ → ℕ)
    (hcoeff : ∀ k, hstarCoeff k = Fintype.card {x : σ // des x = k}) :
    Fintype.card σ = ∑ k ∈ Finset.univ.image des, hstarCoeff k := by
  classical
  have hpartition :
      Fintype.card σ =
        ∑ k ∈ (Finset.univ : Finset σ).image des,
          Fintype.card {x : σ // des x = k} := by
    calc
      Fintype.card σ = (Finset.univ : Finset σ).card := by simp
      _ = ∑ k ∈ (Finset.univ : Finset σ).image des,
            ((Finset.univ : Finset σ).filter fun x => des x = k).card := by
          simpa using
            (Finset.card_eq_sum_card_image (f := des) (s := (Finset.univ : Finset σ)))
      _ = ∑ k ∈ (Finset.univ : Finset σ).image des,
            Fintype.card {x : σ // des x = k} := by
          refine Finset.sum_congr rfl ?_
          intro k _
          exact (Fintype.card_subtype (p := fun x : σ => des x = k)).symm
  calc
    Fintype.card σ =
        ∑ k ∈ (Finset.univ : Finset σ).image des,
          Fintype.card {x : σ // des x = k} := hpartition
    _ = ∑ k ∈ Finset.univ.image des, hstarCoeff k := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [← hcoeff k]

end Omega.Conclusion
