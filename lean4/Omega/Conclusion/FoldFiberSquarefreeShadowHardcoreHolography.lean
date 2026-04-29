import Omega.Conclusion.FoldFiberFaceposetSquarefreeDivisibilityShadow

open scoped BigOperators

namespace Omega

lemma conclusion_fold_fiber_squarefree_shadow_hardcore_holography_product_injective
    {V : Type*} [Fintype V] [DecidableEq V] (q : V → ℕ) (hqprime : ∀ v, Nat.Prime (q v))
    (hqinj : Function.Injective q) :
    Function.Injective fun I : Finset V => ∏ v ∈ I, q v := by
  classical
  intro I J hIJ
  have hdvdIJ : (∏ v ∈ I, q v) ∣ ∏ v ∈ J, q v := by
    change (fun K : Finset V => ∏ v ∈ K, q v) I ∣
      (fun K : Finset V => ∏ v ∈ K, q v) J
    rw [hIJ]
  have hdvdJI : (∏ v ∈ J, q v) ∣ ∏ v ∈ I, q v := by
    change (fun K : Finset V => ∏ v ∈ K, q v) J ∣
      (fun K : Finset V => ∏ v ∈ K, q v) I
    rw [← hIJ]
  have hsubIJ :=
    ((paper_conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow q hqprime hqinj
      I J).1).2 hdvdIJ
  have hsubJI :=
    ((paper_conclusion_fold_fiber_faceposet_squarefree_divisibility_shadow q hqprime hqinj
      J I).1).2 hdvdJI
  exact Finset.Subset.antisymm hsubIJ hsubJI

theorem paper_conclusion_fold_fiber_squarefree_shadow_hardcore_holography
    {V : Type*} [Fintype V] [DecidableEq V] (q : V → ℕ) (hqprime : ∀ v, Nat.Prime (q v))
    (hqinj : Function.Injective q) (r : ℕ) :
    (((Finset.univ : Finset (Finset V)).filter (fun I => I.card = r)).card =
      (((Finset.univ : Finset (Finset V)).image (fun I => ∏ v ∈ I, q v)).filter
        (fun n => ∃ I : Finset V, I.card = r ∧ n = ∏ v ∈ I, q v)).card) := by
  classical
  let U : Finset (Finset V) := Finset.univ
  let f : Finset V → ℕ := fun I => ∏ v ∈ I, q v
  have hfilter :
      ((U.image f).filter (fun n => ∃ I : Finset V, I.card = r ∧ n = f I)) =
        (U.filter fun I => I.card = r).image f := by
    ext n
    simp [U, f]
    constructor
    · intro h
      rcases h with ⟨_, I, hcard, hn⟩
      exact ⟨I, hcard, hn.symm⟩
    · intro h
      rcases h with ⟨I, hcard, hn⟩
      exact ⟨⟨I, hn⟩, I, hcard, hn.symm⟩
  rw [hfilter, Finset.card_image_of_injective]
  exact conclusion_fold_fiber_squarefree_shadow_hardcore_holography_product_injective q hqprime
    hqinj

end Omega
