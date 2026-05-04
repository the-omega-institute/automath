import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-smith-local-profile-young-hessian-unification`. -/
theorem paper_conclusion_smith_local_profile_young_hessian_unification
    (m : Nat) (e : Fin m -> Nat) :
    (let Delta : Nat -> Nat := fun k =>
      (Finset.univ.filter (fun i : Fin m => k ≤ e i)).card
    (∀ k, Delta (k + 1) ≤ Delta k) ∧
      (∀ l, 1 ≤ l ->
        (Finset.univ.filter (fun i : Fin m => e i = l)).card =
          Delta l - Delta (l + 1))) := by
  dsimp only
  constructor
  · intro k
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact Nat.le_of_succ_le hi
  · intro l _hl
    let A : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => l ≤ e i)
    let B : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => l + 1 ≤ e i)
    have hsub : B ⊆ A := by
      intro i hi
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact Nat.le_of_succ_le hi
    have hset : Finset.univ.filter (fun i : Fin m => e i = l) = A \ B := by
      ext i
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · intro hi
        constructor
        · exact hi.ge
        · omega
      · intro hi
        exact Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge hi.2)) hi.1
    calc
      (Finset.univ.filter (fun i : Fin m => e i = l)).card = (A \ B).card := by
        rw [hset]
      _ = A.card - (B ∩ A).card := Finset.card_sdiff
      _ = A.card - B.card := by
        congr 1
        apply congr_arg Finset.card
        exact Finset.inter_eq_left.mpr hsub

end Omega.Conclusion
