import Mathlib.Tactic

namespace Omega.Conclusion

private lemma conclusion_collision_hierarchy_affine_rank_one_den_ne
    (q : Nat) (hq : 2 <= q) : (2 : Rat) ^ q - 2 ≠ 0 := by
  have hpow : (2 : Rat) ^ 2 <= (2 : Rat) ^ q := by
    exact pow_le_pow_right₀ (by norm_num : (0 : Rat) <= 2) hq
  have hpos : 0 < (2 : Rat) ^ q - 2 := by
    norm_num at hpow ⊢
    linarith
  exact ne_of_gt hpos

/-- Paper label: `prop:conclusion-collision-hierarchy-affine-rank-one`. -/
theorem paper_conclusion_collision_hierarchy_affine_rank_one (S : Nat -> Nat -> Rat)
    (C : Nat -> Rat)
    (hS : forall q n, 2 <= q -> S q n - 2 = (((2 : Rat) ^ q - 2) * C n)) :
    forall q q' n, 2 <= q -> 2 <= q' ->
      S q' n - 2 = (((2 : Rat) ^ q' - 2) / ((2 : Rat) ^ q - 2)) *
        (S q n - 2) := by
  intro q q' n hq hq'
  have hden : (2 : Rat) ^ q - 2 ≠ 0 :=
    conclusion_collision_hierarchy_affine_rank_one_den_ne q hq
  rw [hS q' n hq', hS q n hq]
  field_simp [hden]

end Omega.Conclusion
