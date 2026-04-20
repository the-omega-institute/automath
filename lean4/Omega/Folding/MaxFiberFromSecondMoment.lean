import Omega.Folding.MomentSum

namespace Omega

/-- The second moment is bounded by the number of stable states times the square of the maximal
fiber multiplicity.
    prop:fold-maxfiber-from-second-moment -/
theorem paper_fold_maxfiber_from_second_moment (m : Nat) :
    momentSum 2 m ≤ Nat.fib (m + 2) * X.maxFiberMultiplicity m ^ 2 := by
  unfold momentSum
  calc
    ∑ x : X m, X.fiberMultiplicity x ^ 2
      ≤ ∑ _x : X m, X.maxFiberMultiplicity m ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact Nat.pow_le_pow_left (X.fiberMultiplicity_le_max x) 2
    _ = Nat.fib (m + 2) * X.maxFiberMultiplicity m ^ 2 := by
          simp [X.card_eq_fib]

/-- The maximal fiber contributes one summand to the second moment, so its square is bounded by
the full collision moment.
    thm:fold-collision-max-fiber -/
theorem paper_fold_collision_max_fiber (m : ℕ) : (X.maxFiberMultiplicity m) ^ 2 ≤ momentSum 2 m := by
  obtain ⟨x, hx⟩ := X.maxFiberMultiplicity_achieved m
  calc
    X.maxFiberMultiplicity m ^ 2 = X.fiberMultiplicity x ^ 2 := by rw [hx]
    _ ≤ ∑ y : X m, X.fiberMultiplicity y ^ 2 :=
      Finset.single_le_sum (f := fun y => X.fiberMultiplicity y ^ 2)
        (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
    _ = momentSum 2 m := rfl

end Omega
