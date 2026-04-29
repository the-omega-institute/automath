import Mathlib.Tactic
import Omega.Folding.Fiber

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-fold-collision-resolvent-finite-pole`.
The collision moment decomposes by grouping stable words according to their fiber multiplicity. -/
theorem paper_conclusion_fold_collision_resolvent_finite_pole (m q : ℕ) :
    (∑ x : Omega.X m, Omega.X.fiberMultiplicity x ^ q) =
      ∑ d ∈
        (Finset.univ.image (fun x : Omega.X m => Omega.X.fiberMultiplicity x)),
        (Fintype.card {x : Omega.X m // Omega.X.fiberMultiplicity x = d}) * d ^ q := by
  classical
  let f : Omega.X m → ℕ := fun x => Omega.X.fiberMultiplicity x
  calc
    ∑ x : Omega.X m, Omega.X.fiberMultiplicity x ^ q =
        ∑ x : Omega.X m, f x ^ q := rfl
    _ = ∑ d ∈ (Finset.univ.image f), ∑ x ∈ (Finset.univ.filter fun x => f x = d),
          d ^ q := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (Omega.X m))) (t := Finset.univ.image f)
          (g := f) (f := fun x => f x ^ q) (fun x hx => Finset.mem_image_of_mem f hx)]
        refine Finset.sum_congr rfl ?_
        intro d hd
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact congrArg (fun a => a ^ q) (Finset.mem_filter.mp hx).2
    _ = ∑ d ∈ (Finset.univ.image f),
        (Fintype.card {x : Omega.X m // Omega.X.fiberMultiplicity x = d}) * d ^ q := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        simp [f, Fintype.card_subtype]

end

end Omega.Conclusion
