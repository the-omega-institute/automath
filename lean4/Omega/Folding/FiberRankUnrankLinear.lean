import Omega.Folding.Fiber

namespace Omega

noncomputable section

/-- Paper-facing wrapper for rank/unrank on a fold fiber.
    This packages the existing inverse maps on `X.fiber x` together with the
    fact that unranking always lands back in the fiber over `x`.
    prop:fold-fiber-rank-unrank-linear -/
theorem paper_fold_fiber_rank_unrank_linear (x : X m) :
    ∃ rank : X.FiberElem x → Fin (X.fiber x).card,
      ∃ unrank : Fin (X.fiber x).card → X.FiberElem x,
        (∀ i, rank (unrank i) = i) ∧
        (∀ w, unrank (rank w) = w) ∧
        (∀ i, Fold (unrank i).1 = x) := by
  refine ⟨X.rank x, X.unrank x, ?_⟩
  constructor
  · intro i
    exact X.rank_unrank x i
  · constructor
    · intro w
      exact X.unrank_rank x w
    · intro i
      exact (X.mem_fiber).1 (X.unrank x i).2

end

end Omega
