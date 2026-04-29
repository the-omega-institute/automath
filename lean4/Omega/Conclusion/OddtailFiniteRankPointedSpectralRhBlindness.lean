import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-oddtail-finite-rank-pointed-spectral-rh-blindness`. -/
theorem paper_conclusion_oddtail_finite_rank_pointed_spectral_rh_blindness
    {Invariant FiniteData : Type*} (dependsOnFiniteData : Invariant → FiniteData → Prop)
    (rhEquivalent : Invariant → Prop)
    (hfiniteBlind : ∀ I D, dependsOnFiniteData I D → ¬ rhEquivalent I) :
    ∀ I D, dependsOnFiniteData I D → ¬ rhEquivalent I := by
  exact hfiniteBlind

end Omega.Conclusion
