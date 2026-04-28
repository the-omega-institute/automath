import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-oddtail-arithmetic-sensitivity-infinite-rank-threshold`.
Finite-rank RH-blindness rules out any finite-rank compressor factorization of an
RH-equivalent criterion, and the designated operator supplies the infinite-rank witness. -/
theorem paper_conclusion_oddtail_arithmetic_sensitivity_infinite_rank_threshold
    {Criterion Compressor «Operator» : Type*} (finiteRankCompressor : Compressor → Prop)
    (factorsThrough : Criterion → Compressor → Prop) (rhEquivalent : Criterion → Prop)
    (finiteRank : «Operator» → Prop) (K_RH : «Operator»)
    (hblind : ∀ C F, finiteRankCompressor F → factorsThrough C F → ¬ rhEquivalent C)
    (hinfinite : ¬ finiteRank K_RH) :
    (∀ C F, finiteRankCompressor F → rhEquivalent C → ¬ factorsThrough C F) ∧
      ¬ finiteRank K_RH := by
  refine ⟨?_, hinfinite⟩
  intro C F hfinite hrh hfactors
  exact hblind C F hfinite hfactors hrh

end Omega.Conclusion
