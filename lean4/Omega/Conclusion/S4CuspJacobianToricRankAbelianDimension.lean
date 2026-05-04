import Omega.Conclusion.S4CuspStableLimitNormalizationNodeGenus

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-s4-cusp-jacobian-toric-rank-abelian-dimension`. -/
theorem paper_conclusion_s4_cusp_jacobian_toric_rank_abelian_dimension
    (tail nodes b1 main toricRank abelianDim : Fin 3 → ℕ)
    (htail : tail 0 = 12 ∧ tail 1 = 6 ∧ tail 2 = 4)
    (hnodes : nodes 0 = 24 ∧ nodes 1 = 12 ∧ nodes 2 = 8)
    (hb1 : ∀ i, b1 i = nodes i - tail i) (hmain : ∀ i, main i + b1 i = 16)
    (htoric : ∀ i, toricRank i = b1 i) (habel : ∀ i, abelianDim i = main i) :
    toricRank 0 = 12 ∧ toricRank 1 = 6 ∧ toricRank 2 = 4 ∧
      abelianDim 0 = 4 ∧ abelianDim 1 = 10 ∧ abelianDim 2 = 12 := by
  rcases paper_conclusion_s4_cusp_stable_limit_normalization_node_genus tail nodes b1 main
      htail hnodes hb1 hmain with
    ⟨hb10, hb11, hb12, hmain0, hmain1, hmain2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htoric 0, hb10]
  · rw [htoric 1, hb11]
  · rw [htoric 2, hb12]
  · rw [habel 0, hmain0]
  · rw [habel 1, hmain1]
  · rw [habel 2, hmain2]

end Omega.Conclusion
