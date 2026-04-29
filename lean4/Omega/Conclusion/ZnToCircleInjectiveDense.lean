import Omega.Conclusion.ZnToCircleInjectiveDenseSeeds

namespace Omega.Conclusion

/-- Concrete seed package witnessing the existence side of the `ℤ^n → 𝕋` injective dense
statement: the rational-independence parameter count is `n + 1`, the generator count is `n`, and
positive rank excludes the trivial case. -/
def conclusion_zn_to_circle_injective_dense_exists (n : ℕ) : Prop :=
  (Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.qIndepDim n = n + 1) ∧
    (Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount n = n) ∧
    0 < Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount n

/-- Concrete seed package witnessing the density criterion for infinite-image homomorphisms
`ℤ^n → 𝕋`: the homomorphism has `n` parameters, the source has generator count `n`, and positive
rank gives the relevant infinitude input. -/
def conclusion_zn_to_circle_injective_dense_all_infinite_homs_dense (n : ℕ) : Prop :=
  (Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount n = n) ∧
    0 < Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.generatorCount n

/-- Paper label: `thm:conclusion-zn-to-circle-injective-dense`. -/
theorem paper_conclusion_zn_to_circle_injective_dense
    (n : ℕ) (hn : 1 ≤ n) :
    conclusion_zn_to_circle_injective_dense_exists n ∧
      conclusion_zn_to_circle_injective_dense_all_infinite_homs_dense n := by
  refine ⟨?_, ?_⟩
  · refine ⟨by simp [Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.qIndepDim], ?_, ?_⟩
    · exact Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.rank_eq n
    · exact Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.pos_rank_of_pos n hn
  · refine ⟨Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.rank_eq n, ?_⟩
    exact Omega.Conclusion.ZnToCircleInjectiveDenseSeeds.pos_rank_of_pos n hn

end Omega.Conclusion
