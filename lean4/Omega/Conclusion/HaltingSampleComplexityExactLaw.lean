import Omega.Conclusion.HaltingTvSpectralEmbeddingOn2adicAttractor

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `cor:conclusion-halting-sample-complexity-exact-law`. -/
theorem paper_conclusion_halting_sample_complexity_exact_law
    (D : conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data) (N : ℕ) :
    (let δ := D.totalVariation; ((1 - δ) ^ N) / 2) =
      (match D.haltingTime with
      | none => ((1 - 0) ^ N) / 2
      | some t =>
          ((1 - conclusion_halting_tv_spectral_embedding_on_2adic_attractor_tail t) ^ N) /
            2) := by
  cases hτ : D.haltingTime with
  | none =>
      simp [hτ, conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.totalVariation,
        conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.commonMass]
  | some t =>
      simp [hτ, conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.totalVariation,
        conclusion_halting_tv_spectral_embedding_on_2adic_attractor_data.commonMass]

end
end Omega.Conclusion
