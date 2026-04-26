import Omega.POM.HankelSyndromeModuleRankAndGenerators

namespace Omega.POM

/-- Paper label: `cor:pom-hankel-syndrome-hnf-unique`.
The standard-basis generators are the canonical column-HNF representative in the concrete
rank-and-generators model, and the explicit equality clause gives uniqueness. -/
theorem paper_pom_hankel_syndrome_hnf_unique (n d : ℕ) (hd : d ≤ n) :
    ∃! B : Fin (n - d) → pom_hankel_syndrome_module_rank_and_generators_module n d,
      B = pom_hankel_syndrome_module_rank_and_generators_generators n d hd ∧
      LinearIndependent ℤ B ∧
      Submodule.span ℤ (Set.range B) = ⊤ := by
  let G := pom_hankel_syndrome_module_rank_and_generators_generators n d hd
  rcases paper_pom_hankel_syndrome_module_rank_and_generators n d hd with
    ⟨hlin, hspan, _hcard⟩
  refine ⟨G, ?_, ?_⟩
  · exact ⟨rfl, hlin, hspan⟩
  · intro B hB
    exact hB.1

end Omega.POM
