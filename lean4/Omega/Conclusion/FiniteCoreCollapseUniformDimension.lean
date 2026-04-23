import Omega.Conclusion.CofinalSparsificationSemanticCompleteness
import Omega.Zeta.XiOracleCollapseToeplitzPsdFiniteTruncation

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-core-collapse-uniform-dimension`. The bounded Toeplitz
cutoff from the oracle-collapse package combines with cofinal semantic completeness to collapse
the two-parameter inverse system to a fixed finite core and any cofinal depth chain. -/
theorem paper_conclusion_finite_core_collapse_uniform_dimension
    (D : Omega.Zeta.XiOracleCollapseToeplitzPsdData)
    (S : Omega.Conclusion.ConclusionCofinalSparsificationSemanticCompletenessData)
    (hbound : S.dimensionBound = D.uniformBound) :
    ∃ N0 ≤ 2 * D.uniformBound,
      D.finiteTruncationEquivalent N0 ∧ S.cofinalReconstruction ∧ S.finiteLevelDetermination := by
  let _ := hbound
  rcases Omega.Zeta.paper_xi_oracle_collapse_toeplitz_psd_finite_truncation D with
    ⟨N0, hN0, hFiniteTruncation, _hWitness⟩
  rcases Omega.Conclusion.paper_conclusion_cofinal_sparsification_semantic_completeness S with
    ⟨hCofinal, hFiniteLevel⟩
  exact ⟨N0, hN0, hFiniteTruncation, hCofinal, hFiniteLevel⟩

end Omega.Conclusion
